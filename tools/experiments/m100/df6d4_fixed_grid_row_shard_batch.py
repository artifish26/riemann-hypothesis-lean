#!/usr/bin/env python3
"""Generate and verify DF6D4 fixed-grid row shards with a resumable manifest."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, required=True)
    parser.add_argument("--end", type=int, required=True,
                        help="inclusive final shard index")
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--manifest", required=True, type=Path)
    parser.add_argument(
        "--max-seconds",
        type=float,
        help="stop before starting another shard after this wall-clock budget",
    )
    return parser.parse_args()


def run_timed(command: list[str], cwd: Path) -> tuple[float, str]:
    started = time.perf_counter()
    result = subprocess.run(
        command, cwd=cwd, capture_output=True, text=True, check=False,
    )
    elapsed = time.perf_counter() - started
    if result.returncode:
        raise RuntimeError(
            f"command failed ({result.returncode}): {' '.join(command)}\n"
            f"{result.stdout}\n{result.stderr}"
        )
    return elapsed, result.stdout


def load_manifest(path: Path) -> dict:
    if not path.exists():
        return {
            "experiment": "M100-DF6D4",
            "artifact": "fixed-grid-row-shard-completion-manifest",
            "schema_version": 1,
            "shards": {},
        }
    return json.loads(path.read_text(encoding="utf-8"))


def save_manifest(path: Path, manifest: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def module_name(index: int, stage: int) -> str:
    return (
        "RiemannHypothesisProject.Experiments.M100."
        f"SuzukiEndpointGalerkinResidualFixedGridShard{index:03d}"
        f"Stage{stage}Check"
    )


def main() -> int:
    args = parse_args()
    if not 0 <= args.start <= args.end < 300:
        raise ValueError("require 0 <= start <= end < 300")
    root = Path(__file__).resolve().parents[3]
    manifest_path = args.manifest
    if not manifest_path.is_absolute():
        manifest_path = root / manifest_path
    manifest = load_manifest(manifest_path)
    run_started = time.perf_counter()
    generator = (
        root / "tools/experiments/m100/"
        "df6d4_fixed_grid_row_shard_materializer.py"
    )

    # Prevent lean --run from loading a stale exporter dependency.
    dependency_elapsed, _ = run_timed(
        [
            str(args.lake), "build",
            "RiemannHypothesisProject.Experiments.M100."
            "SuzukiEndpointGalerkinResidualFixedGridCell",
        ],
        root,
    )
    manifest["dependency_build_seconds"] = round(dependency_elapsed, 3)
    manifest["lake"] = str(args.lake)

    for index in range(args.start, args.end + 1):
        key = f"{index:03d}"
        if manifest["shards"].get(key, {}).get("status") == "verified":
            print(f"skip={key}", flush=True)
            continue
        if (
            args.max_seconds is not None
            and time.perf_counter() - run_started >= args.max_seconds
        ):
            elapsed = time.perf_counter() - run_started
            manifest["last_stop"] = {
                "reason": "time-budget",
                "elapsed_seconds": round(elapsed, 3),
                "next_index": index,
                "max_seconds": args.max_seconds,
                "stopped_at_utc": datetime.now(timezone.utc).isoformat(),
            }
            save_manifest(manifest_path, manifest)
            print(
                f"stop=time-budget elapsed={elapsed:.1f}s next={index:03d}",
                flush=True,
            )
            break
        try:
            generate_elapsed, generator_output = run_timed(
                [
                    sys.executable, str(generator), str(index),
                    "--lake", str(args.lake),
                ],
                root,
            )
            stage0_elapsed, _ = run_timed(
                [str(args.lake), "build", module_name(index, 0)],
                root,
            )
            stage1_elapsed, _ = run_timed(
                [str(args.lake), "build", module_name(index, 1)],
                root,
            )
            manifest["shards"][key] = {
                "status": "verified",
                "kind": "solve-and-residual" if index < 256 else "residual-only",
                "residual_mode": 301 + index,
                "generated_blocks": generator_output.strip().splitlines()[-1],
                "generation_seconds": round(generate_elapsed, 3),
                "stage0_build_seconds": round(stage0_elapsed, 3),
                "stage1_build_seconds": round(stage1_elapsed, 3),
                "verified_at_utc": datetime.now(timezone.utc).isoformat(),
            }
            save_manifest(manifest_path, manifest)
            print(
                f"verified={key} generation={generate_elapsed:.1f}s "
                f"stage0={stage0_elapsed:.1f}s stage1={stage1_elapsed:.1f}s",
                flush=True,
            )
        except Exception as error:
            manifest["shards"][key] = {
                "status": "failed",
                "error": str(error),
                "failed_at_utc": datetime.now(timezone.utc).isoformat(),
            }
            save_manifest(manifest_path, manifest)
            raise

    manifest["last_completed_run_utc"] = datetime.now(timezone.utc).isoformat()
    save_manifest(manifest_path, manifest)
    print(f"manifest={manifest_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
