#!/usr/bin/env python3
"""Generate and verify bounded DF6D4 fixed-grid soundness adapter batches."""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


MODULE_STEM = "SuzukiEndpointGalerkinResidualFixedGridShard{index:03d}Soundness"
SHARED_STEM = "SuzukiEndpointGalerkinResidualFixedGridSoundness"
FULL_TEMPLATE_INDEX = 3
FULL_TEMPLATE_MODE = 304
RESIDUAL_TEMPLATE_INDEX = 256
RESIDUAL_TEMPLATE_MODE = 557
MANIFEST = "EXPERIMENTS/M100_DF6D4_SOUNDNESS_ADAPTER_MANIFEST.json"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--start", required=True, type=int)
    parser.add_argument("--stop", required=True, type=int)
    parser.add_argument("--max-seconds", type=float, default=3600.0)
    return parser.parse_args()


def timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_manifest(path: Path) -> dict:
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return {
        "schema": 1,
        "track": "M100-DF6D4-fixed-grid-soundness-adapters",
        "entries": {},
        "last_stop": None,
    }


def save_manifest(path: Path, manifest: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    os.replace(temporary, path)


def render_adapter(
    template: str, index: int, template_index: int, template_mode: int
) -> str:
    mode = 301 + index
    rendered = template.replace(
        f"Shard{template_index:03d}", f"Shard{index:03d}"
    )
    rendered = re.sub(rf"\b{template_mode}\b", str(mode), rendered)
    if template_index < 256:
        rendered = re.sub(rf"\b{template_index}\b", str(index), rendered)
    return rendered


def compile_module(
    root: Path, lake: Path, source: Path, module_stem: str
) -> None:
    relative_stem = Path("RiemannHypothesisProject/Experiments/M100") / module_stem
    output = root / ".lake/build/lib/lean" / relative_stem.with_suffix(".olean")
    interface = root / ".lake/build/lib/lean" / relative_stem.with_suffix(".ilean")
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [
        str(lake),
        "env",
        "lean",
        str(source.relative_to(root)),
        "-o",
        str(output.relative_to(root)),
        "-i",
        str(interface.relative_to(root)),
    ]
    environment = os.environ.copy()
    environment["GIT_CONFIG_COUNT"] = "1"
    environment["GIT_CONFIG_KEY_0"] = "safe.directory"
    environment["GIT_CONFIG_VALUE_0"] = "*"
    subprocess.run(command, cwd=root, env=environment, check=True)


def ensure_shared_module(root: Path, lake: Path, module_dir: Path) -> None:
    source = module_dir / f"{SHARED_STEM}.lean"
    output = (
        root
        / ".lake/build/lib/lean/RiemannHypothesisProject/Experiments/M100"
        / f"{SHARED_STEM}.olean"
    )
    if output.exists() and output.stat().st_mtime >= source.stat().st_mtime:
        return
    print("shared=start", flush=True)
    compile_module(root, lake, source, SHARED_STEM)
    print("shared=verified", flush=True)


def ensure_shard_inputs(
    root: Path, lake: Path, module_dir: Path, index: int
) -> None:
    base = f"SuzukiEndpointGalerkinResidualFixedGridShard{index:03d}"
    for suffix in ("Data", "Stage0Check", "Stage1Check"):
        module_stem = base + suffix
        source = module_dir / f"{module_stem}.lean"
        output = (
            root
            / ".lake/build/lib/lean/RiemannHypothesisProject/Experiments/M100"
            / f"{module_stem}.olean"
        )
        if output.exists() and output.stat().st_mtime >= source.stat().st_mtime:
            continue
        print(f"input={index:03d}:{suffix}:start", flush=True)
        compile_module(root, lake, source, module_stem)
        print(f"input={index:03d}:{suffix}:verified", flush=True)


def main() -> int:
    args = parse_args()
    if not 4 <= args.start <= args.stop <= 299:
        raise ValueError("adapter batches must stay within managed shards 004..299")
    if args.max_seconds < 0:
        raise ValueError("max-seconds must be nonnegative")

    root = Path(__file__).resolve().parents[3]
    module_dir = root / "RiemannHypothesisProject/Experiments/M100"
    full_template_path = (
        module_dir / MODULE_STEM.format(index=FULL_TEMPLATE_INDEX)
    ).with_suffix(".lean")
    residual_template_path = (
        module_dir / MODULE_STEM.format(index=RESIDUAL_TEMPLATE_INDEX)
    ).with_suffix(".lean")
    full_template = full_template_path.read_text(encoding="utf-8")
    residual_template = residual_template_path.read_text(encoding="utf-8")
    manifest_path = root / MANIFEST
    manifest = load_manifest(manifest_path)
    ensure_shared_module(root, args.lake, module_dir)
    started = time.monotonic()

    for index in range(args.start, args.stop + 1):
        key = f"{index:03d}"
        if manifest["entries"].get(key, {}).get("status") == "verified":
            print(f"skip={key}", flush=True)
            continue
        if time.monotonic() - started >= args.max_seconds:
            manifest["last_stop"] = {
                "reason": "time-budget",
                "next_index": index,
                "timestamp": timestamp(),
            }
            save_manifest(manifest_path, manifest)
            print(f"stop=time-budget next={key}", flush=True)
            return 0

        module_stem = MODULE_STEM.format(index=index)
        source = module_dir / f"{module_stem}.lean"
        ensure_shard_inputs(root, args.lake, module_dir, index)
        if index < 256:
            rendered = render_adapter(
                full_template, index, FULL_TEMPLATE_INDEX, FULL_TEMPLATE_MODE
            )
        else:
            rendered = render_adapter(
                residual_template,
                index,
                RESIDUAL_TEMPLATE_INDEX,
                RESIDUAL_TEMPLATE_MODE,
            )
        source.write_text(rendered, encoding="utf-8")
        print(f"start={key}", flush=True)
        shard_started = time.monotonic()
        try:
            compile_module(root, args.lake, source, module_stem)
        except subprocess.CalledProcessError as error:
            manifest["entries"][key] = {
                "status": "failed",
                "timestamp": timestamp(),
                "returncode": error.returncode,
            }
            manifest["last_stop"] = {
                "reason": "failure",
                "next_index": index,
                "timestamp": timestamp(),
            }
            save_manifest(manifest_path, manifest)
            raise
        elapsed = time.monotonic() - shard_started
        manifest["entries"][key] = {
            "status": "verified",
            "elapsed_seconds": round(elapsed, 3),
            "timestamp": timestamp(),
        }
        manifest["last_stop"] = {
            "reason": "checkpoint",
            "next_index": index + 1,
            "timestamp": timestamp(),
        }
        save_manifest(manifest_path, manifest)
        print(f"verified={key} seconds={elapsed:.3f}", flush=True)

    manifest["last_stop"] = {
        "reason": "completed-range",
        "next_index": args.stop + 1,
        "timestamp": timestamp(),
    }
    save_manifest(manifest_path, manifest)
    print(f"completed={args.start:03d}..{args.stop:03d}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
