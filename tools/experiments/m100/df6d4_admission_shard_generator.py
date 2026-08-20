#!/usr/bin/env python3
"""Generate the bounded Lean admission shards for M100-DF6D4.

Each row is checked in its own module so Lake can retain the successful
native_decide result without rebuilding one monolithic all-entry decision.
The generated assembly module combines the row theorems without performing
any further certificate computation.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


MODULE_STEM = (
    "RiemannHypothesisProject.Experiments.M100."
    "SuzukiEndpointGalerkinResidualRoundedCertificateAdmission"
)
FILE_STEM = "SuzukiEndpointGalerkinResidualRoundedCertificateAdmission"
BASE_MODULE = (
    "RiemannHypothesisProject.Experiments.M100."
    "SuzukiEndpointGalerkinResidualRoundedCertificateEnclosures"
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="directory receiving the generated Lean modules",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail instead of writing if a generated module is stale",
    )
    return parser.parse_args()


def row_module(parity: str, dimension: int, row: int) -> str:
    lower = parity.lower()
    return f"""import {BASE_MODULE}

/-! Exact admission check for {lower} residual-certificate row `{row}`. -/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem suzukiDF6D4{parity}RoundedResidualTargetEntryIntervals_admitted_row{row:02d} :
    let solveResidual := suzukiDF6D4{parity}RoundedSolveResidualIntervalCache
    let residualColumn := suzukiDF6D4{parity}RoundedResidualColumnIntervalCache
    forall j : Fin {dimension},
      suzukiDF6D4{parity}RoundedResidualTargetEntryIntervalAdmittedFromCaches
        solveResidual residualColumn {row} j := by
  unfold suzukiDF6D4{parity}RoundedResidualTargetEntryIntervalAdmittedFromCaches
  native_decide

end RiemannHypothesisProject.Experiments.M100
"""


def assembly_theorem(parity: str, dimension: int) -> str:
    cases = "\n".join(
        "    | exact "
        f"suzukiDF6D4{parity}RoundedResidualTargetEntryIntervals_admitted_row{row:02d} j"
        for row in range(dimension)
    )
    return f"""theorem suzukiDF6D4{parity}RoundedResidualTargetEntryIntervals_admitted :
    let solveResidual := suzukiDF6D4{parity}RoundedSolveResidualIntervalCache
    let residualColumn := suzukiDF6D4{parity}RoundedResidualColumnIntervalCache
    forall i j : Fin {dimension},
      suzukiDF6D4{parity}RoundedResidualTargetEntryIntervalAdmittedFromCaches
        solveResidual residualColumn i j := by
  dsimp only
  intro i j
  fin_cases i <;>
  first
{cases}
"""


def assembly_module() -> str:
    imports = "\n".join(
        f"import {MODULE_STEM}{parity}Row{row:02d}"
        for parity, dimension in (("Even", 45), ("Odd", 44))
        for row in range(dimension)
    )
    return f"""{imports}

/-!
# Assembled exact admission checks for the M100-DF6D4 residual certificates

The proof below only dispatches finite row indices to independently compiled
row theorems.  All expensive exact decisions remain in the retained shards.
-/

namespace RiemannHypothesisProject.Experiments.M100

{assembly_theorem("Even", 45)}
{assembly_theorem("Odd", 44)}
end RiemannHypothesisProject.Experiments.M100
"""


def expected_files(output_dir: Path) -> dict[Path, str]:
    files = {
        output_dir / f"{FILE_STEM}{parity}Row{row:02d}.lean":
            row_module(parity, dimension, row)
        for parity, dimension in (("Even", 45), ("Odd", 44))
        for row in range(dimension)
    }
    files[output_dir / f"{FILE_STEM}.lean"] = assembly_module()
    return files


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[3]
    output_dir = args.output_dir or (
        repo_root / "RiemannHypothesisProject" / "Experiments" / "M100"
    )
    if not output_dir.is_absolute():
        output_dir = repo_root / output_dir

    files = expected_files(output_dir)
    stale = [
        path
        for path, content in files.items()
        if not path.exists() or path.read_text(encoding="utf-8") != content
    ]
    if args.check:
        if stale:
            print(json.dumps({"stale": [str(path) for path in stale]}, indent=2))
            return 1
    else:
        output_dir.mkdir(parents=True, exist_ok=True)
        for path in stale:
            content = files[path]
            path.write_text(content, encoding="utf-8", newline="\n")

    print(
        json.dumps(
            {
                "experiment": "M100-DF6D4",
                "artifact": "lean-admission-row-shards",
                "even_rows": 45,
                "odd_rows": 44,
                "assembly": str(output_dir / f"{FILE_STEM}.lean"),
                "written": 0 if args.check else len(stale),
                "check_pass": not stale if args.check else True,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
