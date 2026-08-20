#!/usr/bin/env python3
"""Generate one bounded DF6D4 fixed-grid row shard and its Lean checkers."""

from __future__ import annotations

import argparse
import subprocess
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("index", type=int)
    parser.add_argument("--lake", required=True, type=Path)
    return parser.parse_args()


def parse_blocks(output: str) -> dict[str, list[tuple[int, int]]]:
    blocks: dict[str, list[tuple[int, int]]] = {}
    current: str | None = None
    for raw_line in output.splitlines():
        line = raw_line.strip()
        if line.startswith("BEGIN "):
            current = line[6:]
            blocks[current] = []
        elif line.startswith("END "):
            if current != line[4:]:
                raise ValueError(f"mismatched block terminator: {line}")
            current = None
        elif current is not None:
            lower, upper = line.split(",", maxsplit=1)
            blocks[current].append((int(lower), int(upper)))
    if current is not None:
        raise ValueError(f"unterminated block: {current}")
    return blocks


def render_array(name: str, entries: list[tuple[int, int]]) -> str:
    body = ",\n".join(
        f"  {{ lower := {lower}, upper := {upper} }}"
        for lower, upper in entries
    )
    return f"def {name} : Array FixedGridInterval := #[\n{body}\n]\n"


def names(index: int) -> dict[str, str]:
    tag = f"{index:03d}"
    return {
        key: f"suzukiDF6D4FixedGridShard{tag}{key[0].upper()}{key[1:]}Data"
        for key in (
            "evenComparison", "evenCross", "evenSolve",
            "oddComparison", "oddCross", "oddSolve",
            "evenResidualComparison", "evenFull", "evenResidual",
            "oddResidualComparison", "oddFull", "oddResidual",
        )
    }


def render_data(index: int, blocks: dict[str, list[tuple[int, int]]]) -> str:
    ns = names(index)
    arrays = "\n\n".join(render_array(ns[key], value)
                           for key, value in blocks.items())
    return f"""import RiemannHypothesisProject.Experiments.M100.FixedGridIntervalArithmetic

/-! Generated fixed-grid row shard {index}; checked by separate Stage-0/1 modules. -/
namespace RiemannHypothesisProject.Experiments.M100

{arrays}

end RiemannHypothesisProject.Experiments.M100
"""


def render_stage0(index: int, data_module: str) -> str:
    ns = names(index)
    mode = 301 + index
    solve = ""
    solve_goal = "True"
    if index < 256:
        solve = f"""
private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval {index} k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i {index})
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval {index} k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i {index})
"""
        solve_goal = f"""{ns["evenComparison"]} = liveEvenComparison /\\
    {ns["evenCross"]} = liveEvenCross /\\
    {ns["oddComparison"]} = liveOddComparison /\\
    {ns["oddCross"]} = liveOddCross"""
    return f"""import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import {data_module}

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I
{solve}
private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) {mode})
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) {mode})
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) {mode})
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) {mode})

theorem suzukiDF6D4FixedGridShard{index:03d}Stage0_valid :
    ({solve_goal}) /\\
    {ns["evenResidualComparison"]} = liveEvenResidualComparison /\\
    {ns["evenFull"]} = liveEvenFull /\\
    {ns["oddResidualComparison"]} = liveOddResidualComparison /\\
    {ns["oddFull"]} = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
"""


def render_stage1(index: int, data_module: str) -> str:
    ns = names(index)
    solve_defs = ""
    solve_goal = "True"
    if index < 256:
        solve_defs = f"""
private def evenSolve := Array.ofFn fun i : Fin 45 =>
  ({ns["evenCross"]}[i.val]!).sub (evenDot i.val {ns["evenComparison"]})
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  ({ns["oddCross"]}[i.val]!).sub (oddDot i.val {ns["oddComparison"]})
"""
        solve_goal = f"""{ns["evenSolve"]} = evenSolve /\\
    {ns["oddSolve"]} = oddSolve"""
    return f"""import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import {data_module}

namespace RiemannHypothesisProject.Experiments.M100
private def coefficientDenominator : Nat := 1000000000000000000000000
private def evenNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)
private def oddNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4OddGalerkinApproximantData[k * 44 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)
private def evenDot (i : Nat) (a : Array FixedGridInterval) :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenNumerator k i) (fun k => a[k.val]!)
private def oddDot (i : Nat) (a : Array FixedGridInterval) :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => oddNumerator k i) (fun k => a[k.val]!)
{solve_defs}
private def evenResidual := Array.ofFn fun i : Fin 45 =>
  ({ns["evenFull"]}[i.val]!).sub
    (evenDot i.val {ns["evenResidualComparison"]})
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  ({ns["oddFull"]}[i.val]!).sub
    (oddDot i.val {ns["oddResidualComparison"]})

theorem suzukiDF6D4FixedGridShard{index:03d}Stage1_valid :
    ({solve_goal}) /\\
    {ns["evenResidual"]} = evenResidual /\\
    {ns["oddResidual"]} = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
"""


def main() -> int:
    args = parse_args()
    if not 0 <= args.index < 300:
        raise ValueError("index must be in 0..299")
    root = Path(__file__).resolve().parents[3]
    exporter = root / "tools/experiments/m100/df6d4_fixed_grid_row_shard_materializer.lean"
    result = subprocess.run(
        [str(args.lake), "env", "lean", "--run", str(exporter), str(args.index)],
        cwd=root, capture_output=True, text=True, check=False,
    )
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    blocks = parse_blocks(result.stdout)
    stem = f"SuzukiEndpointGalerkinResidualFixedGridShard{args.index:03d}"
    module = f"RiemannHypothesisProject.Experiments.M100.{stem}Data"
    base = root / "RiemannHypothesisProject/Experiments/M100"
    (base / f"{stem}Data.lean").write_text(
        render_data(args.index, blocks), encoding="utf-8")
    (base / f"{stem}Stage0Check.lean").write_text(
        render_stage0(args.index, module), encoding="utf-8")
    (base / f"{stem}Stage1Check.lean").write_text(
        render_stage1(args.index, module), encoding="utf-8")
    print(f"index={args.index}")
    print(f"blocks={','.join(blocks)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
