#!/usr/bin/env python3
"""Render the bounded even DF6D4 fixed-grid Stage-2 row-00 prototype."""

from __future__ import annotations

from pathlib import Path


MODULE = "SuzukiEndpointGalerkinResidualFixedGridStage2Row00Prototype"


def shard_import(index: int) -> str:
    stem = "SuzukiEndpointGalerkinResidualFixedGridShard"
    return (
        "import RiemannHypothesisProject.Experiments.M100."
        f"{stem}{index:03d}Data"
    )


def solve_row(index: int) -> str:
    if index == 0:
        return "suzukiDF6D4FixedGridStage1SolveRow00Data"
    if index == 1:
        return "suzukiDF6D4FixedGridStage1SolveRow01Data"
    return f"suzukiDF6D4FixedGridShard{index:03d}EvenSolveData"


def residual_row(index: int) -> str:
    if index == 0:
        return "suzukiDF6D4FixedGridStage1ResidualRow301Data"
    if index == 1:
        return "suzukiDF6D4FixedGridStage1ResidualRow302Data"
    return f"suzukiDF6D4FixedGridShard{index:03d}EvenResidualData"


def match_body(count: int, row_name) -> str:
    cases = "\n".join(
        f"    | {index} => {row_name(index)}[column.val]!"
        for index in range(count)
    )
    return cases + "\n    | _ => default"


def render() -> str:
    imports = "\n".join(shard_import(index) for index in range(2, 300))
    solve_cases = match_body(256, solve_row)
    residual_cases = match_body(300, residual_row)
    return f"""{imports}
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStageData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Bounded fixed-grid Stage-2 row-00 efficacy prototype

This module assembles one complete even target row from already materialized
Stage-1 shard literals. It performs no analytic shard regeneration.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def fixedGridDenominator : Nat := 1000000000000000000
private def coefficientDenominator : Nat := 1000000000000000000000000

private def evenCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def solveEntry (row : Fin 256) (column : Fin 45) :
    FixedGridInterval :=
  match row.val with
{solve_cases}

private def residualEntry (row : Fin 300) (column : Fin 45) :
    FixedGridInterval :=
  match row.val with
{residual_cases}

private def dotForColumn
    (i : Nat) (entries : Fin 256 -> FixedGridInterval) :
    FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenCoefficientNumerator k i) entries

private def galerkinBaseRow00 (j : Fin 45) : FixedGridInterval :=
  (dotForColumn j.val fun k : Fin 256 =>
    FixedGridInterval.ofRationalInterval fixedGridDenominator
      (suzukiDF6D4EvenCompleteCrossEntryInterval 0 k)).add
  (dotForColumn 0 fun k : Fin 256 => solveEntry k j)

private def finiteResidualGramRow00 (j : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun k : Fin 256 => solveEntry k 0)
    (fun k : Fin 256 => solveEntry k j)).add
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun r : Fin 300 => residualEntry r 0)
    (fun r : Fin 300 => residualEntry r j))

private def targetRow00 (j : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.scale
    (19 / 1000 * (1 - 1 / 1000000000) : Rat)
    (FixedGridInterval.ofRationalInterval fixedGridDenominator
      (suzukiDF6D4EvenEndpointEntryInterval 0 j))).sub
  (((galerkinBaseRow00 j).add
    (FixedGridInterval.scale (1 / 5 : Rat)
      (finiteResidualGramRow00 j))).add
    (FixedGridInterval.scale (1 / 5 : Rat)
      (FixedGridInterval.ofRationalInterval fixedGridDenominator
        (suzukiDF6D4EvenAnalyticTailEntryInterval 0 j))))

theorem suzukiDF6D4FixedGridEvenStage2Row00_admitted :
    forall j : Fin 45,
      (suzukiDF6D4EvenResidualTargetCertificate.entry 0 j).lower <=
          (FixedGridInterval.toRationalInterval fixedGridDenominator
            (targetRow00 j)).lower /\\
        (FixedGridInterval.toRationalInterval fixedGridDenominator
          (targetRow00 j)).upper <=
          (suzukiDF6D4EvenResidualTargetCertificate.entry 0 j).upper := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
"""


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    output = (
        root
        / "RiemannHypothesisProject/Experiments/M100"
        / f"{MODULE}.lean"
    )
    output.write_text(render(), encoding="utf-8")
    print(f"output={output}")


if __name__ == "__main__":
    main()
