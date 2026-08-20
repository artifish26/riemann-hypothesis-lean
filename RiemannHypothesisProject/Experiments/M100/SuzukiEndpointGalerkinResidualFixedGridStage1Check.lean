import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStageData

/-!
# DF6D4 fixed-grid Stage-1 bounded cache check

The numerical evaluator in this module consumes only literal Stage-0 grids and
the frozen literal Galerkin coefficients.  It does not import or unfold the
live analytic interval formulas.
-/

namespace RiemannHypothesisProject.Experiments.M100

private def coefficientDenominator : Nat :=
  1000000000000000000000000

private def evenCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def oddCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4OddGalerkinApproximantData[k * 44 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def dotForColumn
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def solveRow00FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridStage0SolveCrossRow00Data[i.val]!).sub
      (dotForColumn i.val suzukiDF6D4FixedGridStage0ComparisonRow00Data)

private def residualRow301FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridStage0FullPrefixRow301Data[i.val]!).sub
      (dotForColumn i.val
        suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data)

private def oddDotForColumn
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => oddCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def oddSolveRow00FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data[i.val]!).sub
      (oddDotForColumn i.val
        suzukiDF6D4FixedGridOddStage0ComparisonRow00Data)

private def oddResidualRow301FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data[i.val]!).sub
      (oddDotForColumn i.val
        suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data)

private def solveRow01FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridStage0SolveCrossRow01Data[i.val]!).sub
      (dotForColumn i.val suzukiDF6D4FixedGridStage0ComparisonRow01Data)

private def residualRow302FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridStage0FullPrefixRow302Data[i.val]!).sub
      (dotForColumn i.val
        suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data)

private def oddSolveRow01FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data[i.val]!).sub
      (oddDotForColumn i.val
        suzukiDF6D4FixedGridOddStage0ComparisonRow01Data)

private def oddResidualRow302FromStage0 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data[i.val]!).sub
      (oddDotForColumn i.val
        suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data)

theorem suzukiDF6D4FixedGridStage1BoundedBlock_valid :
    suzukiDF6D4FixedGridStage1SolveRow00Data = solveRow00FromStage0 /\
    suzukiDF6D4FixedGridStage1ResidualRow301Data =
      residualRow301FromStage0 := by
  native_decide

theorem suzukiDF6D4FixedGridOddStage1BoundedBlock_valid :
    suzukiDF6D4FixedGridOddStage1SolveRow00Data =
      oddSolveRow00FromStage0 /\
    suzukiDF6D4FixedGridOddStage1ResidualRow301Data =
      oddResidualRow301FromStage0 := by
  native_decide

theorem suzukiDF6D4FixedGridStage1Shard01_valid :
    suzukiDF6D4FixedGridStage1SolveRow01Data = solveRow01FromStage0 /\
    suzukiDF6D4FixedGridStage1ResidualRow302Data =
      residualRow302FromStage0 := by
  native_decide

theorem suzukiDF6D4FixedGridOddStage1Shard01_valid :
    suzukiDF6D4FixedGridOddStage1SolveRow01Data =
      oddSolveRow01FromStage0 /\
    suzukiDF6D4FixedGridOddStage1ResidualRow302Data =
      oddResidualRow302FromStage0 := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
