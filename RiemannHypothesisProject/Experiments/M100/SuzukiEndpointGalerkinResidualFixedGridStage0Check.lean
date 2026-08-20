import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStageData

/-!
# DF6D4 fixed-grid Stage-0 bounded source check

This module is the semantic boundary.  It checks one bounded bundle of literal
source grids against the live rational interval formulas.  Later numerical
stages import only the generated literal data.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveComparisonRow00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 0 k)

private def liveSolveCrossRow00 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4EvenCompleteCrossEntryInterval i 0)

private def liveComparisonPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 301)

private def liveFullPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4FullEvenOffDiagonalInterval
      (suzukiDF6D4EvenLowMode i) 301)

private def liveTargetCrossColumn00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4EvenCompleteCrossEntryInterval 0 k)

private def liveOddComparisonRow00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4OddComparisonGalerkinEntryInterval 0 k)

private def liveOddSolveCrossRow00 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4OddCompleteCrossEntryInterval i 0)

private def liveOddComparisonPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4ComparisonOddOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 301)

private def liveOddFullPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4FullOddOffDiagonalInterval
      (suzukiDF6D4OddLowMode i) 301)

private def liveOddTargetCrossColumn00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4OddCompleteCrossEntryInterval 0 k)

private def liveComparisonRow01 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 1 k)

private def liveSolveCrossRow01 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4EvenCompleteCrossEntryInterval i 1)

private def liveComparisonPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 302)

private def liveFullPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4FullEvenOffDiagonalInterval
      (suzukiDF6D4EvenLowMode i) 302)

private def liveOddComparisonRow01 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4OddComparisonGalerkinEntryInterval 1 k)

private def liveOddSolveCrossRow01 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4OddCompleteCrossEntryInterval i 1)

private def liveOddComparisonPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4ComparisonOddOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 302)

private def liveOddFullPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4FullOddOffDiagonalInterval
      (suzukiDF6D4OddLowMode i) 302)

theorem suzukiDF6D4FixedGridStage0BoundedBlock_valid :
    suzukiDF6D4FixedGridStage0ComparisonRow00Data = liveComparisonRow00 /\
    suzukiDF6D4FixedGridStage0SolveCrossRow00Data = liveSolveCrossRow00 /\
    suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data =
      liveComparisonPrefixRow301 /\
    suzukiDF6D4FixedGridStage0FullPrefixRow301Data = liveFullPrefixRow301 /\
    suzukiDF6D4FixedGridStage0TargetCrossColumn00Data =
      liveTargetCrossColumn00 /\
    suzukiDF6D4FixedGridStage0Endpoint00Data =
      #[fixedGridOf (suzukiDF6D4EvenEndpointEntryInterval 0 0)] /\
    suzukiDF6D4FixedGridStage0AnalyticTail00Data =
      #[fixedGridOf (suzukiDF6D4EvenAnalyticTailEntryInterval 0 0)] := by
  native_decide

theorem suzukiDF6D4FixedGridOddStage0BoundedBlock_valid :
    suzukiDF6D4FixedGridOddStage0ComparisonRow00Data =
      liveOddComparisonRow00 /\
    suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data =
      liveOddSolveCrossRow00 /\
    suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data =
      liveOddComparisonPrefixRow301 /\
    suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data =
      liveOddFullPrefixRow301 /\
    suzukiDF6D4FixedGridOddStage0TargetCrossColumn00Data =
      liveOddTargetCrossColumn00 /\
    suzukiDF6D4FixedGridOddStage0Endpoint00Data =
      #[fixedGridOf (suzukiDF6D4OddEndpointEntryInterval 0 0)] /\
    suzukiDF6D4FixedGridOddStage0AnalyticTail00Data =
      #[fixedGridOf (suzukiDF6D4OddAnalyticTailEntryInterval 0 0)] := by
  native_decide

theorem suzukiDF6D4FixedGridStage0Shard01_valid :
    suzukiDF6D4FixedGridStage0ComparisonRow01Data = liveComparisonRow01 /\
    suzukiDF6D4FixedGridStage0SolveCrossRow01Data = liveSolveCrossRow01 /\
    suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data =
      liveComparisonPrefixRow302 /\
    suzukiDF6D4FixedGridStage0FullPrefixRow302Data =
      liveFullPrefixRow302 := by
  native_decide

theorem suzukiDF6D4FixedGridOddStage0Shard01_valid :
    suzukiDF6D4FixedGridOddStage0ComparisonRow01Data =
      liveOddComparisonRow01 /\
    suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data =
      liveOddSolveCrossRow01 /\
    suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data =
      liveOddComparisonPrefixRow302 /\
    suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data =
      liveOddFullPrefixRow302 := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
