import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard186Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 186 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 186)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 186 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 186)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 487)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 487)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 487)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 487)

theorem suzukiDF6D4FixedGridShard186Stage0_valid :
    (suzukiDF6D4FixedGridShard186EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard186EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard186OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard186OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard186EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard186EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard186OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard186OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
