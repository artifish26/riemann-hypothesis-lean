import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard232Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 232 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 232)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 232 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 232)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 533)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 533)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 533)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 533)

theorem suzukiDF6D4FixedGridShard232Stage0_valid :
    (suzukiDF6D4FixedGridShard232EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard232EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard232OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard232OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard232EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard232EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard232OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard232OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
