import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard194Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 194 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 194)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 194 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 194)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 495)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 495)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 495)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 495)

theorem suzukiDF6D4FixedGridShard194Stage0_valid :
    (suzukiDF6D4FixedGridShard194EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard194EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard194OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard194OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard194EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard194EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard194OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard194OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
