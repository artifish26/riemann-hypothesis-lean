import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard244Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 244 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 244)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 244 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 244)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 545)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 545)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 545)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 545)

theorem suzukiDF6D4FixedGridShard244Stage0_valid :
    (suzukiDF6D4FixedGridShard244EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard244EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard244OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard244OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard244EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard244EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard244OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard244OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
