import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard135Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 135 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 135)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 135 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 135)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 436)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 436)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 436)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 436)

theorem suzukiDF6D4FixedGridShard135Stage0_valid :
    (suzukiDF6D4FixedGridShard135EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard135EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard135OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard135OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard135EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard135EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard135OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard135OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
