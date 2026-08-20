import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard032Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 32 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 32)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 32 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 32)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 333)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 333)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 333)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 333)

theorem suzukiDF6D4FixedGridShard032Stage0_valid :
    (suzukiDF6D4FixedGridShard032EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard032EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard032OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard032OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard032EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard032EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard032OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard032OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
