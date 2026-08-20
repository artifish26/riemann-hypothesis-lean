import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard219Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 219 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 219)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 219 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 219)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 520)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 520)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 520)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 520)

theorem suzukiDF6D4FixedGridShard219Stage0_valid :
    (suzukiDF6D4FixedGridShard219EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard219EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard219OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard219OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard219EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard219EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard219OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard219OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
