import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard081Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 81 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 81)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 81 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 81)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 382)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 382)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 382)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 382)

theorem suzukiDF6D4FixedGridShard081Stage0_valid :
    (suzukiDF6D4FixedGridShard081EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard081EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard081OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard081OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard081EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard081EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard081OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard081OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
