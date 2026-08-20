import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard018Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 18 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 18)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 18 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 18)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 319)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 319)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 319)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 319)

theorem suzukiDF6D4FixedGridShard018Stage0_valid :
    (suzukiDF6D4FixedGridShard018EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard018EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard018OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard018OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard018EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard018EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard018OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard018OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
