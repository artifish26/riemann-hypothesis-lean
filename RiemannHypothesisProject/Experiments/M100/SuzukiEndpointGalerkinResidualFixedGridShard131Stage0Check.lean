import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard131Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 131 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 131)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 131 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 131)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 432)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 432)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 432)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 432)

theorem suzukiDF6D4FixedGridShard131Stage0_valid :
    (suzukiDF6D4FixedGridShard131EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard131EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard131OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard131OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard131EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard131EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard131OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard131OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
