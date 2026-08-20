import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard248Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 248 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 248)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 248 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 248)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 549)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 549)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 549)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 549)

theorem suzukiDF6D4FixedGridShard248Stage0_valid :
    (suzukiDF6D4FixedGridShard248EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard248EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard248OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard248OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard248EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard248EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard248OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard248OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
