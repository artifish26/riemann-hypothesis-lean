import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard156Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 156 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 156)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 156 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 156)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 457)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 457)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 457)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 457)

theorem suzukiDF6D4FixedGridShard156Stage0_valid :
    (suzukiDF6D4FixedGridShard156EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard156EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard156OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard156OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard156EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard156EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard156OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard156OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
