import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard050Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 50 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 50)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 50 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 50)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 351)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 351)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 351)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 351)

theorem suzukiDF6D4FixedGridShard050Stage0_valid :
    (suzukiDF6D4FixedGridShard050EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard050EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard050OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard050OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard050EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard050EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard050OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard050OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
