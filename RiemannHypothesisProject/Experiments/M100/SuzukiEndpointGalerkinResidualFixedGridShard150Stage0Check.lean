import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard150Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 150 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 150)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 150 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 150)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 451)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 451)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 451)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 451)

theorem suzukiDF6D4FixedGridShard150Stage0_valid :
    (suzukiDF6D4FixedGridShard150EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard150EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard150OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard150OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard150EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard150EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard150OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard150OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
