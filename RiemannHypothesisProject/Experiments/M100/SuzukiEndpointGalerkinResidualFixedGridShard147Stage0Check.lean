import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard147Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 147 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 147)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 147 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 147)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 448)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 448)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 448)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 448)

theorem suzukiDF6D4FixedGridShard147Stage0_valid :
    (suzukiDF6D4FixedGridShard147EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard147EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard147OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard147OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard147EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard147EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard147OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard147OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
