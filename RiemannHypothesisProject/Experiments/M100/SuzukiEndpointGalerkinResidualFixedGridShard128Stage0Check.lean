import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard128Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 128 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 128)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 128 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 128)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 429)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 429)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 429)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 429)

theorem suzukiDF6D4FixedGridShard128Stage0_valid :
    (suzukiDF6D4FixedGridShard128EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard128EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard128OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard128OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard128EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard128EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard128OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard128OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
