import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard016Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 16 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 16)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 16 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 16)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 317)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 317)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 317)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 317)

theorem suzukiDF6D4FixedGridShard016Stage0_valid :
    (suzukiDF6D4FixedGridShard016EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard016EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard016OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard016OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard016EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard016EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard016OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard016OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
