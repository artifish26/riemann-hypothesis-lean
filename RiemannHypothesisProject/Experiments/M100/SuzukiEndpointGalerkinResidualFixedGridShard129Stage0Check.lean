import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard129Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 129 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 129)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 129 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 129)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 430)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 430)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 430)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 430)

theorem suzukiDF6D4FixedGridShard129Stage0_valid :
    (suzukiDF6D4FixedGridShard129EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard129EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard129OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard129OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard129EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard129EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard129OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard129OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
