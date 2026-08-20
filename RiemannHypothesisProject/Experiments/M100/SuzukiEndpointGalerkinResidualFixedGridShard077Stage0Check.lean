import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard077Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 77 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 77)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 77 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 77)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 378)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 378)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 378)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 378)

theorem suzukiDF6D4FixedGridShard077Stage0_valid :
    (suzukiDF6D4FixedGridShard077EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard077EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard077OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard077OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard077EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard077EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard077OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard077OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
