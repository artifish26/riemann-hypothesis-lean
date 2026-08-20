import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard004Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 4 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 4)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 4 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 4)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 305)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 305)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 305)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 305)

theorem suzukiDF6D4FixedGridShard004Stage0_valid :
    (suzukiDF6D4FixedGridShard004EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard004EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard004OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard004OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard004EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard004EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard004OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard004OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
