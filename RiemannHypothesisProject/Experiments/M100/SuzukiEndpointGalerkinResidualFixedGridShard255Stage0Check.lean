import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard255Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 255 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 255)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 255 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 255)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 556)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 556)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 556)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 556)

theorem suzukiDF6D4FixedGridShard255Stage0_valid :
    (suzukiDF6D4FixedGridShard255EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard255EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard255OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard255OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard255EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard255EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard255OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard255OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
