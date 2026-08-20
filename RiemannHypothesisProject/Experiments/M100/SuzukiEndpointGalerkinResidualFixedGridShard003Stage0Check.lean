import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard003Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 3 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 3)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 3 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 3)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 304)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 304)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 304)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 304)

theorem suzukiDF6D4FixedGridShard003Stage0_valid :
    (suzukiDF6D4FixedGridShard003EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard003EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard003OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard003OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard003EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard003EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard003OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard003OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
