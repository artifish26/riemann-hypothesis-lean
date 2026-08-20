import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard111Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 111 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 111)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 111 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 111)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 412)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 412)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 412)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 412)

theorem suzukiDF6D4FixedGridShard111Stage0_valid :
    (suzukiDF6D4FixedGridShard111EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard111EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard111OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard111OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard111EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard111EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard111OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard111OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
