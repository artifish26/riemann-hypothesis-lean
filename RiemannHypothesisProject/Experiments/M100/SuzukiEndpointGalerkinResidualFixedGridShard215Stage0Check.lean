import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard215Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 215 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 215)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 215 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 215)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 516)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 516)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 516)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 516)

theorem suzukiDF6D4FixedGridShard215Stage0_valid :
    (suzukiDF6D4FixedGridShard215EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard215EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard215OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard215OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard215EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard215EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard215OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard215OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
