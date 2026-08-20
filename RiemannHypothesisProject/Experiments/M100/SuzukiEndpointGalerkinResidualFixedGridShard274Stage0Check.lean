import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard274Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 575)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 575)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 575)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 575)

theorem suzukiDF6D4FixedGridShard274Stage0_valid :
    (True) /\
    suzukiDF6D4FixedGridShard274EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard274EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard274OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard274OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
