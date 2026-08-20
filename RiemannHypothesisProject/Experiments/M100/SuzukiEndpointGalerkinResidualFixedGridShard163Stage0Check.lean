import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard163Data

namespace RiemannHypothesisProject.Experiments.M100
open RationalInterval
private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def liveEvenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 163 k)
private def liveEvenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4EvenCompleteCrossEntryInterval i 163)
private def liveOddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4OddComparisonGalerkinEntryInterval 163 k)
private def liveOddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4OddCompleteCrossEntryInterval i 163)

private def liveEvenResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 464)
private def liveEvenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
  (suzukiDF6D4FullEvenOffDiagonalInterval (suzukiDF6D4EvenLowMode i) 464)
private def liveOddResidualComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
  (suzukiDF6D4ComparisonOddOffDiagonalInterval
    (suzukiDF6D4GalerkinMode k) 464)
private def liveOddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
  (suzukiDF6D4FullOddOffDiagonalInterval (suzukiDF6D4OddLowMode i) 464)

theorem suzukiDF6D4FixedGridShard163Stage0_valid :
    (suzukiDF6D4FixedGridShard163EvenComparisonData = liveEvenComparison /\
    suzukiDF6D4FixedGridShard163EvenCrossData = liveEvenCross /\
    suzukiDF6D4FixedGridShard163OddComparisonData = liveOddComparison /\
    suzukiDF6D4FixedGridShard163OddCrossData = liveOddCross) /\
    suzukiDF6D4FixedGridShard163EvenResidualComparisonData = liveEvenResidualComparison /\
    suzukiDF6D4FixedGridShard163EvenFullData = liveEvenFull /\
    suzukiDF6D4FixedGridShard163OddResidualComparisonData = liveOddResidualComparison /\
    suzukiDF6D4FixedGridShard163OddFullData = liveOddFull := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
