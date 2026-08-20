import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard086Data

namespace RiemannHypothesisProject.Experiments.M100
private def coefficientDenominator : Nat := 1000000000000000000000000
private def evenNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)
private def oddNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4OddGalerkinApproximantData[k * 44 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)
private def evenDot (i : Nat) (a : Array FixedGridInterval) :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenNumerator k i) (fun k => a[k.val]!)
private def oddDot (i : Nat) (a : Array FixedGridInterval) :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => oddNumerator k i) (fun k => a[k.val]!)

private def evenSolve := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard086EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard086EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard086OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard086OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard086EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard086EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard086OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard086OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard086Stage1_valid :
    (suzukiDF6D4FixedGridShard086EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard086OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard086EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard086OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
