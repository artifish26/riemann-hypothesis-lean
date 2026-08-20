import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard230Data

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
  (suzukiDF6D4FixedGridShard230EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard230EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard230OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard230OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard230EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard230EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard230OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard230OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard230Stage1_valid :
    (suzukiDF6D4FixedGridShard230EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard230OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard230EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard230OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
