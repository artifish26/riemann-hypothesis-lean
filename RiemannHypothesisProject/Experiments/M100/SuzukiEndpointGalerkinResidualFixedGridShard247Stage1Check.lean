import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard247Data

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
  (suzukiDF6D4FixedGridShard247EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard247EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard247OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard247OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard247EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard247EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard247OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard247OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard247Stage1_valid :
    (suzukiDF6D4FixedGridShard247EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard247OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard247EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard247OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
