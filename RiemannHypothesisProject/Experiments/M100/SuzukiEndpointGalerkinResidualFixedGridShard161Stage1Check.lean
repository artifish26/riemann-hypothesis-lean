import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard161Data

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
  (suzukiDF6D4FixedGridShard161EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard161EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard161OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard161OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard161EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard161EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard161OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard161OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard161Stage1_valid :
    (suzukiDF6D4FixedGridShard161EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard161OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard161EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard161OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
