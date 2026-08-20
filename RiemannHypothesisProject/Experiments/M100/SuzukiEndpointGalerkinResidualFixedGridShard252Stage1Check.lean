import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard252Data

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
  (suzukiDF6D4FixedGridShard252EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard252EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard252OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard252OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard252EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard252EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard252OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard252OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard252Stage1_valid :
    (suzukiDF6D4FixedGridShard252EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard252OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard252EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard252OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
