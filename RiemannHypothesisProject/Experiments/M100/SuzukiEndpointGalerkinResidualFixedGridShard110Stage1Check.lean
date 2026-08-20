import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard110Data

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
  (suzukiDF6D4FixedGridShard110EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard110EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard110OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard110OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard110EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard110EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard110OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard110OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard110Stage1_valid :
    (suzukiDF6D4FixedGridShard110EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard110OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard110EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard110OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
