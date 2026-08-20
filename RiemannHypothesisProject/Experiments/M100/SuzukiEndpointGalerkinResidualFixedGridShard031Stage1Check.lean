import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard031Data

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
  (suzukiDF6D4FixedGridShard031EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard031EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard031OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard031OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard031EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard031EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard031OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard031OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard031Stage1_valid :
    (suzukiDF6D4FixedGridShard031EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard031OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard031EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard031OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
