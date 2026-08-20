import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard241Data

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
  (suzukiDF6D4FixedGridShard241EvenCrossData[i.val]!).sub (evenDot i.val suzukiDF6D4FixedGridShard241EvenComparisonData)
private def oddSolve := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard241OddCrossData[i.val]!).sub (oddDot i.val suzukiDF6D4FixedGridShard241OddComparisonData)

private def evenResidual := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard241EvenFullData[i.val]!).sub
    (evenDot i.val suzukiDF6D4FixedGridShard241EvenResidualComparisonData)
private def oddResidual := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard241OddFullData[i.val]!).sub
    (oddDot i.val suzukiDF6D4FixedGridShard241OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard241Stage1_valid :
    (suzukiDF6D4FixedGridShard241EvenSolveData = evenSolve /\
    suzukiDF6D4FixedGridShard241OddSolveData = oddSolve) /\
    suzukiDF6D4FixedGridShard241EvenResidualData = evenResidual /\
    suzukiDF6D4FixedGridShard241OddResidualData = oddResidual := by
  native_decide
end RiemannHypothesisProject.Experiments.M100
