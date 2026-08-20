import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

def suzukiDF6D4FixedGridSoundnessCoefficientDenominator : Nat :=
  1000000000000000000000000

def suzukiDF6D4FixedGridSoundnessEvenNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((suzukiDF6D4FixedGridSoundnessCoefficientDenominator / q.den : Nat) : Int)

def suzukiDF6D4FixedGridSoundnessOddNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4OddGalerkinApproximantData[k * 44 + i]!
  q.num * ((suzukiDF6D4FixedGridSoundnessCoefficientDenominator / q.den : Nat) : Int)

def suzukiDF6D4FixedGridEvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  FixedGridInterval.dotCommonDenominator
    suzukiDF6D4FixedGridSoundnessCoefficientDenominator
    (fun k : Fin 256 => suzukiDF6D4FixedGridSoundnessEvenNumerator k i)
    (fun k => a[k.val]!)

def suzukiDF6D4FixedGridOddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  FixedGridInterval.dotCommonDenominator
    suzukiDF6D4FixedGridSoundnessCoefficientDenominator
    (fun k : Fin 256 => suzukiDF6D4FixedGridSoundnessOddNumerator k i)
    (fun k => a[k.val]!)

theorem suzukiDF6D4FixedGridEvenCoefficient_exact
    (k : Fin 256) (i : Fin 45) :
    (1 / (suzukiDF6D4FixedGridSoundnessCoefficientDenominator : Rat)) *
        (suzukiDF6D4FixedGridSoundnessEvenNumerator k i : Rat) =
      suzukiDF6D4EvenGalerkinApproximant k i := by
  native_decide +revert

theorem suzukiDF6D4FixedGridOddCoefficient_exact
    (k : Fin 256) (i : Fin 44) :
    (1 / (suzukiDF6D4FixedGridSoundnessCoefficientDenominator : Rat)) *
        (suzukiDF6D4FixedGridSoundnessOddNumerator k i : Rat) =
      suzukiDF6D4OddGalerkinApproximant k i := by
  native_decide +revert

theorem suzukiDF6D4FixedGridEvenCoefficient_real
    (k : Fin 256) (i : Fin 45) :
    (((1 / (suzukiDF6D4FixedGridSoundnessCoefficientDenominator : Rat)) : Rat) :
          Real) *
        (suzukiDF6D4FixedGridSoundnessEvenNumerator k i : Real) =
      ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) := by
  exact_mod_cast suzukiDF6D4FixedGridEvenCoefficient_exact k i

theorem suzukiDF6D4FixedGridOddCoefficient_real
    (k : Fin 256) (i : Fin 44) :
    (((1 / (suzukiDF6D4FixedGridSoundnessCoefficientDenominator : Rat)) : Rat) :
          Real) *
        (suzukiDF6D4FixedGridSoundnessOddNumerator k i : Real) =
      ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) := by
  exact_mod_cast suzukiDF6D4FixedGridOddCoefficient_exact k i

theorem suzukiDF6D4FixedGridEvenDotSoundness_contains
    (i : Fin 45) (a : Array FixedGridInterval) (x : Fin 256 -> Real)
    (hx : forall k, (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGridDenominator (a[k.val]!)).Contains (x k)) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridEvenDotSoundness i a)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) * x k) := by
  have hdot := FixedGridInterval.contains_dotCommonDenominator
    (n := 256) (D := suzukiDF6D4FixedGridDenominator)
    (Q := suzukiDF6D4FixedGridSoundnessCoefficientDenominator)
    (q := fun k => suzukiDF6D4FixedGridSoundnessEvenNumerator k i)
    (I := fun k => a[k.val]!) (x := x)
    suzukiDF6D4FixedGridDenominator_pos hx
  unfold suzukiDF6D4FixedGridEvenDotSoundness
  convert hdot using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← suzukiDF6D4FixedGridEvenCoefficient_real]
  ring

theorem suzukiDF6D4FixedGridOddDotSoundness_contains
    (i : Fin 44) (a : Array FixedGridInterval) (x : Fin 256 -> Real)
    (hx : forall k, (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGridDenominator (a[k.val]!)).Contains (x k)) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridOddDotSoundness i a)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) * x k) := by
  have hdot := FixedGridInterval.contains_dotCommonDenominator
    (n := 256) (D := suzukiDF6D4FixedGridDenominator)
    (Q := suzukiDF6D4FixedGridSoundnessCoefficientDenominator)
    (q := fun k => suzukiDF6D4FixedGridSoundnessOddNumerator k i)
    (I := fun k => a[k.val]!) (x := x)
    suzukiDF6D4FixedGridDenominator_pos hx
  unfold suzukiDF6D4FixedGridOddDotSoundness
  convert hdot using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← suzukiDF6D4FixedGridOddCoefficient_real]
  ring

end RiemannHypothesisProject.Experiments.M100
