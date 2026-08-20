import RiemannHypothesisProject.Experiments.M100.SuzukiRSecondKernel
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailCompleteTransformBounds
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailFourierVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Smooth-transform variation bridge for M100-DF6D4

This module specializes the elementary Fourier-variation estimate to the
actual endpoint and exact `r''` kernel.  The source-specific transform identity
and the sign of the third derivative remain visible hypotheses.  Integrability
is derived automatically from that one-sided sign condition.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set

/-- The DF0 endpoint expression is exactly the value of the project `r''`
kernel at `2 * a_star`. -/
theorem suzukiRSecondKernel_two_mul_aStar_eq_DF0RemainderSecondDerivative :
    suzukiRSecondKernel (2 * suzukiProjectAStar) =
      suzukiDF6D4DF0RemainderSecondDerivative := by
  have ha : 0 < suzukiProjectAStar := suzukiProjectAStar_pos
  have htwoA : 2 * suzukiProjectAStar ≠ 0 := by positivity
  have habs : |2 * suzukiProjectAStar| = 2 * suzukiProjectAStar :=
    abs_of_pos (by positivity)
  have hexpFour :
      Real.exp (-2 * (2 * suzukiProjectAStar)) =
        (Real.exp (-suzukiProjectAStar)) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold suzukiRSecondKernel suzukiR1SecondKernel
    suzukiR1SecondOffOrigin
    suzukiDF6D4DF0RemainderSecondDerivative
  rw [if_neg htwoA, habs, hexpFour, Real.cosh_eq]
  ring_nf

/-- The actual third derivative of the smooth project kernel.  Its sign on
the frozen positive interval is the remaining X21 power-series inequality. -/
def suzukiRThirdKernel (t : Real) : Real :=
  deriv suzukiRSecondKernel t

theorem differentiableAt_suzukiRSecondKernel_of_pos
    {t : Real} (ht : 0 < t) :
    DifferentiableAt Real suzukiRSecondKernel t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hden : 1 - Real.exp (-2 * t) ≠ 0 := by
    rw [sub_ne_zero]
    exact ne_of_gt ((Real.exp_lt_one_iff).2 (by linarith))
  have htwo : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht0
  have hformula :
      suzukiR1SecondKernel =ᶠ[nhds t] suzukiR1SecondOffOrigin := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    have hxpos : 0 < x := mem_Ioi.mp hx
    simp [suzukiR1SecondKernel, hxpos.ne', abs_of_pos hxpos]
  have hR1 : DifferentiableAt Real suzukiR1SecondKernel t := by
    apply (show DifferentiableAt Real suzukiR1SecondOffOrigin t by
      unfold suzukiR1SecondOffOrigin
      fun_prop (disch := assumption)).congr_of_eventuallyEq
    exact hformula
  unfold suzukiRSecondKernel
  apply DifferentiableAt.add
  · fun_prop
  · exact hR1

theorem hasDerivAt_suzukiRSecondKernel_of_pos
    {t : Real} (ht : 0 < t) :
    HasDerivAt suzukiRSecondKernel (suzukiRThirdKernel t) t := by
  exact (differentiableAt_suzukiRSecondKernel_of_pos ht).hasDerivAt

/-- Hyperbolic normal form of the off-origin `r_1''` summand. -/
theorem suzukiR1SecondOffOrigin_eq_hyperbolic
    {t : Real} (ht : 0 < t) :
    suzukiR1SecondOffOrigin t =
      Real.exp (t / 2) / (2 * Real.sinh t) - 1 / (2 * t) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hsinh : Real.sinh t ≠ 0 :=
    ne_of_gt ((Real.sinh_pos_iff).2 ht)
  have hexpCancel : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hexpSquare : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hdenominator :
      1 - Real.exp (-2 * t) =
        Real.exp (-t) * (Real.exp t - Real.exp (-t)) := by
    rw [hexpSquare]
    nlinarith
  have hnumerator :
      Real.exp (-t / 2) = Real.exp (-t) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold suzukiR1SecondOffOrigin
  rw [hdenominator, hnumerator, Real.sinh_eq]
  field_simp [ht0, hsinh, Real.exp_ne_zero]

/-- The elementary positive expression isolated in the X21 power-series
argument. -/
def suzukiRThirdPositivityWitness (t : Real) : Real :=
  t ^ 2 * Real.exp (t / 2) *
      (2 * Real.cosh t - Real.sinh t) -
    2 * Real.sinh t ^ 2

/-- Exponential-series form of the same X21 witness. -/
def suzukiRThirdExponentialWitness (t : Real) : Real :=
  (t ^ 2 / 2) *
      (Real.exp (3 * t / 2) + 3 * Real.exp (-t / 2)) -
    Real.cosh (2 * t) + 1

theorem suzukiRThirdPositivityWitness_eq_exponential (t : Real) :
    suzukiRThirdPositivityWitness t =
      suzukiRThirdExponentialWitness t := by
  have hthreeHalf :
      Real.exp (3 * t / 2) = Real.exp (t / 2) * Real.exp t := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hnegHalf :
      Real.exp (-t / 2) = Real.exp (t / 2) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htwo : Real.exp (2 * t) = Real.exp t ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hnegTwo : Real.exp (-(2 * t)) = Real.exp (-t) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcancel : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  unfold suzukiRThirdPositivityWitness suzukiRThirdExponentialWitness
  simp only [Real.sinh_eq, Real.cosh_eq]
  rw [hthreeHalf, hnegHalf, htwo, hnegTwo]
  ring_nf
  nlinarith

/-- Explicit off-origin derivative normal form. -/
def suzukiRThirdHyperbolic (t : Real) : Real :=
  -Real.sinh (t / 2) -
    suzukiRThirdPositivityWitness t /
      (4 * t ^ 2 * Real.sinh t ^ 2)

theorem hasDerivAt_suzukiRSecondKernel_hyperbolic_of_pos
    {t : Real} (ht : 0 < t) :
    HasDerivAt suzukiRSecondKernel (suzukiRThirdHyperbolic t) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hsinh : Real.sinh t ≠ 0 :=
    ne_of_gt ((Real.sinh_pos_iff).2 ht)
  have hformula :
      suzukiRSecondKernel =ᶠ[nhds t]
        fun x =>
          -(Real.exp (x / 2) + Real.exp (-x / 2)) +
            (Real.exp (x / 2) / (2 * Real.sinh x) - 1 / (2 * x)) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    have hxpos : 0 < x := mem_Ioi.mp hx
    rw [suzukiRSecondKernel, suzukiR1SecondKernel,
      if_neg hxpos.ne', abs_of_pos hxpos,
      suzukiR1SecondOffOrigin_eq_hyperbolic hxpos]
  apply (show HasDerivAt
      (fun x =>
        -(Real.exp (x / 2) + Real.exp (-x / 2)) +
          (Real.exp (x / 2) / (2 * Real.sinh x) - 1 / (2 * x)))
      (suzukiRThirdHyperbolic t) t by
    have hExpPos :
        HasDerivAt (fun x : Real => Real.exp (x / 2))
          (Real.exp (t / 2) / 2) t := by
      have h := (Real.hasDerivAt_exp (t / 2)).comp t
        ((hasDerivAt_id t).div_const 2)
      have heq :
          (Real.exp ∘ fun x : Real => id x / 2) =ᶠ[nhds t]
            fun x : Real => Real.exp (x / 2) := by
        filter_upwards with x
        rfl
      exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
    have hExpNeg :
        HasDerivAt (fun x : Real => Real.exp (-x / 2))
          (-Real.exp (-t / 2) / 2) t := by
      have h := (Real.hasDerivAt_exp (-t / 2)).comp t
        ((hasDerivAt_id t).neg.div_const 2)
      have heq :
          (Real.exp ∘ fun x : Real => (-id) x / 2) =ᶠ[nhds t]
            fun x : Real => Real.exp (-x / 2) := by
        filter_upwards with x
        rfl
      exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)
    have hSinh : HasDerivAt Real.sinh (Real.cosh t) t :=
      Real.hasDerivAt_sinh t
    have hDenominator :
        HasDerivAt (fun x : Real => 2 * Real.sinh x)
          (2 * Real.cosh t) t := hSinh.const_mul 2
    have hLinear :
        HasDerivAt (fun x : Real => 2 * x) 2 t :=
      by simpa using (hasDerivAt_id t).const_mul (2 : Real)
    have hOne :
        HasDerivAt (fun _ : Real => (1 : Real)) (0 : Real) t := by
      exact hasDerivAt_const t (1 : Real)
    have hDerivative :=
      (hExpPos.add hExpNeg).neg.add
        (hExpPos.div hDenominator (mul_ne_zero (by norm_num) hsinh) |>.sub
          (hOne.div hLinear (mul_ne_zero (by norm_num) ht0)))
    have hDerivativeFormula :
        (-((fun x : Real => Real.exp (x / 2)) +
            fun x : Real => Real.exp (-x / 2)) +
          (((fun x : Real => Real.exp (x / 2)) /
              fun x : Real => 2 * Real.sinh x) -
            (fun _ : Real => (1 : Real)) /
              fun x : Real => 2 * x)) =ᶠ[nhds t]
          fun x : Real =>
            -(Real.exp (x / 2) + Real.exp (-x / 2)) +
              (Real.exp (x / 2) / (2 * Real.sinh x) - 1 / (2 * x)) := by
      filter_upwards with x
      rfl
    unfold suzukiRThirdHyperbolic suzukiRThirdPositivityWitness
    apply (hDerivative.congr_of_eventuallyEq hDerivativeFormula).congr_deriv
    have hSinhHalf :
        Real.sinh (t / 2) =
          (Real.exp (t / 2) - Real.exp (-t / 2)) / 2 := by
      simpa only [neg_div] using Real.sinh_eq (t / 2)
    field_simp [ht0, hsinh]
    rw [hSinhHalf]
    ring).congr_of_eventuallyEq hformula

theorem suzukiRThirdKernel_eq_hyperbolic_of_pos
    {t : Real} (ht : 0 < t) :
    suzukiRThirdKernel t = suzukiRThirdHyperbolic t := by
  exact (hasDerivAt_suzukiRSecondKernel_of_pos ht).unique
    (hasDerivAt_suzukiRSecondKernel_hyperbolic_of_pos ht)

/-- Positivity of the elementary X21 witness is sufficient for the required
one-sided derivative sign. -/
theorem suzukiRThirdKernel_nonpos_of_witness_nonneg
    {t : Real} (ht : 0 < t)
    (hwitness : 0 ≤ suzukiRThirdPositivityWitness t) :
    suzukiRThirdKernel t ≤ 0 := by
  rw [suzukiRThirdKernel_eq_hyperbolic_of_pos ht]
  unfold suzukiRThirdHyperbolic
  have hsinh : 0 < Real.sinh t := (Real.sinh_pos_iff).2 ht
  have hden : 0 < 4 * t ^ 2 * Real.sinh t ^ 2 := by positivity
  have hquotient :
      0 ≤ suzukiRThirdPositivityWitness t /
        (4 * t ^ 2 * Real.sinh t ^ 2) :=
    div_nonneg hwitness hden.le
  have hsinhHalf : 0 ≤ Real.sinh (t / 2) := by
    rw [Real.sinh_nonneg_iff]
    linarith
  linarith

theorem suzukiRThirdKernel_nonpos_of_exponentialWitness_nonneg
    {t : Real} (ht : 0 < t)
    (hwitness : 0 ≤ suzukiRThirdExponentialWitness t) :
    suzukiRThirdKernel t ≤ 0 := by
  apply suzukiRThirdKernel_nonpos_of_witness_nonneg ht
  rw [suzukiRThirdPositivityWitness_eq_exponential]
  exact hwitness

/-- Once the source transform is identified with the exact `r''` sine
integral and the off-origin derivative is proved nonpositive, the precise
DF6D4 smooth-transform bound follows. -/
theorem suzukiDF6D4SmoothTransformDifference_abs_le_of_kernelVariation
    (mode : Nat) (hmode : 1 ≤ mode)
    (htransform :
      suzukiDF6D4SmoothTransformDifference mode =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)))
    (hnonpos : ∀ t ∈ Ioc (0 : Real) (2 * suzukiProjectAStar),
      suzukiRThirdKernel t ≤ 0) :
    |suzukiDF6D4SmoothTransformDifference mode| ≤
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
        Real.pi) / mode := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hmodeReal : 0 < (mode : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hmode)
  have hw : 0 < w := by
    dsimp only [w]
    exact div_pos (mul_pos hmodeReal Real.pi_pos) suzukiProjectAStar_pos
  have hcos : Real.cos (w * (2 * suzukiProjectAStar)) = 1 := by
    have harg : w * (2 * suzukiProjectAStar) =
        (mode : Real) * (2 * Real.pi) := by
      dsimp only [w]
      field_simp [suzukiProjectAStar_pos.ne']
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hdifference :
      0 ≤ suzukiRSecondKernel 0 -
        suzukiRSecondKernel (2 * suzukiProjectAStar) := by
    have hvariation := suzukiDF6D4RemainderVariation_nonneg
    rw [suzukiRSecondKernel_two_mul_aStar_eq_DF0RemainderSecondDerivative]
    unfold suzukiDF6D4DF0RemainderVariation at hvariation
    norm_num at hvariation ⊢
    linarith
  have hfourier :=
    abs_neg_two_mul_intervalIntegral_mul_sin_le_of_deriv_nonpos
      (f := suzukiRSecondKernel) (f' := suzukiRThirdKernel)
      (L := 2 * suzukiProjectAStar) (w := w)
      (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le) hw hcos
      (continuous_suzukiRSecondKernel.continuousOn)
      (fun t ht => hasDerivAt_suzukiRSecondKernel_of_pos ht.1)
      hnonpos hdifference
  rw [htransform]
  calc
    abs (-2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiRSecondKernel t * Real.sin (w * t))) ≤
        4 * (suzukiRSecondKernel 0 -
          suzukiRSecondKernel (2 * suzukiProjectAStar)) / w := hfourier
    _ = (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
          Real.pi) / mode := by
      rw [suzukiRSecondKernel_two_mul_aStar_eq_DF0RemainderSecondDerivative,
        suzukiRSecondKernel_zero]
      unfold suzukiDF6D4DF0RemainderVariation
      dsimp only [w]
      field_simp [suzukiProjectAStar_pos.ne', Real.pi_ne_zero,
        ne_of_gt hmodeReal]
      ring

/-- Receiving form whose only monotonicity premise is positivity of the
elementary exponential witness used by the X21 Taylor argument. -/
theorem suzukiDF6D4SmoothTransformDifference_abs_le_of_exponentialWitness
    (mode : Nat) (hmode : 1 ≤ mode)
    (htransform :
      suzukiDF6D4SmoothTransformDifference mode =
        -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t *
            Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)))
    (hwitness : ∀ t ∈ Ioc (0 : Real) (2 * suzukiProjectAStar),
      0 ≤ suzukiRThirdExponentialWitness t) :
    |suzukiDF6D4SmoothTransformDifference mode| ≤
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
        Real.pi) / mode := by
  exact suzukiDF6D4SmoothTransformDifference_abs_le_of_kernelVariation
    mode hmode htransform fun t ht =>
      suzukiRThirdKernel_nonpos_of_exponentialWitness_nonneg ht.1
        (hwitness t ht)

end

end RiemannHypothesisProject.Experiments.M100
