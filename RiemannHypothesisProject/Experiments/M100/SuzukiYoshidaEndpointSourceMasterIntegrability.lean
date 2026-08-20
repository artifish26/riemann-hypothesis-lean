import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointSourcePartialFractions

/-!
# Integrability of the endpoint paired-pole master family

This module identifies the master integrand with the real part of the already
integrable source pairing between the opposite exponential modes `n` and
`-n`.  Thus the analytic master target retains only its exact evaluation.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

/-- The paired-pole master integrand is, almost everywhere, `-n*pi` times the
real part of the opposite-mode endpoint source pairing. -/
theorem suzukiYoshidaEndpointSourceModeMasterIntegrand_ae_eq_oppositeMode
    {r : Real} (hr : 0 < r) (n : Nat) :
    suzukiYoshidaEndpointSourceModeMasterIntegrand r n =ᵐ[volume]
      fun z => -((n : Real) * Real.pi) *
        (suzukiYoshidaEndpointSourceVariableIntegrand
          r (n : Int) (-(n : Int)) z).re := by
  let q : Real := (n : Real) * Real.pi / r
  have hsqrtPos : 0 < Real.sqrt (2 * r) := Real.sqrt_pos.2 (by positivity)
  filter_upwards [volume.ae_ne (-q), volume.ae_ne q] with z hzneg hzpos
  have hzplus : z + q ≠ 0 := by intro h; apply hzneg; linarith
  have hzminus : z - q ≠ 0 := sub_ne_zero.mpr hzpos
  have hplus :
      Real.sin (r * z + (n : Real) * Real.pi) =
        (-1 : Real) ^ n * Real.sin (r * z) :=
    Real.sin_add_nat_mul_pi (r * z) n
  have hminus :
      Real.sin (r * z + -(n : Real) * Real.pi) =
        (-1 : Real) ^ n * Real.sin (r * z) := by
    convert Real.sin_sub_nat_mul_pi (r * z) n using 1 <;> ring
  have hnegativeFrequency :
      (-(n : Real) * Real.pi / r) = -q := by
    dsimp [q]
    ring
  have hprofilePlus :
      suzukiYoshidaEndpointSourceVariableProfile r (n : Int) z =
        (((Real.sqrt (2 * r))⁻¹ *
          (2 * ((-1 : Real) ^ n) * Real.sin (r * z) / (z + q)) : Real) :
            Complex) := by
    unfold suzukiYoshidaEndpointSourceVariableProfile
    simp only [Int.cast_natCast]
    rw [hplus]
    push_cast
    dsimp [q]
    congr 2 <;> push_cast <;> field_simp
  have hprofileMinus :
      suzukiYoshidaEndpointSourceVariableProfile r (-(n : Int)) z =
        (((Real.sqrt (2 * r))⁻¹ *
          (2 * ((-1 : Real) ^ n) * Real.sin (r * z) / (z - q)) : Real) :
            Complex) := by
    unfold suzukiYoshidaEndpointSourceVariableProfile
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [hnegativeFrequency, hminus]
    push_cast
    rw [sub_eq_add_neg]
    congr 2 <;> field_simp
  unfold suzukiYoshidaEndpointSourceModeMasterIntegrand
    suzukiYoshidaEndpointSourceOddRationalProfile
    suzukiYoshidaEndpointSourceModeFrequency
    suzukiYoshidaEndpointSourceVariableIntegrand
  rw [hprofilePlus, hprofileMinus]
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [show ((n : Real) * Real.pi / r) = q by rfl]
  change
    suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
        ((z + q)⁻¹ - (z - q)⁻¹) =
      -((n : Real) * Real.pi) *
        (suzukiYoshidaEndpointSourceVariableWeight z *
          (((Real.sqrt (2 * r))⁻¹ *
              (2 * ((-1 : Real) ^ n) * Real.sin (r * z) /
                (z + q))) *
            ((Real.sqrt (2 * r))⁻¹ *
              (2 * ((-1 : Real) ^ n) * Real.sin (r * z) /
                (z - q)))))
  have hsign : ((-1 : Real) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  have hscaledPlus : r * z + (n : Real) * Real.pi ≠ 0 := by
    have heq : r * (z + q) = r * z + (n : Real) * Real.pi := by
      dsimp [q]
      field_simp [hr.ne']
    rw [← heq]
    exact mul_ne_zero hr.ne' hzplus
  have hscaledMinus : r * z - (n : Real) * Real.pi ≠ 0 := by
    have heq : r * (z - q) = r * z - (n : Real) * Real.pi := by
      dsimp [q]
      field_simp [hr.ne']
    rw [← heq]
    exact mul_ne_zero hr.ne' hzminus
  have hscaledProduct :
      r ^ 2 * z ^ 2 - (n : Real) ^ 2 * Real.pi ^ 2 ≠ 0 := by
    rw [show r ^ 2 * z ^ 2 - (n : Real) ^ 2 * Real.pi ^ 2 =
      (r * z + (n : Real) * Real.pi) *
        (r * z - (n : Real) * Real.pi) by ring]
    exact mul_ne_zero hscaledPlus hscaledMinus
  unfold q at *
  field_simp [hzplus, hzminus, hscaledPlus, hscaledMinus, hscaledProduct,
    hsqrtPos.ne', hr.ne']
  rw [hsign, Real.sq_sqrt (by positivity : 0 ≤ r * 2)]
  ring

/-- Integrability of the master family is inherited from the already checked
all-integer endpoint source pairing. -/
theorem integrable_suzukiYoshidaEndpointSourceModeMasterIntegrand
    {r : Real} (hr : 0 < r) (n : Nat) :
    Integrable (suzukiYoshidaEndpointSourceModeMasterIntegrand r n) := by
  have hsource :=
    integrable_suzukiYoshidaEndpointSourceVariableIntegrand
      hr (n : Int) (-(n : Int))
  have hreal : Integrable (fun z =>
      (suzukiYoshidaEndpointSourceVariableIntegrand
        r (n : Int) (-(n : Int)) z).re) := by
    simpa [Function.comp_def] using Complex.reCLM.integrable_comp hsource
  exact (hreal.const_mul (-((n : Real) * Real.pi))).congr
    (suzukiYoshidaEndpointSourceModeMasterIntegrand_ae_eq_oppositeMode
      hr n).symm

/-- The genuinely remaining analytic theorem: only the exact value of each
positive-mode master integral. -/
def SuzukiYoshidaEndpointSourceModeMasterIntegralEvaluation : Prop :=
  ∀ n : Nat, 0 < n →
    (∫ z : Real,
        suzukiYoshidaEndpointSourceModeMasterIntegrand
          suzukiProjectAStar n z) =
      Real.pi * suzukiYoshidaComparisonSourceSineTransform n

/-- The value-only theorem supplies the earlier combined master package
because integrability is now unconditional. -/
theorem suzukiYoshidaEndpointSourceModeMasterEvaluation_of_integralEvaluation
    (hevaluation :
      SuzukiYoshidaEndpointSourceModeMasterIntegralEvaluation) :
    SuzukiYoshidaEndpointSourceModeMasterEvaluation := by
  intro n hn
  exact ⟨
    integrable_suzukiYoshidaEndpointSourceModeMasterIntegrand
      suzukiProjectAStar_pos n,
    hevaluation n hn⟩

end

end RiemannHypothesisProject.Experiments.M100
