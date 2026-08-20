import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Fourier bounds from one-sided variation for M100-DF6D4

This module isolates the elementary integration-by-parts step used by the
smooth `r''` residual tail.  It does not assert the source-specific transform
identity or the monotonicity of Suzuki's kernel.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set

/-- A nonincreasing differentiable kernel on `[0, L]`, sampled at a frequency
whose cosine has matching endpoint values, has the sine-transform bound used
by the DF6D4 smooth residual.  The factor `4` includes the outer factor `-2`
from the project convolution convention. -/
theorem abs_neg_two_mul_intervalIntegral_mul_sin_le_of_deriv_nonpos
    {f f' : Real → Real} {L w : Real}
    (hL : 0 ≤ L) (hw : 0 < w)
    (hcos : Real.cos (w * L) = 1)
    (hf : ContinuousOn f (Icc 0 L))
    (hderiv : ∀ x ∈ Ioo 0 L, HasDerivAt f (f' x) x)
    (hnonpos : ∀ x ∈ Ioc 0 L, f' x ≤ 0)
    (hdifference : 0 ≤ f 0 - f L) :
    abs (-2 * (∫ t in (0 : Real)..L, f t * Real.sin (w * t))) ≤
      4 * (f 0 - f L) / w := by
  let v : Real → Real := fun t => -Real.cos (w * t) / w
  have hvDeriv (x : Real) : HasDerivAt v (Real.sin (w * x)) x := by
    dsimp only [v]
    simpa [hw.ne'] using
      (((hasDerivAt_const_mul (x := x) w).cos).neg.div_const w)
  have hvContinuous : ContinuousOn v (Icc 0 L) := by
    fun_prop
  have hfU : ContinuousOn f (uIcc 0 L) := by
    rwa [uIcc_of_le hL]
  have hvContinuousU : ContinuousOn v (uIcc 0 L) := by
    rwa [uIcc_of_le hL]
  have hderivU :
      ∀ x ∈ Ioo (min 0 L) (max 0 L), HasDerivAt f (f' x) x := by
    simpa [min_eq_left hL, max_eq_right hL] using hderiv
  have hnonposU :
      ∀ x ∈ Ioo (min 0 L) (max 0 L), f' x ≤ 0 := by
    intro x hx
    have hx' : x ∈ Ioo 0 L := by
      simpa [min_eq_left hL, max_eq_right hL] using hx
    apply hnonpos x
    exact ⟨hx'.1, hx'.2.le⟩
  have hf' : IntervalIntegrable f' volume 0 L := by
    have hcomposed :
        IntervalIntegrable
          (fun x : Real => ((fun _ : Real => 1) ∘ f) x * f' x)
          volume 0 L :=
      (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
        (g := fun _ : Real => 1) hfU hderivU hnonposU).2
          intervalIntegrable_const
    simpa using hcomposed
  have hsinIntegrable :
      IntervalIntegrable (fun t : Real => Real.sin (w * t)) volume 0 L := by
    exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_id)).intervalIntegrable 0 L
  have hparts :
      (∫ t in (0 : Real)..L, f t * Real.sin (w * t)) =
        f L * v L - f 0 * v 0 - ∫ t in (0 : Real)..L, f' t * v t := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hfU hvContinuousU hderivU
      (fun x _ => hvDeriv x) hf' hsinIntegrable
  have hfundamental :
      (∫ t in (0 : Real)..L, f' t) = f L - f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hL hf hderiv hf'
  have hmajorIntegrable :
      IntervalIntegrable (fun t : Real => -f' t / w) volume 0 L := by
    exact hf'.neg.div_const w
  have hderivativeIntegral :
      abs (∫ t in (0 : Real)..L, f' t * v t) ≤
        (f 0 - f L) / w := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le
      (μ := volume) hL
      (f := fun t : Real => f' t * v t)
      (g := fun t : Real => -f' t / w)
      (by
        filter_upwards with t ht
        have hft : f' t ≤ 0 := hnonpos t ht
        have hwNonneg : 0 ≤ w := hw.le
        dsimp only [v]
        rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
          abs_of_pos hw, abs_of_nonpos hft]
        have hcosDiv : |Real.cos (w * t)| / w ≤ w⁻¹ := by
          simpa [one_div] using
            div_le_div_of_nonneg_right (Real.abs_cos_le_one (w * t)) hwNonneg
        exact mul_le_mul_of_nonneg_left
          hcosDiv
          (neg_nonneg.mpr hft))
      hmajorIntegrable
    rw [Real.norm_eq_abs] at hbound
    calc
      abs (∫ t in (0 : Real)..L, f' t * v t) ≤
          ∫ t in (0 : Real)..L, -f' t / w := hbound
      _ = (f 0 - f L) / w := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_neg,
          hfundamental]
        ring
  have hboundary :
      f L * v L - f 0 * v 0 = (f 0 - f L) / w := by
    dsimp only [v]
    rw [hcos]
    simp only [mul_zero, Real.cos_zero]
    field_simp [hw.ne']
    ring
  have hquotientNonneg : 0 ≤ (f 0 - f L) / w :=
    div_nonneg hdifference hw.le
  have hintegral :
      abs (∫ t in (0 : Real)..L, f t * Real.sin (w * t)) ≤
        2 * (f 0 - f L) / w := by
    rw [hparts, hboundary]
    calc
      abs ((f 0 - f L) / w -
          ∫ t in (0 : Real)..L, f' t * v t) ≤
          abs ((f 0 - f L) / w) +
            abs (∫ t in (0 : Real)..L, f' t * v t) := abs_sub _ _
      _ ≤ (f 0 - f L) / w + (f 0 - f L) / w := by
        gcongr
        exact (abs_of_nonneg hquotientNonneg).le
      _ = 2 * (f 0 - f L) / w := by ring
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  calc
    2 * abs (∫ t in (0 : Real)..L, f t * Real.sin (w * t)) ≤
        2 * (2 * (f 0 - f L) / w) :=
      mul_le_mul_of_nonneg_left hintegral (by norm_num)
    _ = 4 * (f 0 - f L) / w := by ring

end

end RiemannHypothesisProject.Experiments.M100
