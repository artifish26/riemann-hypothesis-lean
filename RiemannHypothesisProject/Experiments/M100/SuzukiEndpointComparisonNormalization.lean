import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointSmoothSumIntegral

/-!
# Finite Dirichlet comparison normalization for M100-DF6D4

This module isolates the classical Dirichlet integral as a visible source
theorem and proves the project-specific normalization from it.  The five-term
comparison tail is connected to the finite sinc integral by an exact
integration-by-parts primitive at the resonant endpoint `2 * pi * mode`.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

/-- Literature-shaped source theorem needed by the comparison normalization. -/
def SuzukiDirichletIntegralSource : Prop :=
  Tendsto (fun R : Real => ∫ t in (0 : Real)..R, Real.sinc t)
    atTop (𝓝 (Real.pi / 2))

/-- Nine-step integration-by-parts primitive for the sine-integral tail. -/
def suzukiDF6D4SineTailPrimitive (t : Real) : Real :=
  -Real.cos t / t - Real.sin t / t ^ 2 +
    2 * Real.cos t / t ^ 3 + 6 * Real.sin t / t ^ 4 -
    24 * Real.cos t / t ^ 5 - 120 * Real.sin t / t ^ 6 +
    720 * Real.cos t / t ^ 7 + 5040 * Real.sin t / t ^ 8 -
    40320 * Real.cos t / t ^ 9

theorem hasDerivAt_suzukiDF6D4SineTailPrimitive
    {t : Real} (ht : t ≠ 0) :
    HasDerivAt suzukiDF6D4SineTailPrimitive
      (Real.sin t / t + 362880 * Real.cos t / t ^ 10) t := by
  unfold suzukiDF6D4SineTailPrimitive
  convert (((((((((
    (Real.hasDerivAt_cos t).neg.div (hasDerivAt_id t) ht).sub
      ((Real.hasDerivAt_sin t).div ((hasDerivAt_id t).pow 2)
        (pow_ne_zero 2 ht))).add
      (((Real.hasDerivAt_cos t).const_mul 2).div
        ((hasDerivAt_id t).pow 3) (pow_ne_zero 3 ht))).add
      (((Real.hasDerivAt_sin t).const_mul 6).div
        ((hasDerivAt_id t).pow 4) (pow_ne_zero 4 ht))).sub
      (((Real.hasDerivAt_cos t).const_mul 24).div
        ((hasDerivAt_id t).pow 5) (pow_ne_zero 5 ht))).sub
      (((Real.hasDerivAt_sin t).const_mul 120).div
        ((hasDerivAt_id t).pow 6) (pow_ne_zero 6 ht))).add
      (((Real.hasDerivAt_cos t).const_mul 720).div
        ((hasDerivAt_id t).pow 7) (pow_ne_zero 7 ht))).add
      (((Real.hasDerivAt_sin t).const_mul 5040).div
        ((hasDerivAt_id t).pow 8) (pow_ne_zero 8 ht))).sub
      (((Real.hasDerivAt_cos t).const_mul 40320).div
        ((hasDerivAt_id t).pow 9) (pow_ne_zero 9 ht))) using 1 <;>
    try rfl
  · norm_num [id_eq, Pi.pow_apply]
    field_simp [ht]
    ring

private theorem intervalIntegrable_sineTailDerivative
    {x R : Real} (hx : 0 < x) (hR : x ≤ R) :
    IntervalIntegrable
      (fun t : Real => Real.sin t / t + 362880 * Real.cos t / t ^ 10)
      volume x R := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hR] at ht
  have ht0 : t ≠ 0 := (hx.trans_le ht.1).ne'
  convert ((Real.continuous_sin.continuousAt.div continuousAt_id ht0).add
    ((Real.continuous_cos.continuousAt.div
      (continuousAt_id.pow 10) (pow_ne_zero 10 ht0)).const_mul
        362880)).continuousWithinAt using 1
  · funext y
    simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply, Pi.inv_apply,
      Pi.pow_apply, id_eq, div_eq_mul_inv]
    ring

theorem integral_sinc_tail_eq_primitive_sub
    {x R : Real} (hx : 0 < x) (hR : x ≤ R) :
    (∫ t in x..R, Real.sinc t) =
      suzukiDF6D4SineTailPrimitive R -
        suzukiDF6D4SineTailPrimitive x -
          362880 * (∫ t in x..R, Real.cos t / t ^ 10) := by
  have hderiv : ∀ t ∈ uIcc x R,
      HasDerivAt suzukiDF6D4SineTailPrimitive
        (Real.sin t / t + 362880 * Real.cos t / t ^ 10) t := by
    intro t ht
    rw [uIcc_of_le hR] at ht
    exact hasDerivAt_suzukiDF6D4SineTailPrimitive
      (hx.trans_le ht.1).ne'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_sineTailDerivative hx hR)
  have hsin : IntervalIntegrable (fun t : Real => Real.sin t / t)
      volume x R := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hR] at ht
    exact (Real.continuous_sin.continuousAt.div continuousAt_id
      (hx.trans_le ht.1).ne').continuousWithinAt
  have hcos : IntervalIntegrable (fun t : Real => Real.cos t / t ^ 10)
      volume x R := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hR] at ht
    have ht0 : t ≠ 0 := (hx.trans_le ht.1).ne'
    exact (Real.continuous_cos.continuousAt.div (continuousAt_id.pow 10)
      (pow_ne_zero 10 ht0)).continuousWithinAt
  have hsinc :
      (∫ t in x..R, Real.sinc t) = ∫ t in x..R, Real.sin t / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hR] at ht
    exact Real.sinc_of_ne_zero (hx.trans_le ht.1).ne'
  rw [hsinc]
  have hsplit :
      (∫ t in x..R,
        Real.sin t / t + 362880 * Real.cos t / t ^ 10) =
        (∫ t in x..R, Real.sin t / t) +
          362880 * (∫ t in x..R, Real.cos t / t ^ 10) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hsin (hcos.const_mul 362880)]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hsplit] at hftc
  linarith

private theorem tendsto_trig_div_pow_atTop_zero
    (f : Real → Real) (hbound : ∀ t, |f t| ≤ 1)
    (n : Nat) (hn : n ≠ 0) :
    Tendsto (fun t : Real => f t / t ^ n) atTop (𝓝 0) := by
  have hpow : Tendsto (fun t : Real => (t ^ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop hn)
  have habs : Tendsto (fun t : Real => |f t / t ^ n|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ hpow
    filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
    rw [abs_div, abs_of_pos (pow_pos ht n), div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_right (hbound t)
      (inv_nonneg.mpr (pow_nonneg ht.le n))).trans_eq (one_mul _)
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

theorem tendsto_suzukiDF6D4SineTailPrimitive_atTop :
    Tendsto suzukiDF6D4SineTailPrimitive atTop (𝓝 0) := by
  have hcos (n : Nat) (hn : n ≠ 0) :
      Tendsto (fun t : Real => Real.cos t / t ^ n) atTop (𝓝 0) :=
    tendsto_trig_div_pow_atTop_zero Real.cos Real.abs_cos_le_one n hn
  have hsin (n : Nat) (hn : n ≠ 0) :
      Tendsto (fun t : Real => Real.sin t / t ^ n) atTop (𝓝 0) :=
    tendsto_trig_div_pow_atTop_zero Real.sin Real.abs_sin_le_one n hn
  unfold suzukiDF6D4SineTailPrimitive
  have h1 := (hcos 1 (by norm_num)).neg.sub (hsin 2 (by norm_num))
  have h2 := h1.add ((hcos 3 (by norm_num)).const_mul 2)
  have h3 := h2.add ((hsin 4 (by norm_num)).const_mul 6)
  have h4 := h3.sub ((hcos 5 (by norm_num)).const_mul 24)
  have h5 := h4.sub ((hsin 6 (by norm_num)).const_mul 120)
  have h6 := h5.add ((hcos 7 (by norm_num)).const_mul 720)
  have h7 := h6.add ((hsin 8 (by norm_num)).const_mul 5040)
  have h8 := h7.sub ((hcos 9 (by norm_num)).const_mul 40320)
  simpa [neg_div, mul_div_assoc] using h8

private theorem integrableOn_suzukiDF6D4CosineTailTenth
    {x : Real} (hx : 0 < x) :
    IntegrableOn (fun t : Real => Real.cos t / t ^ 10) (Ioi x) := by
  have hmajor : IntegrableOn (fun t : Real => t ^ (-10 : Real)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  apply hmajor.mono'
  · exact (Real.continuous_cos.aemeasurable.div
      (continuous_id.pow 10).aemeasurable).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hx.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos 10)]
    rw [show t ^ (-10 : Real) = 1 / t ^ 10 by
      norm_num [Real.rpow_neg_ofNat, zpow_neg]
      rfl]
    exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t)
      (pow_nonneg htpos.le 10)

private theorem suzukiDF6D4SineTailPrimitive_at_wave (mode : Nat) :
    suzukiDF6D4SineTailPrimitive (suzukiDF6D4ComparisonWave mode) =
      -(1 / suzukiDF6D4ComparisonWave mode -
        2 / suzukiDF6D4ComparisonWave mode ^ 3 +
        24 / suzukiDF6D4ComparisonWave mode ^ 5 -
        720 / suzukiDF6D4ComparisonWave mode ^ 7 +
        40320 / suzukiDF6D4ComparisonWave mode ^ 9) := by
  have hsin : Real.sin (suzukiDF6D4ComparisonWave mode) = 0 := by
    unfold suzukiDF6D4ComparisonWave
    convert Real.sin_nat_mul_pi (2 * mode) using 1 <;> norm_num <;> ring
  have hcos : Real.cos (suzukiDF6D4ComparisonWave mode) = 1 := by
    unfold suzukiDF6D4ComparisonWave
    convert Real.cos_nat_mul_two_pi mode using 1 <;> ring
  unfold suzukiDF6D4SineTailPrimitive
  rw [hsin, hcos]
  ring

theorem suzukiDF6D4ComparisonSineTail_eq_pi_div_two_sub_integral
    (hdirichlet : SuzukiDirichletIntegralSource)
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D4ComparisonSineTail mode =
      Real.pi / 2 -
        ∫ t in (0 : Real)..suzukiDF6D4ComparisonWave mode, Real.sinc t := by
  let x := suzukiDF6D4ComparisonWave mode
  have hx : 0 < x := by
    unfold x suzukiDF6D4ComparisonWave
    positivity
  have hrem := intervalIntegral_tendsto_integral_Ioi x
    (integrableOn_suzukiDF6D4CosineTailTenth hx) tendsto_id
  have hformula : Tendsto
      (fun R : Real =>
        suzukiDF6D4SineTailPrimitive R -
          suzukiDF6D4SineTailPrimitive x -
            362880 * (∫ t in x..R, Real.cos t / t ^ 10))
      atTop
      (𝓝 (0 - suzukiDF6D4SineTailPrimitive x -
        362880 * (∫ t : Real in Ioi x, Real.cos t / t ^ 10))) :=
    (tendsto_suzukiDF6D4SineTailPrimitive_atTop.sub_const _).sub
      (hrem.const_mul 362880)
  have htailFromFormula : Tendsto
      (fun R : Real => ∫ t in x..R, Real.sinc t)
      atTop
      (𝓝 (0 - suzukiDF6D4SineTailPrimitive x -
        362880 * (∫ t : Real in Ioi x, Real.cos t / t ^ 10))) := by
    apply hformula.congr'
    filter_upwards [eventually_ge_atTop x] with R hR
    exact (integral_sinc_tail_eq_primitive_sub hx hR).symm
  have htailFromDirichlet : Tendsto
      (fun R : Real => ∫ t in x..R, Real.sinc t)
      atTop
      (𝓝 (Real.pi / 2 - ∫ t in (0 : Real)..x, Real.sinc t)) := by
    apply (hdirichlet.sub_const
      (∫ t in (0 : Real)..x, Real.sinc t)).congr'
    filter_upwards [eventually_ge_atTop x] with R hR
    have hleft := Real.continuous_sinc.intervalIntegrable
      (μ := volume) (0 : Real) x
    have hright := Real.continuous_sinc.intervalIntegrable
      (μ := volume) x R
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    linarith
  have hlimits := tendsto_nhds_unique htailFromFormula htailFromDirichlet
  rw [suzukiDF6D4SineTailPrimitive_at_wave mode] at hlimits
  unfold suzukiDF6D4ComparisonSineTail
  dsimp only [x] at hlimits ⊢
  linarith

theorem suzukiDF6D4SingularSineIntegral_eq_comparisonSineIntegral
    (hdirichlet : SuzukiDirichletIntegralSource)
    (mode : Nat) (hmode : 1 ≤ mode) :
    2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (1 / (2 * t)) *
        Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      suzukiDF6D4ComparisonSineIntegral mode := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hmodeReal : (0 : Real) < mode := by
    exact_mod_cast (Nat.zero_lt_of_lt hmode)
  have hw : 0 < w := by
    unfold w
    exact div_pos (mul_pos hmodeReal Real.pi_pos) suzukiProjectAStar_pos
  have hscaled :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        w * Real.sinc (w * t)) =
        ∫ u in (0 : Real)..suzukiDF6D4ComparisonWave mode, Real.sinc u := by
    calc
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        w * Real.sinc (w * t)) =
          w * ∫ t in (0 : Real)..2 * suzukiProjectAStar,
            Real.sinc (w * t) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ∫ u in w * 0..w * (2 * suzukiProjectAStar),
          Real.sinc u := by
        simpa only [smul_eq_mul] using
          (intervalIntegral.smul_integral_comp_mul_left
            Real.sinc w (a := (0 : Real))
              (b := 2 * suzukiProjectAStar))
      _ = ∫ u in (0 : Real)..suzukiDF6D4ComparisonWave mode,
          Real.sinc u := by
        congr 1
        · ring
        · unfold w suzukiDF6D4ComparisonWave
          field_simp [suzukiProjectAStar_pos.ne']
  have hsingular :
      2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (1 / (2 * t)) * Real.sin (w * t)) =
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          w * Real.sinc (w * t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : Real)] with t ht
    intro _
    rw [Real.sinc_of_ne_zero (mul_ne_zero hw.ne' ht)]
    field_simp [ht, hw.ne']
  rw [show (((mode : Real) * Real.pi / suzukiProjectAStar) = w) by rfl]
  rw [hsingular, hscaled]
  unfold suzukiDF6D4ComparisonSineIntegral
  rw [suzukiDF6D4ComparisonSineTail_eq_pi_div_two_sub_integral
    hdirichlet mode hmode]
  ring

theorem suzukiDF6D4ComparisonSineTransform_normalization
    (hdirichlet : SuzukiDirichletIntegralSource)
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D4ComparisonSineTransform mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (1 / (2 * t)) *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) := by
  unfold suzukiDF6D4ComparisonSineTransform
  have h := suzukiDF6D4SingularSineIntegral_eq_comparisonSineIntegral
    hdirichlet mode hmode
  linarith

theorem suzukiDF6D4ArchimedeanIdentity_of_dirichletIntegral
    (hdirichlet : SuzukiDirichletIntegralSource)
    (mode : Nat) (hmode : 1 ≤ mode) :
    -((Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im -
        ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) -
        suzukiDF6D4ComparisonSineTransform mode =
      -2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiR1SecondKernel t *
          Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) :=
  suzukiDF6D4ArchimedeanIdentity_of_comparison mode
    (suzukiDF6D4ComparisonSineTransform_normalization
      hdirichlet mode hmode)

end

end RiemannHypothesisProject.Experiments.M100
