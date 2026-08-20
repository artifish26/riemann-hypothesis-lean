import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaAmbientResidualFunctional
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDiagonalArchimedeanEvaluation

/-!
# Modal-normalization phase audit for the B3R-E residual functionals

This module audits the first comparison-diagonal normalization required to
identify the B3R-E4 completed-mode pairings with the independently frozen
DF6D4 residual coefficients.  It derives the actual improper cosine tail,
retains the former sine-versus-cosine remainder discrepancy as a private
legacy witness, and proves the corrected public tail has the required exact
normalization.  No ambient functional or modal coefficient is admitted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-! ## Comparison cosine tail and diagonal normalization -/

/-- Historical DF6D4 comparison-tail expression whose remainder had the
wrong trigonometric phase.  It is retained locally so the E5 obstruction stays
checkable after correction of the public definition. -/
private def suzukiDF6D5B3RELegacySineRemainderCosineTail
    (mode : Nat) : Real :=
  let x := suzukiDF6D4ComparisonWave mode
  1 / x ^ 2 - 6 / x ^ 4 + 120 / x ^ 6 - 5040 / x ^ 8 +
    362880 / x ^ 10 -
      3628800 * (∫ t : Real in Ioi x, Real.sin t / t ^ 11)

private def suzukiDF6D5B3RECosineTailPrimitive (t : Real) : Real :=
  Real.sin t / t - Real.cos t / t ^ 2 -
    2 * Real.sin t / t ^ 3 + 6 * Real.cos t / t ^ 4 +
    24 * Real.sin t / t ^ 5 - 120 * Real.cos t / t ^ 6 -
    720 * Real.sin t / t ^ 7 + 5040 * Real.cos t / t ^ 8 +
    40320 * Real.sin t / t ^ 9 - 362880 * Real.cos t / t ^ 10

private theorem hasDerivAt_suzukiDF6D5B3RECosineTailPrimitive
    {t : Real} (ht : t ≠ 0) :
    HasDerivAt suzukiDF6D5B3RECosineTailPrimitive
      (Real.cos t / t + 3628800 * Real.cos t / t ^ 11) t := by
  unfold suzukiDF6D5B3RECosineTailPrimitive
  convert ((((((((((
    (Real.hasDerivAt_sin t).div (hasDerivAt_id t) ht).sub
      ((Real.hasDerivAt_cos t).div ((hasDerivAt_id t).pow 2)
        (pow_ne_zero 2 ht))).sub
      (((Real.hasDerivAt_sin t).const_mul 2).div
        ((hasDerivAt_id t).pow 3) (pow_ne_zero 3 ht))).add
      (((Real.hasDerivAt_cos t).const_mul 6).div
        ((hasDerivAt_id t).pow 4) (pow_ne_zero 4 ht))).add
      (((Real.hasDerivAt_sin t).const_mul 24).div
        ((hasDerivAt_id t).pow 5) (pow_ne_zero 5 ht))).sub
      (((Real.hasDerivAt_cos t).const_mul 120).div
        ((hasDerivAt_id t).pow 6) (pow_ne_zero 6 ht))).sub
      (((Real.hasDerivAt_sin t).const_mul 720).div
        ((hasDerivAt_id t).pow 7) (pow_ne_zero 7 ht))).add
      (((Real.hasDerivAt_cos t).const_mul 5040).div
        ((hasDerivAt_id t).pow 8) (pow_ne_zero 8 ht))).add
      (((Real.hasDerivAt_sin t).const_mul 40320).div
        ((hasDerivAt_id t).pow 9) (pow_ne_zero 9 ht))).sub
      (((Real.hasDerivAt_cos t).const_mul 362880).div
        ((hasDerivAt_id t).pow 10) (pow_ne_zero 10 ht))) using 1 <;>
    try rfl
  · norm_num [id_eq, Pi.pow_apply]
    field_simp [ht]
    ring

private theorem intervalIntegrable_cosineTailDerivative
    {x R : Real} (hx : 0 < x) (hR : x ≤ R) :
    IntervalIntegrable
      (fun t : Real => Real.cos t / t + 3628800 * Real.cos t / t ^ 11)
      volume x R := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hR] at ht
  have ht0 : t ≠ 0 := (hx.trans_le ht.1).ne'
  convert ((Real.continuous_cos.continuousAt.div continuousAt_id ht0).add
    ((Real.continuous_cos.continuousAt.div (continuousAt_id.pow 11)
      (pow_ne_zero 11 ht0)).const_mul 3628800)).continuousWithinAt using 1
  · funext y
    simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply, Pi.inv_apply,
      Pi.pow_apply, id_eq, div_eq_mul_inv]
    ring

private theorem integral_cos_tail_eq_primitive_sub
    {x R : Real} (hx : 0 < x) (hR : x ≤ R) :
    (∫ t in x..R, Real.cos t / t) =
        suzukiDF6D5B3RECosineTailPrimitive R -
        suzukiDF6D5B3RECosineTailPrimitive x -
          3628800 * (∫ t in x..R, Real.cos t / t ^ 11) := by
  have hderiv : ∀ t ∈ uIcc x R,
      HasDerivAt suzukiDF6D5B3RECosineTailPrimitive
        (Real.cos t / t + 3628800 * Real.cos t / t ^ 11) t := by
    intro t ht
    rw [uIcc_of_le hR] at ht
    exact hasDerivAt_suzukiDF6D5B3RECosineTailPrimitive
      (hx.trans_le ht.1).ne'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_cosineTailDerivative hx hR)
  have hcos : IntervalIntegrable (fun t : Real => Real.cos t / t)
      volume x R := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hR] at ht
    exact (Real.continuous_cos.continuousAt.div continuousAt_id
      (hx.trans_le ht.1).ne').continuousWithinAt
  have hremInt : IntervalIntegrable (fun t : Real => Real.cos t / t ^ 11)
      volume x R := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hR] at ht
    have ht0 : t ≠ 0 := (hx.trans_le ht.1).ne'
    exact (Real.continuous_cos.continuousAt.div (continuousAt_id.pow 11)
      (pow_ne_zero 11 ht0)).continuousWithinAt
  have hsplit :
      (∫ t in x..R,
        Real.cos t / t + 3628800 * Real.cos t / t ^ 11) =
        (∫ t in x..R, Real.cos t / t) +
          3628800 * (∫ t in x..R, Real.cos t / t ^ 11) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_add hcos (hremInt.const_mul 3628800)]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hsplit] at hftc
  linarith

private theorem tendsto_trig_div_pow_atTop_zero'
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

private theorem tendsto_suzukiDF6D5B3RECosineTailPrimitive_atTop :
    Tendsto suzukiDF6D5B3RECosineTailPrimitive atTop (𝓝 0) := by
  have hcos (n : Nat) (hn : n ≠ 0) :
      Tendsto (fun t : Real => Real.cos t / t ^ n) atTop (𝓝 0) :=
    tendsto_trig_div_pow_atTop_zero' Real.cos Real.abs_cos_le_one n hn
  have hsin (n : Nat) (hn : n ≠ 0) :
      Tendsto (fun t : Real => Real.sin t / t ^ n) atTop (𝓝 0) :=
    tendsto_trig_div_pow_atTop_zero' Real.sin Real.abs_sin_le_one n hn
  unfold suzukiDF6D5B3RECosineTailPrimitive
  have h1 := (hsin 1 (by norm_num)).sub (hcos 2 (by norm_num))
  have h2 := h1.sub ((hsin 3 (by norm_num)).const_mul 2)
  have h3 := h2.add ((hcos 4 (by norm_num)).const_mul 6)
  have h4 := h3.add ((hsin 5 (by norm_num)).const_mul 24)
  have h5 := h4.sub ((hcos 6 (by norm_num)).const_mul 120)
  have h6 := h5.sub ((hsin 7 (by norm_num)).const_mul 720)
  have h7 := h6.add ((hcos 8 (by norm_num)).const_mul 5040)
  have h8 := h7.add ((hsin 9 (by norm_num)).const_mul 40320)
  have h9 := h8.sub ((hcos 10 (by norm_num)).const_mul 362880)
  simpa [mul_div_assoc] using h9

private theorem suzukiDF6D5B3RECosineTailPrimitive_at_wave (mode : Nat) :
    suzukiDF6D5B3RECosineTailPrimitive
        (suzukiDF6D4ComparisonWave mode) =
      -(1 / suzukiDF6D4ComparisonWave mode ^ 2 -
        6 / suzukiDF6D4ComparisonWave mode ^ 4 +
        120 / suzukiDF6D4ComparisonWave mode ^ 6 -
        5040 / suzukiDF6D4ComparisonWave mode ^ 8 +
        362880 / suzukiDF6D4ComparisonWave mode ^ 10) := by
  have hsin : Real.sin (suzukiDF6D4ComparisonWave mode) = 0 := by
    unfold suzukiDF6D4ComparisonWave
    convert Real.sin_nat_mul_pi (2 * mode) using 1 <;> norm_num <;> ring
  have hcos : Real.cos (suzukiDF6D4ComparisonWave mode) = 1 := by
    unfold suzukiDF6D4ComparisonWave
    convert Real.cos_nat_mul_two_pi mode using 1 <;> ring
  unfold suzukiDF6D5B3RECosineTailPrimitive
  rw [hsin, hcos]
  ring

theorem suzukiDF6D4ComparisonCosineTail_phase_discrepancy
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiCosineTailConstant -
        suzukiCosineTailPartialReal (suzukiDF6D4ComparisonWave mode) =
      suzukiDF6D5B3RELegacySineRemainderCosineTail mode + 3628800 *
        ((∫ t : Real in Ioi (suzukiDF6D4ComparisonWave mode),
            Real.sin t / t ^ 11) -
          ∫ t : Real in Ioi (suzukiDF6D4ComparisonWave mode),
            Real.cos t / t ^ 11) := by
  let x := suzukiDF6D4ComparisonWave mode
  have hx : 0 < x := by
    unfold x suzukiDF6D4ComparisonWave
    positivity
  have hxOne : 1 ≤ x := by
    unfold x suzukiDF6D4ComparisonWave
    have hm : (1 : Real) ≤ mode := by exact_mod_cast hmode
    nlinarith [Real.pi_gt_three,
      mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Real.pi by positivity)]
  have hmajor : IntegrableOn (fun t : Real => t ^ (-11 : Real)) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  have hcosInt : IntegrableOn (fun t : Real => Real.cos t / t ^ 11) (Ioi x) := by
    apply hmajor.mono'
    · exact (Real.continuous_cos.aemeasurable.div
        (continuous_id.pow 11).aemeasurable).aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := hx.trans ht
      change ‖Real.cos t / t ^ 11‖ ≤ t ^ (-11 : Real)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos 11)]
      rw [show t ^ (-11 : Real) = 1 / t ^ 11 by
        norm_num [Real.rpow_neg_ofNat, zpow_neg]
        rfl]
      exact div_le_div_of_nonneg_right (Real.abs_cos_le_one t)
        (pow_nonneg htpos.le 11)
  have hrem := intervalIntegral_tendsto_integral_Ioi x hcosInt tendsto_id
  have hformula : Tendsto
      (fun R : Real =>
        suzukiDF6D5B3RECosineTailPrimitive R -
          suzukiDF6D5B3RECosineTailPrimitive x -
            3628800 * (∫ t in x..R, Real.cos t / t ^ 11))
      atTop
      (𝓝 (0 - suzukiDF6D5B3RECosineTailPrimitive x -
        3628800 * (∫ t : Real in Ioi x, Real.cos t / t ^ 11))) :=
    (tendsto_suzukiDF6D5B3RECosineTailPrimitive_atTop.sub_const _).sub
      (hrem.const_mul 3628800)
  have htailFormula : Tendsto
      (fun R : Real => ∫ t in x..R, Real.cos t / t)
      atTop
      (𝓝 (0 - suzukiDF6D5B3RECosineTailPrimitive x -
        3628800 * (∫ t : Real in Ioi x, Real.cos t / t ^ 11))) := by
    apply hformula.congr'
    filter_upwards [eventually_ge_atTop x] with R hR
    exact (integral_cos_tail_eq_primitive_sub hx hR).symm
  have htailFromConstant : Tendsto
      (fun R : Real => ∫ t in x..R, Real.cos t / t)
      atTop
      (𝓝 (suzukiCosineTailConstant -
        suzukiCosineTailPartialReal x)) := by
    apply (tendsto_suzukiCosineTailPartialReal.sub_const
      (suzukiCosineTailPartialReal x)).congr'
    filter_upwards [eventually_ge_atTop x] with R hR
    have hleft := intervalIntegrable_cos_div_of_one_le
      (le_refl (1 : Real)) hxOne
    have hROne : 1 ≤ R := hxOne.trans hR
    have hright := intervalIntegrable_cos_div_of_one_le hxOne hROne
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    unfold suzukiCosineTailPartialReal
    linarith
  have hlimits := tendsto_nhds_unique htailFormula htailFromConstant
  rw [suzukiDF6D5B3RECosineTailPrimitive_at_wave mode] at hlimits
  unfold suzukiDF6D5B3RELegacySineRemainderCosineTail
  dsimp only [x] at hlimits ⊢
  linarith

/-- The frozen DF6D4 cosine tail agrees with the actual improper cosine tail
exactly when its sine remainder happens to equal the cosine remainder produced
by integration by parts.  This is the precise phase obstruction encountered by
the modal-normalization gate. -/
theorem suzukiDF6D4ComparisonCosineTail_eq_improper_iff_remainders_eq
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D5B3RELegacySineRemainderCosineTail mode =
        suzukiCosineTailConstant -
          suzukiCosineTailPartialReal (suzukiDF6D4ComparisonWave mode) ↔
      (∫ t : Real in Ioi (suzukiDF6D4ComparisonWave mode),
          Real.sin t / t ^ 11) =
        ∫ t : Real in Ioi (suzukiDF6D4ComparisonWave mode),
          Real.cos t / t ^ 11 := by
  have hphase := suzukiDF6D4ComparisonCosineTail_phase_discrepancy mode hmode
  constructor <;> intro h
  · linarith
  · linarith

/-- After the DF6D4 phase correction, the public comparison cosine tail is
exactly the independently constructed improper cosine tail. -/
theorem suzukiDF6D4ComparisonCosineTail_eq_improper
    (mode : Nat) (hmode : 1 ≤ mode) :
    suzukiDF6D4ComparisonCosineTail mode =
      suzukiCosineTailConstant -
        suzukiCosineTailPartialReal (suzukiDF6D4ComparisonWave mode) := by
  have hphase := suzukiDF6D4ComparisonCosineTail_phase_discrepancy mode hmode
  unfold suzukiDF6D5B3RELegacySineRemainderCosineTail at hphase
  unfold suzukiDF6D4ComparisonCosineTail
  linarith

theorem integral_suzukiCosineRegularPart_to_wave_with_phase_discrepancy
    (mode : Nat) (hmode : 1 ≤ mode) :
    (∫ t in (0 : Real)..suzukiDF6D4ComparisonWave mode,
      suzukiCosineRegularPart t) =
      -Real.eulerMascheroniConstant -
        Real.log (suzukiDF6D4ComparisonWave mode) -
          suzukiDF6D5B3RELegacySineRemainderCosineTail mode - 3628800 *
            ((∫ t : Real in Ioi (suzukiDF6D4ComparisonWave mode),
                Real.sin t / t ^ 11) -
              ∫ t : Real in Ioi (suzukiDF6D4ComparisonWave mode),
                Real.cos t / t ^ 11) := by
  let x := suzukiDF6D4ComparisonWave mode
  have hx : 1 ≤ x := by
    unfold x suzukiDF6D4ComparisonWave
    have hm : (1 : Real) ≤ mode := by exact_mod_cast hmode
    nlinarith [Real.pi_gt_three,
      mul_le_mul_of_nonneg_left hm (show 0 ≤ 2 * Real.pi by positivity)]
  have hzeroOne := continuous_suzukiCosineRegularPart.intervalIntegrable
    (μ := volume) 0 1
  have honeX : IntervalIntegrable suzukiCosineRegularPart volume 1 x :=
    continuous_suzukiCosineRegularPart.intervalIntegrable 1 x
  have hadd := intervalIntegral.integral_add_adjacent_intervals hzeroOne honeX
  have htailPoint :
      (∫ t in (1 : Real)..x, suzukiCosineRegularPart t) =
        suzukiCosineTailPartialReal x - Real.log x := by
    have hcos := intervalIntegrable_cos_div_of_one_le (le_refl (1 : Real)) hx
    have hinv : IntervalIntegrable (fun t : Real => 1 / t) volume 1 x := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [uIcc_of_le hx] at ht
      exact (continuousAt_const.div continuousAt_id
        (zero_lt_one.trans_le ht.1).ne').continuousWithinAt
    have hinvValue : (∫ t in (1 : Real)..x, 1 / t) = Real.log x := by
      simpa using integral_inv_of_pos zero_lt_one (zero_lt_one.trans_le hx)
    calc
      (∫ t in (1 : Real)..x, suzukiCosineRegularPart t) =
          ∫ t in (1 : Real)..x, Real.cos t / t - 1 / t := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiCosineRegularPart
            ring
      _ = (∫ t in (1 : Real)..x, Real.cos t / t) -
          (∫ t in (1 : Real)..x, 1 / t) :=
            intervalIntegral.integral_sub hcos hinv
      _ = suzukiCosineTailPartialReal x - Real.log x := by
            rw [hinvValue]
            rfl
  have hconstant := suzukiCosineIntegralConstantIdentity
  have htail := suzukiDF6D4ComparisonCosineTail_phase_discrepancy mode hmode
  change suzukiCosineRegularConstant + suzukiCosineTailConstant =
    -Real.eulerMascheroniConstant at hconstant
  unfold suzukiCosineRegularConstant at hconstant
  dsimp only [x] at hadd htailPoint htail ⊢
  linarith

/-- Corrected comparison-diagonal cosine-regular integral, with no residual
phase term. -/
theorem integral_suzukiCosineRegularPart_to_wave
    (mode : Nat) (hmode : 1 ≤ mode) :
    (∫ t in (0 : Real)..suzukiDF6D4ComparisonWave mode,
      suzukiCosineRegularPart t) =
      -Real.eulerMascheroniConstant -
        Real.log (suzukiDF6D4ComparisonWave mode) -
          suzukiDF6D4ComparisonCosineTail mode := by
  have hlegacy :=
    integral_suzukiCosineRegularPart_to_wave_with_phase_discrepancy mode hmode
  unfold suzukiDF6D5B3RELegacySineRemainderCosineTail at hlegacy
  unfold suzukiDF6D4ComparisonCosineTail
  linarith

end

end RiemannHypothesisProject.Experiments.M100
