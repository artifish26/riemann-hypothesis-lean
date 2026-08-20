import Mathlib.Analysis.Calculus.SmoothSeries
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDirichletIntegral
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCutoff44DF0Bridge

namespace RiemannHypothesisProject.Experiments.M100
noncomputable section
open Filter MeasureTheory Set
open scoped Topology

/-!
# DF0 quarter-sine source evaluations for B3F-E

This module proves that DF0's two custom quarter-sine representations agree
with the finite sinc integral.  The small branch is identified with the full
absolutely convergent sine-integral series.  The large branch is identified
through the Dirichlet integral and DF0's independent improper-tail formula.
-/

set_option maxHeartbeats 0

private theorem summable_sineIntegralMagnitude {x : Real} (hx0 : 0 ≤ x) :
    Summable (suzukiDF6D4DF0SineIntegralMagnitude x) := by
  have hs := (Real.hasSum_sinh x).summable
  apply Summable.of_nonneg_of_le
    (fun n => by
      unfold suzukiDF6D4DF0SineIntegralMagnitude
      positivity) _ hs
  intro n
  unfold suzukiDF6D4DF0SineIntegralMagnitude
  have hnum : 0 ≤ x ^ (2 * n + 1) := pow_nonneg hx0 _
  apply div_le_div_of_nonneg_left hnum
  · positivity
  · push_cast
    have hfactor : (1 : Real) ≤ ((2 * n + 1 : Nat) : Real) := by
      exact_mod_cast (show 1 ≤ 2 * n + 1 by omega)
    have hfactorial :
        (0 : Real) ≤ (((2 * n + 1 : Nat).factorial : Nat) : Real) := by
      positivity
    nlinarith

theorem suzukiDF6D4DF0SmallSineIntegral_eq_tsum
    {x : Real} (hx0 : 0 ≤ x) :
    suzukiDF6D4DF0SmallSineIntegral x =
      ∑' n : Nat, (-1 : Real) ^ n *
        suzukiDF6D4DF0SineIntegralMagnitude x n := by
  let f : Nat → Real := fun n => (-1 : Real) ^ n *
    suzukiDF6D4DF0SineIntegralMagnitude x n
  have hf : Summable f := by
    apply (summable_sineIntegralMagnitude hx0).of_norm_bounded
    intro n
    have hmag : 0 ≤ suzukiDF6D4DF0SineIntegralMagnitude x n := by
      unfold suzukiDF6D4DF0SineIntegralMagnitude
      positivity
    dsimp [f]
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg hmag]
  rw [hf.tsum_eq_zero_add]
  have hf1 : Summable (fun n : Nat => f (n + 1)) :=
    hf.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  rw [hf1.tsum_eq_zero_add]
  change suzukiDF6D4DF0SmallSineIntegral x =
    f 0 + (f 1 + ∑' n : Nat, f (n + 1 + 1))
  unfold suzukiDF6D4DF0SmallSineIntegral
  dsimp [f]
  norm_num
  rw [show
    suzukiDF6D4DF0SineIntegralMagnitude x 0 +
      (-suzukiDF6D4DF0SineIntegralMagnitude x 1 +
        ∑' n : Nat, (-1 : Real) ^ (n + 1 + 1) *
          suzukiDF6D4DF0SineIntegralMagnitude x (n + 1 + 1)) =
      suzukiDF6D4DF0SineIntegralMagnitude x 0 -
        suzukiDF6D4DF0SineIntegralMagnitude x 1 +
          ∑' n : Nat, (-1 : Real) ^ (n + 1 + 1) *
            suzukiDF6D4DF0SineIntegralMagnitude x (n + 1 + 1) by ring]
  congr 1
  apply tsum_congr
  intro n
  rw [pow_add]
  norm_num
  ring

private def siTerm (n : Nat) (y : Real) : Real :=
  (-1 : Real) ^ n * suzukiDF6D4DF0SineIntegralMagnitude y n

private def sincSeriesTerm (n : Nat) (y : Real) : Real :=
  (-1 : Real) ^ n * y ^ (2 * n) / (2 * n + 1).factorial

private theorem hasDerivAt_siTerm (n : Nat) (y : Real) :
    HasDerivAt (siTerm n) (sincSeriesTerm n y) y := by
  unfold siTerm sincSeriesTerm suzukiDF6D4DF0SineIntegralMagnitude
  have hpow := (hasDerivAt_id y).pow (2 * n + 1)
  have hconst := hpow.const_mul ((-1 : Real) ^ n)
  have hdiv := hconst.div_const
    (((2 * n + 1 : Nat) * (2 * n + 1).factorial : Nat) : Real)
  apply (hdiv.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
    simp only [id_eq, Pi.pow_apply]
    ring)).congr_deriv
  simp only [id_eq, Nat.add_sub_cancel]
  push_cast
  have hpos : (0 : Real) < 2 * n + 1 := by positivity
  field_simp [hpos.ne']

private theorem tsum_sincSeriesTerm_eq_sinc (y : Real) :
    (∑' n : Nat, sincSeriesTerm n y) = Real.sinc y := by
  by_cases hy : y = 0
  · subst y
    rw [tsum_eq_single 0]
    · simp [sincSeriesTerm]
    · intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      simp [sincSeriesTerm, show 2 * n ≠ 0 by omega]
  · have hs := (Real.hasSum_sin y).div_const y
    have hs' : HasSum (fun n : Nat => sincSeriesTerm n y)
        (Real.sin y / y) := by
      have hterm (n : Nat) :
          (-1 : Real) ^ n * y ^ (2 * n + 1) /
              ((2 * n + 1).factorial : Nat) / y =
            sincSeriesTerm n y := by
        unfold sincSeriesTerm
        field_simp [hy]
        ring
      have ht : Summable (fun n : Nat => sincSeriesTerm n y) :=
        hs.summable.congr hterm
      have htsum : (∑' n : Nat, sincSeriesTerm n y) = Real.sin y / y := by
        rw [← hs.tsum_eq]
        exact tsum_congr fun n => (hterm n).symm
      rw [← htsum]
      exact ht.hasSum
    rw [hs'.tsum_eq]
    exact (Real.sinc_of_ne_zero hy).symm

private def siDerivBound (n : Nat) : Real :=
  6 ^ (2 * n) / (2 * n + 1).factorial

private theorem summable_siDerivBound : Summable siDerivBound := by
  have hsub : Summable (fun n : Nat =>
    (6 : Real) ^ (2 * n + 1) / (2 * n + 1).factorial) :=
    (Real.summable_pow_div_factorial 6).comp_injective
      (i := fun n : Nat => (2 * n + 1 : Nat))
      (by
        intro a b h
        exact Nat.mul_left_cancel (by norm_num) (Nat.add_right_cancel h))
  have hscaled := hsub.mul_left ((6 : Real)⁻¹)
  apply hscaled.congr
  intro n
  unfold siDerivBound
  field_simp
  ring

private theorem norm_sincSeriesTerm_le_bound
    (n : Nat) {y : Real} (hy : y ∈ Ioo (-6 : Real) 6) :
    ‖sincSeriesTerm n y‖ ≤ siDerivBound n := by
  unfold sincSeriesTerm siDerivBound
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]
  have hyabs : |y| ≤ (6 : Real) := by
    rw [abs_le]
    exact ⟨hy.1.le, hy.2.le⟩
  have hpow : |y| ^ (2 * n) ≤ (6 : Real) ^ (2 * n) := by
    exact pow_le_pow_left₀ (abs_nonneg y) hyabs _
  have hden : 0 ≤ (((2 * n + 1).factorial : Nat) : Real) := by positivity
  rw [abs_of_nonneg hden]
  exact div_le_div_of_nonneg_right (by simpa only [abs_pow] using hpow) hden

private theorem hasDerivAt_tsum_siTerm_of_mem
    {y : Real} (hy : y ∈ Ioo (-6 : Real) 6) :
    HasDerivAt (fun z : Real => ∑' n : Nat, siTerm n z)
      (Real.sinc y) y := by
  have hzero : Summable (fun n : Nat => siTerm n 0) := by
    simp [siTerm, suzukiDF6D4DF0SineIntegralMagnitude]
  have h := hasDerivAt_tsum_of_isPreconnected
    summable_siDerivBound isOpen_Ioo isPreconnected_Ioo
    (fun n z hz => hasDerivAt_siTerm n z)
    (fun n z hz => norm_sincSeriesTerm_le_bound n hz)
    (show (0 : Real) ∈ Ioo (-6 : Real) 6 by norm_num)
    hzero hy
  rw [tsum_sincSeriesTerm_eq_sinc] at h
  exact h

theorem suzukiDF6D4DF0SmallSineIntegral_eq_integral
    {x : Real} (hx0 : 0 ≤ x) (hx6 : x < 6) :
    suzukiDF6D4DF0SmallSineIntegral x =
      ∫ t in (0 : Real)..x, Real.sinc t := by
  let S : Real → Real := fun y => ∑' n : Nat, siTerm n y
  have hderiv : ∀ y ∈ uIcc (0 : Real) x,
      HasDerivAt S (Real.sinc y) y := by
    intro y hy
    rw [uIcc_of_le hx0] at hy
    apply hasDerivAt_tsum_siTerm_of_mem
    exact ⟨(by norm_num : (-6 : Real) < 0).trans_le hy.1,
      hy.2.trans_lt hx6⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (Real.continuous_sinc.intervalIntegrable (0 : Real) x)
  have hS0 : S 0 = 0 := by
    simp [S, siTerm, suzukiDF6D4DF0SineIntegralMagnitude]
  have hSx : S x = suzukiDF6D4DF0SmallSineIntegral x := by
    unfold S
    rw [suzukiDF6D4DF0SmallSineIntegral_eq_tsum hx0]
    apply tsum_congr
    intro n
    rfl
  rw [hS0, sub_zero, hSx] at hftc
  exact hftc.symm

private theorem integrableOn_trig_div_pow
    (f : Real → Real) (hf : Continuous f) (hbound : ∀ t, |f t| ≤ 1)
    {x : Real} (hx : 0 < x) (p : Nat) (hp : 1 < p) :
    IntegrableOn (fun t : Real => f t / t ^ p) (Ioi x) := by
  have hmajor : IntegrableOn (fun t : Real => t ^ (-(p : Real))) (Ioi x) :=
    integrableOn_Ioi_rpow_of_lt (by
      have hp' : (1 : Real) < p := by exact_mod_cast hp
      linarith) hx
  apply hmajor.mono'
  · exact (hf.aemeasurable.div
      (continuous_id.pow p).aemeasurable).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := hx.trans ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos htpos p)]
    rw [show t ^ (-(p : Real)) = 1 / t ^ p by
      rw [Real.rpow_neg (le_of_lt htpos)]
      norm_num [Real.rpow_natCast]]
    exact div_le_div_of_nonneg_right (hbound t) (pow_nonneg htpos.le p)

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

theorem integral_cos_div_pow_ten_Ioi
    {x : Real} (hx : 0 < x) :
    (∫ t : Real in Ioi x, Real.cos t / t ^ 10) =
      -Real.sin x / x ^ 10 +
        10 * (∫ t : Real in Ioi x, Real.sin t / t ^ 11) := by
  let u : Real → Real := Real.sin
  let u' : Real → Real := Real.cos
  let v : Real → Real := fun t => 1 / t ^ 10
  let v' : Real → Real := fun t => -10 / t ^ 11
  have hu (t : Real) (ht : t ∈ Ioi x) : HasDerivAt u (u' t) t := by
    exact Real.hasDerivAt_sin t
  have hv (t : Real) (ht : t ∈ Ioi x) : HasDerivAt v (v' t) t := by
    have ht0 : t ≠ 0 := (hx.trans ht).ne'
    unfold v v'
    have h := (hasDerivAt_const t (1 : Real)).div
      ((hasDerivAt_id t).pow 10) (pow_ne_zero 10 ht0)
    apply (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
      rfl)).congr_deriv
    simp only [id_eq, Pi.pow_apply]
    field_simp [ht0]
    ring
  have huv' : IntegrableOn (u * v') (Ioi x) := by
    have hsin := integrableOn_trig_div_pow Real.sin Real.continuous_sin
      Real.abs_sin_le_one hx 11 (by norm_num)
    rw [show u * v' = fun t : Real => -10 * (Real.sin t / t ^ 11) by
      funext t
      simp only [u, v', Pi.mul_apply]
      ring]
    exact hsin.const_mul (-10)
  have hu'v : IntegrableOn (u' * v) (Ioi x) := by
    have hcos := integrableOn_trig_div_pow Real.cos Real.continuous_cos
      Real.abs_cos_le_one hx 10 (by norm_num)
    rw [show u' * v = fun t : Real => Real.cos t / t ^ 10 by
      funext t
      simp only [u', v, Pi.mul_apply]
      ring]
    exact hcos
  have hzero : Tendsto (u * v) (𝓝[>] x) (𝓝 (Real.sin x / x ^ 10)) := by
    have hc : ContinuousAt (fun t : Real => Real.sin t / t ^ 10) x :=
      Real.continuous_sin.continuousAt.div (continuousAt_id.pow 10)
        (pow_ne_zero 10 hx.ne')
    rw [show u * v = fun t : Real => Real.sin t / t ^ 10 by
      funext t
      simp only [u, v, Pi.mul_apply]
      ring]
    exact hc.tendsto.mono_left inf_le_left
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    rw [show u * v = fun t : Real => Real.sin t / t ^ 10 by
      funext t
      simp only [u, v, Pi.mul_apply]
      ring]
    exact
      tendsto_trig_div_pow_atTop_zero' Real.sin Real.abs_sin_le_one 10
        (by norm_num)
  have hparts := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v
    hzero hinfty
  dsimp [u, u', v, v'] at hparts
  rw [show (fun x : Real => Real.sin x * (-10 / x ^ 11)) =
      fun x => -10 * (Real.sin x / x ^ 11) by funext t; ring,
    integral_const_mul] at hparts
  rw [show (fun x : Real => Real.cos x * (1 / x ^ 10)) =
      fun x => Real.cos x / x ^ 10 by funext t; ring] at hparts
  linear_combination hparts

theorem suzukiDF6D4_sinc_tail_eq_primitive_cosine
    {x : Real} (hx : 0 < x) :
    Real.pi / 2 - (∫ t in (0 : Real)..x, Real.sinc t) =
      -suzukiDF6D4SineTailPrimitive x -
        362880 * (∫ t : Real in Ioi x, Real.cos t / t ^ 10) := by
  have hcosInt := integrableOn_trig_div_pow Real.cos Real.continuous_cos
    Real.abs_cos_le_one hx 10 (by norm_num)
  have hrem := intervalIntegral_tendsto_integral_Ioi x hcosInt tendsto_id
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
    apply (suzukiDirichletIntegralSource.sub_const
      (∫ t in (0 : Real)..x, Real.sinc t)).congr'
    filter_upwards [eventually_ge_atTop x] with R hR
    have hleft := Real.continuous_sinc.intervalIntegrable
      (μ := volume) (0 : Real) x
    have hright := Real.continuous_sinc.intervalIntegrable
      (μ := volume) x R
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    linarith
  have hlimits := tendsto_nhds_unique htailFromFormula htailFromDirichlet
  linarith

theorem sin_suzukiDF6D4DF0QuarterWave_eq_sign_of_odd
    (q : Nat) (hq : Odd q) :
    Real.sin (suzukiDF6D4DF0QuarterWave q) =
      ((suzukiDF6D4DF0QuarterSineSign q : Rat) : Real) := by
  obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hq
  rw [hk]
  unfold suzukiDF6D4DF0QuarterWave
  rw [show ((((2 * k + 1 : Nat) : Real) / 2) * Real.pi) =
      (k : Real) * Real.pi + Real.pi / 2 by push_cast; ring]
  rw [Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
  unfold suzukiDF6D4DF0QuarterSineSign
  by_cases hmod : (2 * k + 1) % 4 = 1
  · rw [if_pos hmod]
    norm_num
    exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))
  · rw [if_neg hmod]
    norm_num
    exact Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))

theorem cos_suzukiDF6D4DF0QuarterWave_eq_zero_of_odd
    (q : Nat) (hq : Odd q) :
    Real.cos (suzukiDF6D4DF0QuarterWave q) = 0 := by
  obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hq
  rw [hk]
  unfold suzukiDF6D4DF0QuarterWave
  rw [show ((((2 * k + 1 : Nat) : Real) / 2) * Real.pi) =
      (k : Real) * Real.pi + Real.pi / 2 by push_cast; ring]
  rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  simp

theorem suzukiDF6D4_sinc_tail_eq_quarterSineTail
    (q : Nat) (hq : 1 ≤ q)
    (hcos : Real.cos (suzukiDF6D4DF0QuarterWave q) = 0)
    (hsin : Real.sin (suzukiDF6D4DF0QuarterWave q) =
      ((suzukiDF6D4DF0QuarterSineSign q : Rat) : Real)) :
    Real.pi / 2 -
        (∫ t in (0 : Real)..suzukiDF6D4DF0QuarterWave q, Real.sinc t) =
      suzukiDF6D4DF0QuarterSineTail q := by
  let x := suzukiDF6D4DF0QuarterWave q
  have hx : 0 < x := by
    unfold x suzukiDF6D4DF0QuarterWave
    positivity
  rw [suzukiDF6D4_sinc_tail_eq_primitive_cosine hx,
    integral_cos_div_pow_ten_Ioi hx]
  unfold suzukiDF6D4DF0QuarterSineTail
    suzukiDF6D4DF0QuarterSineTailPolynomial
    suzukiDF6D4SineTailPrimitive
  dsimp only [x] at hcos hsin ⊢
  rw [hcos, hsin]
  ring

theorem suzukiDF6D4DF0QuarterSineIntegral_eq_integral_of_pos_odd
    (q : Nat) (hqpos : 1 ≤ q) (hqodd : Odd q) :
    suzukiDF6D4DF0QuarterSineIntegral q =
      ∫ t in (0 : Real)..suzukiDF6D4DF0QuarterWave q, Real.sinc t := by
  by_cases hsmall : q ≤ 3
  · rw [suzukiDF6D4DF0QuarterSineIntegral, if_pos hsmall]
    apply suzukiDF6D4DF0SmallSineIntegral_eq_integral
    · unfold suzukiDF6D4DF0QuarterWave
      positivity
    · unfold suzukiDF6D4DF0QuarterWave
      have hqreal : (q : Real) ≤ 3 := by exact_mod_cast hsmall
      calc
        ((q : Real) / 2) * Real.pi ≤ (3 / 2 : Real) * Real.pi := by
          gcongr
        _ < 6 := by nlinarith [Real.pi_lt_four]
  · rw [suzukiDF6D4DF0QuarterSineIntegral, if_neg hsmall]
    have htail := suzukiDF6D4_sinc_tail_eq_quarterSineTail q hqpos
      (cos_suzukiDF6D4DF0QuarterWave_eq_zero_of_odd q hqodd)
      (sin_suzukiDF6D4DF0QuarterWave_eq_sign_of_odd q hqodd)
    linarith

theorem suzukiDF6D5B3FEDF0QuarterSineIntegralEvaluation_proved :
    SuzukiDF6D5B3FEDF0QuarterSineIntegralEvaluation := by
  intro index hindex
  apply suzukiDF6D4DF0QuarterSineIntegral_eq_integral_of_pos_odd
  · exact suzukiDF6D4DF0LeakageAbsNumerator_pos index hindex
  · interval_cases index <;> native_decide

theorem suzukiDF6D5B3FECutoff44PrimitiveIdentification_proved :
    SuzukiDF6D5B3FECutoff44PrimitiveIdentification :=
  suzukiDF6D5B3FECutoff44PrimitiveIdentification_of_quarterSine
    suzukiDF6D5B3FEDF0QuarterSineIntegralEvaluation_proved

theorem cardinalSineCutoff44Leakage_eq_suzukiDF6D4DF0LeakageFraction_proved :
    cardinalSineCutoff44Leakage = suzukiDF6D4DF0LeakageFraction :=
  cardinalSineCutoff44Leakage_eq_suzukiDF6D4DF0LeakageFraction
    suzukiDF6D5B3FECutoff44PrimitiveIdentification_proved

end
end RiemannHypothesisProject.Experiments.M100
