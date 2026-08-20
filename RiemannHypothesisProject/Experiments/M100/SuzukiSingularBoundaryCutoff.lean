import RiemannHypothesisProject.Experiments.M100.SuzukiSingularPhysicalCutoff
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# M100-DF6D2 endpoint logarithm from reciprocal cutoffs

This module isolates the one-dimensional endpoint calculation used when the
finite reciprocal-kernel square is expanded.  The clamped logarithms make the
boundary-layer behavior explicit and provide the domination needed as the
inner cutoff tends to zero.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-- One-sided reciprocal mass between the inner cutoff and an endpoint
distance.  It is zero when the endpoint distance lies below the cutoff. -/
def suzukiOneSidedReciprocalMass (ε d : Real) : Real :=
  ∫ t in Icc ε d, 1 / t

/-- The logarithm clamped at the positive inner cutoff. -/
def suzukiClampedLog (ε d : Real) : Real :=
  if ε ≤ d then Real.log d else Real.log ε

theorem measurable_suzukiClampedLog (ε : Real) :
    Measurable (suzukiClampedLog ε) := by
  unfold suzukiClampedLog
  exact Measurable.ite (measurableSet_le measurable_const measurable_id)
    Real.measurable_log
    measurable_const

/-- Exact evaluation of the one-sided reciprocal mass. -/
theorem suzukiOneSidedReciprocalMass_eq
    {ε d : Real} (hε : 0 < ε) (hd : 0 < d) :
    suzukiOneSidedReciprocalMass ε d =
      if ε ≤ d then Real.log (d / ε) else 0 := by
  by_cases hεd : ε ≤ d
  · simp only [hεd, if_true]
    unfold suzukiOneSidedReciprocalMass
    calc
      (∫ t in Icc ε d, 1 / t) = ∫ t in ε..d, 1 / t := by
        rw [integral_Icc_eq_integral_Ioc,
          intervalIntegral.integral_of_le hεd]
      _ = Real.log (d / ε) := integral_one_div_of_pos hε hd
  · have hdε : d < ε := lt_of_not_ge hεd
    rw [suzukiOneSidedReciprocalMass, Icc_eq_empty hεd]
    simp [hεd]

/-- Adding the renormalizing logarithm turns the one-sided reciprocal mass
into the clamped endpoint logarithm. -/
theorem suzukiOneSidedReciprocalMass_add_log
    {ε d : Real} (hε : 0 < ε) (hd : 0 < d) :
    suzukiOneSidedReciprocalMass ε d + Real.log ε =
      suzukiClampedLog ε d := by
  rw [suzukiOneSidedReciprocalMass_eq hε hd]
  by_cases hεd : ε ≤ d
  · simp only [hεd, if_true, suzukiClampedLog]
    rw [Real.log_div hd.ne' hε.ne']
    ring
  · simp [suzukiClampedLog, hεd]

/-- For a fixed positive endpoint distance, the clamped logarithm converges
to the ordinary logarithm as the cutoff tends to zero from the right. -/
theorem tendsto_suzukiClampedLog
    {d : Real} (hd : 0 < d) :
    Tendsto (fun ε : Real => suzukiClampedLog ε d)
      (𝓝[>] (0 : Real)) (𝓝 (Real.log d)) := by
  have heventually : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ d := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < d :=
      mem_inf_of_left (Iio_mem_nhds hd)
    exact hlt.mono fun ε hε => hε.le
  refine (tendsto_congr' (heventually.mono fun ε hε => ?_)).2
    tendsto_const_nhds
  simp [suzukiClampedLog, hε]

/-- On the standard small-cutoff range, the clamped logarithm is dominated by
the endpoint logarithm itself. -/
theorem abs_suzukiClampedLog_le
    {ε d : Real} (hε : 0 < ε) (hεOne : ε ≤ 1) (hd : 0 < d) :
    |suzukiClampedLog ε d| ≤ |Real.log d| := by
  by_cases hεd : ε ≤ d
  · simp [suzukiClampedLog, hεd]
  · have hdε : d < ε := lt_of_not_ge hεd
    have hdOne : d ≤ 1 := (le_of_lt hdε).trans hεOne
    have hlogd : Real.log d ≤ 0 := Real.log_nonpos hd.le hdOne
    have hlogε : Real.log ε ≤ 0 := Real.log_nonpos hε.le hεOne
    have hlogle : Real.log d ≤ Real.log ε :=
      Real.log_le_log hd (le_of_lt hdε)
    rw [suzukiClampedLog, if_neg hεd,
      abs_of_nonpos hlogε, abs_of_nonpos hlogd]
    exact neg_le_neg hlogle

/-- On a positive interval lying below the outer cutoff, the reciprocal
kernel has exactly the one-sided mass defined above. -/
theorem intervalIntegral_re_suzukiReciprocalCutoffKernel_eq_mass
    {ε R d : Real} (hε : 0 < ε) (hd : 0 ≤ d) (hdR : d ≤ R) :
    (∫ t in (0 : Real)..d,
      (suzukiReciprocalCutoffKernel ε R t).re) =
        suzukiOneSidedReciprocalMass ε d := by
  have hk : Integrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel ε R t).re) :=
    (integrable_suzukiReciprocalCutoffKernel (R := R) hε).re
  have hkInterval : IntervalIntegrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel ε R t).re) volume 0 d :=
    hk.intervalIntegrable
  by_cases hεd : ε ≤ d
  · have hkLeft : IntervalIntegrable (fun t : Real =>
        (suzukiReciprocalCutoffKernel ε R t).re) volume 0 ε :=
      hk.intervalIntegrable
    have hkRight : IntervalIntegrable (fun t : Real =>
        (suzukiReciprocalCutoffKernel ε R t).re) volume ε d :=
      hk.intervalIntegrable
    have hleft : (∫ t in (0 : Real)..ε,
        (suzukiReciprocalCutoffKernel ε R t).re) = 0 := by
      calc
        (∫ t in (0 : Real)..ε,
            (suzukiReciprocalCutoffKernel ε R t).re) =
            ∫ _t in (0 : Real)..ε, (0 : Real) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [volume.ae_ne ε] with t ht hmem
          have hmem' : t ∈ Ioc 0 ε := by
            simpa [uIoc_of_le hε.le] using hmem
          have htpos : 0 < t := hmem'.1
          have htlt : t < ε := lt_of_le_of_ne hmem'.2 ht
          have hnot : t ∉ suzukiReciprocalCutoffSet ε R := by
            intro hset
            exact (not_le_of_gt htlt)
              (le_abs_of_mem_suzukiReciprocalCutoffSet hset |>.trans_eq
                (abs_of_pos htpos))
          simp [suzukiReciprocalCutoffKernel, hnot]
        _ = 0 := intervalIntegral.integral_zero
    have hright : (∫ t in ε..d,
        (suzukiReciprocalCutoffKernel ε R t).re) =
          ∫ t in ε..d, 1 / t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne ε] with t ht hmem
      have hmem' : t ∈ Ioc ε d := by
        simpa [uIoc_of_le hεd] using hmem
      have htpos : 0 < t := hε.trans hmem'.1
      have htR : t ≤ R := hmem'.2.trans hdR
      have hset : t ∈ suzukiReciprocalCutoffSet ε R := by
        exact Or.inr ⟨hmem'.1.le, htR⟩
      simp [suzukiReciprocalCutoffKernel, hset, abs_of_pos htpos,
        one_div]
    rw [← intervalIntegral.integral_add_adjacent_intervals hkLeft hkRight,
      hleft, zero_add, hright]
    unfold suzukiOneSidedReciprocalMass
    rw [integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hεd]
  · have hdε : d < ε := lt_of_not_ge hεd
    have hzero : (∫ t in (0 : Real)..d,
        (suzukiReciprocalCutoffKernel ε R t).re) = 0 := by
      calc
        (∫ t in (0 : Real)..d,
            (suzukiReciprocalCutoffKernel ε R t).re) =
            ∫ _t in (0 : Real)..d, (0 : Real) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with t hmem
          have hmem' : t ∈ Ioc 0 d := by
            simpa [uIoc_of_le hd] using hmem
          have htpos : 0 < t := hmem'.1
          have htlt : t < ε := hmem'.2.trans_lt hdε
          have hnot : t ∉ suzukiReciprocalCutoffSet ε R := by
            intro hset
            exact (not_le_of_gt htlt)
              (le_abs_of_mem_suzukiReciprocalCutoffSet hset |>.trans_eq
                (abs_of_pos htpos))
          simp [suzukiReciprocalCutoffKernel, hnot]
        _ = 0 := intervalIntegral.integral_zero
    rw [hzero, suzukiOneSidedReciprocalMass, Icc_eq_empty hεd]
    simp

/-- Reciprocal-kernel mass in the row of the finite Suzuki square. -/
def suzukiReciprocalCutoffRowMass
    (ε R a x : Real) : Real :=
  ∫ y in Icc (-a) a,
    (suzukiReciprocalCutoffKernel ε R (x - y)).re

/-- A row of the finite square splits into the two one-sided endpoint
distances.  The outer cutoff is inactive once it contains the square. -/
theorem suzukiReciprocalCutoffRowMass_eq
    {ε R a x : Real} (hε : 0 < ε) (ha : 0 ≤ a)
    (hx : x ∈ Icc (-a) a) (hR : 2 * a ≤ R) :
    suzukiReciprocalCutoffRowMass ε R a x =
      suzukiOneSidedReciprocalMass ε (a - x) +
        suzukiOneSidedReciprocalMass ε (a + x) := by
  let k : Real → Real := fun t =>
    (suzukiReciprocalCutoffKernel ε R t).re
  have hk : Integrable k := by
    exact (integrable_suzukiReciprocalCutoffKernel (R := R) hε).re
  have hrow : Integrable (fun y : Real => k (x - y)) := by
    exact hk.comp_sub_left x
  have hleftInt : IntervalIntegrable (fun y : Real => k (x - y))
      volume (-a) x := hrow.intervalIntegrable
  have hrightInt : IntervalIntegrable (fun y : Real => k (x - y))
      volume x a := hrow.intervalIntegrable
  have hleftDistance : 0 ≤ a + x := by linarith [hx.1]
  have hrightDistance : 0 ≤ a - x := by linarith [hx.2]
  have hleftDistanceR : a + x ≤ R := by linarith [hx.2, hR]
  have hrightDistanceR : a - x ≤ R := by linarith [hx.1, hR]
  have hleft :
      (∫ y in (-a)..x, k (x - y)) =
        suzukiOneSidedReciprocalMass ε (a + x) := by
    rw [intervalIntegral.integral_comp_sub_left]
    simpa only [k, sub_self, sub_neg_eq_add, add_comm] using
      (intervalIntegral_re_suzukiReciprocalCutoffKernel_eq_mass
        hε hleftDistance hleftDistanceR)
  have hright :
      (∫ y in x..a, k (x - y)) =
        suzukiOneSidedReciprocalMass ε (a - x) := by
    rw [intervalIntegral.integral_comp_sub_left]
    have hneg := intervalIntegral.integral_comp_neg
      (f := k) (a := (0 : Real)) (b := a - x)
    calc
      (∫ t in x - a..x - x, k t) =
          ∫ t in (0 : Real)..(a - x), k (-t) := by
        simpa only [sub_self, neg_sub, neg_zero] using hneg.symm
      _ = ∫ t in (0 : Real)..(a - x), k t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        exact congrArg Complex.re
          (suzukiReciprocalCutoffKernel_neg (ε := ε) (R := R) t)
      _ = suzukiOneSidedReciprocalMass ε (a - x) :=
        intervalIntegral_re_suzukiReciprocalCutoffKernel_eq_mass
          hε hrightDistance hrightDistanceR
  unfold suzukiReciprocalCutoffRowMass
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
    ← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt,
    hleft, hright]
  ring

/-- Endpoint majorant for the renormalized row mass. -/
def suzukiBoundaryCutoffMajorant
    (a : Real) (v : SchwartzLineTestFunction) (x : Real) : Real :=
  (|Real.log (a - x)| + |Real.log (a + x)|) * ‖v x‖ ^ 2

/-- Renormalized finite-cutoff row integrand. -/
def suzukiBoundaryCutoffIntegrand
    (ε a : Real) (v : SchwartzLineTestFunction) (x : Real) : Real :=
  (suzukiClampedLog ε (a - x) +
    suzukiClampedLog ε (a + x)) * ‖v x‖ ^ 2

/-- The endpoint-log majorant is integrable on the finite interval. -/
theorem integrableOn_suzukiBoundaryCutoffMajorant
    {a : Real} (ha : 0 ≤ a) (v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiBoundaryCutoffMajorant a v) (Icc (-a) a) := by
  have hrightLog : IntervalIntegrable (fun x : Real => Real.log (a - x))
      volume (-a) a := by
    have hanalytic : AnalyticOnNhd Real (fun x : Real => a - x) [[-a, a]] :=
      analyticOnNhd_const.sub analyticOnNhd_id
    exact hanalytic.meromorphicOn.intervalIntegrable_log
  have hleftLog : IntervalIntegrable (fun x : Real => Real.log (a + x))
      volume (-a) a := by
    have hanalytic : AnalyticOnNhd Real (fun x : Real => a + x) [[-a, a]] :=
      analyticOnNhd_const.add analyticOnNhd_id
    exact hanalytic.meromorphicOn.intervalIntegrable_log
  have hvContinuous : ContinuousOn (fun x : Real => ‖v x‖ ^ 2) [[-a, a]] := by
    fun_prop
  have hright := hrightLog.norm.mul_continuousOn hvContinuous
  have hleft := hleftLog.norm.mul_continuousOn hvContinuous
  have hsum := hright.add hleft
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -a ≤ a)] at hsum
  change IntegrableOn
    (fun x : Real =>
      (|Real.log (a - x)| + |Real.log (a + x)|) * ‖v x‖ ^ 2)
    (Icc (-a) a)
  simpa only [Real.norm_eq_abs, add_mul] using hsum

/-- Each fixed positive small cutoff has an integrable renormalized endpoint
row integrand. -/
theorem integrableOn_suzukiBoundaryCutoffIntegrand
    {ε a : Real} (hε : 0 < ε) (hεOne : ε ≤ 1) (ha : 0 ≤ a)
    (v : SchwartzLineTestFunction) :
    IntegrableOn (suzukiBoundaryCutoffIntegrand ε a v) (Icc (-a) a) := by
  let μ : Measure Real := volume.restrict (Icc (-a) a)
  have hneLeft : ∀ᵐ x ∂μ, x ≠ -a :=
    (ae_mono Measure.restrict_le_self) (volume.ae_ne (-a))
  have hneRight : ∀ᵐ x ∂μ, x ≠ a :=
    (ae_mono Measure.restrict_le_self) (volume.ae_ne a)
  refine Integrable.mono'
    (integrableOn_suzukiBoundaryCutoffMajorant ha v) ?_ ?_
  · exact (by
      apply Measurable.aestronglyMeasurable
      unfold suzukiBoundaryCutoffIntegrand
      exact (((measurable_suzukiClampedLog ε).comp (by fun_prop)).add
        ((measurable_suzukiClampedLog ε).comp (by fun_prop))).mul (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      hneLeft, hneRight] with x hx hxLeft hxRight
    have hxLeft' : -a < x := lt_of_le_of_ne hx.1 (Ne.symm hxLeft)
    have hxRight' : x < a := lt_of_le_of_ne hx.2 hxRight
    have hright := abs_suzukiClampedLog_le hε hεOne
      (sub_pos.mpr hxRight')
    have hleft := abs_suzukiClampedLog_le hε hεOne
      (by linarith : 0 < a + x)
    have hvSq : |‖v x‖ ^ 2| = ‖v x‖ ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    unfold suzukiBoundaryCutoffIntegrand suzukiBoundaryCutoffMajorant
    rw [Real.norm_eq_abs, abs_mul, hvSq]
    exact mul_le_mul_of_nonneg_right
      ((abs_add_le _ _).trans (add_le_add hright hleft)) (sq_nonneg _)

/-- Dominated convergence turns the two clamped endpoint logarithms into the
exact logarithmic boundary potential. -/
theorem tendsto_integral_suzukiBoundaryCutoffIntegrand
    {a : Real} (ha : 0 < a) (v : SchwartzLineTestFunction) :
    Tendsto
      (fun ε : Real =>
        ∫ x in Icc (-a) a, suzukiBoundaryCutoffIntegrand ε a v x)
      (𝓝[>] (0 : Real))
      (𝓝 (∫ x in Icc (-a) a,
        Real.log (a ^ 2 - x ^ 2) * ‖v x‖ ^ 2)) := by
  let μ : Measure Real := volume.restrict (Icc (-a) a)
  have hneLeft : ∀ᵐ x ∂μ, x ≠ -a :=
    (ae_mono Measure.restrict_le_self) (volume.ae_ne (-a))
  have hneRight : ∀ᵐ x ∂μ, x ≠ a :=
    (ae_mono Measure.restrict_le_self) (volume.ae_ne a)
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : Real),
      AEStronglyMeasurable (suzukiBoundaryCutoffIntegrand ε a v) μ := by
    filter_upwards with ε
    apply Measurable.aestronglyMeasurable
    unfold suzukiBoundaryCutoffIntegrand
    exact (((measurable_suzukiClampedLog ε).comp (by fun_prop)).add
      ((measurable_suzukiClampedLog ε).comp (by fun_prop))).mul (by fun_prop)
  have hεOne : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ 1 := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < 1 :=
      mem_inf_of_left (Iio_mem_nhds zero_lt_one)
    exact hlt.mono fun ε hε => hε.le
  have hεPos : ∀ᶠ ε in 𝓝[>] (0 : Real), 0 < ε := self_mem_nhdsWithin
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : Real), ∀ᵐ x ∂μ,
      ‖suzukiBoundaryCutoffIntegrand ε a v x‖ ≤
        suzukiBoundaryCutoffMajorant a v x := by
    filter_upwards [hεPos, hεOne] with ε hε hεOne
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      hneLeft, hneRight] with x hx hxLeft hxRight
    have hxLeft' : -a < x := lt_of_le_of_ne hx.1 (Ne.symm hxLeft)
    have hxRight' : x < a := lt_of_le_of_ne hx.2 hxRight
    have hright := abs_suzukiClampedLog_le hε hεOne
      (sub_pos.mpr hxRight')
    have hleft := abs_suzukiClampedLog_le hε hεOne
      (by linarith : 0 < a + x)
    have hvSq : |‖v x‖ ^ 2| = ‖v x‖ ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    unfold suzukiBoundaryCutoffIntegrand suzukiBoundaryCutoffMajorant
    rw [Real.norm_eq_abs, abs_mul, hvSq]
    exact mul_le_mul_of_nonneg_right
      ((abs_add_le _ _).trans (add_le_add hright hleft)) (sq_nonneg _)
  have hlimit : ∀ᵐ x ∂μ,
      Tendsto (fun ε : Real => suzukiBoundaryCutoffIntegrand ε a v x)
        (𝓝[>] (0 : Real))
        (𝓝 ((Real.log (a - x) + Real.log (a + x)) * ‖v x‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      hneLeft, hneRight] with x hx hxLeft hxRight
    have hxLeft' : -a < x := lt_of_le_of_ne hx.1 (Ne.symm hxLeft)
    have hxRight' : x < a := lt_of_le_of_ne hx.2 hxRight
    unfold suzukiBoundaryCutoffIntegrand
    exact ((tendsto_suzukiClampedLog (sub_pos.mpr hxRight')).add
      (tendsto_suzukiClampedLog (by linarith : 0 < a + x))).mul_const _
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (suzukiBoundaryCutoffMajorant a v) hmeas hbound
    (integrableOn_suzukiBoundaryCutoffMajorant ha.le v) hlimit
  have htarget :
      (∫ x in Icc (-a) a,
          (Real.log (a - x) + Real.log (a + x)) * ‖v x‖ ^ 2) =
        ∫ x in Icc (-a) a,
          Real.log (a ^ 2 - x ^ 2) * ‖v x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      hneLeft, hneRight] with x hx hxLeft hxRight
    have hxLeft' : -a < x := lt_of_le_of_ne hx.1 (Ne.symm hxLeft)
    have hxRight' : x < a := lt_of_le_of_ne hx.2 hxRight
    rw [← Real.log_mul (sub_pos.mpr hxRight').ne'
      (by linarith : a + x ≠ 0)]
    congr 2
    ring
  change Tendsto _ (𝓝[>] (0 : Real)) _
  rw [htarget] at hdct
  exact hdct

end

end M100
end Experiments
end RiemannHypothesisProject
