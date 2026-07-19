import Mathlib.Analysis.Calculus.LHopital
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaRemainder

/-!
# Binet-kernel normalization at the removable endpoint

This module isolates the cancellation at `t = 0` in the Binet kernel used by
the Gamma remainder.  The production kernel is left unchanged; the result
below proves that its apparent singularity has value `0` when approached from
the positive integration axis.
-/

open Filter
open scoped Topology

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The second-order exponential remainder has its expected right-hand limit. -/
theorem tendsto_exp_sub_one_sub_id_div_sq_nhdsGT_zero :
    Tendsto
      (fun t : Real => (Real.exp t - 1 - t) / t ^ 2)
      (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
  have hfirstOrder :
      Tendsto (fun t : Real => (Real.exp t - 1) / (2 * t))
        (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
    · filter_upwards with t
      simpa using (Real.hasDerivAt_exp t).sub_const 1
    · filter_upwards with t
      simpa using (hasDerivAt_id t).const_mul 2
    · filter_upwards with t
      norm_num
    · have hnum : Continuous (fun t : Real => Real.exp t - 1) :=
        Real.continuous_exp.sub continuous_const
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (hnum.tendsto 0)
    · have hdenom : Continuous (fun t : Real => 2 * t) :=
        continuous_const.mul continuous_id
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (hdenom.tendsto 0)
    · have hderivRatio : Continuous (fun t : Real => Real.exp t / 2) :=
        Real.continuous_exp.div_const 2
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (hderivRatio.tendsto 0)
  apply HasDerivAt.lhopital_zero_nhdsGT
  · filter_upwards with t
    refine (((Real.hasDerivAt_exp t).sub_const 1).sub
      (hasDerivAt_id t)).congr_of_eventuallyEq ?_
    filter_upwards with x
    simp only [Pi.sub_apply, id_eq]
  · filter_upwards with t
    simpa using (hasDerivAt_pow 2 t)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht.ne'
  · have hnum : Continuous (fun t : Real => Real.exp t - 1 - t) :=
      (Real.continuous_exp.sub continuous_const).sub continuous_id
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (hnum.tendsto 0)
  · have hdenom : Continuous (fun t : Real => t ^ 2) :=
      continuous_id.pow 2
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (hdenom.tendsto 0)
  · simpa [div_eq_mul_inv] using hfirstOrder

/-- The real scalar underlying the Binet kernel tends to zero at its removable endpoint. -/
theorem tendsto_bennettGammaBinetKernel_real_nhdsGT_zero :
    Tendsto
      (fun t : Real => (1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1))
      (𝓝[>] 0) (nhds 0) := by
  have hlinear :
      Tendsto (fun t : Real => (Real.exp t - 1) / t) (𝓝[>] 0) (nhds 1) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
    · filter_upwards with t
      simpa using (Real.hasDerivAt_exp t).sub_const 1
    · filter_upwards with t
      exact hasDerivAt_id t
    · simp
    · convert tendsto_nhdsWithin_of_tendsto_nhds
        ((Real.continuous_exp.sub continuous_const).tendsto (0 : Real)) using 1 <;> norm_num
    · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id
    · convert tendsto_nhdsWithin_of_tendsto_nhds
        (Real.continuous_exp.tendsto (0 : Real)) using 1 <;> norm_num
  have hproduct :
      Tendsto
        (fun t : Real =>
          ((Real.exp t - 1 - t) / t ^ 2) /
            ((Real.exp t - 1) / t))
        (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
    have hdiv :=
      tendsto_exp_sub_one_sub_id_div_sq_nhdsGT_zero.div hlinear (by norm_num)
    have hdiv' :
        Tendsto
          ((fun t : Real => (Real.exp t - 1 - t) / t ^ 2) /
            (fun t : Real => (Real.exp t - 1) / t))
          (𝓝[>] 0) (nhds (1 / 2 : Real)) := by
      simpa only [div_one] using hdiv
    apply hdiv'.congr'
    filter_upwards with t
    rfl
  have heq :
      (fun t : Real => (1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)) =ᶠ[𝓝[>] 0]
        (fun t : Real => 1 / 2 -
          ((Real.exp t - 1 - t) / t ^ 2) /
            ((Real.exp t - 1) / t)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht.ne'
    have hexp0 : Real.exp t - 1 ≠ 0 := by
      exact sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr ht).ne'
    field_simp [ht0, hexp0]
    ring
  rw [tendsto_congr' heq]
  convert
    (show Tendsto (fun _ : Real => (1 / 2 : Real)) (𝓝[>] 0) (nhds (1 / 2 : Real)) from
      tendsto_const_nhds).sub hproduct using 1 <;> norm_num

/-- The complex Binet kernel tends to `0` from the positive integration axis. -/
theorem tendsto_bennettGammaBinetKernel_nhdsGT_zero :
    Tendsto bennettGammaBinetKernel (𝓝[>] 0) (nhds 0) := by
  rw [show bennettGammaBinetKernel = fun t : Real =>
      (((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1) : Real) : Complex) by
    funext t
    exact bennettGammaBinetKernel_eq_ofReal t]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    tendsto_bennettGammaBinetKernel_real_nhdsGT_zero

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
