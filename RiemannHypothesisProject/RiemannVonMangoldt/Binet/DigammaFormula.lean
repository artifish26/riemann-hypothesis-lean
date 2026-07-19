import Mathlib.Analysis.Calculus.ParametricIntegral
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.BinetKernelLaplace

/-!
# Unconditional Binet digamma formula

This module promotes the checked positive-real sawtooth/Laplace normalization
to the full right half-plane.  The parameter integral is differentiated under
an explicit compact-local exponential majorant, and the positive real axis
then supplies the accumulating equality set for the complex identity theorem.
-/

open Filter Function MeasureTheory Set Topology

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The project Binet correction as a function of the complex parameter. -/
def bennettGammaBinetIntegral (z : Complex) : Complex :=
  ∫ t : Real in Set.Ioi 0,
    bennettGammaBinetKernel t * Complex.exp (-(t : Complex) * z)

/-- Exact norm of the Binet Laplace factor at an arbitrary complex
parameter. -/
theorem norm_bennettGammaBinetLaplaceFactor (t : Real) (z : Complex) :
    ‖Complex.exp (-(t : Complex) * z)‖ =
      Real.exp (-(t * z.re)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, mul_zero, sub_zero]
  ring

/-- The Binet integrand is measurable on the positive axis for every complex
parameter. -/
theorem aestronglyMeasurable_bennettGammaBinetIntegrand (z : Complex) :
    AEStronglyMeasurable
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * z))
      (volume.restrict (Set.Ioi 0)) := by
  have hcont : ContinuousOn
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * z))
      (Set.Ioi 0) := by
    apply continuousOn_bennettGammaBinetKernel.mul
    fun_prop
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-- The Binet correction is absolutely integrable throughout the open right
half-plane. -/
theorem integrableOn_bennettGammaBinetIntegrand
    {z : Complex} (hz : 0 < z.re) :
    IntegrableOn
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * z))
      (Set.Ioi 0) := by
  have hmajorant : IntegrableOn
      (fun t : Real => (1 / 2 : Real) * Real.exp (-(z.re * t)))
      (Set.Ioi 0) := by
    change Integrable
      (fun t : Real => (1 / 2 : Real) * Real.exp (-(z.re * t)))
      (volume.restrict (Set.Ioi 0))
    have h := (integrableOn_exp_mul_Ioi
      (a := -z.re) (by linarith) 0).const_mul (1 / 2 : Real)
    simpa only [neg_mul] using h
  refine hmajorant.mono'
    (aestronglyMeasurable_bennettGammaBinetIntegrand z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, norm_bennettGammaBinetLaplaceFactor]
  simpa only [mul_comm z.re t] using
    (mul_le_mul_of_nonneg_right
      (norm_bennettGammaBinetKernel_le_one_half_of_pos (Set.mem_Ioi.mp ht))
      (Real.exp_pos (-(t * z.re))).le)

/-- The derivative integrand used for the holomorphic-parameter argument. -/
def bennettGammaBinetIntegralDerivIntegrand
    (z : Complex) (t : Real) : Complex :=
  bennettGammaBinetKernel t *
    (Complex.exp (-(t : Complex) * z) * (-(t : Complex)))

/-- Differentiation under the Binet integral on the right half-plane.  The
majorant is local in the parameter but uniform in the integration variable. -/
theorem hasDerivAt_bennettGammaBinetIntegral
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt bennettGammaBinetIntegral
      (∫ t : Real in Set.Ioi 0,
        bennettGammaBinetIntegralDerivIntegrand z t) z := by
  let μ := volume.restrict (Set.Ioi (0 : Real))
  let r : Real := z.re / 2
  let s : Set Complex := Metric.ball z r
  let F : Complex → Real → Complex := fun w t =>
    bennettGammaBinetKernel t * Complex.exp (-(t : Complex) * w)
  let F' : Complex → Real → Complex := fun w t =>
    bennettGammaBinetIntegralDerivIntegrand w t
  let bound : Real → Real := fun t =>
    (1 / 2 : Real) * (t * Real.exp (-(r * t)))
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hs : s ∈ 𝓝 z := by
    exact Metric.ball_mem_nhds z hr
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) μ := by
    filter_upwards [] with w
    simpa only [F, μ] using
      aestronglyMeasurable_bennettGammaBinetIntegrand w
  have hFint : Integrable (F z) μ := by
    change Integrable
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * z))
      (volume.restrict (Set.Ioi 0))
    exact integrableOn_bennettGammaBinetIntegrand hz
  have hF'meas : AEStronglyMeasurable (F' z) μ := by
    have hcont : ContinuousOn (F' z) (Set.Ioi 0) := by
      dsimp only [F', bennettGammaBinetIntegralDerivIntegrand]
      apply continuousOn_bennettGammaBinetKernel.mul
      fun_prop
    simpa only [μ] using hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᵐ t ∂μ, ∀ w ∈ s, ‖F' w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro w hw
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    have hdist : ‖w - z‖ < r := by
      simpa only [s, Metric.mem_ball, dist_eq_norm] using hw
    have hreNorm : |w.re - z.re| ≤ ‖w - z‖ := by
      change |(w - z).re| ≤ ‖w - z‖
      exact Complex.abs_re_le_norm (w - z)
    have hreDiff : |w.re - z.re| < r := lt_of_le_of_lt hreNorm hdist
    have hwre : r < w.re := by
      rw [abs_lt] at hreDiff
      dsimp only [r] at hreDiff ⊢
      linarith
    have harg : -(t * w.re) ≤ -(r * t) := by
      nlinarith
    dsimp only [F', bound, bennettGammaBinetIntegralDerivIntegrand]
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht0,
      norm_bennettGammaBinetLaplaceFactor]
    calc
      ‖bennettGammaBinetKernel t‖ *
          (Real.exp (-(t * w.re)) * t) ≤
          (1 / 2 : Real) * (Real.exp (-(t * w.re)) * t) := by
            exact mul_le_mul_of_nonneg_right
              (norm_bennettGammaBinetKernel_le_one_half_of_pos ht0)
              (mul_nonneg (Real.exp_pos _).le ht0.le)
      _ ≤ (1 / 2 : Real) * (Real.exp (-(r * t)) * t) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr harg) ht0.le) (by norm_num)
      _ = (1 / 2 : Real) * (t * Real.exp (-(r * t))) := by ring
  have hboundInt : Integrable bound μ := by
    have h := (integrableOn_mul_exp_neg_mul hr).const_mul (1 / 2 : Real)
    simpa only [bound, μ] using h
  have hdiff : ∀ᵐ t ∂μ, ∀ w ∈ s,
      HasDerivAt (F · t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    intro w _
    have hlinear : HasDerivAt
        (fun v : Complex => -(t : Complex) * v) (-(t : Complex)) w :=
      by simpa using (hasDerivAt_id w).const_mul (-(t : Complex))
    have hexp := hlinear.cexp
    simpa only [F, F', bennettGammaBinetIntegralDerivIntegrand] using
      hexp.const_mul (bennettGammaBinetKernel t)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas hFint hF'meas hbound hboundInt hdiff
  change HasDerivAt (fun w => ∫ t, F w t ∂μ) (∫ t, F' z t ∂μ) z
  exact hmain.2

/-- The project Binet correction is analytic on the right half-plane. -/
theorem analyticOnNhd_bennettGammaBinetIntegral :
    AnalyticOnNhd Complex bennettGammaBinetIntegral
      {z : Complex | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (hasDerivAt_bennettGammaBinetIntegral hz).differentiableAt.differentiableWithinAt
  · exact isOpen_Ioi.preimage Complex.continuous_re

/-- The checked sawtooth formula gives Binet's identity at every positive real
parameter. -/
theorem bennettGammaBinetDigammaFormula_ofReal
    {x : Real} (hx : 0 < x) :
    Complex.digamma (x : Complex) =
      Complex.log (x : Complex) - 1 / (2 * (x : Complex)) -
        bennettGammaBinetIntegral (x : Complex) := by
  have hsaw := integral_binetSawtooth_div_sq hx
  have hreal :
      deriv (Real.log ∘ Real.Gamma) x =
        Real.log x - 1 / (2 * x) -
          ∫ u : Real in Set.Ioi 0,
            binetSawtooth u / (x + u) ^ 2 := by
    linarith
  rw [digamma_ofReal_eq_deriv_logGamma hx,
    bennettGammaBinetIntegral,
    integral_bennettGammaBinetKernel_ofReal hx,
    ← Complex.ofReal_log hx.le]
  exact_mod_cast hreal

/-- The Binet right-hand side is analytic on the right half-plane, with the
principal logarithm branch fixed by Mathlib's slit-plane logarithm. -/
theorem analyticOnNhd_bennettGammaBinetRhs :
    AnalyticOnNhd Complex
      (fun z : Complex => Complex.log z - 1 / (2 * z) -
        bennettGammaBinetIntegral z)
      {z : Complex | 0 < z.re} := by
  intro z hz
  change 0 < z.re at hz
  have hzSlit : z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hrecip : AnalyticAt Complex
      (fun w : Complex => 1 / (2 * w)) z := by
    exact analyticAt_const.div (analyticAt_const.mul analyticAt_id)
      (mul_ne_zero (by norm_num) hz0)
  exact (((Complex.contDiffAt_log hzSlit).analyticAt.sub hrecip).sub
    (analyticOnNhd_bennettGammaBinetIntegral z hz))

/-- Positive real Binet identities accumulate at `1`. -/
theorem one_mem_closure_bennettGammaBinetDigamma_eq_rhs :
    (1 : Complex) ∈ closure
      ({z : Complex |
          Complex.digamma z =
            Complex.log z - 1 / (2 * z) -
              bennettGammaBinetIntegral z} \ {1}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let x : Real := 1 + ε / 2
  refine ⟨(x : Complex), ⟨?_, ?_⟩, ?_⟩
  · exact bennettGammaBinetDigammaFormula_ofReal (by
      dsimp only [x]
      linarith)
  · simp only [Set.mem_singleton_iff]
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    dsimp only [x] at hre
    linarith
  · simpa [x, abs_of_pos hε] using (half_lt_self hε)

/-- Binet's identity holds throughout the open right half-plane. -/
theorem bennettGammaBinetDigamma_eqOn :
    Set.EqOn Complex.digamma
      (fun z : Complex => Complex.log z - 1 / (2 * z) -
        bennettGammaBinetIntegral z)
      {z : Complex | 0 < z.re} := by
  have hdigamma : AnalyticOnNhd Complex Complex.digamma
      {z : Complex | 0 < z.re} := fun z hz =>
    analyticAt_digamma_of_re_pos hz
  exact hdigamma.eqOn_of_preconnected_of_mem_closure
    analyticOnNhd_bennettGammaBinetRhs
    (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (1 : Complex) ∈ {z : Complex | 0 < z.re})
    one_mem_closure_bennettGammaBinetDigamma_eq_rhs

/-- Unconditional inhabitant of the exact Binet source proposition used by
the production Burnol estimates. -/
theorem bennettGammaBinetDigammaFormula :
    BennettGammaBinetDigammaFormula := by
  intro z hz
  simpa only [bennettGammaBinetIntegral] using
    bennettGammaBinetDigamma_eqOn hz

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
