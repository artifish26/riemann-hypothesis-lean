import RiemannHypothesisProject.RiemannVonMangoldt.Binet.DigammaFormula
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongElementaryTaylor

/-!
# The critical-line Stirling phase

This module isolates the analytic Gamma-factor estimate used in Hardy's
theorem.  The first part evaluates the classical complex Stirling main term on
`1 / 4 + i t / 2` and bounds its difference from the exact phase in the Hardy
argument.  The remaining source calculation is the Binet log-remainder.
-/

open Complex Filter MeasureTheory Set Topology

namespace RiemannHypothesisProject

namespace Hardy

noncomputable section

/-- The argument of `Gamma` inside `Gammaℝ (1 / 2 + i t)`. -/
def criticalLineGammaArgument (t : Real) : Complex :=
  (1 / 4 : Complex) + (t / 2 : Real) * Complex.I

/-- The phase required by Sangale's display (2.11), in the project
normalization. -/
def criticalLineStirlingPhase (t : Real) : Real :=
  (t / 2) * Real.log (t / (2 * Real.pi)) - t / 2 - Real.pi / 8

/-- The complex Stirling main term for the `Gammaℝ` factor, omitting its
positive real constant, which has no phase. -/
def gammaRStirlingLogMain (z : Complex) : Complex :=
  (z - 1 / 2) * Complex.log z - z - z * Real.log Real.pi

/-- The Stirling main term specialized to the critical-line Gamma argument. -/
def criticalLineGammaStirlingMain (t : Real) : Complex :=
  gammaRStirlingLogMain (criticalLineGammaArgument t)

@[simp]
theorem criticalLineGammaArgument_re (t : Real) :
    (criticalLineGammaArgument t).re = 1 / 4 := by
  simp [criticalLineGammaArgument]

@[simp]
theorem criticalLineGammaArgument_im (t : Real) :
    (criticalLineGammaArgument t).im = t / 2 := by
  simp [criticalLineGammaArgument]

/-- Exact polar radius of the quarter-shifted critical-line Gamma argument. -/
theorem norm_criticalLineGammaArgument (t : Real) :
    ‖criticalLineGammaArgument t‖ =
      (1 / 4 : Real) * Real.sqrt (1 + 4 * t ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply,
    criticalLineGammaArgument_re, criticalLineGammaArgument_im]
  rw [show (1 / 4 : Real) * (1 / 4) + t / 2 * (t / 2) =
      (1 / 4 : Real) ^ 2 * (1 + 4 * t ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg (1 / 4 : Real)), Real.sqrt_sq_eq_abs,
    abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 4)]

/-- Exact principal argument on the positive quarter-line. -/
theorem arg_criticalLineGammaArgument (t : Real) :
    Complex.arg (criticalLineGammaArgument t) = Real.arctan (2 * t) := by
  rw [Complex.arg_of_re_nonneg (by
    rw [criticalLineGammaArgument_re]
    norm_num), Real.arctan_eq_arcsin, criticalLineGammaArgument_im,
    norm_criticalLineGammaArgument]
  congr 1
  have hsqrt : Real.sqrt (1 + 4 * t ^ 2) ≠ 0 := by positivity
  field_simp [hsqrt]
  ring

/-- At positive height, the polar radius is the height scale times a small
quadratic correction. -/
theorem norm_criticalLineGammaArgument_eq_heightFactor
    {t : Real} (ht : 0 < t) :
    ‖criticalLineGammaArgument t‖ =
      (t / 2) * Real.sqrt (1 + 1 / (4 * t ^ 2)) := by
  rw [norm_criticalLineGammaArgument]
  have ht2 : 0 < 2 * t := by positivity
  rw [show (1 + 4 * t ^ 2 : Real) =
      (2 * t) ^ 2 * (1 + 1 / (4 * t ^ 2)) by
        field_simp [ht.ne']
        ring,
    Real.sqrt_mul (sq_nonneg (2 * t)), Real.sqrt_sq_eq_abs,
    abs_of_pos ht2]
  ring

/-- The principal argument differs from `pi / 2` by the reciprocal-height
arctangent correction. -/
theorem arg_criticalLineGammaArgument_eq_pi_div_two_sub
    {t : Real} (ht : 0 < t) :
    Complex.arg (criticalLineGammaArgument t) =
      Real.pi / 2 - Real.arctan (1 / (2 * t)) := by
  rw [arg_criticalLineGammaArgument]
  have hInv := Real.arctan_inv_of_pos (show 0 < 2 * t by positivity)
  have hInv' :
      Real.arctan (1 / (2 * t)) =
        Real.pi / 2 - Real.arctan (2 * t) := by
    simpa only [one_div] using hInv
  linarith

/-- The imaginary part of the complex Stirling main term, before elementary
polar-coordinate simplification. -/
theorem criticalLineGammaStirlingMain_im (t : Real) :
    (criticalLineGammaStirlingMain t).im =
      (t / 2) * Real.log ‖criticalLineGammaArgument t‖ - t / 2 -
        (1 / 4) * Complex.arg (criticalLineGammaArgument t) -
          (t / 2) * Real.log Real.pi := by
  simp only [criticalLineGammaStirlingMain, gammaRStirlingLogMain,
    Complex.sub_im, Complex.mul_im,
    Complex.log_re, Complex.log_im, criticalLineGammaArgument_re,
    criticalLineGammaArgument_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_re, Complex.div_im]
  norm_num
  ring

/-- Exact decomposition of the main Stirling phase into Sangale's phase and
two positive reciprocal-height corrections. -/
theorem criticalLineGammaStirlingMain_im_eq_phase_add_corrections
    {t : Real} (ht : 0 < t) :
    (criticalLineGammaStirlingMain t).im =
      criticalLineStirlingPhase t +
        (t / 4) * Real.log (1 + 1 / (4 * t ^ 2)) +
          (1 / 4) * Real.arctan (1 / (2 * t)) := by
  rw [criticalLineGammaStirlingMain_im,
    norm_criticalLineGammaArgument_eq_heightFactor ht,
    arg_criticalLineGammaArgument_eq_pi_div_two_sub ht]
  have htHalf : 0 < t / 2 := by positivity
  have hcorr : 0 < 1 + 1 / (4 * t ^ 2) := by positivity
  have hsqrt : Real.sqrt (1 + 1 / (4 * t ^ 2)) ≠ 0 := by positivity
  rw [Real.log_mul htHalf.ne' hsqrt,
    Real.log_sqrt hcorr.le]
  have hlogDiv :
      Real.log (t / 2) - Real.log Real.pi =
        Real.log (t / (2 * Real.pi)) := by
    rw [← Real.log_div htHalf.ne' Real.pi_ne_zero]
    congr 1
    ring
  rw [criticalLineStirlingPhase]
  rw [← hlogDiv]
  ring

/-- The elementary polar-coordinate correction in the critical-line
Stirling main term is explicitly `O(1/t)`. -/
theorem abs_criticalLineGammaStirlingMain_im_sub_phase_le
    {t : Real} (ht : 1 ≤ t) :
    |(criticalLineGammaStirlingMain t).im -
        criticalLineStirlingPhase t| ≤ 3 / (16 * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  rw [criticalLineGammaStirlingMain_im_eq_phase_add_corrections ht0]
  let x : Real := 1 / (4 * t ^ 2)
  let y : Real := 1 / (2 * t)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hy_le : y ≤ 1 / 2 := by
    dsimp [y]
    rw [div_le_iff₀ (show 0 < 2 * t by positivity)]
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log (1 + x) :=
    Real.log_nonneg (by linarith)
  have hlog_le : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
    linarith
  have hatan_nonneg : 0 ≤ Real.arctan y :=
    Real.arctan_nonneg.mpr hy
  have hatan_poly :=
    ComplexCompactExhaustion.arctan_quintic_upper hy
  have hy_sq : y ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg y]
  have hatan_le : Real.arctan y ≤ y := by
    have hy3 : y ^ 3 / 3 ≥ y ^ 5 / 5 := by
      nlinarith [mul_nonneg hy (sub_nonneg.mpr hy_sq)]
    linarith
  have hcorr_nonneg :
      0 ≤ (t / 4) * Real.log (1 + x) +
        (1 / 4) * Real.arctan y := by positivity
  have hcorr_le :
      (t / 4) * Real.log (1 + x) +
          (1 / 4) * Real.arctan y ≤ 3 / (16 * t) := by
    calc
      (t / 4) * Real.log (1 + x) + (1 / 4) * Real.arctan y ≤
          (t / 4) * x + (1 / 4) * y := by gcongr
      _ = 3 / (16 * t) := by
        dsimp [x, y]
        field_simp [ht0.ne']
        ring
  change |criticalLineStirlingPhase t +
      (t / 4) * Real.log (1 + x) +
        (1 / 4) * Real.arctan y - criticalLineStirlingPhase t| ≤
    3 / (16 * t)
  rw [show criticalLineStirlingPhase t +
      (t / 4) * Real.log (1 + x) +
        (1 / 4) * Real.arctan y - criticalLineStirlingPhase t =
      (t / 4) * Real.log (1 + x) +
        (1 / 4) * Real.arctan y by ring,
    abs_of_nonneg hcorr_nonneg]
  exact hcorr_le

/-! ## The logarithmic Binet remainder -/

open ComplexCompactExhaustion

/-- Third-order cancellation improves the Binet kernel from a uniform bound
to a linear bound at its removable endpoint. -/
theorem norm_bennettGammaBinetKernel_le_half_mul
    {u : Real} (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖bennettGammaBinetKernel u‖ ≤ u / 2 := by
  rw [bennettGammaBinetKernel_eq_ofReal, Complex.norm_real]
  have huAbs : |u| ≤ 1 := by simpa [abs_of_pos hu] using hu1
  have hexp := Real.exp_bound (n := 3) huAbs (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos hu] at hexp
  have hdenLower : u ≤ Real.exp u - 1 := by
    nlinarith [Real.add_one_le_exp u]
  have hdenPos : 0 < Real.exp u - 1 := lt_of_lt_of_le hu hdenLower
  rw [Real.norm_eq_abs]
  have hkernel :
      (1 / 2 : Real) - 1 / u + 1 / (Real.exp u - 1) =
        (u * (Real.exp u - 1) - 2 * (Real.exp u - 1) + 2 * u) /
          (2 * u * (Real.exp u - 1)) := by
    field_simp [hu.ne', hdenPos.ne']
  rw [hkernel]
  have hprod : 0 < 2 * u * (Real.exp u - 1) := by positivity
  let r : Real := Real.exp u - (1 + u + u ^ 2 / 2)
  have hrLower : -(u ^ 3 * (2 / 9 : Real)) ≤ r := by
    exact (abs_le.mp hexp).1
  have hrUpper : r ≤ u ^ 3 * (2 / 9 : Real) := by
    exact (abs_le.mp hexp).2
  have hc : u - 2 ≤ 0 := by linarith
  have hcLower := mul_le_mul_of_nonpos_left hrUpper hc
  have hcUpper := mul_le_mul_of_nonpos_left hrLower hc
  have hnum :
      u * (Real.exp u - 1) - 2 * (Real.exp u - 1) + 2 * u =
        u ^ 3 / 2 + (u - 2) * r := by
    dsimp [r]
    ring
  have hnumLower :
      -(u ^ 3) ≤
        u * (Real.exp u - 1) - 2 * (Real.exp u - 1) + 2 * u := by
    rw [hnum]
    nlinarith [mul_nonneg hu.le (sq_nonneg u)]
  have hnumUpper :
      u * (Real.exp u - 1) - 2 * (Real.exp u - 1) + 2 * u ≤
        u ^ 3 := by
    rw [hnum]
    nlinarith [mul_nonneg hu.le (sq_nonneg u)]
  have hscale : u ^ 3 ≤ u ^ 2 * (Real.exp u - 1) := by
    have := mul_le_mul_of_nonneg_left hdenLower (sq_nonneg u)
    nlinarith
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hprod]
    nlinarith
  · rw [div_le_iff₀ hprod]
    nlinarith

/-- The kernel divided by its Laplace variable is globally bounded on the
positive axis.  This is the cancellation needed by Binet's logarithmic
remainder. -/
theorem norm_bennettGammaBinetKernel_div_le_one_half
    {u : Real} (hu : 0 < u) :
    ‖bennettGammaBinetKernel u / (u : Complex)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  by_cases hu1 : u ≤ 1
  · calc
      ‖bennettGammaBinetKernel u‖ / u ≤ (u / 2) / u := by
        exact div_le_div_of_nonneg_right
          (norm_bennettGammaBinetKernel_le_half_mul hu hu1) hu.le
      _ = 1 / 2 := by field_simp [hu.ne']
  · have hOne : 1 ≤ u := le_of_lt (lt_of_not_ge hu1)
    calc
      ‖bennettGammaBinetKernel u‖ / u ≤ (1 / 2 : Real) / u := by
        exact div_le_div_of_nonneg_right
          (norm_bennettGammaBinetKernel_le_one_half_of_pos hu) hu.le
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hu]
        nlinarith

/-- Binet's logarithmic remainder on the open right half-plane. -/
def gammaBinetLogRemainder (z : Complex) : Complex :=
  ∫ u : Real in Set.Ioi 0,
    (bennettGammaBinetKernel u / (u : Complex)) *
      Complex.exp (-(u : Complex) * z)

/-- The logarithmic Binet integrand is absolutely integrable throughout the
open right half-plane. -/
theorem integrableOn_gammaBinetLogRemainderIntegrand
    {z : Complex} (hz : 0 < z.re) :
    IntegrableOn
      (fun u : Real =>
        (bennettGammaBinetKernel u / (u : Complex)) *
          Complex.exp (-(u : Complex) * z))
      (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun u : Real =>
        (bennettGammaBinetKernel u / (u : Complex)) *
          Complex.exp (-(u : Complex) * z))
      (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn
        (fun u : Real =>
          (bennettGammaBinetKernel u / (u : Complex)) *
            Complex.exp (-(u : Complex) * z))
        (Set.Ioi 0) := by
      intro u hu
      have hu0 : 0 < u := Set.mem_Ioi.mp hu
      exact (((hasDerivAt_bennettGammaBinetKernel hu0).continuousAt.div
        Complex.continuous_ofReal.continuousAt
        (by exact_mod_cast hu0.ne')).mul (by fun_prop)).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hmajorant : IntegrableOn
      (fun u : Real => (1 / 2 : Real) * Real.exp (-(z.re * u)))
      (Set.Ioi 0) := by
    change Integrable
      (fun u : Real => (1 / 2 : Real) * Real.exp (-(z.re * u)))
      (volume.restrict (Set.Ioi 0))
    have h := (integrableOn_exp_mul_Ioi
      (a := -z.re) (by linarith) 0).const_mul (1 / 2 : Real)
    simpa only [neg_mul] using h
  refine hmajorant.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 < u := Set.mem_Ioi.mp hu
  rw [norm_mul,
    ComplexCompactExhaustion.norm_bennettGammaBinetLaplaceFactor]
  simpa only [mul_comm u z.re] using
    (mul_le_mul_of_nonneg_right
      (norm_bennettGammaBinetKernel_div_le_one_half hu0)
      (Real.exp_pos (-(u * z.re))).le)

/-- A first absolute bound for the logarithmic Binet remainder.  The H2 phase
estimate will sharpen this in the vertical direction by integration by parts. -/
theorem norm_gammaBinetLogRemainder_le
    {z : Complex} (hz : 0 < z.re) :
    ‖gammaBinetLogRemainder z‖ ≤ 1 / (2 * z.re) := by
  calc
    ‖gammaBinetLogRemainder z‖ ≤
        ∫ u : Real in Set.Ioi 0,
          (1 / 2 : Real) * Real.exp (-(z.re * u)) := by
      apply norm_integral_le_of_norm_le
      · have h := (integrableOn_exp_mul_Ioi
          (a := -z.re) (by linarith) 0).const_mul (1 / 2 : Real)
        simpa only [neg_mul] using h
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := Set.mem_Ioi.mp hu
        rw [norm_mul,
          ComplexCompactExhaustion.norm_bennettGammaBinetLaplaceFactor]
        simpa only [mul_comm u z.re] using
          (mul_le_mul_of_nonneg_right
            (norm_bennettGammaBinetKernel_div_le_one_half hu0)
            (Real.exp_pos (-(u * z.re))).le)
    _ = 1 / (2 * z.re) := by
      rw [integral_const_mul]
      have hExp := integral_exp_mul_Ioi (a := -z.re) (by linarith) 0
      have hExp' :
          (∫ u : Real in Set.Ioi 0, Real.exp (-(z.re * u))) =
            1 / z.re := by
        rw [show (fun u : Real => Real.exp (-(z.re * u))) =
            fun u : Real => Real.exp (-z.re * u) by
              funext u
              congr 1
              ring,
          hExp]
        simp only [mul_zero, neg_zero, Real.exp_zero]
        field_simp [hz.ne']
      rw [hExp']
      field_simp [hz.ne']

/-- The logarithmic Binet remainder is a primitive of the negative Binet
digamma correction on the open right half-plane. -/
theorem hasDerivAt_gammaBinetLogRemainder
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt gammaBinetLogRemainder
      (-bennettGammaBinetIntegral z) z := by
  let μ := volume.restrict (Set.Ioi (0 : Real))
  let r : Real := z.re / 2
  let s : Set Complex := Metric.ball z r
  let F : Complex → Real → Complex := fun w u =>
    (bennettGammaBinetKernel u / (u : Complex)) *
      Complex.exp (-(u : Complex) * w)
  let F' : Complex → Real → Complex := fun w u =>
    -bennettGammaBinetKernel u * Complex.exp (-(u : Complex) * w)
  let bound : Real → Real := fun u =>
    (1 / 2 : Real) * Real.exp (-(r * u))
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) μ := by
    filter_upwards [] with w
    have hcont : ContinuousOn (F w) (Set.Ioi 0) := by
      intro u hu
      have hu0 : 0 < u := Set.mem_Ioi.mp hu
      dsimp only [F]
      exact (((hasDerivAt_bennettGammaBinetKernel hu0).continuousAt.div
        Complex.continuous_ofReal.continuousAt
        (by exact_mod_cast hu0.ne')).mul (by fun_prop)).continuousWithinAt
    simpa only [μ] using hcont.aestronglyMeasurable measurableSet_Ioi
  have hFint : Integrable (F z) μ := by
    change Integrable
      (fun u : Real =>
        (bennettGammaBinetKernel u / (u : Complex)) *
          Complex.exp (-(u : Complex) * z))
      (volume.restrict (Set.Ioi 0))
    exact integrableOn_gammaBinetLogRemainderIntegrand hz
  have hF'meas : AEStronglyMeasurable (F' z) μ := by
    have hcont : ContinuousOn (F' z) (Set.Ioi 0) := by
      dsimp only [F']
      exact continuousOn_bennettGammaBinetKernel.neg.mul (by fun_prop)
    simpa only [μ] using hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ s, ‖F' w u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
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
    have harg : -(u * w.re) ≤ -(r * u) := by nlinarith
    dsimp only [F', bound]
    rw [norm_mul, norm_neg,
      ComplexCompactExhaustion.norm_bennettGammaBinetLaplaceFactor]
    exact le_trans
      (mul_le_mul_of_nonneg_right
        (norm_bennettGammaBinetKernel_le_one_half_of_pos hu0)
        (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num))
  have hboundInt : Integrable bound μ := by
    have h := (integrableOn_exp_mul_Ioi
      (a := -r) (by linarith) 0).const_mul (1 / 2 : Real)
    simpa only [bound, μ, neg_mul] using h
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ s,
      HasDerivAt (F · u) (F' w u) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w _
    have hu0 : (u : Complex) ≠ 0 := by
      exact_mod_cast (Set.mem_Ioi.mp hu).ne'
    have hlinear : HasDerivAt
        (fun v : Complex => -(u : Complex) * v) (-(u : Complex)) w := by
      simpa using (hasDerivAt_id w).const_mul (-(u : Complex))
    have hexp := hlinear.cexp
    have hraw := hexp.const_mul
      (bennettGammaBinetKernel u / (u : Complex))
    simpa only [F, F'] using hraw.congr_deriv (by
      field_simp [hu0])
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas hFint hF'meas hbound hboundInt hdiff
  have hderiv : HasDerivAt gammaBinetLogRemainder
      (∫ u : Real in Set.Ioi 0, F' z u) z := by
    change HasDerivAt (fun w => ∫ u, F w u ∂μ) (∫ u, F' z u ∂μ) z
    exact hmain.2
  convert hderiv using 1
  rw [show (fun u : Real => F' z u) = fun u : Real =>
      -(bennettGammaBinetKernel u * Complex.exp (-(u : Complex) * z)) by
        funext u
        simp only [F']
        ring,
    integral_neg]
  rfl

/-- The derivative of the elementary `Gammaℝ` Stirling main term on the
right half-plane. -/
theorem hasDerivAt_gammaRStirlingLogMain
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt gammaRStirlingLogMain
      (Complex.log z - 1 / (2 * z) - Real.log Real.pi) z := by
  have hzSlit : z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hlog := Complex.hasDerivAt_log hzSlit
  have hraw := ((((hasDerivAt_id z).sub
      (hasDerivAt_const z (1 / 2 : Complex))).mul hlog).sub
        (hasDerivAt_id z)).sub
          ((hasDerivAt_id z).const_mul (Real.log Real.pi : Complex))
  have hfun : gammaRStirlingLogMain =
      ((id - fun _ : Complex => (1 / 2 : Complex)) * Complex.log - id -
        fun w : Complex => (Real.log Real.pi : Complex) * id w) := by
    funext w
    simp only [gammaRStirlingLogMain, Pi.sub_apply, Pi.mul_apply, id_eq]
    ring
  rw [hfun]
  exact hraw.congr_deriv (by
    simp only [id_eq, Pi.sub_apply]
    field_simp [hz0]
    ring)

/-- Binet's formula identifies the derivative of the complete Stirling log
expression with the `Gammaℝ` logarithmic derivative. -/
theorem hasDerivAt_gammaRStirlingLogWithRemainder
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt
      (fun w => gammaRStirlingLogMain w + gammaBinetLogRemainder w)
      (Complex.digamma z - Real.log Real.pi) z := by
  have hraw := (hasDerivAt_gammaRStirlingLogMain hz).add
    (hasDerivAt_gammaBinetLogRemainder hz)
  have hBinet := bennettGammaBinetDigamma_eqOn hz
  have hderivEq :
      Complex.digamma z - Real.log Real.pi =
        (Complex.log z - 1 / (2 * z) - Real.log Real.pi) +
          -bennettGammaBinetIntegral z := by
    rw [hBinet]
    ring
  change HasDerivAt
    (fun w : Complex => gammaRStirlingLogMain w + gammaBinetLogRemainder w)
    _ z at hraw
  exact hraw.congr_deriv hderivEq.symm

/-! ## The periodic Binet primitive -/

/-- The nonnegative periodic primitive of the centered Binet sawtooth.  On
each open unit interval its derivative is `binetSawtooth`. -/
def binetSawtoothPrimitive (u : Real) : Real :=
  Int.fract u * (1 - Int.fract u) / 2

/-- The periodic Binet primitive is bounded by `1/8`. -/
theorem abs_binetSawtoothPrimitive_le (u : Real) :
    |binetSawtoothPrimitive u| ≤ 1 / 8 := by
  have hx0 : 0 ≤ Int.fract u := Int.fract_nonneg u
  have hx1 : Int.fract u ≤ 1 := (Int.fract_lt_one u).le
  have hprod0 : 0 ≤ Int.fract u * (1 - Int.fract u) := mul_nonneg hx0 (by linarith)
  have hsquare : 0 ≤ (Int.fract u - 1 / 2) ^ 2 := sq_nonneg _
  rw [binetSawtoothPrimitive, abs_of_nonneg (div_nonneg hprod0 (by norm_num))]
  nlinarith

/-- The periodic Binet primitive is measurable. -/
theorem measurable_binetSawtoothPrimitive :
    Measurable binetSawtoothPrimitive := by
  unfold binetSawtoothPrimitive
  fun_prop

/-- On each open unit interval the periodic primitive is an elementary
quadratic polynomial. -/
theorem binetSawtoothPrimitive_eq_on_nat_interval
    (n : Nat) {u : Real} (hu : u ∈ Set.Ioo (n : Real) (n + 1 : Real)) :
    binetSawtoothPrimitive u =
      (u - n) * ((n : Real) + 1 - u) / 2 := by
  have hlocal : Int.fract (u - n) = u - n :=
    Int.fract_eq_self.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
  unfold binetSawtoothPrimitive
  rw [← Int.fract_sub_natCast u n, hlocal]
  ring

/-- The same quadratic description extends continuously to the closed unit
interval, where both endpoint values vanish. -/
theorem binetSawtoothPrimitive_eq_on_nat_closedInterval
    (n : Nat) {u : Real} (hu : u ∈ Set.Icc (n : Real) (n + 1 : Real)) :
    binetSawtoothPrimitive u =
      (u - n) * ((n : Real) + 1 - u) / 2 := by
  rcases hu with ⟨hu0, hu1⟩
  rcases hu0.eq_or_lt with rfl | hu0
  · simp [binetSawtoothPrimitive]
  rcases hu1.eq_or_lt with rfl | hu1
  · simp [binetSawtoothPrimitive]
  exact binetSawtoothPrimitive_eq_on_nat_interval n ⟨hu0, hu1⟩

/-- The periodic Binet primitive is continuous on every natural unit
interval. -/
theorem continuousOn_binetSawtoothPrimitive_natInterval (n : Nat) :
    ContinuousOn binetSawtoothPrimitive
      (Set.Icc (n : Real) (n + 1 : Real)) := by
  let q : Real → Real := fun x =>
    (x - n) * ((n : Real) + 1 - x) / 2
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  exact hq.continuousOn.congr fun u hu => by
    dsimp only [q]
    exact binetSawtoothPrimitive_eq_on_nat_closedInterval n hu

/-- The derivative of the periodic primitive away from its integer joints is
the centered Binet sawtooth. -/
theorem hasDerivAt_binetSawtoothPrimitive_on_nat_interval
    (n : Nat) {u : Real} (hu : u ∈ Set.Ioo (n : Real) (n + 1 : Real)) :
    HasDerivAt binetSawtoothPrimitive (binetSawtooth u) u := by
  let q : Real → Real := fun x =>
    (x - n) * ((n : Real) + 1 - x) / 2
  have hq : HasDerivAt q ((n : Real) + 1 / 2 - u) u := by
    dsimp only [q]
    convert (((hasDerivAt_id u).sub_const (n : Real)).mul
      ((hasDerivAt_const u ((n : Real) + 1)).sub
        (hasDerivAt_id u))).div_const 2 using 1
    all_goals first
      | rfl
      | (simp only [Pi.sub_apply, id_eq]; ring)
  have hlocal : binetSawtoothPrimitive =ᶠ[𝓝 u] q := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with x hx
    exact binetSawtoothPrimitive_eq_on_nat_interval n hx
  have hsaw := binetSawtooth_eq_on_nat_interval n hu
  rw [hsaw]
  exact hq.congr_of_eventuallyEq hlocal

/-- Unit-interval integration by parts converts the centered sawtooth kernel
to the absolutely convergent periodic-primitive kernel. -/
theorem intervalIntegral_binetSawtooth_div_sq_eq_primitive
    {z : Complex} (hz : 0 < z.re) (n : Nat) :
    (∫ u in (n : Real)..(n + 1 : Real),
      (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) =
        2 * ∫ u in (n : Real)..(n + 1 : Real),
          (binetSawtoothPrimitive u : Complex) /
            (z + (u : Complex)) ^ 3 := by
  let U : Real → Complex := fun u => (binetSawtoothPrimitive u : Complex)
  let U' : Real → Complex := fun u => (binetSawtooth u : Complex)
  let V : Real → Complex := fun u => -1 / (z + (u : Complex)) ^ 2
  let V' : Real → Complex := fun u => 2 / (z + (u : Complex)) ^ 3
  have hU : ContinuousOn U (Set.uIcc (n : Real) (n + 1 : Real)) := by
    rw [Set.uIcc_of_le (by norm_num)]
    exact Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_binetSawtoothPrimitive_natInterval n)
  have hU' : IntervalIntegrable U' volume (n : Real) (n + 1 : Real) := by
    let q : Real → Complex := fun u => ((n : Real) + 1 / 2 - u : Real)
    have hq : IntervalIntegrable q volume (n : Real) (n + 1 : Real) := by
      apply ContinuousOn.intervalIntegrable
      dsimp only [q]
      fun_prop
    exact hq.congr_uIoo fun u hu => by
      rw [Set.uIoo_of_le (by norm_num)] at hu
      dsimp only [q, U']
      rw [binetSawtooth_eq_on_nat_interval n hu]
  have hVderiv : ∀ u ∈ Set.uIcc (n : Real) (n + 1 : Real),
      HasDerivAt V (V' u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hzu : z + (u : Complex) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re] at hre
      norm_num at hre
      have hun : 0 ≤ u := le_trans (Nat.cast_nonneg n) hu.1
      linarith
    have hlin : HasDerivAt (fun w : Complex => z + w) 1 (u : Complex) :=
      (hasDerivAt_id (u : Complex)).const_add z
    have hcomplex := ((hlin.pow 2).inv (pow_ne_zero 2 hzu)).neg
    have hreal := hcomplex.comp_ofReal
    refine (hreal.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with x
      dsimp only [V]
      simp only [Pi.neg_apply, Pi.inv_apply, Pi.pow_apply, one_div]
      ring
    · dsimp only [V']
      simp only [Pi.pow_apply, Nat.reduceSub, one_mul]
      field_simp [hzu]
      ring
  have hV : ContinuousOn V (Set.uIcc (n : Real) (n + 1 : Real)) :=
    fun u hu => (hVderiv u hu).continuousAt.continuousWithinAt
  have hV' : IntervalIntegrable V' volume (n : Real) (n + 1 : Real) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hzu : z + (u : Complex) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re] at hre
      norm_num at hre
      have hun : 0 ≤ u := le_trans (Nat.cast_nonneg n) hu.1
      linarith
    dsimp only [V']
    fun_prop (disch := exact pow_ne_zero 3 hzu)
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := U) (v := V) (u' := U') (v' := V')
    hU hV
    (fun u hu => by
      rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at hu
      exact (hasDerivAt_binetSawtoothPrimitive_on_nat_interval n hu).ofReal_comp)
    (fun u hu => hVderiv u (Set.mem_Icc_of_Ioo hu)) hU' hV'
  dsimp only [U, U', V, V'] at hparts ⊢
  rw [show binetSawtoothPrimitive (n : Real) = 0 by
        simp [binetSawtoothPrimitive],
      show binetSawtoothPrimitive (n + 1 : Real) = 0 by
        simp [binetSawtoothPrimitive]] at hparts
  have hparts' :
      (∫ u in (n : Real)..(n + 1 : Real),
        (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) =
          ∫ u in (n : Real)..(n + 1 : Real),
            (binetSawtoothPrimitive u : Complex) *
              (2 / (z + (u : Complex)) ^ 3) := by
    calc
      (∫ u in (n : Real)..(n + 1 : Real),
          (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) =
          -(∫ u in (n : Real)..(n + 1 : Real),
            (binetSawtooth u : Complex) *
              (-1 / (z + (u : Complex)) ^ 2)) := by
            rw [← intervalIntegral.integral_neg]
            apply intervalIntegral.integral_congr
            intro u _
            ring
      _ = ∫ u in (n : Real)..(n + 1 : Real),
            (binetSawtoothPrimitive u : Complex) *
              (2 / (z + (u : Complex)) ^ 3) := by
            simpa only [ofReal_zero, zero_mul, sub_zero, zero_sub] using hparts.symm
  rw [hparts', ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  ring

/-- The complex centered-sawtooth remainder is absolutely integrable on the
right half-plane. -/
theorem integrableOn_complexBinetSawtooth_div_sq
    {z : Complex} (hz : 0 < z.re) :
    IntegrableOn (fun u : Real =>
      (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2)
      (Set.Ioi 0) := by
  have hbase := integrableOn_add_rpow_Ioi_of_lt
    (a := (-2 : Real)) (c := (0 : Real)) (m := z.re)
    (by norm_num) (by linarith)
  have hmajor : IntegrableOn
      (fun u : Real => (1 / 2 : Real) * (1 / (u + z.re) ^ 2))
      (Set.Ioi 0) := by
    apply Integrable.const_mul
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have huz : 0 < u + z.re := by linarith [Set.mem_Ioi.mp hu]
    change (u + z.re) ^ (-2 : Real) = 1 / (u + z.re) ^ 2
    rw [show (-2 : Real) = -(2 : Real) by norm_num,
      Real.rpow_neg huz.le, Real.rpow_two]
    simp only [one_div]
  refine hmajor.mono' ?_ ?_
  · have hmeas : Measurable (fun u : Real =>
        (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) := by
      exact measurable_binetSawtooth.complex_ofReal.div
        ((measurable_const.add measurable_id.complex_ofReal).pow_const 2)
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    have huz : 0 < u + z.re := by linarith
    let w : Complex := z + (u : Complex)
    have hwRe : w.re = z.re + u := by simp [w]
    have hnorm : u + z.re ≤ ‖w‖ := by
      have hwRePos : 0 < w.re := by rw [hwRe]; linarith
      calc
        u + z.re = w.re := by rw [hwRe]; ring
        _ = |w.re| := (abs_of_pos hwRePos).symm
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hden : (u + z.re) ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    simpa only [w, div_eq_mul_inv, one_mul] using
      (div_le_div₀ (by norm_num) (abs_binetSawtooth_le u)
        (sq_pos_of_pos huz) hden)

/-- The cubic periodic-primitive integrand is absolutely integrable on the
right half-plane. -/
theorem integrableOn_periodicBinetPrimitive_div_cube
    {z : Complex} (hz : 0 < z.re) :
    IntegrableOn (fun u : Real =>
      (binetSawtoothPrimitive u : Complex) / (z + (u : Complex)) ^ 3)
      (Set.Ioi 0) := by
  have hbase := integrableOn_add_rpow_Ioi_of_lt
    (a := (-3 : Real)) (c := (0 : Real)) (m := z.re)
    (by norm_num) (by linarith)
  have hmajor : IntegrableOn
      (fun u : Real => (1 / 8 : Real) * (1 / (u + z.re) ^ 3))
      (Set.Ioi 0) := by
    apply Integrable.const_mul
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro u hu
    have huz : 0 < u + z.re := by linarith [Set.mem_Ioi.mp hu]
    change (u + z.re) ^ (-3 : Real) = 1 / (u + z.re) ^ 3
    rw [show (-3 : Real) = -(3 : Real) by norm_num,
      Real.rpow_neg huz.le]
    calc
      ((u + z.re) ^ (3 : Real))⁻¹ =
          ((u + z.re) ^ (3 : Nat))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (u + z.re) 3)
      _ = 1 / (u + z.re) ^ 3 := by simp only [one_div]
  refine hmajor.mono' ?_ ?_
  · have hmeas : Measurable (fun u : Real =>
        (binetSawtoothPrimitive u : Complex) / (z + (u : Complex)) ^ 3) := by
      exact measurable_binetSawtoothPrimitive.complex_ofReal.div
        ((measurable_const.add measurable_id.complex_ofReal).pow_const 3)
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    have huz : 0 < u + z.re := by linarith
    let w : Complex := z + (u : Complex)
    have hwRe : w.re = z.re + u := by simp [w]
    have hnorm : u + z.re ≤ ‖w‖ := by
      have hwRePos : 0 < w.re := by rw [hwRe]; linarith
      calc
        u + z.re = w.re := by rw [hwRe]; ring
        _ = |w.re| := (abs_of_pos hwRePos).symm
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hden : (u + z.re) ^ 3 ≤ ‖w‖ ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hnorm 3
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    simpa only [w, div_eq_mul_inv, one_mul] using
      (div_le_div₀ (by norm_num) (abs_binetSawtoothPrimitive_le u)
        (pow_pos huz 3) hden)

/-- Summing the unit-interval identity gives its finite Euler form. -/
theorem intervalIntegral_binetSawtooth_div_sq_zero_nat_eq_primitive
    {z : Complex} (hz : 0 < z.re) (N : Nat) :
    (∫ u in (0 : Real)..(N : Real),
      (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) =
        2 * ∫ u in (0 : Real)..(N : Real),
          (binetSawtoothPrimitive u : Complex) /
            (z + (u : Complex)) ^ 3 := by
  let f : Real → Complex := fun u =>
    (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2
  let g : Real → Complex := fun u =>
    (binetSawtoothPrimitive u : Complex) / (z + (u : Complex)) ^ 3
  have hf := integrableOn_complexBinetSawtooth_div_sq hz
  have hg := integrableOn_periodicBinetPrimitive_div_cube hz
  have hsumF :
      (∫ u in (0 : Real)..(N : Real), f u) =
        ∑ n ∈ Finset.range N,
          ∫ u in (n : Real)..(n + 1 : Real), f u := by
    symm
    simpa using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : Nat => (n : Real)) (f := f) (μ := volume) (n := N)
      (fun n _ => by
        have hlocal : IntervalIntegrable f volume (n : Real) (n + 1 : Real) := by
          apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
            (by norm_num : (n : Real) ≤ n + 1)).mpr
          exact hf.mono_set (by
            intro u hu
            exact Set.mem_Ioi.mpr (lt_of_le_of_lt (Nat.cast_nonneg n) hu.1))
        simpa only [Nat.cast_add, Nat.cast_one] using hlocal)
  have hsumG :
      (∫ u in (0 : Real)..(N : Real), g u) =
        ∑ n ∈ Finset.range N,
          ∫ u in (n : Real)..(n + 1 : Real), g u := by
    symm
    simpa using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun n : Nat => (n : Real)) (f := g) (μ := volume) (n := N)
      (fun n _ => by
        have hlocal : IntervalIntegrable g volume (n : Real) (n + 1 : Real) := by
          apply (intervalIntegrable_iff_integrableOn_Ioo_of_le
            (by norm_num : (n : Real) ≤ n + 1)).mpr
          exact hg.mono_set (by
            intro u hu
            exact Set.mem_Ioi.mpr (lt_of_le_of_lt (Nat.cast_nonneg n) hu.1))
        simpa only [Nat.cast_add, Nat.cast_one] using hlocal)
  change (∫ u in (0 : Real)..(N : Real), f u) =
    2 * ∫ u in (0 : Real)..(N : Real), g u
  rw [hsumF, hsumG, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact intervalIntegral_binetSawtooth_div_sq_eq_primitive hz n

/-- Passing the finite Euler identity to the improper limit gives the global
second-Binet integration-by-parts formula. -/
theorem integral_binetSawtooth_div_sq_eq_periodicPrimitive
    {z : Complex} (hz : 0 < z.re) :
    (∫ u : Real in Set.Ioi 0,
      (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) =
        2 * ∫ u : Real in Set.Ioi 0,
          (binetSawtoothPrimitive u : Complex) /
            (z + (u : Complex)) ^ 3 := by
  let f : Real → Complex := fun u =>
    (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2
  let g : Real → Complex := fun u =>
    (binetSawtoothPrimitive u : Complex) / (z + (u : Complex)) ^ 3
  have hf := integrableOn_complexBinetSawtooth_div_sq hz
  have hg := integrableOn_periodicBinetPrimitive_div_cube hz
  have hlimF := intervalIntegral_tendsto_integral_Ioi
    (f := f) (μ := volume) (b := fun n : Nat => (n : Real))
    (l := atTop) 0 hf tendsto_natCast_atTop_atTop
  have hlimG := intervalIntegral_tendsto_integral_Ioi
    (f := g) (μ := volume) (b := fun n : Nat => (n : Real))
    (l := atTop) 0 hg tendsto_natCast_atTop_atTop
  have hlimTwoG := (tendsto_const_nhds.mul hlimG :
    Tendsto (fun n : Nat =>
      2 * ∫ u in (0 : Real)..(n : Real), g u) atTop
        (𝓝 (2 * ∫ u : Real in Set.Ioi 0, g u)))
  have hseq : (fun n : Nat => ∫ u in (0 : Real)..(n : Real), f u) =
      fun n : Nat => 2 * ∫ u in (0 : Real)..(n : Real), g u := by
    funext n
    exact intervalIntegral_binetSawtooth_div_sq_zero_nat_eq_primitive hz n
  rw [hseq] at hlimF
  exact tendsto_nhds_unique hlimF hlimTwoG

/-- The absolutely convergent second Binet remainder.  Its quadratic
denominator exposes vertical decay directly. -/
def periodicBinetLogRemainder (z : Complex) : Complex :=
  ∫ u : Real in Set.Ioi 0,
    (binetSawtoothPrimitive u : Complex) / (z + (u : Complex)) ^ 2

/-- Integrability of the elementary quadratic tail used below. -/
theorem integrableOn_one_div_add_sq {b : Real} (hb : 0 < b) :
    IntegrableOn (fun u : Real => 1 / (u + b) ^ 2) (Set.Ioi 0) := by
  have hbase := integrableOn_add_rpow_Ioi_of_lt
    (a := (-2 : Real)) (c := (0 : Real)) (m := b)
    (by norm_num) (by linarith)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro u hu
  have hub : 0 < u + b := by linarith [Set.mem_Ioi.mp hu]
  change (u + b) ^ (-2 : Real) = 1 / (u + b) ^ 2
  rw [show (-2 : Real) = -(2 : Real) by norm_num,
    Real.rpow_neg hub.le, Real.rpow_two]
  simp only [one_div]

/-- The elementary quadratic tail integral used in the vertical remainder
bound. -/
theorem integral_Ioi_one_div_add_sq {b : Real} (hb : 0 < b) :
    (∫ u : Real in Set.Ioi 0, 1 / (u + b) ^ 2) = 1 / b := by
  have hint := integrableOn_one_div_add_sq hb
  have hderiv : ∀ u ∈ Set.Ici (0 : Real),
      HasDerivAt (fun x : Real => -(1 / (x + b)))
        (1 / (u + b) ^ 2) u := by
    intro u hu
    have hub : u + b ≠ 0 := by linarith [Set.mem_Ici.mp hu]
    have hraw := (((hasDerivAt_id u).add_const b).inv hub).neg
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with x
      simp only [Pi.neg_apply, Pi.inv_apply, id_eq, one_div]
    · simp only [id_eq]
      ring
  have htend : Tendsto (fun x : Real => -(1 / (x + b))) atTop (𝓝 0) := by
    have htop : Tendsto (fun x : Real => x + b) atTop atTop :=
      tendsto_atTop_add_const_right atTop b tendsto_id
    simpa only [one_div, neg_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp htop).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  field_simp [hb.ne']
  ring

/-- The periodic second-Binet remainder is absolutely integrable throughout
the open right half-plane. -/
theorem integrableOn_periodicBinetLogRemainder
    {z : Complex} (hz : 0 < z.re) :
    IntegrableOn (fun u : Real =>
      (binetSawtoothPrimitive u : Complex) /
        (z + (u : Complex)) ^ 2) (Set.Ioi 0) := by
  have hmajor : IntegrableOn
      (fun u : Real => (1 / 8 : Real) * (1 / (u + z.re) ^ 2))
      (Set.Ioi 0) :=
    (integrableOn_one_div_add_sq hz).const_mul (1 / 8 : Real)
  refine hmajor.mono' ?_ ?_
  · exact (measurable_binetSawtoothPrimitive.complex_ofReal.div
      ((measurable_const.add measurable_id.complex_ofReal).pow_const 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
    have huz : 0 < u + z.re := by linarith
    let w : Complex := z + (u : Complex)
    have hwRe : w.re = z.re + u := by simp [w]
    have hnorm : u + z.re ≤ ‖w‖ := by
      have hwRePos : 0 < w.re := by rw [hwRe]; linarith
      calc
        u + z.re = w.re := by rw [hwRe]; ring
        _ = |w.re| := (abs_of_pos hwRePos).symm
        _ ≤ ‖w‖ := Complex.abs_re_le_norm w
    have hden : (u + z.re) ^ 2 ≤ ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg w]
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    simpa only [w, div_eq_mul_inv, one_mul] using
      (div_le_div₀ (by norm_num) (abs_binetSawtoothPrimitive_le u)
        (sq_pos_of_pos huz) hden)

/-- On the right half-plane, the periodic second-Binet remainder has its
natural reciprocal-real-part bound. -/
theorem norm_periodicBinetLogRemainder_le
    {z : Complex} (hz : 0 < z.re) :
    ‖periodicBinetLogRemainder z‖ ≤ 1 / (8 * z.re) := by
  calc
    ‖periodicBinetLogRemainder z‖ ≤
        ∫ u : Real in Set.Ioi 0,
          (1 / 8 : Real) * (1 / (u + z.re) ^ 2) := by
      apply norm_integral_le_of_norm_le
      · exact (integrableOn_one_div_add_sq hz).const_mul (1 / 8 : Real)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := Set.mem_Ioi.mp hu
        have huz : 0 < u + z.re := by linarith
        let w : Complex := z + (u : Complex)
        have hwRe : w.re = z.re + u := by simp [w]
        have hnorm : u + z.re ≤ ‖w‖ := by
          have hwRePos : 0 < w.re := by rw [hwRe]; linarith
          calc
            u + z.re = w.re := by rw [hwRe]; ring
            _ = |w.re| := (abs_of_pos hwRePos).symm
            _ ≤ ‖w‖ := Complex.abs_re_le_norm w
        have hden : (u + z.re) ^ 2 ≤ ‖w‖ ^ 2 := by
          nlinarith [norm_nonneg w]
        rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
        simpa only [w, div_eq_mul_inv, one_mul] using
          (div_le_div₀ (by norm_num) (abs_binetSawtoothPrimitive_le u)
            (sq_pos_of_pos huz) hden)
    _ = 1 / (8 * z.re) := by
      rw [integral_const_mul, integral_Ioi_one_div_add_sq hz]
      field_simp [hz.ne']

/-- Differentiating the absolutely convergent periodic remainder recovers the
complexified sawtooth correction. -/
theorem hasDerivAt_periodicBinetLogRemainder
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt periodicBinetLogRemainder
      (-∫ u : Real in Set.Ioi 0,
        (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) z := by
  let μ := volume.restrict (Set.Ioi (0 : Real))
  let r : Real := z.re / 2
  let s : Set Complex := Metric.ball z r
  let F : Complex → Real → Complex := fun w u =>
    (binetSawtoothPrimitive u : Complex) *
      ((w + (u : Complex)) ^ 2)⁻¹
  let F' : Complex → Real → Complex := fun w u =>
    -2 * (binetSawtoothPrimitive u : Complex) /
      (w + (u : Complex)) ^ 3
  let bound : Real → Real := fun u =>
    (1 / 4 : Real) * (1 / (u + r) ^ 3)
  have hr : 0 < r := by
    dsimp only [r]
    linarith
  have hs : s ∈ 𝓝 z := Metric.ball_mem_nhds z hr
  have hFmeas : ∀ᶠ w in 𝓝 z, AEStronglyMeasurable (F w) μ := by
    filter_upwards [] with w
    have hmeas : Measurable (F w) := by
      exact measurable_binetSawtoothPrimitive.complex_ofReal.mul
        ((measurable_const.add measurable_id.complex_ofReal).pow_const 2).inv
    simpa only [μ] using hmeas.aestronglyMeasurable.restrict
  have hFint : Integrable (F z) μ := by
    simpa only [F, div_eq_mul_inv] using
      (integrableOn_periodicBinetLogRemainder hz).integrable
  have hF'meas : AEStronglyMeasurable (F' z) μ := by
    have hmeas : Measurable (F' z) := by
      exact (measurable_const.mul
        measurable_binetSawtoothPrimitive.complex_ofReal).div
          ((measurable_const.add measurable_id.complex_ofReal).pow_const 3)
    simpa only [μ] using hmeas.aestronglyMeasurable.restrict
  have hbound : ∀ᵐ u ∂μ, ∀ w ∈ s, ‖F' w u‖ ≤ bound u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
    have hu0 : 0 < u := Set.mem_Ioi.mp hu
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
    have hur : 0 < u + r := by positivity
    let v : Complex := w + (u : Complex)
    have hvRe : v.re = w.re + u := by simp [v]
    have hnorm : u + r ≤ ‖v‖ := by
      have hvRePos : 0 < v.re := by rw [hvRe]; linarith
      calc
        u + r ≤ v.re := by rw [hvRe]; linarith
        _ = |v.re| := (abs_of_pos hvRePos).symm
        _ ≤ ‖v‖ := Complex.abs_re_le_norm v
    have hden : (u + r) ^ 3 ≤ ‖v‖ ^ 3 :=
      pow_le_pow_left₀ (by positivity) hnorm 3
    dsimp only [F', bound]
    rw [norm_div, norm_mul, norm_neg, norm_ofNat, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
    have hnum : 2 * |binetSawtoothPrimitive u| ≤ (1 / 4 : Real) := by
      nlinarith [abs_binetSawtoothPrimitive_le u]
    simpa only [v, div_eq_mul_inv, one_mul] using
      (div_le_div₀ (by norm_num) hnum (pow_pos hur 3) hden)
  have hboundInt : Integrable bound μ := by
    have hbase := integrableOn_add_rpow_Ioi_of_lt
      (a := (-3 : Real)) (c := (0 : Real)) (m := r)
      (by norm_num) (by linarith)
    have hpow : IntegrableOn (fun u : Real => 1 / (u + r) ^ 3)
        (Set.Ioi 0) := by
      refine hbase.congr_fun ?_ measurableSet_Ioi
      intro u hu
      have hur : 0 < u + r := by linarith [Set.mem_Ioi.mp hu]
      change (u + r) ^ (-3 : Real) = 1 / (u + r) ^ 3
      rw [show (-3 : Real) = -(3 : Real) by norm_num,
        Real.rpow_neg hur.le]
      calc
        ((u + r) ^ (3 : Real))⁻¹ = ((u + r) ^ (3 : Nat))⁻¹ :=
          congrArg Inv.inv (Real.rpow_natCast (u + r) 3)
        _ = 1 / (u + r) ^ 3 := by simp only [one_div]
    simpa only [bound, μ] using hpow.const_mul (1 / 4 : Real)
  have hdiff : ∀ᵐ u ∂μ, ∀ w ∈ s,
      @HasDerivAt Complex _ Complex instNormedAddCommGroup.toAddCommGroup
        RCLike.innerProductSpace.toModule _ _ (F · u) (F' w u) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro w hw
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
    have hw0 : w + (u : Complex) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith [Set.mem_Ioi.mp hu]
    have hbase : HasDerivAt (fun v : Complex => v + (u : Complex)) 1 w := by
      simpa only [id_eq] using (hasDerivAt_id w).add_const (u : Complex)
    have hnum : HasDerivAt
        (fun _ : Complex => (binetSawtoothPrimitive u : Complex)) 0 w :=
      hasDerivAt_const w _
    have hraw := hnum.div (hbase.pow 2) (pow_ne_zero 2 hw0)
    have hfun :
        ((fun _ : Complex => (binetSawtoothPrimitive u : Complex)) /
          (fun v : Complex => v + (u : Complex)) ^ 2) =
        (fun v : Complex => (binetSawtoothPrimitive u : Complex) /
          (v + (u : Complex)) ^ 2) := by
      funext v
      rfl
    rw [hfun] at hraw
    simpa only [F, F', div_eq_mul_inv] using
      hraw.congr_deriv (by
        simp only [Pi.pow_apply, Nat.reduceSub, pow_one, mul_one,
          zero_mul, zero_sub]
        field_simp [hw0]
        ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas hFint hF'meas hbound hboundInt hdiff
  have hderiv : HasDerivAt periodicBinetLogRemainder
      (∫ u : Real in Set.Ioi 0, F' z u) z := by
    change HasDerivAt (fun w => ∫ u, F w u ∂μ) (∫ u, F' z u ∂μ) z
    exact hmain.2
  have hF'eq : (fun u : Real => F' z u) = fun u : Real =>
      -2 * ((binetSawtoothPrimitive u : Complex) /
        (z + (u : Complex)) ^ 3) := by
    funext u
    dsimp only [F']
    ring
  have hvalue : (∫ u : Real in Set.Ioi 0, F' z u) =
      -(∫ u : Real in Set.Ioi 0,
        (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2) := by
    rw [hF'eq, integral_const_mul,
      integral_binetSawtooth_div_sq_eq_periodicPrimitive hz]
    ring
  exact hderiv.congr_deriv hvalue

/-- The complexified centered-sawtooth correction in Binet's digamma
formula. -/
def complexBinetSawtoothCorrection (z : Complex) : Complex :=
  ∫ u : Real in Set.Ioi 0,
    (binetSawtooth u : Complex) / (z + (u : Complex)) ^ 2

/-- On the positive real axis, the complex sawtooth correction is exactly the
project's Laplace-form Binet correction. -/
theorem complexBinetSawtoothCorrection_ofReal
    {x : Real} (hx : 0 < x) :
    complexBinetSawtoothCorrection (x : Complex) =
      bennettGammaBinetIntegral (x : Complex) := by
  rw [complexBinetSawtoothCorrection, bennettGammaBinetIntegral,
    integral_bennettGammaBinetKernel_ofReal hx]
  calc
    (∫ u : Real in Set.Ioi 0,
        (binetSawtooth u : Complex) /
          ((x : Complex) + (u : Complex)) ^ 2) =
        ∫ u : Real in Set.Ioi 0,
          ((binetSawtooth u / (x + u) ^ 2 : Real) : Complex) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u _
      push_cast
      rfl
    _ = ((∫ u : Real in Set.Ioi 0,
        binetSawtooth u / (x + u) ^ 2 : Real) : Complex) := integral_ofReal

/-- The complex sawtooth correction is analytic on the open right
half-plane. -/
theorem analyticOnNhd_complexBinetSawtoothCorrection :
    AnalyticOnNhd Complex complexBinetSawtoothCorrection
      {z : Complex | 0 < z.re} := by
  let U : Set Complex := {z : Complex | 0 < z.re}
  have hU : IsOpen U := isOpen_Ioi.preimage Complex.continuous_re
  have hperiodic : AnalyticOnNhd Complex periodicBinetLogRemainder U := by
    apply DifferentiableOn.analyticOnNhd
    · intro z hz
      exact (hasDerivAt_periodicBinetLogRemainder hz).differentiableAt.differentiableWithinAt
    · exact hU
  have hEq : U.EqOn (fun z => -deriv periodicBinetLogRemainder z)
      complexBinetSawtoothCorrection := by
    intro z hz
    have hderiv := (hasDerivAt_periodicBinetLogRemainder hz).deriv
    change -deriv periodicBinetLogRemainder z =
      complexBinetSawtoothCorrection z
    rw [hderiv]
    simp only [complexBinetSawtoothCorrection, neg_neg]
  exact hperiodic.deriv.neg.congr hU hEq

/-- Positive real agreement accumulates at `1`, providing the uniqueness set
for the two analytic Binet corrections. -/
theorem one_mem_closure_complexBinetSawtooth_eq_bennett :
    (1 : Complex) ∈ closure
      ({z : Complex |
          complexBinetSawtoothCorrection z = bennettGammaBinetIntegral z} \
        {1}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let x : Real := 1 + ε / 2
  refine ⟨(x : Complex), ⟨?_, ?_⟩, ?_⟩
  · exact complexBinetSawtoothCorrection_ofReal (by
      dsimp only [x]
      linarith)
  · simp only [Set.mem_singleton_iff]
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    dsimp only [x] at hre
    linarith
  · simpa [x, abs_of_pos hε] using (half_lt_self hε)

/-- The periodic and Laplace descriptions of Binet's digamma correction agree
throughout the right half-plane. -/
theorem complexBinetSawtoothCorrection_eq_bennett
    {z : Complex} (hz : 0 < z.re) :
    complexBinetSawtoothCorrection z = bennettGammaBinetIntegral z := by
  have hEqOn : Set.EqOn complexBinetSawtoothCorrection
      bennettGammaBinetIntegral {z : Complex | 0 < z.re} :=
    analyticOnNhd_complexBinetSawtoothCorrection.eqOn_of_preconnected_of_mem_closure
      analyticOnNhd_bennettGammaBinetIntegral
      (convex_halfSpace_re_gt 0).isPreconnected
      (by norm_num : (1 : Complex) ∈ {z : Complex | 0 < z.re})
      one_mem_closure_complexBinetSawtooth_eq_bennett
  exact hEqOn hz

/-- After identifying the complex sawtooth correction, the periodic remainder
has exactly the same derivative as the Laplace-form logarithmic remainder. -/
theorem hasDerivAt_periodicBinetLogRemainder_bennett
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt periodicBinetLogRemainder
      (-bennettGammaBinetIntegral z) z := by
  refine (hasDerivAt_periodicBinetLogRemainder hz).congr_deriv ?_
  change -complexBinetSawtoothCorrection z =
    -bennettGammaBinetIntegral z
  rw [complexBinetSawtoothCorrection_eq_bennett hz]

/-- The periodic remainder tends to zero along the positive integers. -/
theorem tendsto_periodicBinetLogRemainder_natCast_add_one :
    Tendsto (fun n : Nat =>
      periodicBinetLogRemainder ((n + 1 : Nat) : Complex))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero
    (fun n => norm_nonneg
      (periodicBinetLogRemainder ((n + 1 : Nat) : Complex)))
    (fun n => by
      have hb := norm_periodicBinetLogRemainder_le
        (z := ((n + 1 : Nat) : Complex)) (by
          simp only [Complex.natCast_re]
          positivity)
      calc
        ‖periodicBinetLogRemainder ((n + 1 : Nat) : Complex)‖ ≤
            1 / (8 * (((n + 1 : Nat) : Complex).re)) := hb
        _ ≤ 1 / ((n : Real) + 1) := by
          simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
            Nat.cast_add, Nat.cast_one]
          apply one_div_le_one_div_of_le (by positivity)
          have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
          nlinarith)
    hbase

/-- The Laplace-form logarithmic remainder tends to zero along the positive
integers. -/
theorem tendsto_gammaBinetLogRemainder_natCast_add_one :
    Tendsto (fun n : Nat =>
      gammaBinetLogRemainder ((n + 1 : Nat) : Complex))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase : Tendsto (fun n : Nat => (1 : Real) / (n + 1))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero
    (fun n => norm_nonneg
      (gammaBinetLogRemainder ((n + 1 : Nat) : Complex)))
    (fun n => by
      have hb := norm_gammaBinetLogRemainder_le
        (z := ((n + 1 : Nat) : Complex)) (by
          simp only [Complex.natCast_re]
          positivity)
      calc
        ‖gammaBinetLogRemainder ((n + 1 : Nat) : Complex)‖ ≤
            1 / (2 * (((n + 1 : Nat) : Complex).re)) := hb
        _ ≤ 1 / ((n : Real) + 1) := by
          simp only [Complex.add_re, Complex.natCast_re, Complex.one_re,
            Nat.cast_add, Nat.cast_one]
          apply one_div_le_one_div_of_le (by positivity)
          have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
          nlinarith)
    hbase

/-- The periodic second-Binet remainder is the Laplace logarithmic remainder
on the whole right half-plane.  Equality of derivatives determines the two
forms up to a constant; their independent decay at positive-real infinity
forces that constant to vanish. -/
theorem periodicBinetLogRemainder_eq_gammaBinetLogRemainder
    {z : Complex} (hz : 0 < z.re) :
    periodicBinetLogRemainder z = gammaBinetLogRemainder z := by
  let U : Set Complex := {w : Complex | 0 < w.re}
  have hU : IsOpen U := isOpen_Ioi.preimage Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hp : DifferentiableOn Complex periodicBinetLogRemainder U := by
    intro w hw
    exact (hasDerivAt_periodicBinetLogRemainder_bennett hw).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn Complex gammaBinetLogRemainder U := by
    intro w hw
    exact (hasDerivAt_gammaBinetLogRemainder hw).differentiableAt.differentiableWithinAt
  have hderiv : U.EqOn (deriv periodicBinetLogRemainder)
      (deriv gammaBinetLogRemainder) := by
    intro w hw
    rw [(hasDerivAt_periodicBinetLogRemainder_bennett hw).deriv,
      (hasDerivAt_gammaBinetLogRemainder hw).deriv]
  obtain ⟨a, ha⟩ := hU.exists_eq_add_of_deriv_eq hUpre hp hg hderiv
  have hlimDiff : Tendsto (fun n : Nat =>
      periodicBinetLogRemainder ((n + 1 : Nat) : Complex) -
        gammaBinetLogRemainder ((n + 1 : Nat) : Complex))
      atTop (𝓝 0) := by
    simpa only [sub_zero] using
      tendsto_periodicBinetLogRemainder_natCast_add_one.sub
        tendsto_gammaBinetLogRemainder_natCast_add_one
  have hseq : (fun n : Nat =>
      periodicBinetLogRemainder ((n + 1 : Nat) : Complex) -
        gammaBinetLogRemainder ((n + 1 : Nat) : Complex)) =
      fun _ : Nat => a := by
    funext n
    have hnU : ((n + 1 : Nat) : Complex) ∈ U := by
      change 0 < (((n + 1 : Nat) : Complex).re)
      simp only [Complex.natCast_re]
      positivity
    rw [ha hnU]
    ring
  rw [hseq] at hlimDiff
  have ha0 : a = 0 := tendsto_nhds_unique tendsto_const_nhds hlimDiff
  have hzU : z ∈ U := hz
  simpa only [ha0, add_zero] using ha hzU

/-- The periodic Binet integrand has a quadratic height majorant on the
critical Gamma line. -/
theorem norm_periodicBinetLogIntegrand_le
    {t u : Real} (ht : 0 < t) (hu : 0 < u) :
    ‖(binetSawtoothPrimitive u : Complex) /
        (criticalLineGammaArgument t + (u : Complex)) ^ 2‖ ≤
      (1 / 4 : Real) * (1 / (u + t / 2) ^ 2) := by
  let w : Complex := criticalLineGammaArgument t + (u : Complex)
  have hb : 0 < t / 2 := by positivity
  have hub : 0 < u + t / 2 := by positivity
  have hwNormSq : ‖w‖ ^ 2 = (u + 1 / 4) ^ 2 + (t / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [w, Complex.add_re, Complex.add_im,
      criticalLineGammaArgument_re, criticalLineGammaArgument_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hdenLower : (u + t / 2) ^ 2 / 2 ≤ ‖w‖ ^ 2 := by
    rw [hwNormSq]
    nlinarith [sq_nonneg (u - t / 2)]
  have hdenPos : 0 < ‖w‖ ^ 2 := lt_of_lt_of_le
    (div_pos (sq_pos_of_pos hub) (by norm_num)) hdenLower
  have hmajorPos : 0 < (u + t / 2) ^ 2 := sq_pos_of_pos hub
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hnum := abs_binetSawtoothPrimitive_le u
  calc
    |binetSawtoothPrimitive u| / ‖w‖ ^ 2 ≤
        (1 / 8 : Real) / ((u + t / 2) ^ 2 / 2) := by
          exact div_le_div₀ (by norm_num) hnum
            (div_pos hmajorPos (by norm_num)) hdenLower
    _ = (1 / 4 : Real) * (1 / (u + t / 2) ^ 2) := by
      field_simp [hmajorPos.ne']
      ring

/-- The periodic Binet remainder is absolutely integrable on the critical
Gamma line at positive height. -/
theorem integrableOn_periodicBinetLogRemainder_criticalLine
    {t : Real} (ht : 0 < t) :
    IntegrableOn (fun u : Real =>
      (binetSawtoothPrimitive u : Complex) /
        (criticalLineGammaArgument t + (u : Complex)) ^ 2)
      (Set.Ioi 0) := by
  have hmajor : IntegrableOn
      (fun u : Real => (1 / 4 : Real) * (1 / (u + t / 2) ^ 2))
      (Set.Ioi 0) :=
    (integrableOn_one_div_add_sq (show 0 < t / 2 by positivity)).const_mul
      (1 / 4 : Real)
  refine hmajor.mono' ?_ ?_
  · have hmeas : Measurable (fun u : Real =>
        (binetSawtoothPrimitive u : Complex) /
          (criticalLineGammaArgument t + (u : Complex)) ^ 2) := by
      exact measurable_binetSawtoothPrimitive.complex_ofReal.div
        ((measurable_const.add measurable_id.complex_ofReal).pow_const 2)
    exact hmeas.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_periodicBinetLogIntegrand_le ht (Set.mem_Ioi.mp hu)

/-- The second Binet form gives the required reciprocal-height decay before
its identification with the Laplace-form logarithmic remainder. -/
theorem norm_periodicBinetLogRemainder_criticalLine_le
    {t : Real} (ht : 0 < t) :
    ‖periodicBinetLogRemainder (criticalLineGammaArgument t)‖ ≤ 1 / (2 * t) := by
  calc
    ‖periodicBinetLogRemainder (criticalLineGammaArgument t)‖ ≤
        ∫ u : Real in Set.Ioi 0,
          (1 / 4 : Real) * (1 / (u + t / 2) ^ 2) := by
      apply norm_integral_le_of_norm_le
      · exact (integrableOn_one_div_add_sq
          (show 0 < t / 2 by positivity)).const_mul (1 / 4 : Real)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact norm_periodicBinetLogIntegrand_le ht (Set.mem_Ioi.mp hu)
    _ = 1 / (2 * t) := by
      rw [integral_const_mul, integral_Ioi_one_div_add_sq
        (show 0 < t / 2 by positivity)]
      field_simp [ht.ne']
      ring

/-- The Laplace-form Binet remainder inherits the sharp reciprocal-height
bound furnished by the periodic second-Binet representation. -/
theorem norm_gammaBinetLogRemainder_criticalLine_le
    {t : Real} (ht : 0 < t) :
    ‖gammaBinetLogRemainder (criticalLineGammaArgument t)‖ ≤ 1 / (2 * t) := by
  rw [← periodicBinetLogRemainder_eq_gammaBinetLogRemainder (by
    rw [criticalLineGammaArgument_re]
    norm_num)]
  exact norm_periodicBinetLogRemainder_criticalLine_le ht

/-- The imaginary part of the full Stirling logarithm differs from the Hardy
phase by at most `11 / (16t)` for `t ≥ 1`. -/
theorem abs_criticalLineGammaStirlingLog_im_sub_phase_le
    {t : Real} (ht : 1 ≤ t) :
    |(criticalLineGammaStirlingMain t +
          gammaBinetLogRemainder (criticalLineGammaArgument t)).im -
        criticalLineStirlingPhase t| ≤ 11 / (16 * t) := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hmain := abs_criticalLineGammaStirlingMain_im_sub_phase_le ht
  have hremNorm := norm_gammaBinetLogRemainder_criticalLine_le ht0
  have hrem :
      |(gammaBinetLogRemainder (criticalLineGammaArgument t)).im| ≤
        1 / (2 * t) :=
    (Complex.abs_im_le_norm _).trans hremNorm
  rw [Complex.add_im]
  calc
    |(criticalLineGammaStirlingMain t).im +
          (gammaBinetLogRemainder (criticalLineGammaArgument t)).im -
        criticalLineStirlingPhase t| =
        |((criticalLineGammaStirlingMain t).im -
            criticalLineStirlingPhase t) +
          (gammaBinetLogRemainder (criticalLineGammaArgument t)).im| := by
            congr 1
            ring
    _ ≤ |(criticalLineGammaStirlingMain t).im -
          criticalLineStirlingPhase t| +
        |(gammaBinetLogRemainder (criticalLineGammaArgument t)).im| :=
      abs_add_le _ _
    _ ≤ 3 / (16 * t) + 1 / (2 * t) := add_le_add hmain hrem
    _ = 11 / (16 * t) := by
      field_simp [ht0.ne']
      ring

/-- On the positive real axis the complete Binet logarithm is real.  This is
the branch anchor used to identify its exponential with the actual Gamma
factor. -/
theorem gammaRStirlingLogWithRemainder_im_ofReal
    {x : Real} (hx : 0 < x) :
    (gammaRStirlingLogMain (x : Complex) +
        gammaBinetLogRemainder (x : Complex)).im = 0 := by
  have hint := integrableOn_periodicBinetLogRemainder
    (z := (x : Complex)) (by simpa using hx)
  have him : (periodicBinetLogRemainder (x : Complex)).im = 0 := by
    rw [periodicBinetLogRemainder]
    have himEq := integral_im hint
    change (∫ u : Real in Set.Ioi 0,
        ((binetSawtoothPrimitive u : Complex) /
          ((x : Complex) + (u : Complex)) ^ 2).im) =
      (∫ u : Real in Set.Ioi 0,
        (binetSawtoothPrimitive u : Complex) /
          ((x : Complex) + (u : Complex)) ^ 2).im at himEq
    rw [← himEq]
    have hfun : (fun u : Real =>
        ((binetSawtoothPrimitive u : Complex) /
          ((x : Complex) + (u : Complex)) ^ 2).im) = 0 := by
      funext u
      have hden : (((x : Complex) + (u : Complex)) ^ 2).im = 0 := by
        have hreal : ((x : Complex) + (u : Complex)) ^ 2 =
            (((x + u) ^ 2 : Real) : Complex) := by
          push_cast
          rfl
        rw [hreal]
        rfl
      simp [Complex.div_im, hden]
    rw [hfun]
    simp
  rw [← periodicBinetLogRemainder_eq_gammaBinetLogRemainder
    (z := (x : Complex)) (by simpa using hx)]
  rw [Complex.add_im, him, add_zero]
  have hlogim : (Complex.log (x : Complex)).im = 0 := by
    rw [← Complex.ofReal_log hx.le]
    simp
  simp [gammaRStirlingLogMain, hlogim]

/-- The exact Gamma factor at the doubled argument satisfies the same
first-order equation as the exponential of the complete Binet logarithm. -/
theorem hasDerivAt_pi_cpow_neg_mul_Gamma
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt
      (fun w : Complex => (Real.pi : Complex) ^ (-w) * Complex.Gamma w)
      (((Real.pi : Complex) ^ (-z) * Complex.Gamma z) *
        (Complex.digamma z - Real.log Real.pi)) z := by
  have hpow :
      HasDerivAt (fun w : Complex => (Real.pi : Complex) ^ (-w))
        ((Real.pi : Complex) ^ (-z) * Complex.log Real.pi * (-1)) z :=
    (hasDerivAt_id z).neg.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hgammaDiff : DifferentiableAt Complex Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (fun m hm => by
      have hre := congrArg Complex.re hm
      simp at hre
      linarith)
  have hraw := hpow.mul hgammaDiff.hasDerivAt
  refine hraw.congr_deriv ?_
  rw [Complex.digamma_def, logDeriv_apply,
    ← Complex.ofReal_log Real.pi_pos.le]
  have hgammaNe : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hz
  field_simp [hgammaNe]
  ring

/-- The exponential of the complete Binet logarithm satisfies the exact
Gamma logarithmic-derivative equation on the right half-plane. -/
theorem hasDerivAt_exp_gammaRStirlingLogWithRemainder
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt
      (fun w : Complex => Complex.exp
        (gammaRStirlingLogMain w + gammaBinetLogRemainder w))
      (Complex.exp (gammaRStirlingLogMain z + gammaBinetLogRemainder z) *
        (Complex.digamma z - Real.log Real.pi)) z := by
  exact (Complex.hasDerivAt_exp _).comp z
    (hasDerivAt_gammaRStirlingLogWithRemainder hz)

/-- The quotient of the actual Gamma factor by the complete Binet
exponential has zero derivative on the right half-plane. -/
theorem hasDerivAt_gammaBinetExponentialRatio
    {z : Complex} (hz : 0 < z.re) :
    HasDerivAt
      (fun w : Complex =>
        ((Real.pi : Complex) ^ (-w) * Complex.Gamma w) /
          Complex.exp
            (gammaRStirlingLogMain w + gammaBinetLogRemainder w))
      0 z := by
  have hnum := hasDerivAt_pi_cpow_neg_mul_Gamma hz
  have hden := hasDerivAt_exp_gammaRStirlingLogWithRemainder hz
  have hdenNe : Complex.exp
      (gammaRStirlingLogMain z + gammaBinetLogRemainder z) ≠ 0 :=
    Complex.exp_ne_zero _
  refine (hnum.div hden hdenNe).congr_deriv ?_
  field_simp [hdenNe]
  ring

/-- The Gamma/Binet exponential quotient is constant throughout the open
right half-plane. -/
theorem gammaBinetExponentialRatio_eq_at_one
    {z : Complex} (hz : 0 < z.re) :
    ((Real.pi : Complex) ^ (-z) * Complex.Gamma z) /
        Complex.exp
          (gammaRStirlingLogMain z + gammaBinetLogRemainder z) =
      ((Real.pi : Complex) ^ (-(1 : Complex)) * Complex.Gamma 1) /
        Complex.exp
          (gammaRStirlingLogMain 1 + gammaBinetLogRemainder 1) := by
  let U : Set Complex := {w : Complex | 0 < w.re}
  let Q : Complex → Complex := fun w =>
    ((Real.pi : Complex) ^ (-w) * Complex.Gamma w) /
      Complex.exp
        (gammaRStirlingLogMain w + gammaBinetLogRemainder w)
  have hU : IsOpen U := isOpen_Ioi.preimage Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hQ : DifferentiableOn Complex Q U := by
    intro w hw
    exact (hasDerivAt_gammaBinetExponentialRatio hw).differentiableAt.differentiableWithinAt
  have hconst : DifferentiableOn Complex (fun _ : Complex => Q 1) U :=
    differentiableOn_const (c := Q 1)
  have hderiv : U.EqOn (deriv Q) (deriv fun _ : Complex => Q 1) := by
    intro w hw
    rw [(hasDerivAt_gammaBinetExponentialRatio hw).deriv]
    simp
  obtain ⟨a, ha⟩ := hU.exists_eq_add_of_deriv_eq
    hUpre hQ hconst hderiv
  have hOneU : (1 : Complex) ∈ U := by
    norm_num [U]
  have haOne := ha hOneU
  have haZero : a = 0 := by
    dsimp only [Q] at haOne
    have hcancel := congrArg (fun w : Complex => w -
      ((Real.pi : Complex) ^ (-(1 : Complex)) * Complex.Gamma 1) /
        Complex.exp
          (gammaRStirlingLogMain 1 + gammaBinetLogRemainder 1)) haOne
    simpa only [sub_self, add_sub_cancel_left] using hcancel.symm
  have hzU : z ∈ U := hz
  have haz := ha hzU
  dsimp only [Q] at haz ⊢
  simpa only [haZero, add_zero] using haz

/-- At the positive-real anchor, the constant Gamma/Binet quotient is a
strictly positive real number. -/
theorem exists_pos_gammaBinetExponentialRatio_at_one :
    ∃ c : Real, 0 < c ∧
      ((Real.pi : Complex) ^ (-(1 : Complex)) * Complex.Gamma 1) /
          Complex.exp
            (gammaRStirlingLogMain 1 + gammaBinetLogRemainder 1) =
        (c : Complex) := by
  let L : Complex := gammaRStirlingLogMain (1 : Complex) +
    gammaBinetLogRemainder (1 : Complex)
  have hLim : L.im = 0 := by
    dsimp only [L]
    convert (gammaRStirlingLogWithRemainder_im_ofReal
      (x := 1) (by norm_num)) using 1 <;> norm_num
  have hExp : Complex.exp L = (Real.exp L.re : Complex) := by
    rw [Complex.exp_eq_exp_re_mul_sin_add_cos, hLim]
    simp
  have hNum :
      (Real.pi : Complex) ^ (-(1 : Complex)) * Complex.Gamma 1 =
        ((1 / Real.pi : Real) : Complex) := by
    rw [Complex.Gamma_one, mul_one, Complex.cpow_neg_one]
    push_cast
    simp only [one_div]
  refine ⟨(1 / Real.pi) / Real.exp L.re, by positivity, ?_⟩
  rw [hNum, show gammaRStirlingLogMain 1 + gammaBinetLogRemainder 1 = L by rfl,
    hExp]
  push_cast
  rfl

/-- Normalizing a complex exponential by its norm retains exactly the
exponential of its imaginary part. -/
theorem exp_div_norm_eq_exp_I_mul_im (z : Complex) :
    Complex.exp z / ‖Complex.exp z‖ =
      Complex.exp (Complex.I * z.im) := by
  have hz : z = (z.re : Complex) + Complex.I * z.im := by
    apply Complex.ext <;> simp
  have hExpDecomp : Complex.exp z =
      Complex.exp (z.re : Complex) * Complex.exp (Complex.I * z.im) := by
    calc
      Complex.exp z = Complex.exp
          ((z.re : Complex) + Complex.I * z.im) := congrArg Complex.exp hz
      _ = Complex.exp (z.re : Complex) *
          Complex.exp (Complex.I * z.im) := Complex.exp_add _ _
  rw [Complex.norm_exp]
  rw [hExpDecomp, ← Complex.ofReal_exp]
  have hexpNe : (Real.exp z.re : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero z.re)
  field_simp [hexpNe]

/-- The unit normalization of the exact Gamma factor agrees with the phase
of the complete Binet logarithm throughout the right half-plane. -/
theorem pi_cpow_neg_mul_Gamma_div_norm_eq_exp_stirling_im
    {z : Complex} (hz : 0 < z.re) :
    ((Real.pi : Complex) ^ (-z) * Complex.Gamma z) /
        ‖(Real.pi : Complex) ^ (-z) * Complex.Gamma z‖ =
      Complex.exp (Complex.I *
        (gammaRStirlingLogMain z + gammaBinetLogRemainder z).im) := by
  obtain ⟨c, hc, hcAnchor⟩ :=
    exists_pos_gammaBinetExponentialRatio_at_one
  have hratio := gammaBinetExponentialRatio_eq_at_one hz
  rw [hcAnchor] at hratio
  have hExpNe : Complex.exp
      (gammaRStirlingLogMain z + gammaBinetLogRemainder z) ≠ 0 :=
    Complex.exp_ne_zero _
  have hfactor :
      (Real.pi : Complex) ^ (-z) * Complex.Gamma z =
        (c : Complex) * Complex.exp
          (gammaRStirlingLogMain z + gammaBinetLogRemainder z) :=
    (div_eq_iff hExpNe).mp hratio
  rw [hfactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc]
  have hcNe : (c : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hc.ne'
  have hnormExpNe :
      ‖Complex.exp
        (gammaRStirlingLogMain z + gammaBinetLogRemainder z)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hExpNe
  calc
    (c : Complex) *
          Complex.exp
            (gammaRStirlingLogMain z + gammaBinetLogRemainder z) /
        ((c * ‖Complex.exp
          (gammaRStirlingLogMain z + gammaBinetLogRemainder z)‖ : Real) :
            Complex) =
        Complex.exp
            (gammaRStirlingLogMain z + gammaBinetLogRemainder z) /
          ‖Complex.exp
            (gammaRStirlingLogMain z + gammaBinetLogRemainder z)‖ := by
      push_cast
      field_simp [hcNe, hnormExpNe]
    _ = Complex.exp (Complex.I *
        (gammaRStirlingLogMain z + gammaBinetLogRemainder z).im) :=
      exp_div_norm_eq_exp_I_mul_im _

/-- On the critical line, the unit normalization of `Gammaℝ` is exactly
the phase of the complete Binet logarithm at `1 / 4 + i t / 2`. -/
theorem criticalLineGammaR_div_norm_eq_exp_stirling_im (t : Real) :
    Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t) /
        ‖Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t)‖ =
      Complex.exp (Complex.I *
        (criticalLineGammaStirlingMain t +
          gammaBinetLogRemainder (criticalLineGammaArgument t)).im) := by
  have hz : 0 < (criticalLineGammaArgument t).re := by
    rw [criticalLineGammaArgument_re]
    norm_num
  have hsHalf :
      ((1 / 2 : Complex) + Complex.I * t) / 2 =
        criticalLineGammaArgument t := by
    apply Complex.ext <;> simp [criticalLineGammaArgument] <;> ring
  have hGammaR :
      Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t) =
        (Real.pi : Complex) ^ (-criticalLineGammaArgument t) *
          Complex.Gamma (criticalLineGammaArgument t) := by
    rw [Complex.Gammaℝ_def, neg_div, hsHalf]
  rw [hGammaR]
  simpa only [criticalLineGammaStirlingMain] using
    (pi_cpow_neg_mul_Gamma_div_norm_eq_exp_stirling_im hz)

/-- The exponential map restricted to the imaginary axis is one-Lipschitz
when its phases are measured without reducing modulo `2 * pi`. -/
theorem norm_exp_I_mul_sub_exp_I_mul_le (a b : Real) :
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ ≤
      |a - b| := by
  have hphase :
      Complex.I * (a : Complex) =
        Complex.I * (b : Complex) + Complex.I * ((a - b : Real) : Complex) := by
    push_cast
    ring
  calc
    ‖Complex.exp (Complex.I * a) - Complex.exp (Complex.I * b)‖ =
        ‖Complex.exp (Complex.I * b) *
          (Complex.exp (Complex.I * ((a - b : Real) : Complex)) - 1)‖ := by
      rw [hphase, Complex.exp_add, mul_sub, mul_one]
    _ = ‖Complex.exp (Complex.I * b)‖ *
        ‖Complex.exp (Complex.I * ((a - b : Real) : Complex)) - 1‖ :=
      norm_mul _ _
    _ = ‖Complex.exp (Complex.I * ((a - b : Real) : Complex)) - 1‖ := by
      rw [Complex.norm_exp]
      simp
    _ ≤ ‖a - b‖ := by
      simpa only using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))
    _ = |a - b| := Real.norm_eq_abs _

/-- Explicit H2 critical-line Stirling estimate.  The unit phase of the exact
real Gamma factor differs from the project phase by at most `11 / (16 * t)`
for every `t ≥ 1`. -/
theorem norm_criticalLineGammaR_unit_sub_exp_stirlingPhase_le
    {t : Real} (ht : 1 ≤ t) :
    ‖Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t) /
          ‖Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t)‖ -
        Complex.exp (Complex.I * criticalLineStirlingPhase t)‖ ≤
      11 / (16 * t) := by
  rw [criticalLineGammaR_div_norm_eq_exp_stirling_im]
  exact (norm_exp_I_mul_sub_exp_I_mul_le
    (criticalLineGammaStirlingMain t +
      gammaBinetLogRemainder (criticalLineGammaArgument t)).im
    (criticalLineStirlingPhase t)).trans
      (abs_criticalLineGammaStirlingLog_im_sub_phase_le ht)

/-- Uniform existence form of the H2 critical-line Stirling estimate, with
the explicit choices `Kγ = 11 / 16` and `Tγ = 1`. -/
theorem exists_uniform_criticalLineGammaR_stirlingPhase :
    ∃ Kγ Tγ : Real,
      0 < Kγ ∧ 1 ≤ Tγ ∧ ∀ t : Real, Tγ ≤ t →
        ‖Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t) /
              ‖Complex.Gammaℝ ((1 / 2 : Complex) + Complex.I * t)‖ -
            Complex.exp (Complex.I * criticalLineStirlingPhase t)‖ ≤
          Kγ / t := by
  refine ⟨11 / 16, 1, by norm_num, le_rfl, ?_⟩
  intro t ht
  convert norm_criticalLineGammaR_unit_sub_exp_stirlingPhase_le ht using 1 <;>
    ring

end


end Hardy


end RiemannHypothesisProject
