import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongElementaryTaylor

/-!
# Bellotti-Wong's continuous Gamma remainder

The imaginary part of `log Gamma(1/4 + iT/2)` in the Riemann-von Mangoldt
formula is a continuous argument, not the principal complex logarithm.  We
therefore normalize it intrinsically by integrating its derivative
`Re digamma(1/4 + it/2) / 2` from height zero.  This fixes the branch and gives
the concrete function to which the published `1 / (25*T)` remainder estimate
applies.
-/

open MeasureTheory

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The vertical Gamma line occurring in the Riemann-von Mangoldt formula. -/
def bellottiWongGammaLine (T : Real) : Complex :=
  (1 / 4 : Complex) + (T / 2 : Real) * Complex.I

@[simp]
theorem bellottiWongGammaLine_re (T : Real) :
    (bellottiWongGammaLine T).re = 1 / 4 := by
  simp [bellottiWongGammaLine]

/-- The Binet kernel whose Laplace transform controls the complex digamma remainder. -/
def bennettGammaBinetKernel (t : Real) : Complex :=
  (1 / 2 : Complex) - 1 / (t : Complex) +
    1 / (Complex.exp (t : Complex) - 1)

/-- The exact derivative of Binet's kernel on the positive axis. -/
def bennettGammaBinetKernelDeriv (t : Real) : Complex :=
  1 / (t : Complex) ^ 2 -
    Complex.exp (t : Complex) / (Complex.exp (t : Complex) - 1) ^ 2

/-- Binet's kernel has the expected derivative away from the origin. -/
theorem hasDerivAt_bennettGammaBinetKernel {t : Real} (ht : 0 < t) :
    HasDerivAt bennettGammaBinetKernel (bennettGammaBinetKernelDeriv t) t := by
  have ht0 : (t : Complex) ≠ 0 := by exact_mod_cast ht.ne'
  have hden : Complex.exp (t : Complex) - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : Real.exp t - 1 = 0 := by
      simpa [Complex.exp_ofReal_re] using hre
    nlinarith [Real.add_one_lt_exp ht.ne']
  have hinv : HasDerivAt (fun x : Real => 1 / (x : Complex))
      (-(1 : Complex) / (t : Complex) ^ 2) t := by
    simpa only [Function.comp_apply, one_div, neg_div] using!
      (hasDerivAt_inv ht0).comp_ofReal
  have hexp : HasDerivAt (fun x : Real => Complex.exp (x : Complex))
      (Complex.exp (t : Complex)) t :=
    (Complex.hasDerivAt_exp (t : Complex)).comp_ofReal
  have hdenInv : HasDerivAt
      (fun x : Real => 1 / (Complex.exp (x : Complex) - 1))
      (-(Complex.exp (t : Complex)) /
        (Complex.exp (t : Complex) - 1) ^ 2) t := by
    simpa only [Function.comp_apply, one_div] using!
      ((Complex.hasDerivAt_exp (t : Complex)).sub_const 1).inv hden |>.comp_ofReal
  convert ((hasDerivAt_const t (1 / 2 : Complex)).sub hinv).add hdenInv using 1
  all_goals first
    | rfl
    | (simp only [bennettGammaBinetKernelDeriv, one_div,
        sub_eq_add_neg]; ring)

/-- The Binet-kernel derivative is continuous on the positive axis. -/
theorem continuousAt_bennettGammaBinetKernelDeriv {t : Real} (ht : 0 < t) :
    ContinuousAt bennettGammaBinetKernelDeriv t := by
  have ht0 : (t : Complex) ≠ 0 := by exact_mod_cast ht.ne'
  have hden : Complex.exp (t : Complex) - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    have hre' : Real.exp t - 1 = 0 := by
      simpa [Complex.exp_ofReal_re] using hre
    nlinarith [Real.add_one_lt_exp ht.ne']
  unfold bennettGammaBinetKernelDeriv
  apply ContinuousAt.sub
  · exact continuousAt_const.div
      (Complex.continuous_ofReal.continuousAt.pow 2) (pow_ne_zero 2 ht0)
  · exact
      ((Complex.continuous_exp.comp Complex.continuous_ofReal).continuousAt.div
        (((Complex.continuous_exp.comp Complex.continuous_ofReal).sub
          continuous_const).continuousAt.pow 2) (pow_ne_zero 2 hden))

/--
Finite-interval integration by parts for the Binet remainder on the Gamma
line.  This exposes the boundary and derivative terms that produce the
height-sensitive oscillatory estimate.
-/
theorem intervalIntegral_bennettGammaBinetKernel_mul_exp_onGammaLine
    {a b T : Real} (ha : 0 < a) (hab : a <= b) :
    let E : Real -> Complex := fun t =>
      Complex.exp (-(t : Complex) * bellottiWongGammaLine T)
    let V : Real -> Complex := fun t => E t / (-bellottiWongGammaLine T)
    ∫ t in a..b, bennettGammaBinetKernel t * E t =
      bennettGammaBinetKernel b * V b - bennettGammaBinetKernel a * V a -
        ∫ t in a..b, bennettGammaBinetKernelDeriv t * V t := by
  dsimp
  let E : Real -> Complex := fun t =>
    Complex.exp (-(t : Complex) * bellottiWongGammaLine T)
  let V : Real -> Complex := fun t => E t / (-bellottiWongGammaLine T)
  have hline : bellottiWongGammaLine T ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    rw [bellottiWongGammaLine_re] at hre
    norm_num at hre
  have hkernel : ContinuousOn bennettGammaBinetKernel (Set.uIcc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact (hasDerivAt_bennettGammaBinetKernel (lt_of_lt_of_le ha hx.1)).continuousAt
  have hkernelDeriv : IntervalIntegrable bennettGammaBinetKernelDeriv volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact continuousAt_bennettGammaBinetKernelDeriv (lt_of_lt_of_le ha hx.1)
  have hEderiv (x : Real) : HasDerivAt E (E x * (-bellottiWongGammaLine T)) x := by
    unfold E
    have hinter : HasDerivAt
        (fun y : Real => -(y : Complex) * bellottiWongGammaLine T)
        (-bellottiWongGammaLine T) x := by
      have hcomplex : HasDerivAt
          (fun z : Complex => -z * bellottiWongGammaLine T)
          (-bellottiWongGammaLine T) (x : Complex) := by
        convert ((hasDerivAt_id (x : Complex)).neg.mul_const
          (bellottiWongGammaLine T)) using 1
        all_goals first | rfl | ring
      exact hcomplex.comp_ofReal
    simpa using hinter.cexp
  have hVderiv (x : Real) : HasDerivAt V (E x) x := by
    unfold V
    have hdiv := (hEderiv x).div_const (-bellottiWongGammaLine T)
    convert hdiv using 1
    all_goals first | rfl | (field_simp [hline] <;> ring)
  have hV : ContinuousOn V (Set.uIcc a b) :=
    continuousOn_of_forall_continuousAt fun x _ => (hVderiv x).continuousAt
  have hE : IntervalIntegrable E volume a b :=
    (continuousOn_of_forall_continuousAt fun x _ => (hEderiv x).continuousAt).intervalIntegrable
  simpa only [E, V] using
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := bennettGammaBinetKernel) (v := V)
      (u' := bennettGammaBinetKernelDeriv) (v' := E)
      (fun x _ => hasDerivAt_bennettGammaBinetKernel
        (lt_of_lt_of_le ha (by
          rw [Set.uIcc_of_le hab] at ‹x ∈ Set.uIcc a b›
          exact ‹x ∈ Set.Icc a b›.1)))
      (fun x _ => hVderiv x) hkernelDeriv hE

/-- The Binet kernel is real on the positive integration axis. -/
theorem bennettGammaBinetKernel_eq_ofReal (t : Real) :
    bennettGammaBinetKernel t =
      ((1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1) : Real) := by
  simp [bennettGammaBinetKernel, ← Complex.ofReal_exp]

/-- A coarse uniform tail bound for Binet's real kernel. -/
theorem norm_bennettGammaBinetKernel_le_five_halves {t : Real} (ht : 1 <= t) :
    ‖bennettGammaBinetKernel t‖ <= 5 / 2 := by
  rw [bennettGammaBinetKernel_eq_ofReal, Complex.norm_real]
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hinv_nonneg : 0 <= 1 / t := by positivity
  have hinv_le : 1 / t <= 1 := by
    rw [div_le_iff₀ ht_pos]
    linarith
  have hexp : 2 < Real.exp t := by
    calc
      (2 : Real) < Real.exp 1 := Real.exp_one_gt_two
      _ <= Real.exp t := Real.exp_le_exp.mpr ht
  have hden_pos : 0 < Real.exp t - 1 := by linarith
  have hden_ge : 1 <= Real.exp t - 1 := by linarith
  have htail_nonneg : 0 <= 1 / (Real.exp t - 1) := by positivity
  have htail_le : 1 / (Real.exp t - 1) <= 1 := by
    rw [div_le_iff₀ hden_pos]
    linarith
  calc
    |(1 / 2 : Real) - 1 / t + 1 / (Real.exp t - 1)| <=
        |(1 / 2 : Real) - 1 / t| + |1 / (Real.exp t - 1)| :=
      abs_add_le _ _
    _ <= |(1 / 2 : Real)| + |-(1 / t)| + |1 / (Real.exp t - 1)| := by
      gcongr
      simpa [abs_neg] using abs_sub (1 / 2 : Real) (1 / t)
    _ <= 5 / 2 := by
      rw [abs_of_nonneg (by norm_num : (0 : Real) <= 1 / 2),
        abs_neg, abs_of_nonneg hinv_nonneg, abs_of_nonneg htail_nonneg]
      nlinarith

/-- The Binet-kernel cancellation gives a uniform compact bound near zero. -/
theorem norm_bennettGammaBinetKernel_le_one_half {t : Real}
    (ht_pos : 0 < t) (ht_one : t <= 1) :
    ‖bennettGammaBinetKernel t‖ <= 1 / 2 := by
  rw [bennettGammaBinetKernel_eq_ofReal, Complex.norm_real]
  have ht_abs : |t| <= 1 := by
    rw [abs_of_pos ht_pos]
    exact ht_one
  have hexp_error := Real.abs_exp_sub_one_sub_id_le ht_abs
  have hden_lower : t <= Real.exp t - 1 := by
    nlinarith [Real.add_one_le_exp t]
  have hden_pos : 0 < Real.exp t - 1 := lt_of_lt_of_le ht_pos hden_lower
  have hden_upper : Real.exp t - 1 <= t + t ^ 2 := by
    have := (abs_le.mp hexp_error).2
    nlinarith
  have hrecip_upper : 1 / (Real.exp t - 1) <= 1 / t :=
    one_div_le_one_div_of_le ht_pos hden_lower
  have hcompact_pos : 0 < t + t ^ 2 := by positivity
  have hrecip_lower : 1 / (t + t ^ 2) <= 1 / (Real.exp t - 1) :=
    one_div_le_one_div_of_le hden_pos hden_upper
  apply abs_le.mpr
  constructor
  · have hbaseline :
        -(1 / 2 : Real) <= 1 / 2 - 1 / t + 1 / (t + t ^ 2) := by
      have hone_pos : 0 < 1 + t := by linarith
      field_simp [ht_pos.ne', hone_pos.ne']
      nlinarith [sq_nonneg t]
    linarith
  · linarith

/-- The compact cancellation and elementary tail bound give one global kernel bound. -/
theorem norm_bennettGammaBinetKernel_le_five_halves_of_pos {t : Real}
    (ht_pos : 0 < t) : ‖bennettGammaBinetKernel t‖ <= 5 / 2 := by
  by_cases ht_one : t <= 1
  · exact (norm_bennettGammaBinetKernel_le_one_half ht_pos ht_one).trans (by norm_num)
  · exact norm_bennettGammaBinetKernel_le_five_halves (le_of_lt (lt_of_not_ge ht_one))

/-- Binet-kernel cancellation gives the sharp elementary bound on the positive axis. -/
theorem norm_bennettGammaBinetKernel_le_one_half_of_pos {t : Real}
    (ht_pos : 0 < t) : ‖bennettGammaBinetKernel t‖ <= 1 / 2 := by
  by_cases ht_one : t <= 1
  · exact norm_bennettGammaBinetKernel_le_one_half ht_pos ht_one
  · rw [bennettGammaBinetKernel_eq_ofReal, Complex.norm_real]
    have ht_ge_one : 1 <= t := le_of_lt (lt_of_not_ge ht_one)
    have hinv_nonneg : 0 <= 1 / t := by positivity
    have hinv_le_one : 1 / t <= 1 := by
      rw [div_le_iff₀ ht_pos]
      linarith
    have hden_lower : t <= Real.exp t - 1 := by
      nlinarith [Real.add_one_le_exp t]
    have hden_pos : 0 < Real.exp t - 1 := lt_of_lt_of_le ht_pos hden_lower
    have htail_nonneg : 0 <= 1 / (Real.exp t - 1) := by positivity
    have htail_le : 1 / (Real.exp t - 1) <= 1 / t :=
      one_div_le_one_div_of_le ht_pos hden_lower
    apply abs_le.mpr
    constructor <;> linarith

/--
Binet's complex digamma formula on the right half-plane.  This is the precise
literature-shaped analytic theorem needed to replace the current shifted
Stirling source input; it is deliberately a visible target, not an envelope
assumption.
-/
def BennettGammaBinetDigammaFormula : Prop :=
  forall z : Complex, 0 < z.re ->
    Complex.digamma z = Complex.log z - 1 / (2 * z) -
      ∫ t : Real in Set.Ioi 0,
        bennettGammaBinetKernel t * Complex.exp (-(t : Complex) * z)

/-- Binet's right-half-plane formula specializes directly to the Gamma line. -/
theorem BennettGammaBinetDigammaFormula.onGammaLine
    (hBinet : BennettGammaBinetDigammaFormula) (T : Real) :
    Complex.digamma (bellottiWongGammaLine T) =
      Complex.log (bellottiWongGammaLine T) -
        1 / (2 * bellottiWongGammaLine T) -
          ∫ t : Real in Set.Ioi 0,
            bennettGammaBinetKernel t *
              Complex.exp (-(t : Complex) * bellottiWongGammaLine T) := by
  apply hBinet
  rw [bellottiWongGammaLine_re]
  norm_num

/-- The Binet Laplace factor has exact real exponential decay on the Gamma line. -/
theorem norm_bennettGammaBinetLaplaceFactor_onGammaLine (t T : Real) :
    ‖Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ =
      Real.exp (-(t / 4)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [bellottiWongGammaLine]
  ring

/-- The Binet integrand on the Gamma line separates into kernel size and decay. -/
theorem norm_bennettGammaBinetIntegrand_onGammaLine (t T : Real) :
    ‖bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ =
      ‖bennettGammaBinetKernel t‖ * Real.exp (-(t / 4)) := by
  rw [norm_mul, norm_bennettGammaBinetLaplaceFactor_onGammaLine]

/-- The Binet integrand has a uniform exponentially decaying majorant. -/
theorem norm_bennettGammaBinetIntegrand_onGammaLine_le (t T : Real)
    (ht_pos : 0 < t) :
    ‖bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ <=
      (5 / 2 : Real) * Real.exp (-(t / 4)) := by
  rw [norm_bennettGammaBinetIntegrand_onGammaLine]
  exact mul_le_mul_of_nonneg_right
    (norm_bennettGammaBinetKernel_le_five_halves_of_pos ht_pos) (Real.exp_pos _).le

/-- The sharp elementary kernel estimate gives a smaller exponential majorant. -/
theorem norm_bennettGammaBinetIntegrand_onGammaLine_le_one_half (t T : Real)
    (ht_pos : 0 < t) :
    ‖bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ <=
      (1 / 2 : Real) * Real.exp (-(t / 4)) := by
  rw [norm_bennettGammaBinetIntegrand_onGammaLine]
  exact mul_le_mul_of_nonneg_right
    (norm_bennettGammaBinetKernel_le_one_half_of_pos ht_pos) (Real.exp_pos _).le

/-- The Binet kernel is continuous away from the origin. -/
theorem continuousOn_bennettGammaBinetKernel :
    ContinuousOn bennettGammaBinetKernel (Set.Ioi 0) := by
  intro t ht
  exact (hasDerivAt_bennettGammaBinetKernel ht).continuousAt.continuousWithinAt

/-- The Binet integrand is measurable on its positive integration axis. -/
theorem aestronglyMeasurable_bennettGammaBinetIntegrand_onGammaLine (T : Real) :
    AEStronglyMeasurable
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T))
      (volume.restrict (Set.Ioi 0)) := by
  have hcont : ContinuousOn
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T))
      (Set.Ioi 0) := by
    apply continuousOn_bennettGammaBinetKernel.mul
    fun_prop
  exact hcont.aestronglyMeasurable measurableSet_Ioi

/-- The Binet integrand has an integrable exponential majorant. -/
theorem integrableOn_bennettGammaBinetIntegrandMajorant :
    IntegrableOn (fun t : Real => (5 / 2 : Real) * Real.exp (-(t / 4)))
      (Set.Ioi 0) := by
  change Integrable (fun t : Real => (5 / 2 : Real) * Real.exp (-(t / 4)))
    (volume.restrict (Set.Ioi 0))
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (integrableOn_exp_mul_Ioi (a := -(1 / 4 : Real)) (by norm_num) 0).const_mul (5 / 2 : Real)

/-- The sharp Binet majorant is integrable on the whole positive axis. -/
theorem integrableOn_bennettGammaBinetIntegrandSharpMajorant :
    IntegrableOn (fun t : Real => (1 / 2 : Real) * Real.exp (-(t / 4)))
      (Set.Ioi 0) := by
  change Integrable (fun t : Real => (1 / 2 : Real) * Real.exp (-(t / 4)))
    (volume.restrict (Set.Ioi 0))
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (integrableOn_exp_mul_Ioi (a := -(1 / 4 : Real)) (by norm_num) 0).const_mul (1 / 2 : Real)

/-- The Binet remainder integral on the Gamma line is absolutely convergent. -/
theorem integrableOn_bennettGammaBinetIntegrand_onGammaLine (T : Real) :
    IntegrableOn
      (fun t : Real => bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T))
      (Set.Ioi 0) := by
  refine Integrable.mono' integrableOn_bennettGammaBinetIntegrandMajorant
    (aestronglyMeasurable_bennettGammaBinetIntegrand_onGammaLine T) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact norm_bennettGammaBinetIntegrand_onGammaLine_le t T ht

/-- A first explicit absolute bound for the Binet remainder integral. -/
theorem norm_integral_bennettGammaBinetIntegrand_onGammaLine_le_ten (T : Real) :
    ‖∫ t : Real in Set.Ioi 0,
      bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ <= 10 := by
  calc
    ‖∫ t : Real in Set.Ioi 0,
        bennettGammaBinetKernel t *
          Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ <=
        ∫ t : Real in Set.Ioi 0, (5 / 2 : Real) * Real.exp (-(t / 4)) := by
      apply norm_integral_le_of_norm_le integrableOn_bennettGammaBinetIntegrandMajorant
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact norm_bennettGammaBinetIntegrand_onGammaLine_le t T ht
    _ = 10 := by
      rw [integral_const_mul]
      have hexp : (fun t : Real => Real.exp (-(t / 4))) =
          fun t : Real => Real.exp (-(1 / 4 : Real) * t) := by
        funext t
        congr 1
        ring
      rw [hexp, integral_exp_mul_Ioi (a := -(1 / 4 : Real)) (by norm_num) 0]
      norm_num

/-- The sharp kernel bound controls the full Binet remainder integral by `2`. -/
theorem norm_integral_bennettGammaBinetIntegrand_onGammaLine_le_two (T : Real) :
    ‖∫ t : Real in Set.Ioi 0,
      bennettGammaBinetKernel t *
        Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ <= 2 := by
  calc
    ‖∫ t : Real in Set.Ioi 0,
        bennettGammaBinetKernel t *
          Complex.exp (-(t : Complex) * bellottiWongGammaLine T)‖ <=
        ∫ t : Real in Set.Ioi 0, (1 / 2 : Real) * Real.exp (-(t / 4)) := by
      apply norm_integral_le_of_norm_le integrableOn_bennettGammaBinetIntegrandSharpMajorant
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact norm_bennettGammaBinetIntegrand_onGammaLine_le_one_half t T ht
    _ = 2 := by
      rw [integral_const_mul]
      have hexp : (fun t : Real => Real.exp (-(t / 4))) =
          fun t : Real => Real.exp (-(1 / 4 : Real) * t) := by
        funext t
        congr 1
        ring
      rw [hexp, integral_exp_mul_Ioi (a := -(1 / 4 : Real)) (by norm_num) 0]
      norm_num

/-- Binet's formula turns the digamma error on the Gamma line into a bounded remainder. -/
theorem norm_digamma_sub_log_sub_inv_onGammaLine_le_two
    (hBinet : BennettGammaBinetDigammaFormula) (T : Real) :
    ‖Complex.digamma (bellottiWongGammaLine T) -
        (Complex.log (bellottiWongGammaLine T) -
          1 / (2 * bellottiWongGammaLine T))‖ <= 2 := by
  rw [hBinet.onGammaLine T]
  have hrewrite :
      (Complex.log (bellottiWongGammaLine T) -
          1 / (2 * bellottiWongGammaLine T) -
          ∫ t : Real in Set.Ioi 0,
            bennettGammaBinetKernel t *
              Complex.exp (-(t : Complex) * bellottiWongGammaLine T)) -
        (Complex.log (bellottiWongGammaLine T) -
          1 / (2 * bellottiWongGammaLine T)) =
        -(∫ t : Real in Set.Ioi 0,
          bennettGammaBinetKernel t *
            Complex.exp (-(t : Complex) * bellottiWongGammaLine T)) := by
    ring
  rw [hrewrite, norm_neg]
  exact norm_integral_bennettGammaBinetIntegrand_onGammaLine_le_two T

/-- Gamma is analytic at every point of the open right half-plane. -/
theorem analyticAt_Gamma_of_re_pos
    {z : Complex} (hz : 0 < z.re) :
    AnalyticAt Complex Complex.Gamma z := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hopen : IsOpen {w : Complex | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact Complex.differentiableAt_Gamma w (fun m hwm => by
    have hre : w.re = -(m : Real) := by
      simpa using congrArg Complex.re hwm
    have hm : 0 <= (m : Real) := Nat.cast_nonneg m
    linarith)

/-- The digamma function is analytic on the open right half-plane. -/
theorem analyticAt_digamma_of_re_pos
    {z : Complex} (hz : 0 < z.re) :
    AnalyticAt Complex Complex.digamma z := by
  have hGamma := analyticAt_Gamma_of_re_pos hz
  have hquot :
      AnalyticAt Complex
        (fun w => deriv Complex.Gamma w / Complex.Gamma w) z :=
    hGamma.deriv.div hGamma (Complex.Gamma_ne_zero_of_re_pos hz)
  rw [Complex.digamma_def]
  change AnalyticAt Complex
    (fun w => deriv Complex.Gamma w / Complex.Gamma w) z
  exact hquot

/-- The derivative of the continuous Gamma phase along the critical vertical line. -/
def bellottiWongGammaPhaseIntegrand (T : Real) : Real :=
  (Complex.digamma (bellottiWongGammaLine T)).re / 2

/-- The Gamma-phase derivative is continuous at every real height. -/
theorem continuous_bellottiWongGammaPhaseIntegrand :
    Continuous bellottiWongGammaPhaseIntegrand := by
  rw [continuous_iff_continuousAt]
  intro T
  have hline : ContinuousAt bellottiWongGammaLine T := by
    unfold bellottiWongGammaLine
    fun_prop
  have hpsi :
      ContinuousAt (fun t : Real =>
        Complex.digamma (bellottiWongGammaLine t)) T :=
    (analyticAt_digamma_of_re_pos (by
      rw [bellottiWongGammaLine_re]
      norm_num)).continuousAt.comp hline
  exact (Complex.continuous_re.continuousAt.comp hpsi).div_const 2

/--
The branch-normalized continuous value of
`Im log Gamma(1/4 + iT/2)`, fixed to be zero at height zero.
-/
def bellottiWongGammaPhase (T : Real) : Real :=
  ∫ t in 0..T, bellottiWongGammaPhaseIntegrand t

@[simp]
theorem bellottiWongGammaPhase_zero :
    bellottiWongGammaPhase 0 = 0 := by
  simp [bellottiWongGammaPhase]

/-- The continuous Gamma phase has the expected digamma derivative. -/
theorem hasDerivAt_bellottiWongGammaPhase (T : Real) :
    HasDerivAt bellottiWongGammaPhase
      (bellottiWongGammaPhaseIntegrand T) T := by
  unfold bellottiWongGammaPhase
  exact
    (continuous_bellottiWongGammaPhaseIntegrand.integral_hasStrictDerivAt 0 T).hasDerivAt

/--
Bellotti-Wong's `g(T)` remainder in a branch-independent continuous-phase
normalization.
-/
def bellottiWongGammaRemainder (T : Real) : Real :=
  (2 / Real.pi) * bellottiWongGammaPhase T -
    (T / Real.pi) * Real.log (T / (2 * Real.exp 1)) + 1 / 4

/--
The concrete remainder has the expected derivative at positive height.  This
is the normalization bridge needed to attack the published remainder bound by
quantitative digamma/Stirling estimates.
-/
theorem hasDerivAt_bellottiWongGammaRemainder
    {T : Real} (hT : 0 < T) :
    HasDerivAt bellottiWongGammaRemainder
      ((2 / Real.pi) * bellottiWongGammaPhaseIntegrand T -
        ((1 / Real.pi) * Real.log (T / (2 * Real.exp 1)) +
          (T / Real.pi) * (1 / T))) T := by
  have hden : (2 * Real.exp 1 : Real) ≠ 0 := by positivity
  have harg : T / (2 * Real.exp 1) ≠ 0 := div_ne_zero hT.ne' hden
  have hlog0 :=
    ((hasDerivAt_id T).div_const (2 * Real.exp 1)).log harg
  have hlog :
      HasDerivAt (fun t : Real => Real.log (t / (2 * Real.exp 1)))
        (1 / T) T := by
    have heq :
        1 / (2 * Real.exp 1) / (T / (2 * Real.exp 1)) = 1 / T := by
      field_simp [hT.ne', hden]
    simpa only [id_eq, heq] using hlog0
  have hmain := ((hasDerivAt_id T).div_const Real.pi).mul hlog
  have hphase :=
    (hasDerivAt_bellottiWongGammaPhase T).const_mul (2 / Real.pi)
  have hconst : HasDerivAt (fun _ : Real => (1 / 4 : Real)) 0 T :=
    hasDerivAt_const T (1 / 4 : Real)
  have hraw := (hphase.sub hmain).add hconst
  simpa only [id_eq, add_zero] using hraw.congr_of_eventuallyEq
    (show bellottiWongGammaRemainder =ᶠ[nhds T] _ by
      filter_upwards with x
      rfl)

/--
The explicit elementary approximation in Bennett-Martin-O'Bryant-Rechnitzer,
Proposition 3.2, specialized to the even (`a = 0`) Gamma factor used for zeta.
-/
def bennettGammaApproximation (T : Real) : Real :=
  (16 + 12 * Real.pi - 60 * T * Real.sqrt (81 + 4 * T ^ 2)) /
      (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) +
    T / (2 * Real.pi) * Real.log (1 + 81 / (4 * T ^ 2)) +
    2 / Real.pi *
      (Real.arctan (1 / (2 * T)) + Real.arctan (5 / (2 * T)) -
        (7 / 4 : Real) * Real.arctan (9 / (2 * T)))

/-- The arctangent combination in Bennett's elementary approximation. -/
def bennettGammaArctanCombination (u : Real) : Real :=
  Real.arctan (u / 2) + Real.arctan (5 * u / 2) -
    (7 / 4 : Real) * Real.arctan (9 * u / 2)

/-- The lower alternating-polynomial bound for Bennett's arctangent combination. -/
theorem bennettGammaArctanCombination_lower {u : Real} (hu : 0 <= u) :
    -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
        (413343 / 640 : Real) * u ^ 5 <=
      bennettGammaArctanCombination u := by
  have h1 := arctan_cubic_lower (show 0 <= u / 2 by positivity)
  have h5 := arctan_cubic_lower (show 0 <= 5 * u / 2 by positivity)
  have h9 := arctan_quintic_upper (show 0 <= 9 * u / 2 by positivity)
  unfold bennettGammaArctanCombination
  calc
    -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
        (413343 / 640 : Real) * u ^ 5 =
      (u / 2 - (u / 2) ^ 3 / 3) +
        (5 * u / 2 - (5 * u / 2) ^ 3 / 3) -
          (7 / 4 : Real) *
            (9 * u / 2 - (9 * u / 2) ^ 3 / 3 + (9 * u / 2) ^ 5 / 5) := by
              ring
    _ <= Real.arctan (u / 2) + Real.arctan (5 * u / 2) -
        (7 / 4 : Real) * Real.arctan (9 * u / 2) := by
      gcongr

/-- The upper alternating-polynomial bound for Bennett's arctangent combination. -/
theorem bennettGammaArctanCombination_upper {u : Real} (hu : 0 <= u) :
    bennettGammaArctanCombination u <=
      -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 +
        (1563 / 80 : Real) * u ^ 5 := by
  have h1 := arctan_quintic_upper (show 0 <= u / 2 by positivity)
  have h5 := arctan_quintic_upper (show 0 <= 5 * u / 2 by positivity)
  have h9 := arctan_cubic_lower (show 0 <= 9 * u / 2 by positivity)
  unfold bennettGammaArctanCombination
  calc
    Real.arctan (u / 2) + Real.arctan (5 * u / 2) -
        (7 / 4 : Real) * Real.arctan (9 * u / 2) <=
      (u / 2 - (u / 2) ^ 3 / 3 + (u / 2) ^ 5 / 5) +
        (5 * u / 2 - (5 * u / 2) ^ 3 / 3 + (5 * u / 2) ^ 5 / 5) -
          (7 / 4 : Real) * (9 * u / 2 - (9 * u / 2) ^ 3 / 3) := by
      gcongr
    _ = -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 +
        (1563 / 80 : Real) * u ^ 5 := by ring

/-- A ninth-order lower enclosure for Bennett's arctangent combination. -/
theorem bennettGammaArctanCombination_nonic_lower
    {u : Real} (hu : 0 <= u) :
    -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
        (400839 / 640 : Real) * u ^ 5 +
          (33168279 / 3584 : Real) * u ^ 7 -
            (301327047 / 2048 : Real) * u ^ 9 <=
      bennettGammaArctanCombination u := by
  have h1 := arctan_septic_lower (show 0 <= u / 2 by positivity)
  have h5 := arctan_septic_lower (show 0 <= 5 * u / 2 by positivity)
  have h9 := arctan_nonic_upper (show 0 <= 9 * u / 2 by positivity)
  unfold bennettGammaArctanCombination
  calc
    -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
        (400839 / 640 : Real) * u ^ 5 +
          (33168279 / 3584 : Real) * u ^ 7 -
            (301327047 / 2048 : Real) * u ^ 9 =
      (u / 2 - (u / 2) ^ 3 / 3 + (u / 2) ^ 5 / 5 - (u / 2) ^ 7 / 7) +
        (5 * u / 2 - (5 * u / 2) ^ 3 / 3 + (5 * u / 2) ^ 5 / 5 -
          (5 * u / 2) ^ 7 / 7) -
            (7 / 4 : Real) *
              (9 * u / 2 - (9 * u / 2) ^ 3 / 3 + (9 * u / 2) ^ 5 / 5 -
                (9 * u / 2) ^ 7 / 7 + (9 * u / 2) ^ 9 / 9) := by ring
    _ <= Real.arctan (u / 2) + Real.arctan (5 * u / 2) -
        (7 / 4 : Real) * Real.arctan (9 * u / 2) := by
      gcongr

/-- A ninth-order upper enclosure for Bennett's arctangent combination. -/
theorem bennettGammaArctanCombination_nonic_upper
    {u : Real} (hu : 0 <= u) :
    bennettGammaArctanCombination u <=
      -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
        (400839 / 640 : Real) * u ^ 5 +
          (33168279 / 3584 : Real) * u ^ 7 +
            (108507 / 256 : Real) * u ^ 9 := by
  have h1 := arctan_nonic_upper (show 0 <= u / 2 by positivity)
  have h5 := arctan_nonic_upper (show 0 <= 5 * u / 2 by positivity)
  have h9 := arctan_septic_lower (show 0 <= 9 * u / 2 by positivity)
  unfold bennettGammaArctanCombination
  calc
    Real.arctan (u / 2) + Real.arctan (5 * u / 2) -
        (7 / 4 : Real) * Real.arctan (9 * u / 2) <=
      (u / 2 - (u / 2) ^ 3 / 3 + (u / 2) ^ 5 / 5 -
        (u / 2) ^ 7 / 7 + (u / 2) ^ 9 / 9) +
          (5 * u / 2 - (5 * u / 2) ^ 3 / 3 + (5 * u / 2) ^ 5 / 5 -
            (5 * u / 2) ^ 7 / 7 + (5 * u / 2) ^ 9 / 9) -
              (7 / 4 : Real) *
                (9 * u / 2 - (9 * u / 2) ^ 3 / 3 +
                  (9 * u / 2) ^ 5 / 5 - (9 * u / 2) ^ 7 / 7) := by
      gcongr
    _ = -(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
        (400839 / 640 : Real) * u ^ 5 +
          (33168279 / 3584 : Real) * u ^ 7 +
            (108507 / 256 : Real) * u ^ 9 := by ring

/-- The logarithm and arctangent terms, separated from the Stirling term. -/
def bennettGammaTranscendentalPart (T : Real) : Real :=
  T / (2 * Real.pi) * Real.log (1 + 81 / (4 * T ^ 2)) +
    2 / Real.pi *
      (Real.arctan (1 / (2 * T)) + Real.arctan (5 / (2 * T)) -
        (7 / 4 : Real) * Real.arctan (9 / (2 * T)))

/-- The shifted-Stirling error accompanying `bennettGammaApproximation`. -/
def bennettGammaApproximationError (T : Real) : Real :=
  ((8 + 6 * Real.pi) / 45) /
    (81 + 4 * T ^ 2) ^ (3 / 2 : Real)

/-- The approximation error is nonnegative at every real height. -/
theorem bennettGammaApproximationError_nonneg (T : Real) :
    0 <= bennettGammaApproximationError T := by
  unfold bennettGammaApproximationError
  positivity

/-- Rewrite the `3/2` power in the Stirling denominator as `x * sqrt x`. -/
theorem bennettGammaDenominator_rpow_three_halves (T : Real) :
    (81 + 4 * T ^ 2) ^ (3 / 2 : Real) =
      (81 + 4 * T ^ 2) * Real.sqrt (81 + 4 * T ^ 2) := by
  have hbase : 0 <= (81 + 4 * T ^ 2 : Real) := by positivity
  rw [Real.rpow_div_two_eq_sqrt 3 hbase]
  calc
    Real.sqrt (81 + 4 * T ^ 2) ^ (3 : Real) =
        Real.sqrt (81 + 4 * T ^ 2) ^ (3 : Nat) :=
      Real.rpow_natCast _ 3
    _ =
        Real.sqrt (81 + 4 * T ^ 2) ^ 2 *
          Real.sqrt (81 + 4 * T ^ 2) := by ring
    _ = (81 + 4 * T ^ 2) * Real.sqrt (81 + 4 * T ^ 2) := by
      rw [Real.sq_sqrt hbase]

/--
The square root in the first term of Bennett's approximation cancels exactly
against the `3/2`-power denominator.  This exposes the term as an elementary
rational contribution plus a positive cubic-order remainder.
-/
theorem bennettGammaStirlingTerm_eq (T : Real) :
    (16 + 12 * Real.pi - 60 * T * Real.sqrt (81 + 4 * T ^ 2)) /
        (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) =
      (16 + 12 * Real.pi) /
          (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) -
        4 * T / (3 * Real.pi * (81 + 4 * T ^ 2)) := by
  have hB : 0 < (81 + 4 * T ^ 2 : Real) := by positivity
  have hsqrt : 0 < Real.sqrt (81 + 4 * T ^ 2) := Real.sqrt_pos.2 hB
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [bennettGammaDenominator_rpow_three_halves]
  field_simp [hpi, hB.ne', hsqrt.ne']
  ring

/--
After the leading cancellation, the logarithm/arctangent contribution has a
fully rational lower bound in the reciprocal height.
-/
theorem bennettGammaTranscendentalPart_lower
    {T : Real} (hT : 0 < T) :
    ((3 / 8 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 -
        (413343 / 320 : Real) * (1 / T) ^ 5) / Real.pi <=
      bennettGammaTranscendentalPart T := by
  let u : Real := 1 / T
  let y : Real := 81 / (4 * T ^ 2)
  have hu : 0 <= u := by dsimp [u]; positivity
  have hy : 0 <= y := by dsimp [y]; positivity
  have hlog := log_one_add_quadratic_lower hy
  have hatan := bennettGammaArctanCombination_lower hu
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    ((3 / 8 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 -
        (413343 / 320 : Real) * (1 / T) ^ 5) / Real.pi =
      T / (2 * Real.pi) * (y - y ^ 2 / 2) +
        2 / Real.pi *
          (-(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
            (413343 / 640 : Real) * u ^ 5) := by
      dsimp [u, y]
      field_simp [hT.ne', hpi]
      ring
    _ <= T / (2 * Real.pi) * Real.log (1 + y) +
        2 / Real.pi * bennettGammaArctanCombination u :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlog (by positivity))
        (mul_le_mul_of_nonneg_left hatan (by positivity))
    _ = bennettGammaTranscendentalPart T := by
      dsimp [u, y]
      unfold bennettGammaTranscendentalPart bennettGammaArctanCombination
      field_simp [hT.ne']

/--
The matching rational upper bound for the logarithm/arctangent contribution.
-/
theorem bennettGammaTranscendentalPart_upper
    {T : Real} (hT : 0 < T) :
    bennettGammaTranscendentalPart T <=
      ((3 / 8 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 +
        ((1563 / 40 : Real) + 531441 / 384) * (1 / T) ^ 5) /
          Real.pi := by
  let u : Real := 1 / T
  let y : Real := 81 / (4 * T ^ 2)
  have hu : 0 <= u := by dsimp [u]; positivity
  have hy : 0 <= y := by dsimp [y]; positivity
  have hlog := log_one_add_cubic_upper hy
  have hatan := bennettGammaArctanCombination_upper hu
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    bennettGammaTranscendentalPart T =
      T / (2 * Real.pi) * Real.log (1 + y) +
        2 / Real.pi * bennettGammaArctanCombination u := by
      dsimp [u, y]
      unfold bennettGammaTranscendentalPart bennettGammaArctanCombination
      field_simp [hT.ne']
    _ <= T / (2 * Real.pi) * (y - y ^ 2 / 2 + y ^ 3 / 3) +
        2 / Real.pi *
          (-(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 +
            (1563 / 80 : Real) * u ^ 5) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlog (by positivity))
        (mul_le_mul_of_nonneg_left hatan (by positivity))
    _ = ((3 / 8 : Real) * (1 / T) -
        (429 / 64 : Real) * (1 / T) ^ 3 +
          ((1563 / 40 : Real) + 531441 / 384) * (1 / T) ^ 5) /
            Real.pi := by
      dsimp [u, y]
      field_simp [hT.ne', hpi]
      ring

/-- The ninth-order reciprocal-height lower bound for the transcendental part. -/
theorem bennettGammaTranscendentalPart_nonic_lower
    {T : Real} (hT : 0 < T) :
    ((3 / 8 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 +
        (84057 / 640 : Real) * (1 / T) ^ 5 -
          (35980815 / 14336 : Real) * (1 / T) ^ 7 -
            (301327047 / 1024 : Real) * (1 / T) ^ 9) / Real.pi <=
      bennettGammaTranscendentalPart T := by
  let u : Real := 1 / T
  let y : Real := 81 / (4 * T ^ 2)
  have hu : 0 <= u := by dsimp [u]; positivity
  have hy : 0 <= y := by dsimp [y]; positivity
  have hlog := log_one_add_quartic_lower hy
  have hatan := bennettGammaArctanCombination_nonic_lower hu
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    ((3 / 8 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 +
        (84057 / 640 : Real) * (1 / T) ^ 5 -
          (35980815 / 14336 : Real) * (1 / T) ^ 7 -
            (301327047 / 1024 : Real) * (1 / T) ^ 9) / Real.pi =
      T / (2 * Real.pi) * (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4) +
        2 / Real.pi *
          (-(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
            (400839 / 640 : Real) * u ^ 5 +
              (33168279 / 3584 : Real) * u ^ 7 -
                (301327047 / 2048 : Real) * u ^ 9) := by
      dsimp [u, y]
      field_simp [hT.ne', hpi]
      ring
    _ <= T / (2 * Real.pi) * Real.log (1 + y) +
        2 / Real.pi * bennettGammaArctanCombination u :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlog (by positivity))
        (mul_le_mul_of_nonneg_left hatan (by positivity))
    _ = bennettGammaTranscendentalPart T := by
      dsimp [u, y]
      unfold bennettGammaTranscendentalPart bennettGammaArctanCombination
      field_simp [hT.ne']

/-- The ninth-order reciprocal-height upper bound for the transcendental part. -/
theorem bennettGammaTranscendentalPart_nonic_upper
    {T : Real} (hT : 0 < T) :
    bennettGammaTranscendentalPart T <=
      ((3 / 8 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 +
        (84057 / 640 : Real) * (1 / T) ^ 5 -
          (35980815 / 14336 : Real) * (1 / T) ^ 7 +
            (3495464961 / 10240 : Real) * (1 / T) ^ 9) /
              Real.pi := by
  let u : Real := 1 / T
  let y : Real := 81 / (4 * T ^ 2)
  have hu : 0 <= u := by dsimp [u]; positivity
  have hy : 0 <= y := by dsimp [y]; positivity
  have hlog := log_one_add_quintic_upper hy
  have hatan := bennettGammaArctanCombination_nonic_upper hu
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    bennettGammaTranscendentalPart T =
      T / (2 * Real.pi) * Real.log (1 + y) +
        2 / Real.pi * bennettGammaArctanCombination u := by
      dsimp [u, y]
      unfold bennettGammaTranscendentalPart bennettGammaArctanCombination
      field_simp [hT.ne']
    _ <= T / (2 * Real.pi) *
        (y - y ^ 2 / 2 + y ^ 3 / 3 - y ^ 4 / 4 + y ^ 5 / 5) +
          2 / Real.pi *
            (-(39 / 8 : Real) * u + (1533 / 32 : Real) * u ^ 3 -
              (400839 / 640 : Real) * u ^ 5 +
                (33168279 / 3584 : Real) * u ^ 7 +
                  (108507 / 256 : Real) * u ^ 9) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hlog (by positivity))
        (mul_le_mul_of_nonneg_left hatan (by positivity))
    _ = ((3 / 8 : Real) * (1 / T) -
        (429 / 64 : Real) * (1 / T) ^ 3 +
          (84057 / 640 : Real) * (1 / T) ^ 5 -
            (35980815 / 14336 : Real) * (1 / T) ^ 7 +
              (3495464961 / 10240 : Real) * (1 / T) ^ 9) /
                Real.pi := by
      dsimp [u, y]
      field_simp [hT.ne', hpi]
      ring

/-- A simple lower bound for the negative rational Stirling contribution. -/
theorem bennettGammaRationalStirlingTerm_lower
    {T : Real} (hT : 0 < T) :
    -(1 / (3 * Real.pi) : Real) * (1 / T) <=
      -4 * T / (3 * Real.pi * (81 + 4 * T ^ 2)) := by
  let y : Real := 81 / (4 * T ^ 2)
  have hy : 0 <= y := by dsimp [y]; positivity
  have hden : 0 < 1 + y := by positivity
  have hrecip : 1 / (1 + y) <= 1 := by
    rw [div_le_iff₀ hden]
    linarith
  have hcoef : -(1 / (3 * Real.pi * T) : Real) <= 0 :=
    neg_nonpos.mpr (by positivity)
  have hmul := mul_le_mul_of_nonpos_left hrecip hcoef
  have heq :
      -4 * T / (3 * Real.pi * (81 + 4 * T ^ 2)) =
        -(1 / (3 * Real.pi * T) : Real) * (1 / (1 + y)) := by
    dsimp [y]
    field_simp [hT.ne', Real.pi_pos.ne']
    ring
  rw [heq]
  convert hmul using 1
  all_goals first | rfl | ring

/--
The first reciprocal correction gives an upper bound for the negative
rational Stirling contribution.
-/
theorem bennettGammaRationalStirlingTerm_upper
    {T : Real} (hT : 0 < T) :
    -4 * T / (3 * Real.pi * (81 + 4 * T ^ 2)) <=
      -(1 / (3 * Real.pi) : Real) * (1 / T) +
        (27 / (4 * Real.pi) : Real) * (1 / T) ^ 3 := by
  let y : Real := 81 / (4 * T ^ 2)
  have hy : 0 <= y := by dsimp [y]; positivity
  have hden : 0 < 1 + y := by positivity
  have hrecip : 1 - y <= 1 / (1 + y) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg y]
  have hcoef : -(1 / (3 * Real.pi * T) : Real) <= 0 :=
    neg_nonpos.mpr (by positivity)
  have hmul := mul_le_mul_of_nonpos_left hrecip hcoef
  have heqLeft :
      -4 * T / (3 * Real.pi * (81 + 4 * T ^ 2)) =
        -(1 / (3 * Real.pi * T) : Real) * (1 / (1 + y)) := by
    dsimp [y]
    field_simp [hT.ne', Real.pi_pos.ne']
    ring
  have heqRight :
      -(1 / (3 * Real.pi * T) : Real) * (1 - y) =
        -(1 / (3 * Real.pi) : Real) * (1 / T) +
          (27 / (4 * Real.pi) : Real) * (1 / T) ^ 3 := by
    dsimp [y]
    field_simp [hT.ne', Real.pi_pos.ne']
    ring
  rw [heqLeft, <- heqRight]
  exact hmul

/-- The positive cubic-order Stirling contribution is genuinely nonnegative. -/
theorem bennettGammaPositiveStirlingTerm_nonneg (T : Real) :
    0 <= (16 + 12 * Real.pi) /
      (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) := by
  positivity

/--
At positive height, the residual positive Stirling contribution is bounded by
the simple cubic majorant used in the large-height certificate.
-/
theorem bennettGammaPositiveStirlingTerm_le
    {T : Real} (hT : 0 < T) :
    (16 + 12 * Real.pi) /
        (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) <=
      1 / (20 * T ^ 3) := by
  let B : Real := 81 + 4 * T ^ 2
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hB_nonneg : 0 <= B := hB_pos.le
  have hB_lower : 4 * T ^ 2 <= B := by dsimp [B]; linarith
  have hsqrt_lower : 2 * T <= Real.sqrt B := by
    apply Real.le_sqrt_of_sq_le
    dsimp [B]
    nlinarith
  have hden_lower : 8 * T ^ 3 <= B ^ (3 / 2 : Real) := by
    rw [show B ^ (3 / 2 : Real) = B * Real.sqrt B by
      dsimp [B]
      exact bennettGammaDenominator_rpow_three_halves T]
    calc
      8 * T ^ 3 = (4 * T ^ 2) * (2 * T) := by ring
      _ <= B * Real.sqrt B :=
        mul_le_mul hB_lower hsqrt_lower (by positivity) hB_nonneg
  have hden_pos : 0 < B ^ (3 / 2 : Real) := Real.rpow_pos_of_pos hB_pos _
  have hsmall_pos : 0 < 45 * Real.pi * (8 * T ^ 3) := by positivity
  have hfullDen :
      45 * Real.pi * (8 * T ^ 3) <=
        45 * Real.pi * B ^ (3 / 2 : Real) :=
    mul_le_mul_of_nonneg_left hden_lower (by positivity)
  have hnum : 16 + 12 * Real.pi <= 18 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  change (16 + 12 * Real.pi) / (45 * Real.pi * B ^ (3 / 2 : Real)) <=
    1 / (20 * T ^ 3)
  calc
    (16 + 12 * Real.pi) / (45 * Real.pi * B ^ (3 / 2 : Real)) <=
        (18 * Real.pi) / (45 * Real.pi * B ^ (3 / 2 : Real)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ <= (18 * Real.pi) / (45 * Real.pi * (8 * T ^ 3)) :=
      div_le_div_of_nonneg_left (by positivity) hsmall_pos hfullDen
    _ = 1 / (20 * T ^ 3) := by
      field_simp [hT.ne', Real.pi_pos.ne']
      ring

/-- A rational reciprocal-height lower bound for the full approximation. -/
theorem bennettGammaApproximation_lower
    {T : Real} (hT : 0 < T) :
    ((1 / 24 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 -
        (413343 / 320 : Real) * (1 / T) ^ 5) / Real.pi <=
      bennettGammaApproximation T := by
  have hpositive := bennettGammaPositiveStirlingTerm_nonneg T
  have hrational := bennettGammaRationalStirlingTerm_lower hT
  have htranscendental := bennettGammaTranscendentalPart_lower hT
  calc
    ((1 / 24 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 -
        (413343 / 320 : Real) * (1 / T) ^ 5) / Real.pi =
      0 + (-(1 / (3 * Real.pi) : Real) * (1 / T)) +
        (((3 / 8 : Real) * (1 / T) -
          (429 / 64 : Real) * (1 / T) ^ 3 -
            (413343 / 320 : Real) * (1 / T) ^ 5) / Real.pi) := by
      field_simp [Real.pi_pos.ne']
      ring
    _ <= (16 + 12 * Real.pi) /
          (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) +
        (-4 * T / (3 * Real.pi * (81 + 4 * T ^ 2))) +
          bennettGammaTranscendentalPart T :=
      add_le_add (add_le_add hpositive hrational) htranscendental
    _ = bennettGammaApproximation T := by
      unfold bennettGammaApproximation bennettGammaTranscendentalPart
      rw [bennettGammaStirlingTerm_eq]
      ring

/-- A rational reciprocal-height upper bound for the full approximation. -/
theorem bennettGammaApproximation_upper
    {T : Real} (hT : 0 < T) :
    bennettGammaApproximation T <=
      (1 / 20 : Real) * (1 / T) ^ 3 +
        ((1 / 24 : Real) * (1 / T) +
          (3 / 64 : Real) * (1 / T) ^ 3 +
            ((1563 / 40 : Real) + 531441 / 384) * (1 / T) ^ 5) /
              Real.pi := by
  have hpositive := bennettGammaPositiveStirlingTerm_le hT
  have hrational := bennettGammaRationalStirlingTerm_upper hT
  have htranscendental := bennettGammaTranscendentalPart_upper hT
  calc
    bennettGammaApproximation T =
      (16 + 12 * Real.pi) /
          (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) +
        (-4 * T / (3 * Real.pi * (81 + 4 * T ^ 2))) +
          bennettGammaTranscendentalPart T := by
      unfold bennettGammaApproximation bennettGammaTranscendentalPart
      rw [bennettGammaStirlingTerm_eq]
      ring
    _ <= 1 / (20 * T ^ 3) +
        (-(1 / (3 * Real.pi) : Real) * (1 / T) +
          (27 / (4 * Real.pi) : Real) * (1 / T) ^ 3) +
            (((3 / 8 : Real) * (1 / T) -
              (429 / 64 : Real) * (1 / T) ^ 3 +
                ((1563 / 40 : Real) + 531441 / 384) * (1 / T) ^ 5) /
                  Real.pi) :=
      add_le_add (add_le_add hpositive hrational) htranscendental
    _ = (1 / 20 : Real) * (1 / T) ^ 3 +
        ((1 / 24 : Real) * (1 / T) +
          (3 / 64 : Real) * (1 / T) ^ 3 +
            ((1563 / 40 : Real) + 531441 / 384) * (1 / T) ^ 5) /
              Real.pi := by
      field_simp [hT.ne', Real.pi_pos.ne']
      ring

/-- The ninth-order reciprocal-height lower bound for the full approximation. -/
theorem bennettGammaApproximation_nonic_lower
    {T : Real} (hT : 0 < T) :
    ((1 / 24 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 +
        (84057 / 640 : Real) * (1 / T) ^ 5 -
          (35980815 / 14336 : Real) * (1 / T) ^ 7 -
            (301327047 / 1024 : Real) * (1 / T) ^ 9) / Real.pi <=
      bennettGammaApproximation T := by
  have hpositive := bennettGammaPositiveStirlingTerm_nonneg T
  have hrational := bennettGammaRationalStirlingTerm_lower hT
  have htranscendental := bennettGammaTranscendentalPart_nonic_lower hT
  calc
    ((1 / 24 : Real) * (1 / T) - (429 / 64 : Real) * (1 / T) ^ 3 +
        (84057 / 640 : Real) * (1 / T) ^ 5 -
          (35980815 / 14336 : Real) * (1 / T) ^ 7 -
            (301327047 / 1024 : Real) * (1 / T) ^ 9) / Real.pi =
      0 + (-(1 / (3 * Real.pi) : Real) * (1 / T)) +
        (((3 / 8 : Real) * (1 / T) -
          (429 / 64 : Real) * (1 / T) ^ 3 +
            (84057 / 640 : Real) * (1 / T) ^ 5 -
              (35980815 / 14336 : Real) * (1 / T) ^ 7 -
                (301327047 / 1024 : Real) * (1 / T) ^ 9) / Real.pi) := by
      field_simp [Real.pi_pos.ne']
      ring
    _ <= (16 + 12 * Real.pi) /
          (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) +
        (-4 * T / (3 * Real.pi * (81 + 4 * T ^ 2))) +
          bennettGammaTranscendentalPart T :=
      add_le_add (add_le_add hpositive hrational) htranscendental
    _ = bennettGammaApproximation T := by
      unfold bennettGammaApproximation bennettGammaTranscendentalPart
      rw [bennettGammaStirlingTerm_eq]
      ring

/-- The ninth-order reciprocal-height upper bound for the full approximation. -/
theorem bennettGammaApproximation_nonic_upper
    {T : Real} (hT : 0 < T) :
    bennettGammaApproximation T <=
      (1 / 20 : Real) * (1 / T) ^ 3 +
        ((1 / 24 : Real) * (1 / T) +
          (3 / 64 : Real) * (1 / T) ^ 3 +
            (84057 / 640 : Real) * (1 / T) ^ 5 -
              (35980815 / 14336 : Real) * (1 / T) ^ 7 +
                (3495464961 / 10240 : Real) * (1 / T) ^ 9) /
                  Real.pi := by
  have hpositive := bennettGammaPositiveStirlingTerm_le hT
  have hrational := bennettGammaRationalStirlingTerm_upper hT
  have htranscendental := bennettGammaTranscendentalPart_nonic_upper hT
  calc
    bennettGammaApproximation T =
      (16 + 12 * Real.pi) /
          (45 * Real.pi * (81 + 4 * T ^ 2) ^ (3 / 2 : Real)) +
        (-4 * T / (3 * Real.pi * (81 + 4 * T ^ 2))) +
          bennettGammaTranscendentalPart T := by
      unfold bennettGammaApproximation bennettGammaTranscendentalPart
      rw [bennettGammaStirlingTerm_eq]
      ring
    _ <= 1 / (20 * T ^ 3) +
        (-(1 / (3 * Real.pi) : Real) * (1 / T) +
          (27 / (4 * Real.pi) : Real) * (1 / T) ^ 3) +
            (((3 / 8 : Real) * (1 / T) -
              (429 / 64 : Real) * (1 / T) ^ 3 +
                (84057 / 640 : Real) * (1 / T) ^ 5 -
                  (35980815 / 14336 : Real) * (1 / T) ^ 7 +
                    (3495464961 / 10240 : Real) * (1 / T) ^ 9) /
                      Real.pi) :=
      add_le_add (add_le_add hpositive hrational) htranscendental
    _ = (1 / 20 : Real) * (1 / T) ^ 3 +
        ((1 / 24 : Real) * (1 / T) +
          (3 / 64 : Real) * (1 / T) ^ 3 +
            (84057 / 640 : Real) * (1 / T) ^ 5 -
              (35980815 / 14336 : Real) * (1 / T) ^ 7 +
                (3495464961 / 10240 : Real) * (1 / T) ^ 9) /
                  Real.pi := by
      field_simp [hT.ne', Real.pi_pos.ne']
      ring

/-- The Bennett approximation is nonnegative from height `20` onward. -/
theorem bennettGammaApproximation_nonneg_of_twenty_le
    {T : Real} (hT20 : 20 <= T) :
    0 <= bennettGammaApproximation T := by
  have hT : 0 < T := by linarith
  let u : Real := 1 / T
  have hu : 0 <= u := by dsimp [u]; positivity
  have hu_le : u <= (1 / 20 : Real) := by
    dsimp [u]
    rw [div_le_iff₀ hT]
    nlinarith
  have hu2 : u ^ 2 <= (1 / 400 : Real) := by
    have h := pow_le_pow_left₀ hu hu_le 2
    norm_num at h ⊢
    exact h
  have hu4 : u ^ 4 <= (1 / 160000 : Real) := by
    have h := pow_le_pow_left₀ (sq_nonneg u) hu2 2
    norm_num [pow_two] at h ⊢
    nlinarith
  have hbracket :
      0 <= (1 / 24 : Real) - (429 / 64 : Real) * u ^ 2 -
        (413343 / 320 : Real) * u ^ 4 := by
    nlinarith
  have hpoly :
      0 <= (1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 -
        (413343 / 320 : Real) * u ^ 5 := by
    calc
      0 <= u * ((1 / 24 : Real) - (429 / 64 : Real) * u ^ 2 -
          (413343 / 320 : Real) * u ^ 4) := mul_nonneg hu hbracket
      _ = (1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 -
          (413343 / 320 : Real) * u ^ 5 := by ring
  have hlower :
      0 <= ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 -
        (413343 / 320 : Real) * u ^ 5) / Real.pi := by positivity
  apply hlower.trans
  simpa [u] using bennettGammaApproximation_lower hT

/--
The published interval estimate is unconditional above height `12`; only the
compact interval `[5/7, 12]` remains for interval certification.
-/
theorem bennettGammaApproximation_abs_le_of_twelve_le
    {T : Real} (hT12 : 12 <= T) :
    |bennettGammaApproximation T| <= 19 / (500 * T) := by
  have hT : 0 < T := by linarith
  let u : Real := 1 / T
  let q : Real :=
    (1 / 24 : Real) + (3 / 64 : Real) * u ^ 2 +
      ((1563 / 40 : Real) + 531441 / 384) * u ^ 4
  let p : Real :=
    (1 / 24 : Real) - (429 / 64 : Real) * u ^ 2 -
      (413343 / 320 : Real) * u ^ 4
  have hu : 0 <= u := by dsimp [u]; positivity
  have hu_le : u <= (1 / 12 : Real) := by
    dsimp [u]
    rw [div_le_iff₀ hT]
    nlinarith
  have hu2 : u ^ 2 <= (1 / 144 : Real) := by
    have h := pow_le_pow_left₀ hu hu_le 2
    norm_num at h ⊢
    exact h
  have hu4 : u ^ 4 <= (1 / 20736 : Real) := by
    have h := pow_le_pow_left₀ (sq_nonneg u) hu2 2
    norm_num [pow_two] at h ⊢
    nlinarith
  have hq_nonneg : 0 <= q := by dsimp [q]; positivity
  have hq_bound :
      q <= (1 / 24 : Real) + (3 / 64 : Real) * (1 / 144) +
        ((1563 / 40 : Real) + 531441 / 384) * (1 / 20736) := by
    dsimp [q]
    nlinarith
  have hq_div : q / Real.pi <= q / 3 :=
    div_le_div_of_nonneg_left hq_nonneg (by norm_num) Real.pi_gt_three.le
  have hq_bound_div :
      q / (3 : Real) <=
        ((1 / 24 : Real) + (3 / 64 : Real) * (1 / 144) +
          ((1563 / 40 : Real) + 531441 / 384) * (1 / 20736)) / 3 :=
    div_le_div_of_nonneg_right hq_bound (by norm_num)
  have hbracket :
      (1 / 20 : Real) * u ^ 2 + q / Real.pi <= 19 / 500 := by
    calc
      (1 / 20 : Real) * u ^ 2 + q / Real.pi <=
          (1 / 20 : Real) * (1 / 144) + q / 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hu2 (by norm_num)) hq_div
      _ <= (1 / 20 : Real) * (1 / 144) +
          ((1 / 24 : Real) + (3 / 64 : Real) * (1 / 144) +
            ((1563 / 40 : Real) + 531441 / 384) *
              (1 / 20736)) / 3 :=
        by
          simpa [add_comm] using
            add_le_add_left hq_bound_div ((1 / 20 : Real) * (1 / 144))
      _ <= 19 / 500 := by norm_num
  have hmajorant :
      (1 / 20 : Real) * u ^ 3 +
          ((1 / 24 : Real) * u + (3 / 64 : Real) * u ^ 3 +
            ((1563 / 40 : Real) + 531441 / 384) * u ^ 5) /
              Real.pi <=
        (19 / 500 : Real) * u := by
    calc
      (1 / 20 : Real) * u ^ 3 +
          ((1 / 24 : Real) * u + (3 / 64 : Real) * u ^ 3 +
            ((1563 / 40 : Real) + 531441 / 384) * u ^ 5) /
              Real.pi =
        u * ((1 / 20 : Real) * u ^ 2 + q / Real.pi) := by
          dsimp [q]
          field_simp [Real.pi_pos.ne']
      _ <= u * (19 / 500 : Real) := mul_le_mul_of_nonneg_left hbracket hu
      _ = (19 / 500 : Real) * u := by ring
  have hupper := (bennettGammaApproximation_upper hT).trans hmajorant
  have hp_lower : -(19 / 500 : Real) * Real.pi <= p := by
    dsimp [p]
    nlinarith [Real.pi_gt_three]
  have hp_div : -(19 / 500 : Real) <= p / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    exact hp_lower
  have hlowerMajorant :
      -(19 / 500 : Real) * u <=
        ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 -
          (413343 / 320 : Real) * u ^ 5) / Real.pi := by
    calc
      -(19 / 500 : Real) * u = u * (-(19 / 500 : Real)) := by ring
      _ <= u * (p / Real.pi) := mul_le_mul_of_nonneg_left hp_div hu
      _ = ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 -
          (413343 / 320 : Real) * u ^ 5) / Real.pi := by
        dsimp [p]
        field_simp [Real.pi_pos.ne']
  apply abs_le.2
  constructor
  · calc
      -(19 / (500 * T)) = -(19 / 500 : Real) * u := by
        dsimp [u]
        field_simp [hT.ne']
      _ <= ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 -
          (413343 / 320 : Real) * u ^ 5) / Real.pi := hlowerMajorant
      _ <= bennettGammaApproximation T := by
        simpa [u] using bennettGammaApproximation_lower hT
  · calc
      bennettGammaApproximation T <= (19 / 500 : Real) * u := hupper
      _ = 19 / (500 * T) := by
        dsimp [u]
        field_simp [hT.ne']

/--
The higher-order alternating bounds push the unconditional approximation
estimate down to height `8`.
-/
theorem bennettGammaApproximation_abs_le_of_eight_le
    {T : Real} (hT8 : 8 <= T) :
    |bennettGammaApproximation T| <= 19 / (500 * T) := by
  have hT : 0 < T := by linarith
  let u : Real := 1 / T
  let p : Real :=
    (1 / 24 : Real) - (429 / 64 : Real) * u ^ 2 +
      (84057 / 640 : Real) * u ^ 4 -
        (35980815 / 14336 : Real) * u ^ 6 -
          (301327047 / 1024 : Real) * u ^ 8
  let q : Real :=
    (1 / 24 : Real) + (3 / 64 : Real) * u ^ 2 +
      (84057 / 640 : Real) * u ^ 4 -
        (35980815 / 14336 : Real) * u ^ 6 +
          (3495464961 / 10240 : Real) * u ^ 8
  have hu : 0 <= u := by dsimp [u]; positivity
  have hu_le : u <= (1 / 8 : Real) := by
    dsimp [u]
    rw [div_le_iff₀ hT]
    nlinarith
  have hu2 : u ^ 2 <= (1 / 64 : Real) := by
    have h := pow_le_pow_left₀ hu hu_le 2
    norm_num at h ⊢
    exact h
  have hu4 : u ^ 4 <= (1 / 4096 : Real) := by
    have h := pow_le_pow_left₀ hu hu_le 4
    norm_num at h ⊢
    exact h
  have hu6 : u ^ 6 <= (1 / 262144 : Real) := by
    have h := pow_le_pow_left₀ hu hu_le 6
    norm_num at h ⊢
    exact h
  have hu8 : u ^ 8 <= (1 / 16777216 : Real) := by
    have h := pow_le_pow_left₀ hu hu_le 8
    norm_num at h ⊢
    exact h
  have hp_lower : -(19 / 500 : Real) * Real.pi <= p := by
    dsimp [p]
    nlinarith [sq_nonneg (u ^ 2), Real.pi_gt_three]
  have hp_div : -(19 / 500 : Real) <= p / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    exact hp_lower
  have hlowerMajorant :
      -(19 / 500 : Real) * u <=
        ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 +
          (84057 / 640 : Real) * u ^ 5 -
            (35980815 / 14336 : Real) * u ^ 7 -
              (301327047 / 1024 : Real) * u ^ 9) / Real.pi := by
    calc
      -(19 / 500 : Real) * u = u * (-(19 / 500 : Real)) := by ring
      _ <= u * (p / Real.pi) := mul_le_mul_of_nonneg_left hp_div hu
      _ = ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 +
          (84057 / 640 : Real) * u ^ 5 -
            (35980815 / 14336 : Real) * u ^ 7 -
              (301327047 / 1024 : Real) * u ^ 9) / Real.pi := by
        dsimp [p]
        field_simp [Real.pi_pos.ne']
  have hq_nonneg : 0 <= q := by
    dsimp [q]
    nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
  have hq_bound :
      q <= (1 / 24 : Real) + (3 / 64 : Real) * (1 / 64) +
        (84057 / 640 : Real) * (1 / 4096) +
          (3495464961 / 10240 : Real) * (1 / 16777216) := by
    dsimp [q]
    nlinarith [sq_nonneg (u ^ 3)]
  have hq_div : q / Real.pi <= q / 3 :=
    div_le_div_of_nonneg_left hq_nonneg (by norm_num) Real.pi_gt_three.le
  have hq_bound_div :
      q / (3 : Real) <=
        ((1 / 24 : Real) + (3 / 64 : Real) * (1 / 64) +
          (84057 / 640 : Real) * (1 / 4096) +
            (3495464961 / 10240 : Real) * (1 / 16777216)) / 3 :=
    div_le_div_of_nonneg_right hq_bound (by norm_num)
  have hbracket :
      (1 / 20 : Real) * u ^ 2 + q / Real.pi <= 19 / 500 := by
    calc
      (1 / 20 : Real) * u ^ 2 + q / Real.pi <=
          (1 / 20 : Real) * (1 / 64) + q / 3 :=
        add_le_add (mul_le_mul_of_nonneg_left hu2 (by norm_num)) hq_div
      _ <= (1 / 20 : Real) * (1 / 64) +
          ((1 / 24 : Real) + (3 / 64 : Real) * (1 / 64) +
            (84057 / 640 : Real) * (1 / 4096) +
              (3495464961 / 10240 : Real) * (1 / 16777216)) / 3 := by
        simpa [add_comm] using
          add_le_add_left hq_bound_div ((1 / 20 : Real) * (1 / 64))
      _ <= 19 / 500 := by norm_num
  have hmajorant :
      (1 / 20 : Real) * u ^ 3 +
          ((1 / 24 : Real) * u + (3 / 64 : Real) * u ^ 3 +
            (84057 / 640 : Real) * u ^ 5 -
              (35980815 / 14336 : Real) * u ^ 7 +
                (3495464961 / 10240 : Real) * u ^ 9) /
                  Real.pi <=
        (19 / 500 : Real) * u := by
    calc
      (1 / 20 : Real) * u ^ 3 +
          ((1 / 24 : Real) * u + (3 / 64 : Real) * u ^ 3 +
            (84057 / 640 : Real) * u ^ 5 -
              (35980815 / 14336 : Real) * u ^ 7 +
                (3495464961 / 10240 : Real) * u ^ 9) /
                  Real.pi =
        u * ((1 / 20 : Real) * u ^ 2 + q / Real.pi) := by
          dsimp [q]
          field_simp [Real.pi_pos.ne']
      _ <= u * (19 / 500 : Real) := mul_le_mul_of_nonneg_left hbracket hu
      _ = (19 / 500 : Real) * u := by ring
  have hupper := (bennettGammaApproximation_nonic_upper hT).trans hmajorant
  apply abs_le.2
  constructor
  · calc
      -(19 / (500 * T)) = -(19 / 500 : Real) * u := by
        dsimp [u]
        field_simp [hT.ne']
      _ <= ((1 / 24 : Real) * u - (429 / 64 : Real) * u ^ 3 +
          (84057 / 640 : Real) * u ^ 5 -
            (35980815 / 14336 : Real) * u ^ 7 -
              (301327047 / 1024 : Real) * u ^ 9) / Real.pi := hlowerMajorant
      _ <= bennettGammaApproximation T := by
        simpa [u] using bennettGammaApproximation_nonic_lower hT
  · calc
      bennettGammaApproximation T <= (19 / 500 : Real) * u := hupper
      _ = 19 / (500 * T) := by
        dsimp [u]
        field_simp [hT.ne']

/--
The shifted-Stirling error is already much smaller than the final `1/(25*T)`
budget.  This bound is unconditional and valid on the whole published domain.
-/
theorem bennettGammaApproximationError_le_inv_fiveHundred_mul
    {T : Real} (hT : (5 : Real) / 7 <= T) :
    bennettGammaApproximationError T <= 1 / (500 * T) := by
  have hT_pos : 0 < T := by norm_num at hT ⊢; linarith
  let B : Real := 81 + 4 * T ^ 2
  have hB_nonneg : 0 <= B := by dsimp [B]; positivity
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hB_linear : 36 * T <= B := by
    dsimp [B]
    nlinarith [sq_nonneg (2 * T - 9)]
  have hsqrt_nine : 9 <= Real.sqrt B := by
    apply Real.le_sqrt_of_sq_le
    dsimp [B]
    nlinarith
  have hden : 324 * T <= B ^ (3 / 2 : Real) := by
    rw [show B ^ (3 / 2 : Real) = B * Real.sqrt B by
      dsimp [B]
      exact bennettGammaDenominator_rpow_three_halves T]
    calc
      324 * T = (36 * T) * 9 := by ring
      _ <= B * Real.sqrt B :=
        mul_le_mul hB_linear hsqrt_nine (by norm_num) hB_nonneg
  have hden_pos : 0 < B ^ (3 / 2 : Real) := Real.rpow_pos_of_pos hB_pos _
  have hsmallDen_pos : 0 < 324 * T := by positivity
  have hcoef : (8 + 6 * Real.pi) / 45 <= (3 / 5 : Real) := by
    nlinarith [Real.pi_lt_d2]
  unfold bennettGammaApproximationError
  change ((8 + 6 * Real.pi) / 45) / B ^ (3 / 2 : Real) <=
    1 / (500 * T)
  calc
    ((8 + 6 * Real.pi) / 45) / B ^ (3 / 2 : Real) <=
        (3 / 5 : Real) / B ^ (3 / 2 : Real) :=
      div_le_div_of_nonneg_right hcoef hden_pos.le
    _ <= (3 / 5 : Real) / (324 * T) :=
      div_le_div_of_nonneg_left (by norm_num) hsmallDen_pos hden
    _ <= 1 / (500 * T) := by
      field_simp [hT_pos.ne']
      norm_num

/--
The shifted complex-Stirling estimate used in Bennett et al. Proposition 3.2,
stated for the project's concrete continuous Gamma remainder.
-/
def BennettGammaStirlingApproximation : Prop :=
  forall T : Real,
    (5 : Real) / 7 <= T ->
      |bellottiWongGammaRemainder T - bennettGammaApproximation T| <=
        bennettGammaApproximationError T

/--
The faithful Bennett envelope: the elementary approximation and its explicit
Stirling error share the final `1/(25*T)` budget.
-/
def BennettGammaCombinedEstimate : Prop :=
  forall T : Real,
    (5 : Real) / 7 <= T ->
      bennettGammaApproximationError T + |bennettGammaApproximation T| <=
        1 / (25 * T)

/--
The genuinely finite interval-certificate target left after the analytic
large-height estimate.
-/
def BennettGammaCompactCombinedEstimate : Prop :=
  forall T : Real,
    (5 : Real) / 7 <= T ->
      T <= 8 ->
        bennettGammaApproximationError T + |bennettGammaApproximation T| <=
          1 / (25 * T)

/-- The compact certificate and the analytic large-height proof cover the domain. -/
theorem bennettGammaCombinedEstimate_of_compact
    (hCompact : BennettGammaCompactCombinedEstimate) :
    BennettGammaCombinedEstimate := by
  intro T hT
  by_cases hTupper : T <= 8
  · exact hCompact T hT hTupper
  · have hT8 : (8 : Real) <= T := (lt_of_not_ge hTupper).le
    have hT_pos : 0 < T := by linarith
    calc
      bennettGammaApproximationError T + |bennettGammaApproximation T| <=
          1 / (500 * T) + 19 / (500 * T) :=
        add_le_add (bennettGammaApproximationError_le_inv_fiveHundred_mul hT)
          (bennettGammaApproximation_abs_le_of_eight_le hT8)
      _ = 1 / (25 * T) := by
        field_simp [hT_pos.ne']
        ring

/-- The two published proof ingredients give the concrete Gamma remainder bound. -/
theorem bellottiWongGammaRemainder_abs_le
    (hStirling : BennettGammaStirlingApproximation)
    (hCombined : BennettGammaCombinedEstimate)
    {T : Real} (hT : (5 : Real) / 7 <= T) :
    |bellottiWongGammaRemainder T| <= 1 / (25 * T) := by
  calc
    |bellottiWongGammaRemainder T| =
        |(bellottiWongGammaRemainder T - bennettGammaApproximation T) +
          bennettGammaApproximation T| := by rw [sub_add_cancel]
    _ <= |bellottiWongGammaRemainder T - bennettGammaApproximation T| +
        |bennettGammaApproximation T| := abs_add_le _ _
    _ <= bennettGammaApproximationError T +
        |bennettGammaApproximation T| :=
      add_le_add (hStirling T hT) le_rfl
    _ <= 1 / (25 * T) := hCombined T hT

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
