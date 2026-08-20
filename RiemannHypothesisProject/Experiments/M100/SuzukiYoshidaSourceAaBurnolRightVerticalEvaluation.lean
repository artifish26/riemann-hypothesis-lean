import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaBurnolVerticalLimit
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVerticalEvaluation
import RiemannHypothesisProject.WeilPositivity.BurnolFormulaIdentification

/-!
# M100-DF6F evaluation of the Burnol xi right vertical

This module evaluates the actual compact-support Burnol right vertical in the
project's prime, pole, and Gamma normalization.  The first step below supplies
the non-Gaussian Archimedean bound uniformly across the contour-shift strip.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set Filter MeasureTheory Topology
open SchwartzLineTestFunction
open ComplexCompactExhaustion
open scoped ComplexConjugate FourierTransform

private theorem norm_log_quarter_fiveEighths_strip_le
    (a t : Real) (haLower : 1 / 4 ≤ a) (haUpper : a ≤ 5 / 8) :
    ‖Complex.log ((a : Complex) + (t / 2 : Real) * Complex.I)‖ ≤
      |t| + (|Real.log (1 / 4)| + Real.pi + 1) := by
  let z : Complex := (a : Complex) + (t / 2 : Real) * Complex.I
  have hzre : z.re = a := by simp [z]
  have haPos : 0 < a := (by norm_num : (0 : Real) < 1 / 4).trans_le haLower
  have hnormLower : (1 / 4 : Real) ≤ ‖z‖ := by
    calc
      (1 / 4 : Real) ≤ |z.re| := by
        rw [hzre, abs_of_pos haPos]
        exact haLower
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hnormPos : 0 < ‖z‖ :=
    (by norm_num : (0 : Real) < 1 / 4).trans_le hnormLower
  have hnormUpper : ‖z‖ ≤ 1 + |t| := by
    calc
      ‖(a : Complex) + (t / 2 : Real) * Complex.I‖ ≤
          ‖(a : Complex)‖ + ‖((t / 2 : Real) : Complex) * Complex.I‖ :=
        norm_add_le _ _
      _ = a + |t| / 2 := by
        rw [norm_mul]
        simp [abs_of_pos haPos]
      _ ≤ 1 + |t| := by nlinarith [abs_nonneg t]
  have hlogLower : Real.log (1 / 4) ≤ Real.log ‖z‖ :=
    Real.log_le_log (by norm_num) hnormLower
  have hlogUpper : Real.log ‖z‖ ≤ |t| := by
    have hlog := Real.log_le_sub_one_of_pos hnormPos
    linarith
  have habsLog : |Real.log ‖z‖| ≤ |Real.log (1 / 4)| + |t| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (1 / 4)), abs_nonneg t]
    · linarith [abs_nonneg (Real.log (1 / 4))]
  have harg := Complex.abs_arg_le_pi z
  unfold Complex.log
  calc
    ‖((Real.log ‖z‖ : Real) : Complex) + (z.arg : Complex) * Complex.I‖ ≤
        ‖((Real.log ‖z‖ : Real) : Complex)‖ +
          ‖(z.arg : Complex) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by rw [norm_mul]; simp
    _ ≤ |t| + (|Real.log (1 / 4)| + Real.pi + 1) := by linarith

private theorem norm_bennettGammaBinetIntegral_quarter_fiveEighths_strip_le
    (a t : Real) (haLower : 1 / 4 ≤ a) :
    ‖bennettGammaBinetIntegral
        ((a : Complex) + (t / 2 : Real) * Complex.I)‖ ≤ 2 := by
  let z : Complex := (a : Complex) + (t / 2 : Real) * Complex.I
  rw [bennettGammaBinetIntegral]
  calc
    ‖∫ x : Real in Ioi 0,
        bennettGammaBinetKernel x * Complex.exp (-(x : Complex) * z)‖ ≤
        ∫ x : Real in Ioi 0,
          (1 / 2 : Real) * Real.exp (-(1 / 4 : Real) * x) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi
          (a := -(1 / 4 : Real)) (by norm_num) 0).const_mul (1 / 2 : Real))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, norm_bennettGammaBinetLaplaceFactor]
      have hk := norm_bennettGammaBinetKernel_le_one_half_of_pos hx
      have hzre : z.re = a := by simp [z]
      rw [hzre]
      have hexp : Real.exp (-(x * a)) ≤
          Real.exp (-(1 / 4 : Real) * x) := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right haLower hx.le
        nlinarith
      exact mul_le_mul hk hexp (Real.exp_pos _).le (by norm_num)
    _ = 2 := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(1 / 4 : Real)) (by norm_num) 0]
      norm_num

/-- The Binet formula gives a uniform linear digamma bound throughout the
entire spectral contour-shift strip. -/
theorem norm_digamma_quarter_fiveEighths_strip_le_linear
    (a t : Real) (haLower : 1 / 4 ≤ a) (haUpper : a ≤ 5 / 8) :
    ‖Complex.digamma
        ((a : Complex) + (t / 2 : Real) * Complex.I)‖ ≤
      |t| + (|Real.log (1 / 4)| + Real.pi + 6) := by
  let z : Complex := (a : Complex) + (t / 2 : Real) * Complex.I
  have hz : 0 < z.re := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero]
    exact (by norm_num : (0 : Real) < 1 / 4).trans_le haLower
  rw [bennettGammaBinetDigammaFormula z hz]
  have hlog : ‖Complex.log z‖ ≤
      |t| + (|Real.log (1 / 4)| + Real.pi + 1) := by
    simpa only [z] using
      norm_log_quarter_fiveEighths_strip_le a t haLower haUpper
  have hinv : ‖1 / (2 * z)‖ ≤ 2 := by
    have hnorm : (1 / 4 : Real) ≤ ‖z‖ := by
      calc
        (1 / 4 : Real) ≤ |z.re| := by
          simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
            sub_zero, add_zero]
          rw [abs_of_pos
            ((by norm_num : (0 : Real) < 1 / 4).trans_le haLower)]
          exact haLower
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [norm_div, norm_one, norm_mul]
    norm_num only [Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hrem : ‖bennettGammaBinetIntegral z‖ ≤ 2 := by
    simpa only [z] using
      norm_bennettGammaBinetIntegral_quarter_fiveEighths_strip_le
        a t haLower
  calc
    ‖Complex.log z - 1 / (2 * z) - bennettGammaBinetIntegral z‖ ≤
        ‖Complex.log z‖ + ‖1 / (2 * z)‖ +
          ‖bennettGammaBinetIntegral z‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ |t| + (|Real.log (1 / 4)| + Real.pi + 6) := by linarith

/-- The actual Burnol Archimedean summand is absolutely integrable on the xi
right vertical. -/
theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_archimedean_right
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        (-(Real.log Real.pi : Complex) / 2 +
          Complex.digamma
            (((5 / 8 : Real) : Complex) + (t / 2 : Real) * Complex.I) / 2) := by
  obtain ⟨E, hE, hweight⟩ :=
    exists_pos_const_one_add_sq_sq_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  let A : Real := |Real.log Real.pi| / 2 +
    (|Real.log (1 / 4)| + Real.pi + 6) / 2 + 1
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hmajor : Integrable fun t : Real =>
      (2 * E * A) * (1 + t ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul (2 * E * A)
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hdigammaContinuous : Continuous fun t : Real =>
        Complex.digamma
          (((5 / 8 : Real) : Complex) +
            (t / 2 : Real) * Complex.I) := by
      let line : Real → Complex := fun t =>
        ((5 / 8 : Real) : Complex) + (t / 2 : Real) * Complex.I
      have hline : Continuous line := by
        dsimp only [line]
        fun_prop
      rw [continuous_iff_continuousAt]
      intro t
      have hpsi : ContinuousAt Complex.digamma (line t) :=
        (analyticAt_digamma_of_re_pos (by
          dsimp only [line]
          norm_num)).continuousAt
      exact hpsi.comp hline.continuousAt
    have hweightContinuous : Continuous fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) :=
      (differentiable_suzukiSmoothCoreBurnolXiContourWeight v).continuous.comp
        (by fun_prop)
    have hfactorContinuous : Continuous fun t : Real =>
        -(Real.log Real.pi : Complex) / 2 +
          Complex.digamma
            (((5 / 8 : Real) : Complex) +
              (t / 2 : Real) * Complex.I) / 2 :=
      continuous_const.add (hdigammaContinuous.div_const 2)
    exact (hweightContinuous.mul hfactorContinuous).aestronglyMeasurable
  · have hweightProduct := hweight (5 / 4) t
      (by norm_num [guinandWeilXiContourLeft])
      (by norm_num [guinandWeilXiContourRight])
    have hden : 0 < 1 + t ^ 2 := by positivity
    have hdenSq : 0 < (1 + t ^ 2) ^ 2 := sq_pos_of_pos hden
    have hweightNorm :
        ‖suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖ ≤
          E / (1 + t ^ 2) ^ 2 := by
      rw [le_div_iff₀ hdenSq]
      simpa only [mul_comm] using hweightProduct
    have hdigamma :=
      norm_digamma_quarter_fiveEighths_strip_le_linear
        (5 / 8) t (by norm_num) (by norm_num)
    have hfactor :
        ‖-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              (((5 / 8 : Real) : Complex) +
                (t / 2 : Real) * Complex.I) / 2‖ ≤
          A * (1 + |t|) := by
      have htriangle := norm_add_le
        (-(Real.log Real.pi : Complex) / 2)
        (Complex.digamma
          (((5 / 8 : Real) : Complex) +
            (t / 2 : Real) * Complex.I) / 2)
      have hlogTerm :
          ‖-(Real.log Real.pi : Complex) / 2‖ =
            |Real.log Real.pi| / 2 := by
        rw [norm_div, norm_neg]
        norm_num only [Complex.norm_ofNat]
        simp
      have hdigammaTerm :
          ‖Complex.digamma
              (((5 / 8 : Real) : Complex) +
                (t / 2 : Real) * Complex.I) / 2‖ ≤
            (|t| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2 := by
        rw [norm_div]
        norm_num only [Complex.norm_ofNat]
        exact div_le_div_of_nonneg_right (by simpa using hdigamma) (by norm_num)
      have hbase : |Real.log Real.pi| / 2 +
          (|Real.log (1 / 4)| + Real.pi + 6) / 2 ≤ A := by
        dsimp only [A]
        linarith
      have hhalfA : (1 / 2 : Real) ≤ A := by
        dsimp only [A]
        nlinarith [abs_nonneg (Real.log Real.pi),
          abs_nonneg (Real.log (1 / 4)), Real.pi_pos]
      calc
        ‖-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              (((5 / 8 : Real) : Complex) +
                (t / 2 : Real) * Complex.I) / 2‖ ≤
            ‖-(Real.log Real.pi : Complex) / 2‖ +
              ‖Complex.digamma
                (((5 / 8 : Real) : Complex) +
                  (t / 2 : Real) * Complex.I) / 2‖ :=
          htriangle
        _ ≤ |Real.log Real.pi| / 2 +
            (|t| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2 := by
          rw [hlogTerm]
          gcongr
        _ ≤ A + A * |t| := by
          have hmul := mul_le_mul_of_nonneg_right hhalfA (abs_nonneg t)
          nlinarith
        _ = A * (1 + |t|) := by ring
    have habs : 1 + |t| ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    rw [norm_mul]
    calc
      ‖suzukiSmoothCoreBurnolXiContourWeight v
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖ *
          ‖-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              (((5 / 8 : Real) : Complex) +
                (t / 2 : Real) * Complex.I) / 2‖ ≤
          (E / (1 + t ^ 2) ^ 2) * (A * (1 + |t|)) := by
        gcongr
      _ ≤ (E / (1 + t ^ 2) ^ 2) * (A * (2 * (1 + t ^ 2))) := by
        gcongr
      _ = (2 * E * A) * (1 + t ^ 2)⁻¹ := by
        field_simp

/-- The two actual Burnol rational pole summands are absolutely integrable on
the xi right vertical. -/
theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_rational_right
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
          1 / ((1 / 4 : Real) + (t : Complex) * Complex.I)) := by
  obtain ⟨E, hE, hweight⟩ :=
    exists_pos_const_one_add_sq_sq_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  have hmajor : Integrable fun t : Real =>
      (5 * E) * (1 + t ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul (5 * E)
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hweightContinuous : Continuous fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) :=
      (differentiable_suzukiSmoothCoreBurnolXiContourWeight v).continuous.comp
        (by fun_prop)
    have hfirst : Continuous fun t : Real =>
        1 / (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) := by
      apply Continuous.div continuous_const (by fun_prop)
      intro t
      apply ne_of_apply_ne Complex.re
      norm_num
    have hsecond : Continuous fun t : Real =>
        1 / (((1 / 4 : Real) : Complex) + (t : Complex) * Complex.I) := by
      apply Continuous.div continuous_const (by fun_prop)
      intro t
      apply ne_of_apply_ne Complex.re
      norm_num
    exact (hweightContinuous.mul (hfirst.add hsecond)).aestronglyMeasurable
  · have hweightProduct := hweight (5 / 4) t
      (by norm_num [guinandWeilXiContourLeft])
      (by norm_num [guinandWeilXiContourRight])
    have hden : 0 < 1 + t ^ 2 := by positivity
    have hdenSq : 0 < (1 + t ^ 2) ^ 2 := sq_pos_of_pos hden
    have hweightNorm :
        ‖suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖ ≤
          E / (1 + t ^ 2) ^ 2 := by
      rw [le_div_iff₀ hdenSq]
      simpa only [mul_comm] using hweightProduct
    let s1 : Complex := (5 / 4 : Real) + (t : Complex) * Complex.I
    let s2 : Complex := (1 / 4 : Real) + (t : Complex) * Complex.I
    have hs1Norm : (5 / 4 : Real) ≤ ‖s1‖ := by
      calc
        (5 / 4 : Real) = |s1.re| := by
          simp [s1, abs_of_pos (by norm_num : (0 : Real) < 5 / 4)]
        _ ≤ ‖s1‖ := Complex.abs_re_le_norm s1
    have hs2Norm : (1 / 4 : Real) ≤ ‖s2‖ := by
      calc
        (1 / 4 : Real) = |s2.re| := by
          simp [s2]
        _ ≤ ‖s2‖ := Complex.abs_re_le_norm s2
    have hs1Inv : ‖1 / s1‖ ≤ (4 / 5 : Real) := by
      rw [norm_div, norm_one]
      rw [div_le_iff₀ ((by norm_num : (0 : Real) < 5 / 4).trans_le hs1Norm)]
      nlinarith
    have hs2Inv : ‖1 / s2‖ ≤ (4 : Real) := by
      rw [norm_div, norm_one]
      rw [div_le_iff₀ ((by norm_num : (0 : Real) < 1 / 4).trans_le hs2Norm)]
      nlinarith
    have hfactor : ‖1 / s1 + 1 / s2‖ ≤ 5 :=
      (norm_add_le _ _).trans (by linarith)
    change
      ‖suzukiSmoothCoreBurnolXiContourWeight v
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
        (1 / s1 + 1 / s2)‖ ≤ _
    rw [norm_mul]
    calc
      ‖suzukiSmoothCoreBurnolXiContourWeight v
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖ *
          ‖1 / s1 + 1 / s2‖ ≤
          (E / (1 + t ^ 2) ^ 2) * 5 := by gcongr
      _ ≤ (5 * E) * (1 + t ^ 2)⁻¹ := by
        have hone : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
        field_simp
        nlinarith

/-- The actual Burnol von Mangoldt summand is absolutely integrable on the
right line.  This is isolated from the already integrable full, rational, and
Archimedean terms using the checked right-half-plane decomposition. -/
theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_vonMangoldtLSeries_right
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          ((5 / 4 : Real) + (t : Complex) * Complex.I) *
        LSeries (fun n : Nat =>
            (ArithmeticFunction.vonMangoldt n : Complex))
          ((5 / 4 : Real) + (t : Complex) * Complex.I) := by
  let R : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
        1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))
  let A : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (-(Real.log Real.pi : Complex) / 2 +
        Complex.digamma
          (((5 / 8 : Real) : Complex) +
            (t / 2 : Real) * Complex.I) / 2)
  let F : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      logDeriv riemannXi
        ((5 / 4 : Real) + (t : Complex) * Complex.I)
  have hR : Integrable R :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_rational_right v
  have hA : Integrable A :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_archimedean_right v
  have hF : Integrable F := by
    simpa only [guinandWeilXiContourRight] using
      integrable_suzukiSmoothCoreBurnolXiContourWeight_mul_logDeriv_right v
  have hpointwise :
      (fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
            ((5 / 4 : Real) + (t : Complex) * Complex.I) *
          LSeries (fun n : Nat =>
              (ArithmeticFunction.vonMangoldt n : Complex))
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        fun t => R t + A t - F t := by
    funext t
    have hdecomp :=
      logDeriv_riemannXi_eq_rightHalfPlaneLiteratureTerms
        (s := ((5 / 4 : Real) + (t : Complex) * Complex.I)) (by norm_num)
    have hsub :
        ((5 / 4 : Real) + (t : Complex) * Complex.I) - 1 =
          (1 / 4 : Real) + (t : Complex) * Complex.I := by
      push_cast
      ring
    have hhalf :
        ((5 / 4 : Real) + (t : Complex) * Complex.I) / 2 =
          ((5 / 8 : Real) : Complex) +
            (t / 2 : Real) * Complex.I := by
      push_cast
      ring
    rw [hsub, hhalf] at hdecomp
    dsimp only [R, A, F]
    rw [hdecomp]
    ring
  rw [hpointwise]
  exact (hR.add hA).sub hF

/-! ## Exact rational-pole evaluation -/

private def suzukiBurnolXiPolePolynomial (s : Complex) : Complex :=
  s * (s - 1)

private theorem differentiable_suzukiBurnolXiPolePolynomial :
    Differentiable Complex suzukiBurnolXiPolePolynomial := by
  unfold suzukiBurnolXiPolePolynomial
  fun_prop

private theorem logDeriv_suzukiBurnolXiPolePolynomial
    {s : Complex} (hzero : s ≠ 0) (hone : s ≠ 1) :
    logDeriv suzukiBurnolXiPolePolynomial s = 1 / s + 1 / (s - 1) := by
  unfold suzukiBurnolXiPolePolynomial
  rw [logDeriv_mul (f := fun z : Complex => z)
    (g := fun z : Complex => z - 1) s hzero (sub_ne_zero.mpr hone)
    differentiableAt_id (differentiableAt_id.sub_const 1)]
  simp only [logDeriv_apply, deriv_id'', deriv_sub_const, one_div]

private theorem suzukiBurnolXiPolePolynomial_zero_iff (s : Complex) :
    suzukiBurnolXiPolePolynomial s = 0 ↔ s = 0 ∨ s = 1 := by
  unfold suzukiBurnolXiPolePolynomial
  rw [mul_eq_zero, sub_eq_zero]

private theorem analyticOrderAt_suzukiBurnolXiPolePolynomial_ne_top
    (s : Complex) :
    analyticOrderAt suzukiBurnolXiPolePolynomial s ≠ ⊤ := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr
    differentiable_suzukiBurnolXiPolePolynomial).analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := (2 : Complex)) (y := s) trivial trivial
  rw [(differentiable_suzukiBurnolXiPolePolynomial.analyticAt 2).analyticOrderAt_eq_zero.mpr]
  · exact ENat.zero_ne_top
  · norm_num [suzukiBurnolXiPolePolynomial]

private theorem analyticOrderNatAt_suzukiBurnolXiPolePolynomial_one :
    analyticOrderNatAt suzukiBurnolXiPolePolynomial 1 = 1 := by
  have han := differentiable_suzukiBurnolXiPolePolynomial.analyticAt 1
  have hzero : suzukiBurnolXiPolePolynomial 1 = 0 := by
    simp [suzukiBurnolXiPolePolynomial]
  have hderiv : deriv suzukiBurnolXiPolePolynomial 1 ≠ 0 := by
    unfold suzukiBurnolXiPolePolynomial
    have hd := (hasDerivAt_id (1 : Complex)).mul
      ((hasDerivAt_id (1 : Complex)).sub_const 1)
    change HasDerivAt (fun z : Complex => z * (z - 1))
      (1 * (1 - 1) + 1 * 1) 1 at hd
    rw [hd.deriv]
    norm_num
  have horder := han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero hderiv
  rw [analyticOrderNatAt, horder]
  simp

private theorem one_mem_suzukiBurnolPoleRectangle_nhds
    {T : Real} (hT : 0 < T) :
    Complex.Rectangle
        (((1 / 2 : Real) : Complex) - (T : Complex) * Complex.I)
        (((5 / 4 : Real) : Complex) + (T : Complex) * Complex.I) ∈
      nhds (1 : Complex) := by
  rw [guinandWeilRectangle_mem_nhds_iff]
  rw [Complex.mem_reProdIm]
  norm_num [Complex.mul_re, Complex.mul_im]
  rw [Set.uIoo_of_le (by linarith)]
  constructor <;> linarith

private theorem zero_not_mem_suzukiBurnolPoleRectangle (T : Real) :
    (0 : Complex) ∉
      Complex.Rectangle
        (((1 / 2 : Real) : Complex) - (T : Complex) * Complex.I)
        (((5 / 4 : Real) : Complex) + (T : Complex) * Complex.I) := by
  intro hmem
  rw [Complex.Rectangle, Complex.mem_reProdIm] at hmem
  have hre := hmem.1
  rw [Set.uIcc_of_le (by norm_num)] at hre
  norm_num at hre

private theorem normalizedRectangle_suzukiSmoothCoreBurnol_rational
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    {T : Real} (hT : 0 < T) :
    guinandWeilNormalizedRectangleIntegral
        (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
          (1 / s + 1 / (s - 1)))
        (((1 / 2 : Real) : Complex) - (T : Complex) * Complex.I)
        (((5 / 4 : Real) : Complex) + (T : Complex) * Complex.I) =
      suzukiSmoothCoreBurnolXiContourWeight v 1 := by
  let zT : Complex := ((1 / 2 : Real) : Complex) - (T : Complex) * Complex.I
  let wT : Complex := ((5 / 4 : Real) : Complex) + (T : Complex) * Complex.I
  let H : Complex → Complex := suzukiSmoothCoreBurnolXiContourWeight v
  have hzre : zT.re ≤ wT.re := by norm_num [zT, wT]
  have hzim : zT.im ≤ wT.im := by
    norm_num [zT, wT]
    linarith
  have hpN : Complex.Rectangle zT wT ∈ nhds (1 : Complex) := by
    simpa only [zT, wT] using one_mem_suzukiBurnolPoleRectangle_nhds hT
  have hweighted :=
    guinandWeilNormalizedRectangleIntegral_weight_mul_logDeriv_eq_sum
      (H := H) (f := suzukiBurnolXiPolePolynomial)
      (S := {(1 : Complex)}) hzre hzim
      ((analyticOnNhd_suzukiSmoothCoreBurnolXiContourWeight v).mono
        (by simp [H]))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        differentiable_suzukiBurnolXiPolePolynomial).mono (by simp))
      (fun s _ => analyticOrderAt_suzukiBurnolXiPolePolynomial_ne_top s)
      (by
        intro s hs
        have hs' : s = (1 : Complex) := by simpa using hs
        subst s
        exact mem_of_mem_nhds hpN)
      (by
        intro s hs
        simp only [Finset.mem_singleton]
        rw [suzukiBurnolXiPolePolynomial_zero_iff]
        constructor
        · intro h
          exact Or.inr h
        · rintro (h | h)
          · exact (zero_not_mem_suzukiBurnolPoleRectangle T
              (by simpa only [zT, wT, h] using hs)).elim
          · exact h)
      (by
        intro s hs hzero
        have hsR := guinandWeilRectangleBorder_subset_rectangle zT wT hs
        have hsOne : s = (1 : Complex) := by
          rcases (suzukiBurnolXiPolePolynomial_zero_iff s).mp hzero with h | h
          · exact (zero_not_mem_suzukiBurnolPoleRectangle T
              (by simpa only [zT, wT, h] using hsR)).elim
          · exact h
        subst s
        exact (not_mem_guinandWeilRectangleBorder_of_rectangle_mem_nhds
          hzre hzim hpN) hs)
  have hweighted' :
      guinandWeilNormalizedRectangleIntegral
          (fun s => H s * logDeriv suzukiBurnolXiPolePolynomial s) zT wT =
        H 1 := by
    simpa [analyticOrderNatAt_suzukiBurnolXiPolePolynomial_one] using hweighted
  have hcongr : Set.EqOn
      (fun s => H s * (1 / s + 1 / (s - 1)))
      (fun s => H s * logDeriv suzukiBurnolXiPolePolynomial s)
      (guinandWeilRectangleBorder zT wT) := by
    intro s hs
    have hsR := guinandWeilRectangleBorder_subset_rectangle zT wT hs
    have hzero : s ≠ 0 := by
      intro h
      exact zero_not_mem_suzukiBurnolPoleRectangle T
        (by simpa only [zT, wT, h] using hsR)
    have hone : s ≠ 1 := by
      intro h
      subst s
      exact (not_mem_guinandWeilRectangleBorder_of_rectangle_mem_nhds
        hzre hzim hpN) hs
    dsimp only
    rw [logDeriv_suzukiBurnolXiPolePolynomial hzero hone]
  change guinandWeilNormalizedRectangleIntegral
      (fun s => H s * (1 / s + 1 / (s - 1))) zT wT = H 1
  rw [guinandWeilNormalizedRectangleIntegral_congr hcongr]
  exact hweighted'

private theorem suzukiSmoothCoreBurnolXiContourWeight_critical
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (t : Real) :
    suzukiSmoothCoreBurnolXiContourWeight v
        (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) =
      fourierAutocorrelation (suzukiProjectBase v.1) t := by
  unfold suzukiSmoothCoreBurnolXiContourWeight
  rw [show
      ((((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) -
          (1 / 2 : Complex)) / Complex.I = (t : Complex) by
    apply Complex.ext <;> norm_num <;> ring]
  exact burnolFourierLaplaceSource_ofReal _ _

private theorem norm_suzukiBurnolXiRationalFactor_critical_le_four
    (t : Real) :
    ‖1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
        1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1)‖ ≤ 4 := by
  let d1 : Complex := ((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I
  let d2 : Complex := d1 - 1
  have hd1 : (1 / 2 : Real) ≤ ‖d1‖ := by
    calc
      (1 / 2 : Real) = |d1.re| := by norm_num [d1]
      _ ≤ ‖d1‖ := Complex.abs_re_le_norm d1
  have hd2 : (1 / 2 : Real) ≤ ‖d2‖ := by
    calc
      (1 / 2 : Real) = |d2.re| := by norm_num [d1, d2]
      _ ≤ ‖d2‖ := Complex.abs_re_le_norm d2
  have hinv1 : ‖1 / d1‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ ((by norm_num : (0 : Real) < 1 / 2).trans_le hd1)]
    nlinarith
  have hinv2 : ‖1 / d2‖ ≤ 2 := by
    rw [norm_div, norm_one, div_le_iff₀ ((by norm_num : (0 : Real) < 1 / 2).trans_le hd2)]
    nlinarith
  change ‖1 / d1 + 1 / d2‖ ≤ 4
  exact (norm_add_le _ _).trans (by linarith)

private theorem integrable_suzukiSmoothCoreBurnol_rational_critical
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
        (1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
          1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1)) := by
  have hbase : Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
        (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) := by
    simpa only [suzukiSmoothCoreBurnolXiContourWeight_critical] using
      (fourierAutocorrelation (suzukiProjectBase v.1)).integrable
  apply hbase.mul_bdd (c := 4)
  · have hfirst : Continuous fun t : Real =>
        1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) := by
      apply Continuous.div continuous_const (by fun_prop)
      intro t
      apply ne_of_apply_ne Complex.re
      norm_num
    have hsecond : Continuous fun t : Real =>
        1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1) := by
      apply Continuous.div continuous_const (by fun_prop)
      intro t
      apply ne_of_apply_ne Complex.re
      norm_num
    exact (hfirst.add hsecond).aestronglyMeasurable
  · filter_upwards with t
    exact norm_suzukiBurnolXiRationalFactor_critical_le_four t

private theorem re_suzukiSmoothCoreBurnol_rational_critical (v :
    SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (t : Real) :
    (suzukiSmoothCoreBurnolXiContourWeight v
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
        (1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
          1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1))).re = 0 := by
  rw [suzukiSmoothCoreBurnolXiContourWeight_critical]
  have hweightIm := fourierAutocorrelation_im (suzukiProjectBase v.1) t
  have hfactorRe :
      (1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
        1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1)).re = 0 := by
    simp only [one_div]
    rw [Complex.add_re, Complex.inv_re, Complex.inv_re]
    norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    have hden : (1 / 2 : Real) ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp [hden]
    ring
  rw [Complex.mul_re, hweightIm, hfactorRe]
  ring

private theorem re_integral_suzukiSmoothCoreBurnol_rational_critical_eq_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    ((MeasureTheory.integral volume fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
        (1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
          1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1))) :
        Complex).re = 0 := by
  calc
    ((MeasureTheory.integral volume fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
            (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
          (1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
            1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I - 1))) :
          Complex).re =
        ∫ t : Real,
          (suzukiSmoothCoreBurnolXiContourWeight v
              (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
            (1 / (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) +
              1 / (((1 / 2 : Real) : Complex) +
                (t : Complex) * Complex.I - 1))).re :=
      (integral_re (integrable_suzukiSmoothCoreBurnol_rational_critical v)).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with t
      exact re_suzukiSmoothCoreBurnol_rational_critical v t

private theorem re_burnolFourierLaplaceSource_I_div_two_eq_neg
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (burnolFourierLaplaceSource (suzukiProjectBase v.1)
        (Complex.I / 2)).re =
      (burnolFourierLaplaceSource (suzukiProjectBase v.1)
        (-Complex.I / 2)).re := by
  rw [burnolFourierLaplaceSource_suzukiProjectBase,
    burnolFourierLaplaceSource_suzukiProjectBase,
    suzukiFourierSource_autocorrelation_eq_mul_conj
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩) (Complex.I / 2),
    suzukiFourierSource_autocorrelation_eq_mul_conj
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩) (-Complex.I / 2)]
  simp only [map_div₀, map_neg, Complex.conj_I, Complex.conj_ofNat,
    neg_div, neg_neg]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem norm_suzukiBurnolXiRationalFactor_horizontal_le_two
    (sigma T : Real) (hT : 1 ≤ |T|) :
    ‖1 / ((sigma : Complex) + (T : Complex) * Complex.I) +
        1 / ((sigma : Complex) + (T : Complex) * Complex.I - 1)‖ ≤ 2 := by
  let d1 : Complex := (sigma : Complex) + (T : Complex) * Complex.I
  let d2 : Complex := d1 - 1
  have hd1 : 1 ≤ ‖d1‖ := by
    calc
      1 ≤ |T| := hT
      _ = |d1.im| := by simp [d1]
      _ ≤ ‖d1‖ := Complex.abs_im_le_norm d1
  have hd2 : 1 ≤ ‖d2‖ := by
    calc
      1 ≤ |T| := hT
      _ = |d2.im| := by simp [d1, d2]
      _ ≤ ‖d2‖ := Complex.abs_im_le_norm d2
  have hinv1 : ‖1 / d1‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (lt_of_lt_of_le zero_lt_one hd1)]
    exact hd1
  have hinv2 : ‖1 / d2‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one (lt_of_lt_of_le zero_lt_one hd2)]
    exact hd2
  change ‖1 / d1 + 1 / d2‖ ≤ 2
  exact (norm_add_le _ _).trans (by linarith)

private theorem norm_suzukiSmoothCoreBurnol_rational_horizontal_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (C T : Real) (hC : 0 ≤ C) (hT : 1 ≤ |T|)
    (hweight : ∀ sigma : Real,
      guinandWeilXiContourLeft ≤ sigma →
      sigma ≤ guinandWeilXiContourRight →
      |T| ^ 5 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ C) :
    ‖guinandWeilHorizontalIntegral
        (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
          (1 / s + 1 / (s - 1)))
        (1 / 2) (5 / 4) T‖ ≤
      3 * C / (2 * |T| ^ 5) := by
  have hTabs : 0 < |T| := zero_lt_one.trans_le hT
  have hden : 0 < |T| ^ 5 := pow_pos hTabs 5
  unfold guinandWeilHorizontalIntegral
  calc
    ‖∫ sigma in (1 / 2 : Real)..(5 / 4 : Real),
        suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I) *
          (1 / ((sigma : Complex) + (T : Complex) * Complex.I) +
            1 / ((sigma : Complex) + (T : Complex) * Complex.I - 1))‖ ≤
        (2 * C / |T| ^ 5) * |(5 / 4 : Real) - 1 / 2| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro sigma hsigma
      have hsigma' := Set.uIoc_subset_uIcc hsigma
      rw [Set.uIcc_of_le (by norm_num)] at hsigma'
      have hw := hweight sigma
        (by norm_num [guinandWeilXiContourLeft]; linarith [hsigma'.1])
        (by norm_num [guinandWeilXiContourRight]; linarith [hsigma'.2])
      have hw' :
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
              C / |T| ^ 5 := by
        rw [le_div_iff₀ hden]
        simpa only [mul_comm] using hw
      rw [norm_mul]
      calc
        ‖suzukiSmoothCoreBurnolXiContourWeight v
              ((sigma : Complex) + (T : Complex) * Complex.I)‖ *
            ‖1 / ((sigma : Complex) + (T : Complex) * Complex.I) +
              1 / ((sigma : Complex) + (T : Complex) * Complex.I - 1)‖ ≤
            (C / |T| ^ 5) * 2 := mul_le_mul hw'
              (norm_suzukiBurnolXiRationalFactor_horizontal_le_two sigma T hT)
              (norm_nonneg _) (by positivity)
        _ = 2 * C / |T| ^ 5 := by ring
    _ = 3 * C / (2 * |T| ^ 5) := by
      norm_num
      field_simp
      ring

private theorem tendsto_both_suzukiSmoothCoreBurnol_rational_horizontal_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            (1 / s + 1 / (s - 1)))
          (1 / 2) (5 / 4) (N : Real))
        atTop (nhds 0) ∧
      Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            (1 / s + 1 / (s - 1)))
          (1 / 2) (5 / 4) (-(N : Real)))
        atTop (nhds 0) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_pos_const_abs_pow_five_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  let M : Nat → Real := fun N => (3 * C / 2) / (N : Real)
  have hM : Tendsto M atTop (nhds 0) := by
    simpa only [M] using tendsto_const_div_atTop_nhds_zero_nat (3 * C / 2)
  have hmajor (sign : Real) (hsign : |sign| = 1) :
      ∀ᶠ N : Nat in atTop,
        ‖guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            (1 / s + 1 / (s - 1)))
          (1 / 2) (5 / 4) (sign * (N : Real))‖ ≤ M N := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
    have hTN : |sign * (N : Real)| = (N : Real) := by
      rw [abs_mul, hsign, one_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    have hbound := norm_suzukiSmoothCoreBurnol_rational_horizontal_le
      v C (sign * (N : Real)) hC.le (by simpa [hTN] using hNreal)
      (hweight (T := sign * (N : Real)))
    have hpow : (N : Real) ≤ (N : Real) ^ 5 := by
      have hNnonneg : (0 : Real) ≤ N := Nat.cast_nonneg N
      nlinarith [sq_nonneg ((N : Real) ^ 2 - 1),
        mul_self_nonneg ((N : Real) ^ 2)]
    have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNreal
    rw [hTN] at hbound
    exact hbound.trans (by
      dsimp only [M]
      have hscalar : 0 ≤ 3 * C / 2 := by positivity
      calc
        3 * C / (2 * (N : Real) ^ 5) =
            (3 * C / 2) / (N : Real) ^ 5 := by ring
        _ ≤ (3 * C / 2) / (N : Real) :=
          div_le_div_of_nonneg_left hscalar hNpos hpow)
  have htendsto (sign : Real) (hsign : |sign| = 1) :
      Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            (1 / s + 1 / (s - 1)))
          (1 / 2) (5 / 4) (sign * (N : Real)))
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hmajor sign hsign) hM
  constructor
  · simpa only [one_mul] using htendsto 1 (by norm_num)
  · simpa only [neg_one_mul] using htendsto (-1) (by norm_num)

/-- The rational part of the actual Burnol xi right vertical is exactly the
two completed-zeta pole evaluations in the project normalization. -/
theorem one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_rational_right_eq_pole
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (1 / Real.pi) *
        (MeasureTheory.integral volume fun t : Real =>
          suzukiSmoothCoreBurnolXiContourWeight v
              ((5 / 4 : Real) + (t : Complex) * Complex.I) *
            (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
              1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))).re =
      guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v.1) := by
  let F : Complex → Complex := fun s =>
    suzukiSmoothCoreBurnolXiContourWeight v s * (1 / s + 1 / (s - 1))
  let rightLine : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
        1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))
  let leftLine : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        ((1 / 2 : Real) + (t : Complex) * Complex.I) *
      (1 / ((1 / 2 : Real) + (t : Complex) * Complex.I) +
        1 / ((1 / 2 : Real) + (t : Complex) * Complex.I - 1))
  let completeRight : Complex := ∫ t : Real, rightLine t
  let completeLeft : Complex := ∫ t : Real, leftLine t
  let bottom : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F (1 / 2) (5 / 4) (-(N : Real))
  let top : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F (1 / 2) (5 / 4) (N : Real)
  let right : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F (5 / 4) (-(N : Real)) (N : Real)
  let left : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F (1 / 2) (-(N : Real)) (N : Real)
  obtain ⟨htop, hbottom⟩ :=
    tendsto_both_suzukiSmoothCoreBurnol_rational_horizontal_zero v
  have hbottom' : Tendsto bottom atTop (nhds 0) := by
    simpa only [bottom, F] using hbottom
  have htop' : Tendsto top atTop (nhds 0) := by
    simpa only [top, F] using htop
  have hheight : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hright : Tendsto right atTop (nhds (Complex.I * completeRight)) := by
    dsimp only [right, completeRight, rightLine, F]
    unfold guinandWeilVerticalIntegral
    have h := (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnolXiContourWeight_rational_right v)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I
    have hsub (t : Real) :
        ((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I - 1 =
          ((1 / 4 : Real) : Complex) + (t : Complex) * Complex.I := by
      push_cast
      ring
    simpa only [Function.comp_apply, hsub] using h
  have hleft : Tendsto left atTop (nhds (Complex.I * completeLeft)) := by
    dsimp only [left, completeLeft, leftLine, F]
    unfold guinandWeilVerticalIntegral
    have h := (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnol_rational_critical v)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I
    exact h
  have hcontour : Tendsto
      (fun N => (1 / (2 * Real.pi * Complex.I)) *
        (bottom N - top N + right N - left N))
      atTop
      (nhds ((1 / (2 * Real.pi * Complex.I)) *
        ((0 : Complex) - 0 + Complex.I * completeRight -
          Complex.I * completeLeft))) :=
    (((hbottom'.sub htop').add hright).sub hleft).const_mul
      (1 / (2 * Real.pi * Complex.I))
  have hconstant : Tendsto
      (fun N => (1 / (2 * Real.pi * Complex.I)) *
        (bottom N - top N + right N - left N))
      atTop (nhds (suzukiSmoothCoreBurnolXiContourWeight v 1)) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hNpos : (0 : Real) < N := by exact_mod_cast hN
    have hfinite := normalizedRectangle_suzukiSmoothCoreBurnol_rational v hNpos
    unfold guinandWeilNormalizedRectangleIntegral guinandWeilRectangleIntegral at hfinite
    dsimp only [bottom, top, right, left, F]
    convert hfinite.symm using 1 <;> norm_num
  have hlimit := tendsto_nhds_unique hcontour hconstant
  have hlimit' :
      ((1 / (2 * Real.pi) : Real) : Complex) *
          (completeRight - completeLeft) =
        suzukiSmoothCoreBurnolXiContourWeight v 1 := by
    calc
      ((1 / (2 * Real.pi) : Real) : Complex) *
          (completeRight - completeLeft) =
          (1 / (2 * Real.pi * Complex.I)) *
            ((0 : Complex) - 0 + Complex.I * completeRight -
              Complex.I * completeLeft) := by
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
          Complex.I_ne_zero]
        ring
      _ = suzukiSmoothCoreBurnolXiContourWeight v 1 := hlimit
  have hleftRe : completeLeft.re = 0 := by
    simpa only [completeLeft, leftLine] using
      re_integral_suzukiSmoothCoreBurnol_rational_critical_eq_zero v
  have hrightRe :
      (1 / Real.pi) * completeRight.re =
        2 * (suzukiSmoothCoreBurnolXiContourWeight v 1).re := by
    have hre := congrArg Complex.re hlimit'
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.sub_re, hleftRe] at hre
    field_simp [Real.pi_ne_zero] at hre ⊢
    linarith
  have hweightOne :
      suzukiSmoothCoreBurnolXiContourWeight v 1 =
        burnolFourierLaplaceSource (suzukiProjectBase v.1)
          (-Complex.I / 2) := by
    unfold suzukiSmoothCoreBurnolXiContourWeight
    congr 1
    apply Complex.ext <;> norm_num
  change (1 / Real.pi) * completeRight.re = _
  rw [hrightRe, hweightOne]
  unfold guinandWeilBurnolLiteraturePoleSide
  rw [Complex.add_re,
    re_burnolFourierLaplaceSource_I_div_two_eq_neg v]
  ring

/-! ## Exact Archimedean evaluation -/

private def suzukiSmoothCoreBurnolArchimedeanIntegrand
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (s : Complex) : Complex :=
  suzukiSmoothCoreBurnolXiContourWeight v s *
    (-(Real.log Real.pi : Complex) / 2 + Complex.digamma (s / 2) / 2)

private theorem differentiableOn_suzukiSmoothCoreBurnolArchimedeanIntegrand_strip
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    DifferentiableOn Complex (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
      {s : Complex | (1 / 2 : Real) ≤ s.re ∧ s.re ≤ 5 / 4} := by
  intro s hs
  have hsPos : 0 < (s / 2).re := by
    have hre : (s / 2).re = s.re / 2 := by
      norm_num [Complex.div_re]
    rw [hre]
    linarith [hs.1]
  have hdigamma : DifferentiableAt Complex Complex.digamma (s / 2) :=
    (analyticAt_digamma_of_re_pos hsPos).differentiableAt
  have hfactor : DifferentiableAt Complex
      (fun z : Complex =>
        -(Real.log Real.pi : Complex) / 2 + Complex.digamma (z / 2) / 2) s :=
    differentiableAt_const (c := -(Real.log Real.pi : Complex) / 2) |>.add
      ((hdigamma.comp s (differentiableAt_id.div_const 2)).div_const 2)
  unfold suzukiSmoothCoreBurnolArchimedeanIntegrand
  exact ((differentiable_suzukiSmoothCoreBurnolXiContourWeight v).differentiableAt.mul
    hfactor).differentiableWithinAt

private theorem rectangle_suzukiSmoothCoreBurnol_archimedean_eq_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (T : Real) :
    guinandWeilRectangleIntegral
        (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
        (((1 / 2 : Real) : Complex) - (T : Complex) * Complex.I)
        (((5 / 4 : Real) : Complex) + (T : Complex) * Complex.I) = 0 := by
  apply guinandWeilRectangleIntegral_eq_zero_of_differentiableOn
  apply
    (differentiableOn_suzukiSmoothCoreBurnolArchimedeanIntegrand_strip v).mono
  intro s hs
  rw [Complex.Rectangle, Complex.mem_reProdIm] at hs
  have hre := hs.1
  rw [Set.uIcc_of_le (by norm_num)] at hre
  simpa using hre

private theorem norm_suzukiSmoothCoreBurnol_archimedean_horizontal_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (C T : Real) (hC : 0 ≤ C) (hT : 1 ≤ |T|)
    (hweight : ∀ sigma : Real,
      guinandWeilXiContourLeft ≤ sigma →
      sigma ≤ guinandWeilXiContourRight →
      |T| ^ 5 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ C) :
    ‖guinandWeilHorizontalIntegral
        (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
        (1 / 2) (5 / 4) T‖ ≤
      (3 * C / 4) *
        (|Real.log Real.pi| / 2 +
          (|T| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2) /
        |T| ^ 5 := by
  have hTabs : 0 < |T| := zero_lt_one.trans_le hT
  have hden : 0 < |T| ^ 5 := pow_pos hTabs 5
  unfold guinandWeilHorizontalIntegral
  calc
    ‖∫ sigma in (1 / 2 : Real)..(5 / 4 : Real),
        suzukiSmoothCoreBurnolArchimedeanIntegrand v
          ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
        ((C / |T| ^ 5) *
          (|Real.log Real.pi| / 2 +
            (|T| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2)) *
          |(5 / 4 : Real) - 1 / 2| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro sigma hsigma
      have hsigma' := Set.uIoc_subset_uIcc hsigma
      rw [Set.uIcc_of_le (by norm_num)] at hsigma'
      have hw := hweight sigma
        (by norm_num [guinandWeilXiContourLeft]; linarith [hsigma'.1])
        (by norm_num [guinandWeilXiContourRight]; linarith [hsigma'.2])
      have hw' :
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
              C / |T| ^ 5 := by
        rw [le_div_iff₀ hden]
        simpa only [mul_comm] using hw
      have hdigamma :=
        norm_digamma_quarter_fiveEighths_strip_le_linear
          (sigma / 2) T (by linarith [hsigma'.1])
            (by linarith [hsigma'.2])
      have hfactor :
          ‖-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                (((sigma / 2 : Real) : Complex) +
                  (T / 2 : Real) * Complex.I) / 2‖ ≤
            |Real.log Real.pi| / 2 +
              (|T| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2 := by
        calc
          _ ≤ ‖-(Real.log Real.pi : Complex) / 2‖ +
                ‖Complex.digamma
                  (((sigma / 2 : Real) : Complex) +
                    (T / 2 : Real) * Complex.I) / 2‖ := norm_add_le _ _
          _ = |Real.log Real.pi| / 2 +
                ‖Complex.digamma
                  (((sigma / 2 : Real) : Complex) +
                    (T / 2 : Real) * Complex.I)‖ / 2 := by
              rw [norm_div, norm_neg, norm_div]
              norm_num only [Complex.norm_ofNat]
              simp
          _ ≤ _ := by gcongr
      change
        ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I) *
          (-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              (((sigma : Complex) + (T : Complex) * Complex.I) / 2) / 2)‖ ≤ _
      have hhalf :
          ((sigma : Complex) + (T : Complex) * Complex.I) / 2 =
            ((sigma / 2 : Real) : Complex) +
              (T / 2 : Real) * Complex.I := by
        push_cast
        ring
      rw [hhalf, norm_mul]
      exact mul_le_mul hw' hfactor (norm_nonneg _) (by positivity)
    _ = _ := by
      norm_num
      ring

private theorem tendsto_both_suzukiSmoothCoreBurnol_archimedean_horizontal_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
          (1 / 2) (5 / 4) (N : Real))
        atTop (nhds 0) ∧
      Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
          (1 / 2) (5 / 4) (-(N : Real)))
        atTop (nhds 0) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_pos_const_abs_pow_five_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  let K : Real := (3 * C / 4) *
    (|Real.log Real.pi| / 2 +
      (1 + (|Real.log (1 / 4)| + Real.pi + 6)) / 2)
  let M : Nat → Real := fun N => K / (N : Real)
  have hM : Tendsto M atTop (nhds 0) := by
    simpa only [M] using tendsto_const_div_atTop_nhds_zero_nat K
  have hmajor (sign : Real) (hsign : |sign| = 1) :
      ∀ᶠ N : Nat in atTop,
        ‖guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
          (1 / 2) (5 / 4) (sign * (N : Real))‖ ≤ M N := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNreal
    have hTN : |sign * (N : Real)| = (N : Real) := by
      rw [abs_mul, hsign, one_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    have hbound := norm_suzukiSmoothCoreBurnol_archimedean_horizontal_le
      v C (sign * (N : Real)) hC.le (by simpa [hTN] using hNreal)
      (hweight (T := sign * (N : Real)))
    rw [hTN] at hbound
    exact hbound.trans (by
      dsimp only [M, K]
      have hCnonneg : 0 ≤ 3 * C / 4 := by positivity
      have hlogNonneg : 0 ≤ |Real.log Real.pi| / 2 := by positivity
      have hconstNonneg :
          0 ≤ |Real.log (1 / 4)| + Real.pi + 6 := by positivity
      have hpow : (N : Real) ^ 5 ≥ (N : Real) ^ 2 := by
        nlinarith [sq_nonneg ((N : Real) ^ 2 - 1),
          mul_self_nonneg ((N : Real) ^ 2)]
      let D : Real := |Real.log Real.pi| / 2 +
        (1 + (|Real.log (1 / 4)| + Real.pi + 6)) / 2
      have hD : 0 ≤ D := by
        dsimp only [D]
        positivity
      have hpowMul :
          (3 * C / 4 * D) * (N : Real) ^ 2 ≤
            (3 * C / 4 * D) * (N : Real) ^ 5 :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg hCnonneg hD)
      calc
        (3 * C / 4) *
              (|Real.log Real.pi| / 2 +
                ((N : Real) +
                  (|Real.log (1 / 4)| + Real.pi + 6)) / 2) /
            (N : Real) ^ 5 ≤
            (3 * C / 4) *
              ((N : Real) *
                (|Real.log Real.pi| / 2 +
                  (1 + (|Real.log (1 / 4)| + Real.pi + 6)) / 2)) /
              (N : Real) ^ 5 := by
                gcongr
                nlinarith
        _ ≤ ((3 * C / 4) *
              (|Real.log Real.pi| / 2 +
                (1 + (|Real.log (1 / 4)| + Real.pi + 6)) / 2)) /
              (N : Real) := by
                rw [div_le_div_iff₀ (pow_pos hNpos 5) hNpos]
                dsimp only [D] at hpowMul
                ring_nf at hpowMul ⊢
                exact hpowMul)
  have htendsto (sign : Real) (hsign : |sign| = 1) :
      Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolArchimedeanIntegrand v)
          (1 / 2) (5 / 4) (sign * (N : Real)))
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hmajor sign hsign) hM
  constructor
  · simpa only [one_mul] using htendsto 1 (by norm_num)
  · simpa only [neg_one_mul] using htendsto (-1) (by norm_num)

private theorem integrable_suzukiSmoothCoreBurnol_archimedean_critical
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolArchimedeanIntegrand v
        (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) := by
  let g : SchwartzLineTestFunction := suzukiProjectBase v.1
  let A : Real := |Real.log Real.pi| / 2 +
    (|Real.log (1 / 4)| + Real.pi + 6) / 2 + 1
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hmajor : Integrable fun t : Real =>
      A * fourierEnergyDensity g t +
        A * (|t| * fourierEnergyDensity g t) :=
    (integrable_fourierEnergyDensity g).const_mul A |>.add
      ((integrable_abs_mul_fourierEnergyDensity g).const_mul A)
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · unfold suzukiSmoothCoreBurnolArchimedeanIntegrand
    have hweightContinuous : Continuous fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) :=
      (differentiable_suzukiSmoothCoreBurnolXiContourWeight v).continuous.comp
        (by fun_prop)
    have hdigammaContinuous : Continuous fun t : Real =>
        Complex.digamma
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) := by
      let line : Real → Complex := fun t =>
        (1 / 4 : Complex) + (t / 2 : Real) * Complex.I
      have hline : Continuous line := by
        dsimp only [line]
        fun_prop
      rw [continuous_iff_continuousAt]
      intro t
      exact (analyticAt_digamma_of_re_pos (by
        change 0 < ((1 / 4 : Complex) +
          (t / 2 : Real) * Complex.I).re
        norm_num)).continuousAt.comp hline.continuousAt
    have hfactorContinuous : Continuous fun t : Real =>
        -(Real.log Real.pi : Complex) / 2 +
          Complex.digamma
            ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2 :=
      continuous_const.add (hdigammaContinuous.div_const 2)
    have hpointwise :
        (fun t : Real =>
          suzukiSmoothCoreBurnolXiContourWeight v
              (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((((1 / 2 : Real) : Complex) +
                  (t : Complex) * Complex.I) / 2) / 2)) =
          fun t : Real =>
            suzukiSmoothCoreBurnolXiContourWeight v
                (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
              (-(Real.log Real.pi : Complex) / 2 +
                Complex.digamma
                  ((1 / 4 : Complex) +
                    (t / 2 : Real) * Complex.I) / 2) := by
      funext t
      congr 3
      push_cast
      ring
    rw [hpointwise]
    exact (hweightContinuous.mul hfactorContinuous).aestronglyMeasurable
  · have hdigamma :=
      norm_digamma_quarter_fiveEighths_strip_le_linear
        (1 / 4) t (by norm_num) (by norm_num)
    have hfactor :
        ‖-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2‖ ≤
          A * (1 + |t|) := by
      have htriangle := norm_add_le
        (-(Real.log Real.pi : Complex) / 2)
        (Complex.digamma
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2)
      have hhalfA : (1 / 2 : Real) ≤ A := by
        dsimp only [A]
        nlinarith [abs_nonneg (Real.log Real.pi),
          abs_nonneg (Real.log (1 / 4)), Real.pi_pos]
      calc
        _ ≤ ‖-(Real.log Real.pi : Complex) / 2‖ +
              ‖Complex.digamma
                ((1 / 4 : Complex) +
                  (t / 2 : Real) * Complex.I) / 2‖ := htriangle
        _ = |Real.log Real.pi| / 2 +
              ‖Complex.digamma
                ((1 / 4 : Complex) +
                  (t / 2 : Real) * Complex.I)‖ / 2 := by
            rw [norm_div, norm_neg, norm_div]
            norm_num only [Complex.norm_ofNat]
            simp
        _ ≤ |Real.log Real.pi| / 2 +
              (|t| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2 := by
            have hdigamma' :
                ‖Complex.digamma
                    ((1 / 4 : Complex) +
                      (t / 2 : Real) * Complex.I)‖ ≤
                  |t| + (|Real.log (1 / 4)| + Real.pi + 6) := by
              convert hdigamma using 1 <;> norm_num
            have hdiv :
                ‖Complex.digamma
                    ((1 / 4 : Complex) +
                      (t / 2 : Real) * Complex.I)‖ / (2 : Real) ≤
                  (|t| + (|Real.log (1 / 4)| + Real.pi + 6)) / 2 :=
              div_le_div_of_nonneg_right hdigamma' (by norm_num)
            simpa only [add_comm] using
              add_le_add_left hdiv (|Real.log Real.pi| / 2)
        _ ≤ A + A * |t| := by
            have hmul := mul_le_mul_of_nonneg_right hhalfA (abs_nonneg t)
            dsimp only [A] at hmul ⊢
            nlinarith
        _ = A * (1 + |t|) := by ring
    have hweightNorm :
        ‖suzukiSmoothCoreBurnolXiContourWeight v
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I)‖ =
          fourierEnergyDensity g t := by
      rw [suzukiSmoothCoreBurnolXiContourWeight_critical]
      dsimp only [g]
      rw [fourierAutocorrelation_apply, Complex.mul_conj]
      simp only [fourierEnergyDensity, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (Complex.normSq_nonneg _)]
    unfold suzukiSmoothCoreBurnolArchimedeanIntegrand
    have hhalf :
        (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) / 2 =
          (1 / 4 : Complex) + (t / 2 : Real) * Complex.I := by
      push_cast
      ring
    rw [hhalf, norm_mul, hweightNorm]
    have henergy : 0 ≤ fourierEnergyDensity g t :=
      fourierEnergyDensity_nonneg g t
    calc
      fourierEnergyDensity g t *
          ‖-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2‖ ≤
          fourierEnergyDensity g t * (A * (1 + |t|)) := by gcongr
      _ = A * fourierEnergyDensity g t +
          A * (|t| * fourierEnergyDensity g t) := by ring

/-- The complete Burnol Archimedean integral on the xi right vertical shifts
exactly to the critical line. -/
theorem integral_suzukiSmoothCoreBurnol_archimedean_right_eq_critical
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (∫ t : Real,
      suzukiSmoothCoreBurnolArchimedeanIntegrand v
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
      ∫ t : Real,
        suzukiSmoothCoreBurnolArchimedeanIntegrand v
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) := by
  let F : Complex → Complex := suzukiSmoothCoreBurnolArchimedeanIntegrand v
  let completeRight : Complex := ∫ t : Real,
    F (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)
  let completeLeft : Complex := ∫ t : Real,
    F (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I)
  let bottom : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F (1 / 2) (5 / 4) (-(N : Real))
  let top : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F (1 / 2) (5 / 4) (N : Real)
  let right : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F (5 / 4) (-(N : Real)) (N : Real)
  let left : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F (1 / 2) (-(N : Real)) (N : Real)
  obtain ⟨htop, hbottom⟩ :=
    tendsto_both_suzukiSmoothCoreBurnol_archimedean_horizontal_zero v
  have hbottom' : Tendsto bottom atTop (nhds 0) := by
    simpa only [bottom, F] using hbottom
  have htop' : Tendsto top atTop (nhds 0) := by
    simpa only [top, F] using htop
  have hheight : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hright : Tendsto right atTop (nhds (Complex.I * completeRight)) := by
    dsimp only [right, completeRight, F]
    unfold guinandWeilVerticalIntegral
    exact (MeasureTheory.intervalIntegral_tendsto_integral
      (by
        have h :=
          integrable_suzukiSmoothCoreBurnolXiContourWeight_archimedean_right v
        apply h.congr
        filter_upwards with t
        unfold suzukiSmoothCoreBurnolArchimedeanIntegrand
        congr 3
        push_cast
        ring)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I
  have hleft : Tendsto left atTop (nhds (Complex.I * completeLeft)) := by
    dsimp only [left, completeLeft, F]
    unfold guinandWeilVerticalIntegral
    exact (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnol_archimedean_critical v)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I
  have hcontour : Tendsto
      (fun N => bottom N - top N + right N - left N)
      atTop (nhds ((0 : Complex) - 0 + Complex.I * completeRight -
        Complex.I * completeLeft)) :=
    ((hbottom'.sub htop').add hright).sub hleft
  have hzero : Tendsto (fun _ : Nat => (0 : Complex)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hfinite :
      (fun N => bottom N - top N + right N - left N) = fun _ : Nat => 0 := by
    funext N
    have hrectangle := rectangle_suzukiSmoothCoreBurnol_archimedean_eq_zero v (N : Real)
    unfold guinandWeilRectangleIntegral at hrectangle
    dsimp only [bottom, top, right, left, F]
    convert hrectangle using 1 <;> norm_num
  rw [hfinite] at hcontour
  have hlimit := tendsto_nhds_unique hcontour hzero
  change completeRight = completeLeft
  apply mul_left_cancel₀ Complex.I_ne_zero
  exact sub_eq_zero.mp (by simpa using hlimit)

/-- The actual Burnol Archimedean right-line integral is exactly the
project-normalized literature Gamma side. -/
theorem one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_archimedean_right_eq_gamma
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (1 / Real.pi) *
        (∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((5 / 8 : Complex) +
                  (t / 2 : Real) * Complex.I) / 2)).re =
      guinandWeilLiteratureGammaSide
        (fourierAutocorrelation (suzukiProjectBase v.1)) := by
  rw [guinandWeilLiteratureGammaSide_eq_digammaIntegral]
  have hshift := integral_suzukiSmoothCoreBurnol_archimedean_right_eq_critical v
  unfold suzukiSmoothCoreBurnolArchimedeanIntegrand at hshift
  have hright :
      (fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
          (-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              ((((5 / 4 : Real) : Complex) +
                (t : Complex) * Complex.I) / 2) / 2)) =
        fun t : Real =>
          suzukiSmoothCoreBurnolXiContourWeight v
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((5 / 8 : Complex) +
                  (t / 2 : Real) * Complex.I) / 2) := by
    funext t
    congr 3
    push_cast
    ring
  have hcritical :
      (fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
            (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) *
          (-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              ((((1 / 2 : Real) : Complex) +
                (t : Complex) * Complex.I) / 2) / 2)) =
        fun t : Real =>
          fourierAutocorrelation (suzukiProjectBase v.1) t *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((1 / 4 : Complex) +
                  (t / 2 : Real) * Complex.I) / 2) := by
    funext t
    rw [suzukiSmoothCoreBurnolXiContourWeight_critical]
    congr 3
    push_cast
    ring
  rw [hright, hcritical] at hshift
  rw [hshift]
  have hcriticalInt := integrable_suzukiSmoothCoreBurnol_archimedean_critical v
  unfold suzukiSmoothCoreBurnolArchimedeanIntegrand at hcriticalInt
  rw [hcritical] at hcriticalInt
  apply congrArg (fun r : Real => (1 / Real.pi) * r)
  exact (integral_re hcriticalInt).symm

/-! ## Exact von Mangoldt evaluation -/

private theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_line
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (sigma : Real) (hsigmaLower : guinandWeilXiContourLeft ≤ sigma)
    (hsigmaUpper : sigma ≤ guinandWeilXiContourRight) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
        ((sigma : Complex) + (t : Complex) * Complex.I) := by
  obtain ⟨E, hE, hweight⟩ :=
    exists_pos_const_one_add_sq_sq_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  have hmajor : Integrable fun t : Real => E * (1 + t ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul E
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact ((differentiable_suzukiSmoothCoreBurnolXiContourWeight v).continuous.comp
      (by fun_prop)).aestronglyMeasurable
  · have hw := hweight sigma t hsigmaLower hsigmaUpper
    have hden : 0 < 1 + t ^ 2 := by positivity
    have hdenSq : 0 < (1 + t ^ 2) ^ 2 := sq_pos_of_pos hden
    have hw' :
        ‖suzukiSmoothCoreBurnolXiContourWeight v
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
            E / (1 + t ^ 2) ^ 2 := by
      rw [le_div_iff₀ hdenSq]
      simpa only [mul_comm] using hw
    rw [inv_eq_one_div]
    calc
      _ ≤ E / (1 + t ^ 2) ^ 2 := hw'
      _ ≤ E / (1 + t ^ 2) := by
        apply div_le_div_of_nonneg_left hE.le hden
        nlinarith [sq_nonneg (t ^ 2)]
      _ = E * (1 / (1 + t ^ 2)) := by ring

private def suzukiSmoothCoreBurnolMellinKernel
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u : Real) (s : Complex) : Complex :=
  suzukiSmoothCoreBurnolXiContourWeight v s *
    Complex.exp (-(u : Complex) * s)

private theorem differentiable_suzukiSmoothCoreBurnolMellinKernel
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (u : Real) :
    Differentiable Complex (suzukiSmoothCoreBurnolMellinKernel v u) := by
  unfold suzukiSmoothCoreBurnolMellinKernel
  exact (differentiable_suzukiSmoothCoreBurnolXiContourWeight v).mul
    ((differentiable_id.const_mul (-(u : Complex))).cexp)

private theorem norm_suzukiSmoothCoreBurnolMellinExponential_le_one
    {u sigma T : Real} (hu : 0 ≤ u) (hsigma : 1 / 2 ≤ sigma) :
    ‖Complex.exp (-(u : Complex) *
      ((sigma : Complex) + (T : Complex) * Complex.I))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre :
      (-(u : Complex) *
        ((sigma : Complex) + (T : Complex) * Complex.I)).re = -(u * sigma) := by
    simp [Complex.mul_re]
  rw [hre]
  have hsigma0 : 0 ≤ sigma := by linarith
  exact Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg hu hsigma0))

private theorem integrable_suzukiSmoothCoreBurnolMellinKernel_line
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u sigma : Real) (hu : 0 ≤ u)
    (hsigmaHalf : 1 / 2 ≤ sigma)
    (hsigmaLower : guinandWeilXiContourLeft ≤ sigma)
    (hsigmaUpper : sigma ≤ guinandWeilXiContourRight) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolMellinKernel v u
        ((sigma : Complex) + (t : Complex) * Complex.I) := by
  have hbase := integrable_suzukiSmoothCoreBurnolXiContourWeight_line
    v sigma hsigmaLower hsigmaUpper
  unfold suzukiSmoothCoreBurnolMellinKernel
  have hmeas : AEStronglyMeasurable (fun t : Real =>
      Complex.exp (-(u : Complex) *
        ((sigma : Complex) + (t : Complex) * Complex.I))) := by
    fun_prop
  have hmul := hbase.bdd_mul (c := 1) hmeas
    (Eventually.of_forall fun t =>
      norm_suzukiSmoothCoreBurnolMellinExponential_le_one hu hsigmaHalf)
  simpa only [mul_comm] using hmul

private theorem rectangle_suzukiSmoothCoreBurnolMellinKernel_eq_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u T : Real) :
    guinandWeilRectangleIntegral
        (suzukiSmoothCoreBurnolMellinKernel v u)
        (((1 / 2 : Real) : Complex) - (T : Complex) * Complex.I)
        (((5 / 4 : Real) : Complex) + (T : Complex) * Complex.I) = 0 :=
  guinandWeilRectangleIntegral_eq_zero_of_differentiableOn
    (differentiable_suzukiSmoothCoreBurnolMellinKernel v u).differentiableOn

private theorem norm_suzukiSmoothCoreBurnolMellinKernel_horizontal_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u C T : Real) (hu : 0 ≤ u) (hC : 0 ≤ C) (hT : 1 ≤ |T|)
    (hweight : ∀ sigma : Real,
      guinandWeilXiContourLeft ≤ sigma →
      sigma ≤ guinandWeilXiContourRight →
      |T| ^ 5 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ C) :
    ‖guinandWeilHorizontalIntegral
        (suzukiSmoothCoreBurnolMellinKernel v u)
        (1 / 2) (5 / 4) T‖ ≤ 3 * C / (4 * |T| ^ 5) := by
  have hTabs : 0 < |T| := zero_lt_one.trans_le hT
  have hden : 0 < |T| ^ 5 := pow_pos hTabs 5
  unfold guinandWeilHorizontalIntegral
  calc
    ‖∫ sigma in (1 / 2 : Real)..(5 / 4 : Real),
        suzukiSmoothCoreBurnolMellinKernel v u
          ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
        (C / |T| ^ 5) * |(5 / 4 : Real) - 1 / 2| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro sigma hsigma
      have hsigma' := Set.uIoc_subset_uIcc hsigma
      rw [Set.uIcc_of_le (by norm_num)] at hsigma'
      have hw := hweight sigma
        (by norm_num [guinandWeilXiContourLeft]; linarith [hsigma'.1])
        (by norm_num [guinandWeilXiContourRight]; linarith [hsigma'.2])
      have hw' :
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
              C / |T| ^ 5 := by
        rw [le_div_iff₀ hden]
        simpa only [mul_comm] using hw
      unfold suzukiSmoothCoreBurnolMellinKernel
      rw [norm_mul]
      have hexp := norm_suzukiSmoothCoreBurnolMellinExponential_le_one
        (u := u) (sigma := sigma) (T := T) hu hsigma'.1
      calc
        _ ≤ (C / |T| ^ 5) * 1 :=
          mul_le_mul hw' hexp (norm_nonneg _) (by positivity)
        _ = C / |T| ^ 5 := by ring
    _ = _ := by ring

private theorem tendsto_both_suzukiSmoothCoreBurnolMellinKernel_horizontal_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u : Real) (hu : 0 ≤ u) :
    Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolMellinKernel v u)
          (1 / 2) (5 / 4) (N : Real))
        atTop (nhds 0) ∧
      Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolMellinKernel v u)
          (1 / 2) (5 / 4) (-(N : Real)))
        atTop (nhds 0) := by
  obtain ⟨C, hC, hweight⟩ :=
    exists_pos_const_abs_pow_five_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  let M : Nat → Real := fun N => (3 * C / 4) / (N : Real)
  have hM : Tendsto M atTop (nhds 0) := by
    simpa only [M] using tendsto_const_div_atTop_nhds_zero_nat (3 * C / 4)
  have hmajor (sign : Real) (hsign : |sign| = 1) :
      ∀ᶠ N : Nat in atTop,
        ‖guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolMellinKernel v u)
          (1 / 2) (5 / 4) (sign * (N : Real))‖ ≤ M N := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hN => hN⟩] with N hN
    have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
    have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNreal
    have hTN : |sign * (N : Real)| = (N : Real) := by
      rw [abs_mul, hsign, one_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    have hbound := norm_suzukiSmoothCoreBurnolMellinKernel_horizontal_le
      v u C (sign * (N : Real)) hu hC.le
      (by simpa [hTN] using hNreal) (hweight (T := sign * (N : Real)))
    rw [hTN] at hbound
    exact hbound.trans (by
      dsimp only [M]
      have hscalar : 0 ≤ 3 * C / 4 := by positivity
      have hpow : (N : Real) ≤ (N : Real) ^ 5 := by
        nlinarith [sq_nonneg ((N : Real) ^ 2 - 1),
          mul_self_nonneg ((N : Real) ^ 2)]
      calc
        3 * C / (4 * (N : Real) ^ 5) =
            (3 * C / 4) / (N : Real) ^ 5 := by ring
        _ ≤ (3 * C / 4) / (N : Real) :=
          div_le_div_of_nonneg_left hscalar hNpos hpow)
  have htendsto (sign : Real) (hsign : |sign| = 1) :
      Tendsto
        (fun N : Nat => guinandWeilHorizontalIntegral
          (suzukiSmoothCoreBurnolMellinKernel v u)
          (1 / 2) (5 / 4) (sign * (N : Real)))
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      (hmajor sign hsign) hM
  constructor
  · simpa only [one_mul] using htendsto 1 (by norm_num)
  · simpa only [neg_one_mul] using htendsto (-1) (by norm_num)

private theorem integral_suzukiSmoothCoreBurnolMellinKernel_right_eq_critical
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u : Real) (hu : 0 ≤ u) :
    (∫ t : Real,
      suzukiSmoothCoreBurnolMellinKernel v u
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
      ∫ t : Real,
        suzukiSmoothCoreBurnolMellinKernel v u
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) := by
  let F : Complex → Complex := suzukiSmoothCoreBurnolMellinKernel v u
  let completeRight : Complex := ∫ t : Real,
    F (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)
  let completeLeft : Complex := ∫ t : Real,
    F (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I)
  let bottom : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F (1 / 2) (5 / 4) (-(N : Real))
  let top : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F (1 / 2) (5 / 4) (N : Real)
  let right : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F (5 / 4) (-(N : Real)) (N : Real)
  let left : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F (1 / 2) (-(N : Real)) (N : Real)
  obtain ⟨htop, hbottom⟩ :=
    tendsto_both_suzukiSmoothCoreBurnolMellinKernel_horizontal_zero v u hu
  have hbottom' : Tendsto bottom atTop (nhds 0) := by
    simpa only [bottom, F] using hbottom
  have htop' : Tendsto top atTop (nhds 0) := by
    simpa only [top, F] using htop
  have hheight : Tendsto (fun N : Nat => (N : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hright : Tendsto right atTop (nhds (Complex.I * completeRight)) := by
    dsimp only [right, completeRight, F]
    unfold guinandWeilVerticalIntegral
    exact (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnolMellinKernel_line v u (5 / 4) hu
        (by norm_num)
        (by norm_num [guinandWeilXiContourLeft])
        (by norm_num [guinandWeilXiContourRight]))
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I
  have hleft : Tendsto left atTop (nhds (Complex.I * completeLeft)) := by
    dsimp only [left, completeLeft, F]
    unfold guinandWeilVerticalIntegral
    exact (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnolMellinKernel_line v u (1 / 2) hu
        (by norm_num)
        (by norm_num [guinandWeilXiContourLeft])
        (by norm_num [guinandWeilXiContourRight]))
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I
  have hcontour : Tendsto
      (fun N => bottom N - top N + right N - left N)
      atTop (nhds ((0 : Complex) - 0 + Complex.I * completeRight -
        Complex.I * completeLeft)) :=
    ((hbottom'.sub htop').add hright).sub hleft
  have hzero : Tendsto (fun _ : Nat => (0 : Complex)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hfinite :
      (fun N => bottom N - top N + right N - left N) = fun _ : Nat => 0 := by
    funext N
    have hrectangle := rectangle_suzukiSmoothCoreBurnolMellinKernel_eq_zero
      v u (N : Real)
    unfold guinandWeilRectangleIntegral at hrectangle
    dsimp only [bottom, top, right, left, F]
    convert hrectangle using 1 <;> norm_num
  rw [hfinite] at hcontour
  have hlimit := tendsto_nhds_unique hcontour hzero
  change completeRight = completeLeft
  apply mul_left_cancel₀ Complex.I_ne_zero
  exact sub_eq_zero.mp (by simpa using hlimit)

private theorem integral_suzukiSmoothCoreBurnolMellinKernel_right_eq_fourier
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (u : Real) (hu : 0 ≤ u) :
    (∫ t : Real,
      suzukiSmoothCoreBurnolMellinKernel v u
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
      Complex.exp ((-(u / 2) : Real) : Complex) *
        FourierTransform.fourier
          (fun t : Real =>
            fourierAutocorrelation (suzukiProjectBase v.1) t)
          (u / (2 * Real.pi)) := by
  rw [integral_suzukiSmoothCoreBurnolMellinKernel_right_eq_critical v u hu]
  have hpointwise :
      (fun t : Real =>
        suzukiSmoothCoreBurnolMellinKernel v u
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I)) =
        fun t : Real =>
          Complex.exp ((-(u / 2) : Real) : Complex) *
            (fourierAutocorrelation (suzukiProjectBase v.1) t *
              Complex.exp (-Complex.I * (u : Complex) * (t : Complex))) := by
    funext t
    unfold suzukiSmoothCoreBurnolMellinKernel
    rw [suzukiSmoothCoreBurnolXiContourWeight_critical]
    rw [show -(u : Complex) *
          (((1 / 2 : Real) : Complex) + (t : Complex) * Complex.I) =
        ((-(u / 2) : Real) : Complex) +
          (-Complex.I * (u : Complex) * (t : Complex)) by
      apply Complex.ext <;> simp <;> ring]
    rw [Complex.exp_add]
    ring
  rw [hpointwise, MeasureTheory.integral_const_mul]
  congr 1
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  apply congrArg Complex.exp
  push_cast
  field_simp [Real.pi_ne_zero]

private def suzukiSmoothCoreBurnolVonMangoldtComplex (n : Nat) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex)

private def suzukiSmoothCoreBurnolXiRightPrimeIntegrand
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (n : Nat) (t : Real) : Complex :=
  suzukiSmoothCoreBurnolXiContourWeight v
      (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
    LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
      (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) n

private theorem integral_suzukiSmoothCoreBurnolXiRightPrimeIntegrand_eq_fourier
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (n : Nat) :
    (∫ t : Real, suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n t) =
      (ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp
          ((-(1 / 2 : Real) * Real.log (n : Real) : Real) : Complex) *
        FourierTransform.fourier
          (fun t : Real => fourierAutocorrelation (suzukiProjectBase v.1) t)
          (Real.log (n : Real) / (2 * Real.pi)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [suzukiSmoothCoreBurnolXiRightPrimeIntegrand,
      suzukiSmoothCoreBurnolVonMangoldtComplex]
  · have hncast : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hnOne : (1 : Real) ≤ (n : Real) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hterm (t : Real) :
        LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) n =
          (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-(Real.log (n : Real) : Complex) *
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) := by
      rw [LSeries.term_of_ne_zero hn,
        suzukiSmoothCoreBurnolVonMangoldtComplex,
        Complex.cpow_def_of_ne_zero hncast]
      rw [← Complex.natCast_log, div_eq_mul_inv, ← Complex.exp_neg]
      ring
    have hintegrand :
        suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n = fun t : Real =>
          (ArithmeticFunction.vonMangoldt n : Complex) *
            suzukiSmoothCoreBurnolMellinKernel v (Real.log (n : Real))
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) := by
      funext t
      rw [suzukiSmoothCoreBurnolXiRightPrimeIntegrand, hterm]
      unfold suzukiSmoothCoreBurnolMellinKernel
      ring
    rw [hintegrand, MeasureTheory.integral_const_mul,
      integral_suzukiSmoothCoreBurnolMellinKernel_right_eq_fourier v
        (Real.log (n : Real)) (Real.log_nonneg hnOne)]
    ring

private theorem integral_suzukiSmoothCoreBurnolXiRightPrimeIntegrand_eq_invSqrt_fourier
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (n : Nat) :
    (∫ t : Real, suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n t) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
        FourierTransform.fourier
          (fun t : Real => fourierAutocorrelation (suzukiProjectBase v.1) t)
          (Real.log (n : Real) / (2 * Real.pi)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [suzukiSmoothCoreBurnolXiRightPrimeIntegrand]
  · rw [integral_suzukiSmoothCoreBurnolXiRightPrimeIntegrand_eq_fourier,
      exp_neg_half_log_natCast_eq_inv_sqrt n hn]
    push_cast
    ring

private theorem norm_suzukiSmoothCoreBurnolVonMangoldt_term_rightLine
    (n : Nat) (t : Real) :
    ‖LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) n‖ =
      ‖LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
        ((5 / 4 : Real) : Complex) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

private theorem integrable_suzukiSmoothCoreBurnolXiRightPrimeIntegrand
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (n : Nat) :
    Integrable (suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n) := by
  let c : Real := ‖LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
    ((5 / 4 : Real) : Complex) n‖
  have hsource := integrable_suzukiSmoothCoreBurnolXiContourWeight_line
    v (5 / 4)
      (by norm_num [guinandWeilXiContourLeft])
      (by norm_num [guinandWeilXiContourRight])
  have hmajor : Integrable fun t : Real =>
      c * ‖suzukiSmoothCoreBurnolXiContourWeight v
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖ :=
    hsource.norm.const_mul c
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hterm : Continuous fun t : Real =>
        LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) n := by
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero]
        exact continuous_const
      · simp only [LSeries.term_of_ne_zero hn]
        have hpow : Continuous fun t : Real =>
            (n : Complex) ^
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) := by
          simp_rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
          fun_prop
        apply Continuous.div continuous_const hpow
        intro t
        exact Complex.cpow_ne_zero_iff.mpr
          (Or.inl (Nat.cast_ne_zero.mpr hn))
    have hsourceContinuous : Continuous fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
          (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) :=
      (differentiable_suzukiSmoothCoreBurnolXiContourWeight v).continuous.comp
        (by fun_prop)
    exact (hsourceContinuous.mul hterm).aestronglyMeasurable
  · simp only [suzukiSmoothCoreBurnolXiRightPrimeIntegrand, norm_mul]
    rw [norm_suzukiSmoothCoreBurnolVonMangoldt_term_rightLine]
    dsimp only [c]
    rw [mul_comm]

private theorem integral_norm_suzukiSmoothCoreBurnolXiRightPrimeIntegrand
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (n : Nat) :
    (∫ t : Real, ‖suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n t‖) =
      ‖LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
          ((5 / 4 : Real) : Complex) n‖ *
        ∫ t : Real,
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖ := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [suzukiSmoothCoreBurnolXiRightPrimeIntegrand, norm_mul,
    norm_suzukiSmoothCoreBurnolVonMangoldt_term_rightLine]
  ring

private theorem summable_integral_norm_suzukiSmoothCoreBurnolXiRightPrimeIntegrand
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Summable fun n : Nat =>
      ∫ t : Real, ‖suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n t‖ := by
  have hs : LSeriesSummable suzukiSmoothCoreBurnolVonMangoldtComplex
      ((5 / 4 : Real) : Complex) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  have hnorm : Summable fun n : Nat =>
      ‖LSeries.term suzukiSmoothCoreBurnolVonMangoldtComplex
        ((5 / 4 : Real) : Complex) n‖ :=
    summable_norm_iff.mpr hs
  have hmul := hnorm.mul_right
    (∫ t : Real,
      ‖suzukiSmoothCoreBurnolXiContourWeight v
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)‖)
  simpa only [integral_norm_suzukiSmoothCoreBurnolXiRightPrimeIntegrand]
    using hmul

private theorem integral_suzukiSmoothCoreBurnolXiContourWeight_mul_vonMangoldtLSeries_eq_tsum
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (∫ t : Real,
        suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
          LSeries suzukiSmoothCoreBurnolVonMangoldtComplex
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
      ∑' n : Nat,
        ∫ t : Real, suzukiSmoothCoreBurnolXiRightPrimeIntegrand v n t := by
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm
    (integrable_suzukiSmoothCoreBurnolXiRightPrimeIntegrand v)
    (summable_integral_norm_suzukiSmoothCoreBurnolXiRightPrimeIntegrand v)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [suzukiSmoothCoreBurnolXiRightPrimeIntegrand, LSeries]
  rw [← tsum_mul_left]

private theorem summable_suzukiSmoothCoreBurnol_invSqrt_mul_fourier
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Summable fun n : Nat =>
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
        FourierTransform.fourier
          (fun t : Real => fourierAutocorrelation (suzukiProjectBase v.1) t)
          (Real.log (n : Real) / (2 * Real.pi)) := by
  refine
    (summable_integral_norm_suzukiSmoothCoreBurnolXiRightPrimeIntegrand v).of_norm_bounded
      (fun n => ?_)
  rw [← integral_suzukiSmoothCoreBurnolXiRightPrimeIntegrand_eq_invSqrt_fourier]
  exact norm_integral_le_integral_norm _

private theorem integral_suzukiSmoothCoreBurnolXiContourWeight_mul_vonMangoldtLSeries_eq_primeFourierTsum
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (∫ t : Real,
        suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
          LSeries suzukiSmoothCoreBurnolVonMangoldtComplex
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
      ∑' n : Nat,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
          FourierTransform.fourier
            (fun t : Real => fourierAutocorrelation (suzukiProjectBase v.1) t)
            (Real.log (n : Real) / (2 * Real.pi)) := by
  rw [integral_suzukiSmoothCoreBurnolXiContourWeight_mul_vonMangoldtLSeries_eq_tsum]
  apply tsum_congr
  intro n
  exact integral_suzukiSmoothCoreBurnolXiRightPrimeIntegrand_eq_invSqrt_fourier v n

private theorem conj_autocorrelation_neg_schwartz
    (g : SchwartzLineTestFunction) (x : Real) :
    conj (autocorrelation g (-x)) = autocorrelation g x := by
  rw [autocorrelation_apply, autocorrelation_apply,
    MeasureTheory.convolution_def, MeasureTheory.convolution_def,
    ← integral_conj]
  calc
    (∫ t : Real, conj (g t * star g (-x - t))) =
        ∫ t : Real,
          (fun y : Real => g y * conj (g (y - x))) (t + x) := by
      apply integral_congr_ae
      filter_upwards with t
      have hneg : -(-x - t) = t + x := by ring
      have hsub : t + x - x = t := by ring
      simp [star_apply, hneg, hsub]
      ring
    _ = ∫ y : Real, g y * conj (g (y - x)) := by
      exact integral_add_right_eq_self
        (fun y : Real => g y * conj (g (y - x))) x
    _ = ∫ t : Real, g t * star g (x - t) := by
      apply integral_congr_ae
      filter_upwards with t
      have hneg : -(x - t) = t - x := by ring
      simp [star_apply, hneg]

/-- The actual Burnol von Mangoldt right-line integral is exactly the
project-normalized literature prime side. -/
theorem neg_one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_vonMangoldtLSeries_right_eq_prime
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    -(1 / Real.pi) *
        (∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
            LSeries (fun n : Nat =>
                (ArithmeticFunction.vonMangoldt n : Complex))
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)).re =
      guinandWeilLiteraturePrimeSide
        (fourierAutocorrelation (suzukiProjectBase v.1)) := by
  let f : SchwartzLineTestFunction :=
    fourierAutocorrelation (suzukiProjectBase v.1)
  let term : Nat → Complex := fun n =>
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real) : Real) : Complex) *
      FourierTransform.fourier (fun t : Real => f t)
        (Real.log (n : Real) / (2 * Real.pi))
  have hsum : Summable term := by
    simpa only [term, f] using
      summable_suzukiSmoothCoreBurnol_invSqrt_mul_fourier v
  have hintegral :
      (∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
            LSeries (fun n : Nat =>
                (ArithmeticFunction.vonMangoldt n : Complex))
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
        ∑' n : Nat, term n := by
    change
      (∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
            LSeries suzukiSmoothCoreBurnolVonMangoldtComplex
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
        ∑' n : Nat, term n
    simpa only [term, f] using
      integral_suzukiSmoothCoreBurnolXiContourWeight_mul_vonMangoldtLSeries_eq_primeFourierTsum v
  rw [hintegral, Complex.re_tsum hsum]
  rw [guinandWeilLiteraturePrimeSide, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [guinandWeilLiteraturePrimeTerm]
  let x : Real := Real.log (n : Real) / (2 * Real.pi)
  have hnegRe :
      ((SchwartzLineTestFunction.fourier f) (-x)).re =
        ((SchwartzLineTestFunction.fourier f) x).re := by
    dsimp only [f]
    change
      ((𝓕 (fourierAutocorrelation (suzukiProjectBase v.1))) (-x)).re =
        ((𝓕 (fourierAutocorrelation (suzukiProjectBase v.1))) x).re
    rw [fourier_fourierAutocorrelation_apply,
      fourier_fourierAutocorrelation_apply]
    have hsym := congrArg Complex.re
      (conj_autocorrelation_neg_schwartz (suzukiProjectBase v.1) x)
    simp only [Complex.conj_re] at hsym
    simpa using hsym.symm
  rw [show -Real.log (n : Real) / (2 * Real.pi) = -x by
      simp only [x]
      ring,
    show Real.log (n : Real) / (2 * Real.pi) = x by rfl,
    hnegRe]
  have hfourier :
      FourierTransform.fourier (fun t : Real => f t) x =
        (SchwartzLineTestFunction.fourier f) x := by rfl
  simp only [term]
  rw [show Real.log (n : Real) / (2 * Real.pi) = x by rfl, hfourier]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  ring

/-- The complete actual Burnol xi right vertical is exactly the checked
prime/pole/Gamma literature residual for the project base test. -/
theorem one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_logDeriv_riemannXi_right_eq_residual
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (1 / Real.pi) *
        (∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
            logDeriv riemannXi
              (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)).re =
      guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v.1) := by
  let R : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
      (1 / (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) +
        1 / (((1 / 4 : Real) : Complex) + (t : Complex) * Complex.I))
  let A : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
      (-(Real.log Real.pi : Complex) / 2 +
        Complex.digamma
          (((5 / 8 : Real) : Complex) +
            (t / 2 : Real) * Complex.I) / 2)
  let P : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
      LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex))
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)
  have hR : Integrable R :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_rational_right v
  have hA : Integrable A :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_archimedean_right v
  have hP : Integrable P :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_vonMangoldtLSeries_right v
  have hpointwise :
      (fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
          logDeriv riemannXi
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
        fun t => R t + A t - P t := by
    funext t
    have hdecomp :=
      logDeriv_riemannXi_eq_rightHalfPlaneLiteratureTerms
        (s := (((5 / 4 : Real) : Complex) +
          (t : Complex) * Complex.I)) (by norm_num)
    have hsub :
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) - 1 =
          ((1 / 4 : Real) : Complex) + (t : Complex) * Complex.I := by
      push_cast
      ring
    have hhalf :
        (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) / 2 =
          ((5 / 8 : Real) : Complex) +
            (t / 2 : Real) * Complex.I := by
      push_cast
      ring
    rw [hsub, hhalf] at hdecomp
    dsimp only [R, A, P]
    rw [hdecomp]
    ring
  have hintegral :
      (∫ t : Real,
        suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
          logDeriv riemannXi
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I)) =
        (∫ t : Real, R t) + (∫ t : Real, A t) - (∫ t : Real, P t) := by
    rw [hpointwise]
    calc
      (∫ t : Real, R t + A t - P t) =
          (∫ t : Real, R t + A t) - (∫ t : Real, P t) :=
        MeasureTheory.integral_sub (hR.add hA) hP
      _ = (∫ t : Real, R t) + (∫ t : Real, A t) -
          (∫ t : Real, P t) := by
        rw [MeasureTheory.integral_add hR hA]
  have hpole :=
    one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_rational_right_eq_pole v
  have hgamma :=
    one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_archimedean_right_eq_gamma v
  have hprime :=
    neg_one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_vonMangoldtLSeries_right_eq_prime v
  rw [hintegral, Complex.sub_re, Complex.add_re]
  change (1 / Real.pi) *
      ((∫ t : Real, R t).re + (∫ t : Real, A t).re -
        (∫ t : Real, P t).re) = _
  change (1 / Real.pi) * (∫ t : Real, R t).re =
      guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v.1) at hpole
  have hAeq :
      (fun t : Real => A t) = fun t : Real =>
        suzukiSmoothCoreBurnolXiContourWeight v
            (((5 / 4 : Real) : Complex) + (t : Complex) * Complex.I) *
          (-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              ((5 / 8 : Complex) +
                (t / 2 : Real) * Complex.I) / 2) := by
    funext t
    dsimp only [A]
    congr 4
    norm_num
  rw [← hAeq] at hgamma
  change -(1 / Real.pi) * (∫ t : Real, P t).re =
      guinandWeilLiteraturePrimeSide
        (fourierAutocorrelation (suzukiProjectBase v.1)) at hprime
  unfold guinandWeilBurnolLiteratureResidualSide
  linear_combination hpole + hgamma + hprime

end

end RiemannHypothesisProject.Experiments.M100
