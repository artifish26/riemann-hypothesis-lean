import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaBurnolHorizontalDecay
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVertical
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.DigammaFormula
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# M100-DF6F vertical limits for the Burnol xi contour

This module proves convergence of the two actual Burnol vertical contour
integrals. Compact-support transform decay is combined with a direct
right-half-plane bound for the xi logarithmic derivative.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set Filter MeasureTheory Topology
open SchwartzLineTestFunction
open ComplexCompactExhaustion

private theorem one_add_sq_sq_le_four_mul_one_add_abs_pow_five (T : Real) :
    (1 + T ^ 2) ^ 2 ≤ 4 * (1 + |T| ^ 5) := by
  have ha : 0 ≤ |T| := abs_nonneg T
  have hsq : |T| ^ 2 = T ^ 2 := sq_abs T
  by_cases hsmall : |T| ≤ 1
  · have h2 : |T| ^ 2 ≤ 1 := by nlinarith
    have h4 : |T| ^ 4 ≤ 1 := by
      calc
        |T| ^ 4 = (|T| ^ 2) ^ 2 := by ring
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h2 2
        _ = 1 := by norm_num
    rw [← hsq]
    nlinarith [pow_nonneg ha 5]
  · have hlarge : 1 ≤ |T| := le_of_not_ge hsmall
    have h2 : |T| ^ 2 ≤ |T| ^ 5 :=
      pow_le_pow_right₀ hlarge (by omega)
    have h4 : |T| ^ 4 ≤ |T| ^ 5 :=
      pow_le_pow_right₀ hlarge (by omega)
    have h1 : 1 ≤ |T| ^ 5 := by
      simpa using (pow_le_pow_left₀ zero_le_one hlarge 5)
    rw [← hsq]
    nlinarith

/-- The actual Burnol contour weight has a globally integrable fourth-order
majorant, uniformly across the fixed xi strip. -/
theorem exists_pos_const_one_add_sq_sq_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    ∃ E : Real, 0 < E ∧ ∀ sigma T : Real,
      guinandWeilXiContourLeft ≤ sigma →
      sigma ≤ guinandWeilXiContourRight →
      (1 + T ^ 2) ^ 2 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ E := by
  obtain ⟨C, hC, hfive⟩ :=
    exists_pos_const_abs_pow_five_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  let w : SchwartzLineTestFunction := autocorrelation v.1
  let a : Real := 2 * suzukiProjectAStar
  let D : Real := Real.exp a * ∫ x : Real, ‖w x‖
  let E : Real := 4 * (D + C + 1)
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact mul_nonneg (by norm_num) suzukiProjectAStar_pos.le
  have hsupport : Function.support w ⊆ Icc (-a) a := by
    dsimp only [w, a]
    exact support_autocorrelation_subset_Icc_two_mul
      suzukiProjectAStar_pos.le
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity
  have hE : 0 < E := by
    dsimp only [E]
    positivity
  refine ⟨E, hE, ?_⟩
  intro sigma T hsigmaLower hsigmaUpper
  let z : Complex :=
    ((((sigma : Complex) + (T : Complex) * Complex.I) -
      (1 / 2 : Complex)) / Complex.I)
  have hzIm : |z.im| ≤ 1 := by
    have hcoordinate := guinandWeilXiContourCoordinate_horizontal sigma T
    dsimp only [z]
    rw [hcoordinate]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      zero_add]
    rw [abs_le]
    constructor
    · norm_num [guinandWeilXiContourRight] at hsigmaUpper ⊢
      linarith
    · norm_num [guinandWeilXiContourLeft] at hsigmaLower ⊢
      linarith
  have hbase :
      ‖suzukiSmoothCoreBurnolXiContourWeight v
        ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ D := by
    rw [show suzukiSmoothCoreBurnolXiContourWeight v
        ((sigma : Complex) + (T : Complex) * Complex.I) =
          suzukiFourierSource w z by
      rw [suzukiSmoothCoreBurnolXiContourWeight]
      exact burnolFourierLaplaceSource_suzukiProjectBase v.1 _]
    simpa only [D] using
      (norm_suzukiFourierSource_le_of_support_subset_Icc
        ha hsupport hzIm)
  have hfiveT := hfive sigma T hsigmaLower hsigmaUpper
  have hweight0 : 0 ≤
      ‖suzukiSmoothCoreBurnolXiContourWeight v
        ((sigma : Complex) + (T : Complex) * Complex.I)‖ := norm_nonneg _
  calc
    (1 + T ^ 2) ^ 2 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
        4 * (1 + |T| ^ 5) *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ := by
      gcongr
      exact one_add_sq_sq_le_four_mul_one_add_abs_pow_five T
    _ = 4 *
        (‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ +
          |T| ^ 5 *
            ‖suzukiSmoothCoreBurnolXiContourWeight v
              ((sigma : Complex) + (T : Complex) * Complex.I)‖) := by ring
    _ ≤ 4 * (D + C) := by gcongr
    _ ≤ E := by dsimp only [E]; linarith

private theorem norm_log_fiveEighthsLine_le (t : Real) :
    ‖Complex.log
        ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I)‖ ≤
      |t| + (|Real.log (5 / 8)| + Real.pi) := by
  let z : Complex := (5 / 8 : Complex) + (t / 2 : Real) * Complex.I
  have hzre : z.re = 5 / 8 := by simp [z]
  have hnormLower : (5 / 8 : Real) ≤ ‖z‖ := by
    calc
      (5 / 8 : Real) = |z.re| := by rw [hzre]; norm_num
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hnormPos : 0 < ‖z‖ :=
    (by norm_num : (0 : Real) < 5 / 8).trans_le hnormLower
  have hnormUpper : ‖z‖ ≤ 1 + |t| := by
    calc
      ‖(5 / 8 : Complex) + (t / 2 : Real) * Complex.I‖ ≤
          ‖(5 / 8 : Complex)‖ +
            ‖((t / 2 : Real) : Complex) * Complex.I‖ := norm_add_le _ _
      _ = (5 / 8 : Real) + |t| / 2 := by
        rw [norm_mul]
        simp [abs_div]
      _ ≤ 1 + |t| := by nlinarith [abs_nonneg t]
  have hlogLower : Real.log (5 / 8) ≤ Real.log ‖z‖ :=
    Real.log_le_log (by norm_num) hnormLower
  have hlogUpper : Real.log ‖z‖ ≤ |t| := by
    have hlog := Real.log_le_sub_one_of_pos hnormPos
    linarith
  have habsLog : |Real.log ‖z‖| ≤ |Real.log (5 / 8)| + |t| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (5 / 8)), abs_nonneg t]
    · linarith [abs_nonneg (Real.log (5 / 8))]
  have harg := Complex.abs_arg_le_pi z
  unfold Complex.log
  calc
    ‖((Real.log ‖z‖ : Real) : Complex) + (z.arg : Complex) * Complex.I‖ ≤
        ‖((Real.log ‖z‖ : Real) : Complex)‖ +
          ‖(z.arg : Complex) * Complex.I‖ := norm_add_le _ _
    _ = |Real.log ‖z‖| + |z.arg| := by rw [norm_mul]; simp
    _ ≤ |t| + (|Real.log (5 / 8)| + Real.pi) := by linarith

private theorem norm_bennettGammaBinetIntegral_fiveEighthsLine_le
    (t : Real) :
    ‖bennettGammaBinetIntegral
        ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I)‖ ≤
      (4 / 5 : Real) := by
  let z : Complex := (5 / 8 : Complex) + (t / 2 : Real) * Complex.I
  rw [bennettGammaBinetIntegral]
  calc
    ‖∫ x : Real in Ioi 0,
        bennettGammaBinetKernel x * Complex.exp (-(x : Complex) * z)‖ ≤
        ∫ x : Real in Ioi 0,
          (1 / 2 : Real) * Real.exp (-(5 / 8 : Real) * x) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_exp_mul_Ioi
          (a := -(5 / 8 : Real)) (by norm_num) 0).const_mul (1 / 2 : Real))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, norm_bennettGammaBinetLaplaceFactor]
      have hk := norm_bennettGammaBinetKernel_le_one_half_of_pos hx
      have hzre : z.re = 5 / 8 := by simp [z]
      rw [hzre]
      have hexponent : -(5 / 8 : Real) * x = -(x * (5 / 8 : Real)) := by
        ring
      rw [hexponent]
      simpa only [mul_comm] using
        mul_le_mul_of_nonneg_right hk
          (Real.exp_pos (-(x * (5 / 8 : Real)))).le
    _ = 4 / 5 := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (a := -(5 / 8 : Real)) (by norm_num) 0]
      norm_num

private theorem norm_digamma_fiveEighthsLine_le (t : Real) :
    ‖Complex.digamma
        ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I)‖ ≤
      |t| + (|Real.log (5 / 8)| + Real.pi + 2) := by
  let z : Complex := (5 / 8 : Complex) + (t / 2 : Real) * Complex.I
  have hz : 0 < z.re := by simp [z]
  rw [bennettGammaBinetDigammaFormula z hz]
  have hlog : ‖Complex.log z‖ ≤
      |t| + (|Real.log (5 / 8)| + Real.pi) := by
    simpa only [z] using norm_log_fiveEighthsLine_le t
  have hinv : ‖1 / (2 * z)‖ ≤ (4 / 5 : Real) := by
    have hnorm : (5 / 8 : Real) ≤ ‖z‖ := by
      calc
        (5 / 8 : Real) = |z.re| := by
          simp [z, abs_of_pos (by norm_num : (0 : Real) < 5 / 8)]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    rw [norm_div, norm_one, norm_mul]
    norm_num only [Complex.norm_ofNat]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hrem : ‖bennettGammaBinetIntegral z‖ ≤ (4 / 5 : Real) := by
    simpa only [z] using norm_bennettGammaBinetIntegral_fiveEighthsLine_le t
  calc
    ‖Complex.log z - 1 / (2 * z) - bennettGammaBinetIntegral z‖ ≤
        ‖Complex.log z‖ + ‖1 / (2 * z)‖ +
          ‖bennettGammaBinetIntegral z‖ := by
      exact (norm_sub_le _ _).trans
        (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ |t| + (|Real.log (5 / 8)| + Real.pi + 2) := by linarith

private theorem norm_vonMangoldt_term_rightLine
    (n : Nat) (t : Real) :
    ‖LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        ((5 / 4 : Real) + (t : Complex) * Complex.I) n‖ =
      ‖LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (5 / 4 : Real) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp

/-- The von Mangoldt series is uniformly bounded on the complete Burnol
right line. -/
theorem exists_pos_const_norm_vonMangoldtLSeries_right_le :
    ∃ C : Real, 0 < C ∧ ∀ t : Real,
      ‖LSeries
          (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex))
          ((5 / 4 : Real) + (t : Complex) * Complex.I)‖ ≤ C := by
  let C : Real := ∑' n : Nat,
    ‖LSeries.term
      (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
      (5 / 4 : Real) n‖
  have hsNorm : Summable fun n : Nat =>
      ‖LSeries.term
        (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
        (5 / 4 : Real) n‖ := by
    exact summable_norm_iff.mpr
      (ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num))
  have hC : 0 ≤ C := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨C + 1, by linarith, ?_⟩
  intro t
  have hs : LSeriesSummable
      (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex))
      ((5 / 4 : Real) + (t : Complex) * Complex.I) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by norm_num)
  rw [LSeries]
  calc
    ‖∑' n : Nat,
        LSeries.term
          (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
          ((5 / 4 : Real) + (t : Complex) * Complex.I) n‖ ≤
        ∑' n : Nat,
          ‖LSeries.term
            (fun m : Nat => (ArithmeticFunction.vonMangoldt m : Complex))
            ((5 / 4 : Real) + (t : Complex) * Complex.I) n‖ :=
      norm_tsum_le_tsum_norm (summable_norm_iff.mpr hs)
    _ = C := by
      apply tsum_congr
      exact fun n => norm_vonMangoldt_term_rightLine n t
    _ ≤ C + 1 := by linarith

/-- On the right Burnol line, the xi logarithmic derivative grows at most
linearly.  This is the source-side bound needed to pair it with the compact-
support transform decay. -/
theorem exists_pos_const_norm_logDeriv_riemannXi_right_le_linear :
    ∃ D : Real, 0 < D ∧ ∀ t : Real,
      ‖logDeriv riemannXi
          ((5 / 4 : Real) + (t : Complex) * Complex.I)‖ ≤
        D * (1 + |t|) := by
  obtain ⟨C, hC, hseries⟩ :=
    exists_pos_const_norm_vonMangoldtLSeries_right_le
  let D : Real :=
    10 + |Real.log Real.pi| + |Real.log (5 / 8)| + Real.pi + C
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  refine ⟨D, hD, ?_⟩
  intro t
  let s : Complex := (5 / 4 : Real) + (t : Complex) * Complex.I
  have hsRe : s.re = 5 / 4 := by simp [s]
  have hsNorm : (5 / 4 : Real) ≤ ‖s‖ := by
    calc
      (5 / 4 : Real) = |s.re| := by rw [hsRe]; norm_num
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hsNormPos : 0 < ‖s‖ := (by norm_num : (0 : Real) < 5 / 4).trans_le hsNorm
  have hsInv : ‖1 / s‖ ≤ (4 / 5 : Real) := by
    rw [norm_div, norm_one]
    rw [div_le_iff₀ hsNormPos]
    nlinarith
  have hsSubRe : (s - 1).re = 1 / 4 := by
    rw [Complex.sub_re, hsRe]
    norm_num
  have hsSubNorm : (1 / 4 : Real) ≤ ‖s - 1‖ := by
    calc
      (1 / 4 : Real) = |(s - 1).re| := by rw [hsSubRe]; norm_num
      _ ≤ ‖s - 1‖ := Complex.abs_re_le_norm (s - 1)
  have hsSubNormPos : 0 < ‖s - 1‖ :=
    (by norm_num : (0 : Real) < 1 / 4).trans_le hsSubNorm
  have hsSubInv : ‖1 / (s - 1)‖ ≤ (4 : Real) := by
    rw [norm_div, norm_one]
    rw [div_le_iff₀ hsSubNormPos]
    nlinarith
  have hhalf : s / 2 =
      (5 / 8 : Complex) + (t / 2 : Real) * Complex.I := by
    apply Complex.ext <;> simp [s] <;> ring
  have hdigamma : ‖Complex.digamma (s / 2)‖ ≤
      |t| + (|Real.log (5 / 8)| + Real.pi + 2) := by
    rw [hhalf]
    exact norm_digamma_fiveEighthsLine_le t
  have hseries' :
      ‖LSeries
          (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ ≤ C := by
    simpa only [s] using hseries t
  have hdecomp :=
    logDeriv_riemannXi_eq_rightHalfPlaneLiteratureTerms
      (s := s) (by rw [hsRe]; norm_num)
  rw [hdecomp]
  have htriangle :
      ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : Complex) / 2 +
          Complex.digamma (s / 2) / 2 -
          LSeries
            (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ ≤
        ‖1 / s‖ + ‖1 / (s - 1)‖ +
          ‖(Real.log Real.pi : Complex) / 2‖ +
          ‖Complex.digamma (s / 2) / 2‖ +
          ‖LSeries
            (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ := by
    calc
      ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : Complex) / 2 +
          Complex.digamma (s / 2) / 2 -
          LSeries
            (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ ≤
          ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : Complex) / 2 +
              Complex.digamma (s / 2) / 2‖ +
            ‖LSeries
              (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ :=
        norm_sub_le _ _
      _ ≤ (‖1 / s + 1 / (s - 1) - (Real.log Real.pi : Complex) / 2‖ +
              ‖Complex.digamma (s / 2) / 2‖) +
            ‖LSeries
              (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ((‖1 / s + 1 / (s - 1)‖ +
              ‖(Real.log Real.pi : Complex) / 2‖) +
              ‖Complex.digamma (s / 2) / 2‖) +
            ‖LSeries
              (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ ‖1 / s‖ + ‖1 / (s - 1)‖ +
            ‖(Real.log Real.pi : Complex) / 2‖ +
            ‖Complex.digamma (s / 2) / 2‖ +
            ‖LSeries
              (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ := by
        gcongr
        exact norm_add_le _ _
  have hcomponents :
      ‖1 / s‖ + ‖1 / (s - 1)‖ +
          ‖(Real.log Real.pi : Complex) / 2‖ +
          ‖Complex.digamma (s / 2) / 2‖ +
          ‖LSeries
            (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ ≤
        (4 / 5 : Real) + 4 + |Real.log Real.pi| / 2 +
          (|t| + (|Real.log (5 / 8)| + Real.pi + 2)) / 2 + C := by
    have hlogTerm :
        ‖(Real.log Real.pi : Complex) / 2‖ =
          |Real.log Real.pi| / 2 := by
      rw [norm_div]
      norm_num only [Complex.norm_ofNat]
      simp
    have hdigammaTerm :
        ‖Complex.digamma (s / 2) / 2‖ ≤
          (|t| + (|Real.log (5 / 8)| + Real.pi + 2)) / 2 := by
      rw [norm_div]
      norm_num only [Complex.norm_ofNat]
      exact div_le_div_of_nonneg_right hdigamma (by norm_num)
    rw [hlogTerm]
    linarith
  have hconstant :
      (4 / 5 : Real) + 4 + |Real.log Real.pi| / 2 +
          (|Real.log (5 / 8)| + Real.pi + 2) / 2 + C ≤ D := by
    dsimp only [D]
    nlinarith [abs_nonneg (Real.log Real.pi),
      abs_nonneg (Real.log (5 / 8)), Real.pi_pos, hC]
  have hhalfD : (1 / 2 : Real) ≤ D := by linarith
  calc
    ‖1 / s + 1 / (s - 1) - (Real.log Real.pi : Complex) / 2 +
          Complex.digamma (s / 2) / 2 -
          LSeries
            (fun n : Nat => (ArithmeticFunction.vonMangoldt n : Complex)) s‖ ≤
        (4 / 5 : Real) + 4 + |Real.log Real.pi| / 2 +
          (|t| + (|Real.log (5 / 8)| + Real.pi + 2)) / 2 + C :=
      htriangle.trans hcomponents
    _ = ((4 / 5 : Real) + 4 + |Real.log Real.pi| / 2 +
          (|Real.log (5 / 8)| + Real.pi + 2) / 2 + C) + |t| / 2 := by
      ring
    _ ≤ D + D * |t| := by
      have hmul := mul_le_mul_of_nonneg_right hhalfD (abs_nonneg t)
      nlinarith
    _ = D * (1 + |t|) := by ring

private theorem continuous_logDeriv_riemannXi_rightLine :
    Continuous fun t : Real =>
      logDeriv riemannXi
        ((5 / 4 : Real) + (t : Complex) * Complex.I) := by
  have hderiv : Continuous (deriv riemannXi) := by
    exact continuousOn_univ.mp
      (analyticOnNhd_riemannXi univ).deriv.continuousOn
  rw [show (fun t : Real =>
      logDeriv riemannXi
        ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
      fun t : Real =>
        deriv riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I) /
          riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I) by
    funext t
    rw [logDeriv_apply]]
  apply Continuous.div
  · exact hderiv.comp (by fun_prop)
  · exact differentiable_riemannXi.continuous.comp (by fun_prop)
  · intro t
    apply riemannXi_ne_zero_of_one_lt_re
    norm_num

private theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_sigma_height_mul_logDeriv_right
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (sigma : Real) (height : Real → Real)
    (hsigmaLower : guinandWeilXiContourLeft ≤ sigma)
    (hsigmaUpper : sigma ≤ guinandWeilXiContourRight)
    (hheightContinuous : Continuous height)
    (hheightSq : ∀ t : Real, (height t) ^ 2 = t ^ 2) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          ((sigma : Complex) + (height t : Complex) * Complex.I) *
        logDeriv riemannXi
          ((5 / 4 : Real) + (t : Complex) * Complex.I) := by
  obtain ⟨E, hE, hweight⟩ :=
    exists_pos_const_one_add_sq_sq_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  obtain ⟨D, hD, hlogDeriv⟩ :=
    exists_pos_const_norm_logDeriv_riemannXi_right_le_linear
  have hmajor : Integrable fun t : Real =>
      (2 * E * D) * (1 + t ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul (2 * E * D)
  refine hmajor.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact
      ((differentiable_suzukiSmoothCoreBurnolXiContourWeight v).continuous.comp
          (by fun_prop)).mul
        continuous_logDeriv_riemannXi_rightLine |>.aestronglyMeasurable
  · have hweightProduct :=
      hweight sigma (height t) hsigmaLower hsigmaUpper
    rw [hheightSq t] at hweightProduct
    have hden : 0 < 1 + t ^ 2 := by positivity
    have hdenSq : 0 < (1 + t ^ 2) ^ 2 := sq_pos_of_pos hden
    have hweightNorm :
        ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (height t : Complex) * Complex.I)‖ ≤
          E / (1 + t ^ 2) ^ 2 := by
      rw [le_div_iff₀ hdenSq]
      nlinarith
    have habs : 1 + |t| ≤ 2 * (1 + t ^ 2) := by
      nlinarith [sq_nonneg (|t| - 1), sq_abs t]
    have hlog := hlogDeriv t
    rw [norm_mul]
    calc
      ‖suzukiSmoothCoreBurnolXiContourWeight v
          ((sigma : Complex) + (height t : Complex) * Complex.I)‖ *
          ‖logDeriv riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I)‖ ≤
          (E / (1 + t ^ 2) ^ 2) * (D * (1 + |t|)) := by
        gcongr
      _ ≤ (E / (1 + t ^ 2) ^ 2) * (D * (2 * (1 + t ^ 2))) := by
        gcongr
      _ = (2 * E * D) * (1 + t ^ 2)⁻¹ := by
        field_simp

/-- The complete actual Burnol integrand is integrable on the right xi
vertical. -/
theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_mul_logDeriv_right
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) *
        logDeriv riemannXi
          ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) := by
  have h :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_sigma_height_mul_logDeriv_right
      v guinandWeilXiContourRight id
      (by norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight])
      le_rfl continuous_id (fun t => rfl)
  simpa only [id_eq, guinandWeilXiContourRight] using h

/-- The right-line integrand with the Burnol weight reflected to the left
vertical is integrable. -/
theorem integrable_suzukiSmoothCoreBurnolXiContourWeight_reflected_mul_logDeriv_right
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    Integrable fun t : Real =>
      suzukiSmoothCoreBurnolXiContourWeight v
          (1 - ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I)) *
        logDeriv riemannXi
          ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) := by
  have h :=
    integrable_suzukiSmoothCoreBurnolXiContourWeight_sigma_height_mul_logDeriv_right
      v guinandWeilXiContourLeft (fun t : Real => -t) le_rfl
      (by norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight])
      continuous_neg (fun t => by ring)
  apply h.congr
  filter_upwards with t
  congr 2
  norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]
  ring

/-- Xi reflection transports the finite left Burnol vertical to the negative
right vertical with the source weight independently reflected.  No symmetry
of the source weight is assumed. -/
theorem suzukiSmoothCoreBurnolXi_verticalIntegral_left_eq_neg_reflectedRight
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (T : Real) :
    guinandWeilVerticalIntegral
        (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
          logDeriv riemannXi s)
        guinandWeilXiContourLeft (-T) T =
      -guinandWeilVerticalIntegral
        (fun s => suzukiSmoothCoreBurnolXiContourWeight v (1 - s) *
          logDeriv riemannXi s)
        guinandWeilXiContourRight (-T) T := by
  let F : Complex → Complex := fun s =>
    suzukiSmoothCoreBurnolXiContourWeight v s * logDeriv riemannXi s
  let G : Complex → Complex := fun s =>
    suzukiSmoothCoreBurnolXiContourWeight v (1 - s) * logDeriv riemannXi s
  have hreflect (s : Complex) : F (1 - s) = -G s := by
    dsimp only [F, G]
    rw [logDeriv_riemannXi_one_sub_all]
    ring
  have hpoint (t : Real) :
      F ((guinandWeilXiContourLeft : Complex) +
          (t : Complex) * Complex.I) =
        -G ((guinandWeilXiContourRight : Complex) +
          (-t : Complex) * Complex.I) := by
    have h := hreflect
      ((guinandWeilXiContourRight : Complex) +
        (-t : Complex) * Complex.I)
    convert h using 1
    norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]
    ring_nf
  unfold guinandWeilVerticalIntegral
  change Complex.I *
      (∫ t in -T..T,
        F ((guinandWeilXiContourLeft : Complex) +
          (t : Complex) * Complex.I)) = _
  rw [intervalIntegral.integral_congr
      (fun t _ht => hpoint t), intervalIntegral.integral_neg]
  have hneg := intervalIntegral.integral_comp_neg
    (f := fun t : Real =>
      G ((guinandWeilXiContourRight : Complex) +
        (t : Complex) * Complex.I))
    (a := -T) (b := T)
  have hneg' :
      (∫ t in -T..T,
        G ((guinandWeilXiContourRight : Complex) +
          (-t : Complex) * Complex.I)) =
        ∫ t in -T..T,
          G ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) := by
    simpa using hneg
  rw [hneg']
  ring

/-- The finite actual Burnol right verticals converge to their complete
improper integral along any height exhaustion. -/
theorem tendsto_suzukiSmoothCoreBurnolXi_rightVerticalIntegral
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (height : Nat → Real) (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun N : Nat =>
        guinandWeilVerticalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            logDeriv riemannXi s)
          guinandWeilXiContourRight (-(height N)) (height N))
      atTop
      (nhds
        (Complex.I * ∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I) *
            logDeriv riemannXi
              ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I))) := by
  unfold guinandWeilVerticalIntegral
  exact
    (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnolXiContourWeight_mul_logDeriv_right v)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I

/-- The reflected-weight right verticals likewise converge to their complete
improper integral. -/
theorem tendsto_suzukiSmoothCoreBurnolXi_reflectedRightVerticalIntegral
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (height : Nat → Real) (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun N : Nat =>
        guinandWeilVerticalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v (1 - s) *
            logDeriv riemannXi s)
          guinandWeilXiContourRight (-(height N)) (height N))
      atTop
      (nhds
        (Complex.I * ∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (1 - ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I)) *
            logDeriv riemannXi
              ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I))) := by
  unfold guinandWeilVerticalIntegral
  exact
    (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_suzukiSmoothCoreBurnolXiContourWeight_reflected_mul_logDeriv_right v)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I

/-- The actual Burnol left verticals converge, with the functional-equation
sign and the independently reflected source weight kept explicit. -/
theorem tendsto_suzukiSmoothCoreBurnolXi_leftVerticalIntegral
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (height : Nat → Real) (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun N : Nat =>
        guinandWeilVerticalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            logDeriv riemannXi s)
          guinandWeilXiContourLeft (-(height N)) (height N))
      atTop
      (nhds
        (-(Complex.I * ∫ t : Real,
          suzukiSmoothCoreBurnolXiContourWeight v
              (1 - ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I)) *
            logDeriv riemannXi
              ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I)))) := by
  apply
    (tendsto_suzukiSmoothCoreBurnolXi_reflectedRightVerticalIntegral
      v height hheight).neg.congr'
  filter_upwards with N
  exact
    (suzukiSmoothCoreBurnolXi_verticalIntegral_left_eq_neg_reflectedRight
      v (height N)).symm

end

end RiemannHypothesisProject.Experiments.M100
