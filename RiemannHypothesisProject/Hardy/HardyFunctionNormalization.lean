import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import RiemannHypothesisProject.ComplexAnalyticReflection
import RiemannHypothesisProject.Hardy.CriticalLineStirlingPhase
import RiemannHypothesisProject.LiCriterion.CriticalLineGeometry
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXi

/-!
# The actual Hardy function on the critical line

This module supplies the H4A normalization bridge.  It factors the project's
entire xi function on the critical line, proves its global conjugation
symmetry, and packages the resulting real Hardy function without choosing a
square-root branch.
-/

open Complex Filter Set
open scoped ComplexConjugate

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Deligne's real Gamma factor respects complex conjugation. -/
theorem GammaR_conj (s : Complex) :
    Complex.Gammaℝ (conj s) = conj (Complex.Gammaℝ s) := by
  unfold Complex.Gammaℝ
  rw [show conj s / 2 = conj (s / 2) by
      apply Complex.ext <;> norm_num [div_eq_mul_inv],
    Complex.Gamma_conj]
  have hpiArg : Complex.arg (Real.pi : Complex) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  rw [show -(conj s) / 2 = conj (-s / 2) by
      apply Complex.ext <;> norm_num [div_eq_mul_inv],
    Complex.cpow_conj _ _ hpiArg]
  simp

/-- The classical xi product formula wherever the real part is positive and
the removable point `1` is avoided.  Unlike the right-vertical formula, this
includes the critical line. -/
theorem riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta_of_re_pos
    {s : Complex} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s =
      s * (s - 1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp [hgamma]

/-- The entire xi function respects complex conjugation globally. -/
theorem riemannXi_conj (s : Complex) :
    riemannXi (conj s) = conj (riemannXi s) := by
  let reflected : Complex → Complex := fun z => conj (riemannXi (conj z))
  have hreflected : AnalyticOnNhd Complex reflected Set.univ := by
    exact analyticOnNhd_conj_comp_conj
      (analyticOnNhd_riemannXi Set.univ) (fun _ _ => Set.mem_univ _)
  have hxi : AnalyticOnNhd Complex riemannXi Set.univ :=
    analyticOnNhd_riemannXi Set.univ
  have heventually : reflected =ᶠ[nhds (2 : Complex)] riemannXi := by
    have hright : ∀ᶠ z : Complex in nhds (2 : Complex), 1 < z.re :=
      (Complex.continuous_re.tendsto (2 : Complex)).eventually
        (lt_mem_nhds (by norm_num))
    filter_upwards [hright] with z hz
    have hzpos : 0 < z.re := zero_lt_one.trans hz
    have hzcpos : 0 < (conj z).re := by simpa using hzpos
    have hz1 : z ≠ 1 := by
      intro hone
      rw [hone] at hz
      norm_num at hz
    have hzc1 : conj z ≠ 1 := by
      simpa using (map_ne_one_iff _ (starRingEnd Complex).injective).mpr hz1
    dsimp only [reflected]
    rw [riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta_of_re_pos hzcpos hzc1,
      riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta_of_re_pos hzpos hz1,
      GammaR_conj, riemannZeta_conj]
    simp [map_ofNat]
  have hfun : reflected = riemannXi :=
    hreflected.eq_of_eventuallyEq hxi heventually
  have h := congrFun hfun (conj s)
  simpa [reflected] using h.symm

end

end ComplexCompactExhaustion

namespace Hardy

noncomputable section

open ComplexCompactExhaustion

/-- The polynomial-Gamma factor in the critical-line xi product formula. -/
def hardyXiFactor (s : Complex) : Complex :=
  s * (s - 1) * Complex.Gammaℝ s / 2

/-- The complex-valued presentation of Hardy's real critical-line function. -/
def hardyFunction (t : Real) : Complex :=
  riemannXi (criticalLinePoint t) / ‖hardyXiFactor (criticalLinePoint t)‖

/-- The critical-line factor is nonzero. -/
theorem hardyXiFactor_ne_zero (t : Real) :
    hardyXiFactor (criticalLinePoint t) ≠ 0 := by
  have hs0 : criticalLinePoint t ≠ 0 := criticalLinePoint_ne_zero t
  have hs1 : criticalLinePoint t ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    have hre := congrArg Complex.re h
    simp [criticalLinePoint] at hre
  have hgamma : Complex.Gammaℝ (criticalLinePoint t) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [criticalLinePoint])
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) hgamma)
    (by norm_num)

/-- Exact xi/Gamma/zeta factorization on the critical line. -/
theorem riemannXi_criticalLinePoint_eq_factor_mul_riemannZeta (t : Real) :
    riemannXi (criticalLinePoint t) =
      hardyXiFactor (criticalLinePoint t) * riemannZeta (criticalLinePoint t) := by
  rw [hardyXiFactor]
  have hne : criticalLinePoint t ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [criticalLinePoint] at hre
  simpa [div_mul_eq_mul_div, mul_assoc] using
    (riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta_of_re_pos
      (s := criticalLinePoint t) (by simp [criticalLinePoint]) hne)

/-- Complex conjugation agrees with functional-equation reflection on the
critical line. -/
theorem conj_criticalLinePoint_eq_one_sub (t : Real) :
    conj (criticalLinePoint t) = 1 - criticalLinePoint t := by
  apply Complex.ext
  · simp [criticalLinePoint]
    ring
  · simp [criticalLinePoint]

/-- Xi is real-valued on the critical line. -/
theorem riemannXi_criticalLinePoint_conj (t : Real) :
    conj (riemannXi (criticalLinePoint t)) =
      riemannXi (criticalLinePoint t) := by
  rw [← ComplexCompactExhaustion.riemannXi_conj,
    conj_criticalLinePoint_eq_one_sub,
    ComplexCompactExhaustion.riemannXi_one_sub]

/-- The Hardy normalization is fixed by conjugation. -/
theorem hardyFunction_conj (t : Real) :
    conj (hardyFunction t) = hardyFunction t := by
  simp [hardyFunction, riemannXi_criticalLinePoint_conj]

/-- The Hardy normalization has zero imaginary part. -/
theorem hardyFunction_im_eq_zero (t : Real) :
    (hardyFunction t).im = 0 :=
  Complex.conj_eq_iff_im.mp (hardyFunction_conj t)

/-- The real-valued presentation used by the later order and sign arguments. -/
def hardyFunctionReal (t : Real) : Real := (hardyFunction t).re

/-- The real presentation coerces back to the defining xi quotient. -/
theorem ofReal_hardyFunctionReal_eq (t : Real) :
    (hardyFunctionReal t : Complex) = hardyFunction t := by
  exact Complex.conj_eq_iff_re.mp (hardyFunction_conj t)

/-- The standard parametrization of the critical line is continuous. -/
theorem continuous_criticalLinePoint : Continuous criticalLinePoint := by
  unfold criticalLinePoint
  fun_prop

/-- The Gamma factor is continuous along the entire critical line. -/
theorem continuous_criticalLineGammaR :
    Continuous (fun t : Real => Complex.Gammaℝ (criticalLinePoint t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hgamma : Complex.Gammaℝ (criticalLinePoint t) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [criticalLinePoint])
  have hdiff :
      DifferentiableAt Complex Complex.Gammaℝ (criticalLinePoint t) := by
    have hinv := (Complex.differentiable_Gammaℝ_inv
      (criticalLinePoint t)).inv (inv_ne_zero hgamma)
    have hfun :
        (fun z : Complex => (Complex.Gammaℝ z)⁻¹)⁻¹ = Complex.Gammaℝ := by
      funext z
      simp
    rw [hfun] at hinv
    exact hinv
  exact hdiff.continuousAt.comp continuous_criticalLinePoint.continuousAt

/-- The critical-line polynomial-Gamma factor is continuous. -/
theorem continuous_hardyXiFactor_criticalLine :
    Continuous (fun t : Real => hardyXiFactor (criticalLinePoint t)) := by
  unfold hardyXiFactor
  exact (((continuous_criticalLinePoint.mul
    (continuous_criticalLinePoint.sub continuous_const)).mul
      continuous_criticalLineGammaR).div_const 2)

/-- The complex presentation of Hardy's function is continuous. -/
theorem continuous_hardyFunction : Continuous hardyFunction := by
  have hnum :
      Continuous (fun t : Real => riemannXi (criticalLinePoint t)) :=
    ComplexCompactExhaustion.differentiable_riemannXi.continuous.comp
      continuous_criticalLinePoint
  have hdenom :
      Continuous (fun t : Real =>
        (‖hardyXiFactor (criticalLinePoint t)‖ : Complex)) := by
    exact Complex.continuous_ofReal.comp
      continuous_hardyXiFactor_criticalLine.norm
  exact hnum.div hdenom fun t => by
    exact_mod_cast norm_ne_zero_iff.mpr (hardyXiFactor_ne_zero t)

/-- The real presentation of Hardy's function is continuous. -/
theorem continuous_hardyFunctionReal : Continuous hardyFunctionReal := by
  exact Complex.continuous_re.comp continuous_hardyFunction

/-- The Hardy normalization has exactly the norm of zeta on the critical
line. -/
theorem norm_hardyFunction (t : Real) :
    ‖hardyFunction t‖ = ‖riemannZeta (criticalLinePoint t)‖ := by
  rw [hardyFunction, riemannXi_criticalLinePoint_eq_factor_mul_riemannZeta,
    norm_div, norm_mul]
  have hnorm : ‖hardyXiFactor (criticalLinePoint t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (hardyXiFactor_ne_zero t)
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
  field_simp

/-- Hardy's function vanishes exactly at the critical-line zeta zeros. -/
theorem hardyFunction_eq_zero_iff (t : Real) :
    hardyFunction t = 0 ↔ riemannZeta (criticalLinePoint t) = 0 := by
  constructor
  · intro hzero
    have hnorm := congrArg norm hzero
    rw [norm_hardyFunction, norm_zero] at hnorm
    exact norm_eq_zero.mp hnorm
  · intro hzero
    rw [hardyFunction, riemannXi_criticalLinePoint_eq_factor_mul_riemannZeta,
      hzero, mul_zero, zero_div]

/-- The real Hardy function has exactly the absolute value of critical-line
zeta. -/
theorem abs_hardyFunctionReal (t : Real) :
    |hardyFunctionReal t| = ‖riemannZeta (criticalLinePoint t)‖ := by
  have hnorm := congrArg norm (ofReal_hardyFunctionReal_eq t)
  simpa [Complex.norm_real, Real.norm_eq_abs, norm_hardyFunction] using hnorm

/-- The real presentation has the same critical-line zero set. -/
theorem hardyFunctionReal_eq_zero_iff (t : Real) :
    hardyFunctionReal t = 0 ↔ riemannZeta (criticalLinePoint t) = 0 := by
  rw [← hardyFunction_eq_zero_iff]
  constructor
  · intro hzero
    rw [← ofReal_hardyFunctionReal_eq, hzero]
    norm_num
  · intro hzero
    have hre := congrArg Complex.re hzero
    simpa [hardyFunctionReal] using hre

/-- On the critical line, the polynomial part of the xi factor is a negative
positive-real scalar. -/
theorem hardyXiFactor_criticalLine_eq_neg_normSq_mul_gammaR (t : Real) :
    hardyXiFactor (criticalLinePoint t) =
      -((Complex.normSq (criticalLinePoint t) / 2 : Real) : Complex) *
        Complex.Gammaℝ (criticalLinePoint t) := by
  rw [hardyXiFactor, criticalLinePoint_sub_one_eq_neg_conj,
    mul_neg, Complex.mul_conj]
  push_cast
  ring

/-- The unit phase of the full critical-line factor is exactly the negative
unit phase of `Gammaℝ`.  This is the branch-free sign required by H2. -/
theorem hardyXiFactor_div_norm_eq_neg_GammaR_div_norm (t : Real) :
    hardyXiFactor (criticalLinePoint t) /
        ‖hardyXiFactor (criticalLinePoint t)‖ =
      -Complex.Gammaℝ (criticalLinePoint t) /
        ‖Complex.Gammaℝ (criticalLinePoint t)‖ := by
  let r : Real := Complex.normSq (criticalLinePoint t) / 2
  have hr : 0 < r := by
    exact div_pos (Complex.normSq_pos.mpr (criticalLinePoint_ne_zero t)) two_pos
  have hgamma : Complex.Gammaℝ (criticalLinePoint t) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp [criticalLinePoint])
  have hgammaNorm : ‖Complex.Gammaℝ (criticalLinePoint t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hgamma
  rw [hardyXiFactor_criticalLine_eq_neg_normSq_mul_gammaR]
  change (-((r : Real) : Complex) * Complex.Gammaℝ (criticalLinePoint t)) /
      ‖-((r : Real) : Complex) * Complex.Gammaℝ (criticalLinePoint t)‖ = _
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  push_cast
  field_simp [hr.ne']

/-- Hardy's function is the unit critical-line factor times zeta. -/
theorem hardyFunction_eq_factor_unit_mul_riemannZeta (t : Real) :
    hardyFunction t =
      (hardyXiFactor (criticalLinePoint t) /
        ‖hardyXiFactor (criticalLinePoint t)‖) *
          riemannZeta (criticalLinePoint t) := by
  rw [hardyFunction, riemannXi_criticalLinePoint_eq_factor_mul_riemannZeta]
  ring

/-- Exact branch-free phase presentation of Hardy's function. -/
theorem hardyFunction_eq_neg_GammaR_unit_mul_riemannZeta (t : Real) :
    hardyFunction t =
      (-Complex.Gammaℝ (criticalLinePoint t) /
        ‖Complex.Gammaℝ (criticalLinePoint t)‖) *
          riemannZeta (criticalLinePoint t) := by
  rw [hardyFunction_eq_factor_unit_mul_riemannZeta,
    hardyXiFactor_div_norm_eq_neg_GammaR_div_norm]

/-- H2 controls the selected Hardy factor phase, with the exact minus sign
coming from `s * (s - 1)` on the critical line. -/
theorem norm_hardyXiFactor_unit_add_exp_stirlingPhase_le
    {t : Real} (ht : 1 ≤ t) :
    ‖hardyXiFactor (criticalLinePoint t) /
          ‖hardyXiFactor (criticalLinePoint t)‖ +
        Complex.exp (Complex.I * criticalLineStirlingPhase t)‖ ≤
      11 / (16 * t) := by
  rw [hardyXiFactor_div_norm_eq_neg_GammaR_div_norm]
  calc
    ‖-Complex.Gammaℝ (criticalLinePoint t) /
          ‖Complex.Gammaℝ (criticalLinePoint t)‖ +
        Complex.exp (Complex.I * criticalLineStirlingPhase t)‖ =
        ‖-(Complex.Gammaℝ (criticalLinePoint t) /
            ‖Complex.Gammaℝ (criticalLinePoint t)‖ -
          Complex.exp (Complex.I * criticalLineStirlingPhase t))‖ := by
      congr 1
      ring
    _ = ‖Complex.Gammaℝ (criticalLinePoint t) /
          ‖Complex.Gammaℝ (criticalLinePoint t)‖ -
        Complex.exp (Complex.I * criticalLineStirlingPhase t)‖ := norm_neg _
    _ ≤ 11 / (16 * t) := by
      simpa [criticalLinePoint, mul_comm] using
        norm_criticalLineGammaR_unit_sub_exp_stirlingPhase_le ht

end

end Hardy

end RiemannHypothesisProject
