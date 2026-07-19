import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaRemainder

/-!
# Burnol's local coefficient

Burnol's fixed-support argument isolates the real coefficient

`8 * sqrt 2 * cos (log 2 * t) / (1 + 4*t^2)
  - log pi + Re (digamma (1/4 + i*t/2))`.

The source proof uses that this coefficient is continuous and tends to
`+infinity` in both directions.  The second half of this module formalizes the
elementary compact/tail argument: any globally bounded-below coefficient with
that two-sided growth admits a positive cosine correction for one sufficiently
small support radius.
-/

namespace RiemannHypothesisProject

noncomputable section

open Filter
open ComplexCompactExhaustion

/-- The real local coefficient in Burnol's fixed-support proof. -/
def burnolLocalCoefficient (t : Real) : Real :=
  8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2) -
    Real.log Real.pi +
      (Complex.digamma (bellottiWongGammaLine t)).re

/-- Burnol's local coefficient is continuous on the real line. -/
theorem continuous_burnolLocalCoefficient :
    Continuous burnolLocalCoefficient := by
  have hline : Continuous bellottiWongGammaLine := by
    unfold bellottiWongGammaLine
    fun_prop
  have hdigamma : Continuous (fun t : Real =>
      (Complex.digamma (bellottiWongGammaLine t)).re) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpsi : ContinuousAt Complex.digamma (bellottiWongGammaLine t) :=
      (analyticAt_digamma_of_re_pos (by
        rw [bellottiWongGammaLine_re]
        norm_num)).continuousAt
    exact Complex.continuous_re.continuousAt.comp
      (hpsi.comp hline.continuousAt)
  have hden : ∀ t : Real, 1 + 4 * t ^ 2 ≠ 0 := by
    intro t
    nlinarith [sq_nonneg t]
  have hnum : Continuous (fun t : Real =>
      8 * Real.sqrt 2 * Real.cos (Real.log 2 * t)) := by
    fun_prop
  have hdenContinuous : Continuous (fun t : Real => 1 + 4 * t ^ 2) := by
    fun_prop
  unfold burnolLocalCoefficient
  exact ((hnum.div hdenContinuous hden).sub continuous_const).add hdigamma

/-- A two-sided coercivity condition stated in the exact form consumed by the
fixed-support cosine argument. -/
def TwoSidedCoercive (alpha : Real → Real) : Prop :=
  ∀ A : Real, ∃ R > 0, ∀ t : Real, R <= |t| → A <= alpha t

/-- The elementary heart of Burnol's small-support argument.  A continuous
coefficient is not needed here once a global lower bound and two-sided
coercivity have been supplied: the compact region is controlled by a cosine
which stays at least `1/2`, and the tail absorbs the worst value `-1` of the
cosine. -/
theorem exists_burnolCosineCorrection
    {alpha : Real → Real} {M : Real}
    (hM : 0 <= M)
    (hlower : ∀ t : Real, -M <= alpha t)
    (hcoercive : TwoSidedCoercive alpha) :
    ∃ epsilon > 0, ∃ A ≥ 0, ∀ t : Real,
      0 <= A * Real.cos (epsilon * t) + alpha t := by
  obtain ⟨R, hR, htail⟩ := hcoercive (2 * M)
  refine ⟨Real.pi / (3 * R), by positivity, 2 * M, by positivity, ?_⟩
  intro t
  by_cases ht : R <= |t|
  · have hcos := Real.neg_one_le_cos (Real.pi / (3 * R) * t)
    have halpha := htail t ht
    nlinarith
  · have ht' : |t| <= R := le_of_lt (lt_of_not_ge ht)
    have hepsilon_nonneg : 0 <= Real.pi / (3 * R) := by positivity
    have harg : |Real.pi / (3 * R) * t| <= Real.pi / 3 := by
      rw [abs_mul, abs_of_nonneg hepsilon_nonneg]
      calc
        Real.pi / (3 * R) * |t| <= Real.pi / (3 * R) * R := by
          gcongr
        _ = Real.pi / 3 := by
          field_simp [hR.ne']
    have hcos : (1 / 2 : Real) <=
        Real.cos (Real.pi / (3 * R) * t) := by
      calc
        (1 / 2 : Real) = Real.cos (Real.pi / 3) := Real.cos_pi_div_three.symm
        _ <= Real.cos |Real.pi / (3 * R) * t| :=
          Real.cos_le_cos_of_nonneg_of_le_pi
            (abs_nonneg _) (by linarith [Real.pi_pos]) harg
        _ = Real.cos (Real.pi / (3 * R) * t) := Real.cos_abs _
    have halpha := hlower t
    nlinarith

/-- Once the exact Burnol coefficient's boundedness and two-sided asymptotic
are proved, the source cosine correction follows with one fixed positive
support parameter.  The analytic hypotheses remain visible here. -/
theorem exists_burnolLocalCoefficient_cosineCorrection
    {M : Real}
    (hM : 0 <= M)
    (hlower : ∀ t : Real, -M <= burnolLocalCoefficient t)
    (hcoercive : TwoSidedCoercive burnolLocalCoefficient) :
    ∃ epsilon > 0, ∃ A ≥ 0, ∀ t : Real,
      0 <= A * Real.cos (epsilon * t) + burnolLocalCoefficient t :=
  exists_burnolCosineCorrection hM hlower hcoercive

/-- The reciprocal term in Binet's formula stays uniformly bounded on
Burnol's vertical line. -/
theorem norm_one_div_two_mul_bellottiWongGammaLine_le_two (t : Real) :
    ‖1 / (2 * bellottiWongGammaLine t)‖ <= 2 := by
  have hnorm : (1 / 4 : Real) <= ‖bellottiWongGammaLine t‖ := by
    calc
      (1 / 4 : Real) = |(bellottiWongGammaLine t).re| := by
        rw [bellottiWongGammaLine_re]
        norm_num
      _ <= ‖bellottiWongGammaLine t‖ := Complex.abs_re_le_norm _
  rw [norm_div, norm_one, norm_mul]
  norm_num only [Complex.norm_ofNat]
  rw [div_le_iff₀ (by positivity)]
  nlinarith [norm_nonneg (bellottiWongGammaLine t)]

/-- Binet's formula gives the logarithmic lower bound needed in Burnol's
argument.  The source theorem is kept visible as the only analytic input. -/
theorem burnolDigamma_re_lower_of_binet
    (hBinet : BennettGammaBinetDigammaFormula) (t B : Real)
    (ht : 2 * Real.exp (B + 4) <= |t|) :
    B <= (Complex.digamma (bellottiWongGammaLine t)).re := by
  let z := bellottiWongGammaLine t
  have him : |t| / 2 <= ‖z‖ := by
    calc
      |t| / 2 = |z.im| := by
        simp [z, bellottiWongGammaLine, abs_div]
      _ <= ‖z‖ := Complex.abs_im_le_norm _
  have hexp : Real.exp (B + 4) <= ‖z‖ := by
    nlinarith
  have hlog : B + 4 <= (Complex.log z).re := by
    rw [Complex.log_re]
    calc
      B + 4 = Real.log (Real.exp (B + 4)) := by rw [Real.log_exp]
      _ <= Real.log ‖z‖ := Real.log_le_log (Real.exp_pos _) hexp
  have herrnorm :
      ‖Complex.digamma z - (Complex.log z - 1 / (2 * z))‖ <= 2 := by
    simpa [z] using norm_digamma_sub_log_sub_inv_onGammaLine_le_two hBinet t
  have herrre :
      -2 <= (Complex.digamma z - (Complex.log z - 1 / (2 * z))).re := by
    have hre := Complex.abs_re_le_norm
      (Complex.digamma z - (Complex.log z - 1 / (2 * z)))
    linarith [neg_abs_le
      (Complex.digamma z - (Complex.log z - 1 / (2 * z))).re]
  have hinvre : (1 / (2 * z)).re <= 2 := by
    have hre := Complex.re_le_norm (1 / (2 * z))
    have hnorm := norm_one_div_two_mul_bellottiWongGammaLine_le_two t
    simpa [z] using hre.trans hnorm
  change -2 <=
    (Complex.digamma z).re - ((Complex.log z).re - (1 / (2 * z)).re) at herrre
  linarith

/-- The norm of the vertical Gamma-line point grows at most linearly. -/
theorem norm_bellottiWongGammaLine_le_one_add_abs (t : Real) :
    ‖bellottiWongGammaLine t‖ <= 1 + |t| := by
  unfold bellottiWongGammaLine
  calc
    ‖(1 / 4 : Complex) + (t / 2 : Real) * Complex.I‖ <=
        ‖(1 / 4 : Complex)‖ + ‖((t / 2 : Real) : Complex) * Complex.I‖ :=
      norm_add_le _ _
    _ = (1 / 4 : Real) + |t| / 2 := by
      rw [norm_mul]
      simp
    _ <= 1 + |t| := by nlinarith [abs_nonneg t]

/-- A coarse linear bound for the principal logarithm on Burnol's vertical
line. -/
theorem norm_log_bellottiWongGammaLine_le (t : Real) :
    ‖Complex.log (bellottiWongGammaLine t)‖ <=
      |t| + (|Real.log (1 / 4)| + Real.pi) := by
  have hnormLower : (1 / 4 : Real) <= ‖bellottiWongGammaLine t‖ := by
    calc
      (1 / 4 : Real) = |(bellottiWongGammaLine t).re| := by
        rw [bellottiWongGammaLine_re]
        norm_num
      _ <= ‖bellottiWongGammaLine t‖ := Complex.abs_re_le_norm _
  have hnormPos : 0 < ‖bellottiWongGammaLine t‖ :=
    lt_of_lt_of_le (by norm_num) hnormLower
  have hlogLower :
      Real.log (1 / 4) <= Real.log ‖bellottiWongGammaLine t‖ :=
    Real.log_le_log (by norm_num) hnormLower
  have hlogUpper :
      Real.log ‖bellottiWongGammaLine t‖ <= |t| := by
    have hlog := Real.log_le_sub_one_of_pos hnormPos
    have hnorm := norm_bellottiWongGammaLine_le_one_add_abs t
    linarith
  have habsLog :
      |Real.log ‖bellottiWongGammaLine t‖| <=
        |Real.log (1 / 4)| + |t| := by
    rw [abs_le]
    constructor
    · have hbase := neg_abs_le (Real.log (1 / 4))
      linarith [abs_nonneg t]
    · linarith [abs_nonneg (Real.log (1 / 4))]
  have harg := Complex.abs_arg_le_pi (bellottiWongGammaLine t)
  unfold Complex.log
  calc
    ‖((Real.log ‖bellottiWongGammaLine t‖ : Real) : Complex) +
        (bellottiWongGammaLine t).arg * Complex.I‖ <=
        ‖((Real.log ‖bellottiWongGammaLine t‖ : Real) : Complex)‖ +
          ‖((bellottiWongGammaLine t).arg : Complex) * Complex.I‖ :=
      norm_add_le _ _
    _ = |Real.log ‖bellottiWongGammaLine t‖| +
        |(bellottiWongGammaLine t).arg| := by
      rw [norm_mul]
      simp
    _ <= |t| + (|Real.log (1 / 4)| + Real.pi) := by linarith

/-- Binet's formula gives a coarse linear majorant for the exact local
coefficient. This is sufficient for integrating it against Schwartz energy. -/
theorem abs_burnolLocalCoefficient_le_of_binet
    (hBinet : BennettGammaBinetDigammaFormula) (t : Real) :
    |burnolLocalCoefficient t| <=
      (20 + |Real.log Real.pi| + |Real.log (1 / 4)| + Real.pi) + |t| := by
  let z := bellottiWongGammaLine t
  have hinv := norm_one_div_two_mul_bellottiWongGammaLine_le_two t
  have herr := norm_digamma_sub_log_sub_inv_onGammaLine_le_two hBinet t
  have hpsi : ‖Complex.digamma z‖ <= ‖Complex.log z‖ + 4 := by
    calc
      ‖Complex.digamma z‖ =
          ‖(Complex.digamma z - (Complex.log z - 1 / (2 * z))) +
            (Complex.log z - 1 / (2 * z))‖ := by
        congr 1
        ring
      _ <= ‖Complex.digamma z - (Complex.log z - 1 / (2 * z))‖ +
          ‖Complex.log z - 1 / (2 * z)‖ := norm_add_le _ _
      _ <= 2 + (‖Complex.log z‖ + ‖1 / (2 * z)‖) := by
        gcongr
        exact norm_sub_le _ _
      _ <= ‖Complex.log z‖ + 4 := by
        have hinv' : ‖1 / (2 * z)‖ <= 2 := by simpa [z] using hinv
        linarith
  have hsqrt_nonneg : 0 <= Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_le_two : Real.sqrt 2 <= 2 := by nlinarith
  have hcosAbs : |Real.cos (Real.log 2 * t)| <= 1 :=
    abs_le.mpr (Real.cos_mem_Icc _)
  have hnumAbs :
      |8 * Real.sqrt 2 * Real.cos (Real.log 2 * t)| <= 16 := by
    calc
      |8 * Real.sqrt 2 * Real.cos (Real.log 2 * t)| =
          8 * Real.sqrt 2 * |Real.cos (Real.log 2 * t)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hsqrt_nonneg]
        norm_num
      _ <= 8 * Real.sqrt 2 * 1 := by gcongr
      _ <= 16 := by nlinarith
  have hden : 0 < 1 + 4 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hrational :
      |8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2)| <= 16 := by
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    nlinarith [sq_nonneg t]
  have hlocalTriangle :
      |burnolLocalCoefficient t| <=
        |8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2)| +
          |Real.log Real.pi| + |(Complex.digamma z).re| := by
    unfold burnolLocalCoefficient
    dsimp [z]
    have hfirst := abs_add_le
      (8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2) -
        Real.log Real.pi)
      (Complex.digamma (bellottiWongGammaLine t)).re
    have hsecond :
        |8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2) -
            Real.log Real.pi| <=
          |8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2)| +
            |Real.log Real.pi| := by
      rw [sub_eq_add_neg]
      simpa using abs_add_le
        (8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2))
        (-Real.log Real.pi)
    linarith
  have hre : |(Complex.digamma z).re| <= ‖Complex.digamma z‖ :=
    Complex.abs_re_le_norm _
  have hlog := norm_log_bellottiWongGammaLine_le t
  dsimp [z] at hpsi hre
  linarith

/-- The exact Burnol coefficient tends to `+infinity` in both real
directions. -/
theorem twoSidedCoercive_burnolLocalCoefficient_of_binet
    (hBinet : BennettGammaBinetDigammaFormula) :
    TwoSidedCoercive burnolLocalCoefficient := by
  intro A
  let B := A + 16 + Real.log Real.pi
  refine ⟨max 1 (2 * Real.exp (B + 4)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  have ht' : 2 * Real.exp (B + 4) <= |t| :=
    (le_max_right _ _).trans ht
  have hpsi := burnolDigamma_re_lower_of_binet hBinet t B ht'
  have hsqrt_nonneg : 0 <= Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_le_two : Real.sqrt 2 <= 2 := by nlinarith
  have hcos := Real.neg_one_le_cos (Real.log 2 * t)
  have hnum : -16 <= 8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) := by
    have hmul := mul_le_mul_of_nonneg_left hcos
      (show 0 <= 8 * Real.sqrt 2 by positivity)
    nlinarith
  have hden : 0 < 1 + 4 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hrational :
      -16 <= 8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg t]
  unfold burnolLocalCoefficient
  dsimp [B] at hpsi
  linarith

/-- A continuous two-sided coercive real function has a global lower bound. -/
theorem exists_globalLowerBound_of_continuous_of_twoSidedCoercive
    {alpha : Real → Real}
    (hcontinuous : Continuous alpha)
    (hcoercive : TwoSidedCoercive alpha) :
    ∃ M ≥ 0, ∀ t : Real, -M <= alpha t := by
  obtain ⟨R, hR, htail⟩ := hcoercive 0
  obtain ⟨C, hC⟩ := isCompact_Icc.bddBelow_image hcontinuous.continuousOn
  refine ⟨max 0 (-C), le_max_left _ _, ?_⟩
  intro t
  by_cases ht : R <= |t|
  · have hzero := htail t ht
    have hM : 0 <= max 0 (-C) := le_max_left _ _
    linarith
  · have ht_abs : |t| < R := lt_of_not_ge ht
    have ht_mem : t ∈ Set.Icc (-R) R := by
      rw [abs_lt] at ht_abs
      exact ⟨ht_abs.1.le, ht_abs.2.le⟩
    have hcompact : C <= alpha t := hC ⟨t, ht_mem, rfl⟩
    have hM : -max 0 (-C) <= C := by
      have := le_max_right 0 (-C)
      linarith
    exact hM.trans hcompact

/-- Burnol's exact coefficient therefore admits the positive cosine correction
from the single, explicitly named Binet source theorem. -/
theorem exists_burnolLocalCoefficient_cosineCorrection_of_binet
    (hBinet : BennettGammaBinetDigammaFormula) :
    ∃ epsilon > 0, ∃ A ≥ 0, ∀ t : Real,
      0 <= A * Real.cos (epsilon * t) + burnolLocalCoefficient t := by
  have hcoercive := twoSidedCoercive_burnolLocalCoefficient_of_binet hBinet
  obtain ⟨M, hM, hlower⟩ :=
    exists_globalLowerBound_of_continuous_of_twoSidedCoercive
      continuous_burnolLocalCoefficient hcoercive
  exact exists_burnolLocalCoefficient_cosineCorrection hM hlower hcoercive

end

end RiemannHypothesisProject
