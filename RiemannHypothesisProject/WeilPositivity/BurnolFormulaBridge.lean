import RiemannHypothesisProject.GuinandWeilConcrete.ArchimedeanLogDerivative
import RiemannHypothesisProject.WeilPositivity.BurnolFormulaKernel
import RiemannHypothesisProject.WeilPositivity.BurnolLocalSupport
import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicity

/-!
# Burnol fixed-support Guinand-Weil formula bridge

This module identifies Burnol's local spectral quadratic form with the
literature-normalized prime/pole/Gamma residual on the same compact-support
source class. The prime cutoff, pole evaluations, Fourier convention, and
source theorem boundary remain explicit.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open ComplexCompactExhaustion
open scoped ComplexConjugate FourierTransform

namespace SchwartzLineTestFunction

noncomputable section

/-- The Fourier-Laplace source attached to the compactly supported
autocorrelation of a Burnol base test. On the real line it restricts to the
formula-facing Fourier autocorrelation. -/
def burnolFourierLaplaceSource
    (g : SchwartzLineTestFunction) (z : Complex) : Complex :=
  ∫ x : Real,
    Complex.exp (((-2 * Real.pi * x : Real) : Complex) * Complex.I * z) *
      autocorrelation g x

/-- The Fourier-Laplace source has the project Schwartz autocorrelation as
its real restriction. -/
theorem burnolFourierLaplaceSource_ofReal
    (g : SchwartzLineTestFunction) (t : Real) :
    burnolFourierLaplaceSource g (t : Complex) = fourierAutocorrelation g t := by
  rw [burnolFourierLaplaceSource, fourierAutocorrelation,
    SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg (fun z : Complex => z * autocorrelation g x)
  apply congrArg Complex.exp
  push_cast
  ring

/-- The direct completed-zeta pole contribution at the Riemann-Weil
arguments `+i/2` and `-i/2`. -/
def guinandWeilBurnolLiteraturePoleSide
    (g : SchwartzLineTestFunction) : Real :=
  (burnolFourierLaplaceSource g (Complex.I / 2) +
    burnolFourierLaplaceSource g (-Complex.I / 2)).re

/-- The actual literature-normalized residual on the Burnol source: the
existing von-Mangoldt prime side, direct pole evaluations, and existing
completed-zeta Gamma side. -/
def guinandWeilBurnolLiteratureResidualSide
    (g : SchwartzLineTestFunction) : Real :=
  guinandWeilLiteraturePrimeSide (fourierAutocorrelation g) +
    guinandWeilBurnolLiteraturePoleSide g +
      guinandWeilLiteratureGammaSide (fourierAutocorrelation g)

/-- One multiplicity-aware completed-zeta zero weight for the Burnol source.
Project-known trivial zeroes are assigned to the completed-zeta residual and
therefore contribute zero here. -/
def guinandWeilBurnolLiteratureZeroWeight
    (g : SchwartzLineTestFunction) (rho : ZetaZeroSubtype) : Real :=
  by
    classical
    exact
      if IsTrivialZetaZero (rho : Complex) then 0
      else
        zetaZeroMultiplicityReal rho *
          (burnolFourierLaplaceSource g
            (riemannWeilZeroArgument (rho : Complex))).re

/-- The multiplicity-aware completed-zeta zero side of the Burnol source. -/
def guinandWeilBurnolLiteratureZeroSide
    (g : SchwartzLineTestFunction) : Real :=
  ∑' rho : ZetaZeroSubtype, guinandWeilBurnolLiteratureZeroWeight g rho

/-- The borrowed/source Guinand-Weil theorem in the exact Burnol
normalization. Entirety and absolute zero-side convergence remain visible
alongside the formula identity. -/
structure BurnolGuinandWeilSourceAssumptions
    (g : SchwartzLineTestFunction) : Prop where
  source_entire : Differentiable Complex (burnolFourierLaplaceSource g)
  zeroSide_summable :
    Summable (fun rho : ZetaZeroSubtype =>
      norm (guinandWeilBurnolLiteratureZeroWeight g rho))
  formula :
    guinandWeilBurnolLiteratureZeroSide g =
      guinandWeilBurnolLiteratureResidualSide g

/-- Fourier involution sends the formula-facing autocorrelation back to the
reflected physical autocorrelation. -/
theorem fourier_fourierAutocorrelation_apply
    (g : SchwartzLineTestFunction) (x : Real) :
    (𝓕 (fourierAutocorrelation g)) x = autocorrelation g (-x) := by
  rw [SchwartzMap.fourier_coe]
  calc
    (𝓕 (fourierAutocorrelation g : Real → Complex)) x =
        (𝓕⁻ (fourierAutocorrelation g : Real → Complex)) (-x) := by
      symm
      simpa using
        Real.fourierInv_eq_fourier_neg
          (fourierAutocorrelation g : Real → Complex) (-x)
    _ = autocorrelation g (-x) := by
      rw [← SchwartzMap.fourierInv_coe]
      simp [fourierAutocorrelation]

/-- A support interval kills the autocorrelation at either sign once the
absolute displacement is strictly larger than twice the radius. -/
theorem autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
    {g : SchwartzLineTestFunction} {r x : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hx : 2 * r < |x|) :
    autocorrelation g x = 0 := by
  rw [autocorrelation_apply, MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases hgt : g t = 0
  · simp [hgt]
  · have ht := hsupport hgt
    have houtside : t - x ∉ Set.Icc (-r) r := by
      intro hmem
      by_cases hxnonneg : 0 ≤ x
      · rw [abs_of_nonneg hxnonneg] at hx
        linarith [ht.2, hmem.1]
      · have hxneg : x < 0 := lt_of_not_ge hxnonneg
        rw [abs_of_neg hxneg] at hx
        linarith [ht.1, hmem.2]
    have hgshift : g (t - x) = 0 := by
      by_contra hne
      exact houtside (hsupport hne)
    simp [star_apply, hgshift]

/-- On Burnol's exact support window, every nonzero von-Mangoldt sample lies
outside the autocorrelation support. Hence each literature-normalized prime
term vanishes separately. -/
theorem guinandWeilLiteraturePrimeTerm_fourierAutocorrelation_eq_zero
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement)
    (n : Nat) :
    guinandWeilLiteraturePrimeTerm (fourierAutocorrelation g) n = 0 := by
  by_cases hLambda : ArithmeticFunction.vonMangoldt n = 0
  · simp [guinandWeilLiteraturePrimeTerm, hLambda]
  · have hprimePow : IsPrimePow n :=
      ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hLambda
    have hnTwo : 2 ≤ n := hprimePow.one_lt
    have hnCast : (2 : Real) ≤ (n : Real) := by exact_mod_cast hnTwo
    have hlog : Real.log 2 ≤ Real.log (n : Real) :=
      Real.log_le_log (by norm_num) hnCast
    have hdenPos : 0 < 2 * Real.pi := by positivity
    have hsamplePos : 0 < Real.log (n : Real) / (2 * Real.pi) := by
      exact div_pos (Real.log_pos (by exact_mod_cast hprimePow.one_lt)) hdenPos
    have hsampleCutoff :
        2 * r < Real.log (n : Real) / (2 * Real.pi) := by
      exact hcutoff.trans_le
        (div_le_div_of_nonneg_right hlog hdenPos.le)
    have hpositiveSample :
        autocorrelation g (Real.log (n : Real) / (2 * Real.pi)) = 0 :=
      autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
        hsupport (by simpa [abs_of_pos hsamplePos] using hsampleCutoff)
    have hnegativeSample :
        autocorrelation g (-Real.log (n : Real) / (2 * Real.pi)) = 0 := by
      apply autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
        hsupport
      rw [show -Real.log (n : Real) / (2 * Real.pi) =
          -(Real.log (n : Real) / (2 * Real.pi)) by ring,
        abs_neg, abs_of_pos hsamplePos]
      exact hsampleCutoff
    unfold guinandWeilLiteraturePrimeTerm
    change
      -(1 / (2 * Real.pi)) *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
            (((𝓕 (fourierAutocorrelation g))
                (Real.log (n : Real) / (2 * Real.pi))).re +
              ((𝓕 (fourierAutocorrelation g))
                (-Real.log (n : Real) / (2 * Real.pi))).re) = 0
    rw [fourier_fourierAutocorrelation_apply,
      fourier_fourierAutocorrelation_apply]
    rw [show -(Real.log (n : Real) / (2 * Real.pi)) =
        -Real.log (n : Real) / (2 * Real.pi) by ring,
      show -(-Real.log (n : Real) / (2 * Real.pi)) =
        Real.log (n : Real) / (2 * Real.pi) by ring,
      hnegativeSample, hpositiveSample]
    simp

/-- The complete literature prime side vanishes on the fixed-support Burnol
class. This is the actual prime-power cutoff, not a replacement assumption. -/
theorem guinandWeilLiteraturePrimeSide_fourierAutocorrelation_eq_zero
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement) :
    guinandWeilLiteraturePrimeSide (fourierAutocorrelation g) = 0 := by
  unfold guinandWeilLiteraturePrimeSide
  have hzero :
      guinandWeilLiteraturePrimeTerm (fourierAutocorrelation g) = 0 := by
    funext n
    exact guinandWeilLiteraturePrimeTerm_fourierAutocorrelation_eq_zero
      hsupport hcutoff n
  rw [hzero]
  exact tsum_zero

end

end SchwartzLineTestFunction

end RiemannHypothesisProject
