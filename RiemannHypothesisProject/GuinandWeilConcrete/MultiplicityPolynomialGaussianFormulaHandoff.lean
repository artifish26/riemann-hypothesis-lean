import RiemannHypothesisProject.GuinandWeilConcrete.LiteratureNormalization
import RiemannHypothesisProject.GuinandWeilConcrete.UnconditionalMultiplicityPolynomialGaussianZeroSide
import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicity

/-!
# Multiplicity-aware polynomial-Gaussian formula handoff

This module is the endpoint assembly between the unconditional xi/Jensen
zero-side estimates and the literature-normalized Guinand-Weil formula.
The zero side counts analytic multiplicity, its finite compact-exhaustion
windows converge without a counting or decay hypothesis, and a finite contour
identity with vanishing error therefore yields the exact restricted formula.
-/

namespace RiemannHypothesisProject

open Filter
open ComplexCompactExhaustion
open scoped BigOperators Topology

noncomputable section

/-- The faithful completed-zeta zero weight in the literature-normalized
polynomial-Gaussian formula. -/
def guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
    (p : Polynomial Complex) (rho : ZetaZeroSubtype) : Real :=
  zetaZeroMultiplicityReal rho *
    guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho

/-- The multiplicity-aware limiting zero side of the literature-normalized
polynomial-Gaussian formula. -/
def guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
    (p : Polynomial Complex) : Real :=
  ∑' rho : ZetaZeroSubtype,
    guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight p rho

/-- The multiplicity-aware zero side truncated to one compact-exhaustion
window. -/
def guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat) : Real :=
  exhaustion.zetaZeroWindowSum cutoff
    (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight p)

/-- The literature prime side truncated by the natural-index partial sum. -/
def guinandWeilPiPolynomialGaussianLiteratureTruncatedPrimeSide
    (p : Polynomial Complex) (cutoff : Nat) : Real :=
  (Finset.range (cutoff + 1)).sum
    (guinandWeilLiteraturePrimeTerm
      (guinandWeilPiPolynomialGaussianSchwartz p))

/-- The literature-normalized residual side with only its prime series
truncated. -/
def guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide
    (p : Polynomial Complex) (cutoff : Nat) : Real :=
  guinandWeilPiPolynomialGaussianLiteratureTruncatedPrimeSide p cutoff +
    guinandWeilPiPolynomialGaussianLiteraturePoleSide p +
      guinandWeilLiteratureGammaSide
        (guinandWeilPiPolynomialGaussianSchwartz p)

/-- The multiplicity-correct restricted Guinand-Weil formula proposition for
one polynomial-Gaussian source. -/
def GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula
    (p : Polynomial Complex) : Prop :=
  guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide p =
    guinandWeilPiPolynomialGaussianLiteratureResidualSide p

/-- The borrowed finite contour identity, with a visible signed error, in the
multiplicity-correct literature normalization. -/
def GuinandWeilPiMultiplicityPolynomialGaussianFiniteCutoffIdentityWithError
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat → Real)
    (cutoff : Nat) : Prop :=
  guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
      p exhaustion cutoff =
    guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide p cutoff +
      errorSide cutoff

/-- The multiplicity-aware literature zero weight is unconditionally
absolutely summable. -/
theorem summable_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      norm
        (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
          p rho)) := by
  simpa [guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight] using
    ComplexCompactExhaustion.summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional
      p

/-- The multiplicity-aware literature zero weight is unconditionally
summable. -/
theorem summable_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
    (p : Polynomial Complex) :
    Summable
      (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight p) :=
  (summable_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
    p).of_norm

/-- Every compact exhaustion gives the finite zero-window limit needed by the
restricted formula. -/
theorem tendsto_guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Tendsto
      (guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
        p exhaustion)
      atTop
      (nhds
        (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide p)) := by
  change Tendsto
    (fun cutoff : Nat =>
      exhaustion.zetaZeroWindowSum cutoff
        (fun rho : ZetaZeroSubtype =>
          zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))
    atTop
    (nhds
      (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))
  exact
    ComplexCompactExhaustion.tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_unconditional
      p exhaustion

/-- The absolute contribution outside the formula's compact zero window
tends to zero unconditionally. -/
theorem tendsto_tsum_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight_compl
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Tendsto
      (fun cutoff : Nat =>
        ∑' rho :
          {rho : ZetaZeroSubtype //
            rho ∉ exhaustion.zetaZeroSubtypeFinset cutoff},
          norm
            (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
              p rho.1))
      atTop (nhds 0) := by
  simpa [guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight] using
    ComplexCompactExhaustion.tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_unconditional
      p exhaustion

/-- At every cutoff, the signed literature zero-side truncation error is
bounded by the absolute complementary contribution. -/
theorem norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide_sub_truncated_le
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat) :
    norm
        (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide p -
          guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
            p exhaustion cutoff) ≤
      ∑' rho :
        {rho : ZetaZeroSubtype //
          rho ∉ exhaustion.zetaZeroSubtypeFinset cutoff},
        norm
          (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
            p rho.1) := by
  let weight : ZetaZeroSubtype → Real :=
    guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight p
  have hnorm : Summable (fun rho : ZetaZeroSubtype => norm (weight rho)) := by
    simpa [weight] using
      summable_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight
        p
  have hsummable : Summable weight := hnorm.of_norm
  unfold guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
  unfold guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
  unfold ComplexCompactExhaustion.zetaZeroWindowSum
  change
    norm
        ((∑' rho : ZetaZeroSubtype, weight rho) -
          ∑ rho ∈ exhaustion.zetaZeroSubtypeFinset cutoff, weight rho) ≤
      ∑' rho :
        {rho : ZetaZeroSubtype //
          rho ∉ exhaustion.zetaZeroSubtypeFinset cutoff},
        norm (weight rho.1)
  rw [← hsummable.sum_add_tsum_subtype_compl
    (exhaustion.zetaZeroSubtypeFinset cutoff), add_sub_cancel_left]
  exact norm_tsum_le_tsum_norm (hnorm.subtype _)

/-- Consequently, the signed literature zero-side truncation error tends to
zero without any counting or decay parameter. -/
theorem tendsto_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide_sub_truncated
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Tendsto
      (fun cutoff : Nat =>
        norm
          (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide p -
            guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
              p exhaustion cutoff))
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall fun cutoff => norm_nonneg _
  · exact Eventually.of_forall fun cutoff =>
      norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide_sub_truncated_le
        p exhaustion cutoff
  · exact
      tendsto_tsum_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight_compl
        p exhaustion

/-- The literature-normalized residual cutoffs converge: the prime series is
absolutely summable and the pole and gamma terms are constant. -/
theorem tendsto_guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide
    (p : Polynomial Complex) :
    Tendsto
      (guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide p)
      atTop
      (nhds (guinandWeilPiPolynomialGaussianLiteratureResidualSide p)) := by
  have hprime :
      Tendsto
        (guinandWeilPiPolynomialGaussianLiteratureTruncatedPrimeSide p)
        atTop
        (nhds
          (guinandWeilLiteraturePrimeSide
            (guinandWeilPiPolynomialGaussianSchwartz p))) := by
    change Tendsto
      (fun cutoff : Nat =>
        (Finset.range (cutoff + 1)).sum
          (guinandWeilLiteraturePrimeTerm
            (guinandWeilPiPolynomialGaussianSchwartz p)))
      atTop
      (nhds
        (guinandWeilLiteraturePrimeSide
          (guinandWeilPiPolynomialGaussianSchwartz p)))
    simpa [guinandWeilLiteraturePrimeSide, Function.comp_def] using
      (summable_guinandWeilLiteraturePrimeTerm_guinandWeilPiPolynomialGaussianSchwartz
        p).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  change Tendsto
    (fun cutoff : Nat =>
      guinandWeilPiPolynomialGaussianLiteratureTruncatedPrimeSide p cutoff +
        guinandWeilPiPolynomialGaussianLiteraturePoleSide p +
          guinandWeilLiteratureGammaSide
            (guinandWeilPiPolynomialGaussianSchwartz p))
    atTop
    (nhds
      (guinandWeilLiteraturePrimeSide
          (guinandWeilPiPolynomialGaussianSchwartz p) +
        guinandWeilPiPolynomialGaussianLiteraturePoleSide p +
          guinandWeilLiteratureGammaSide
            (guinandWeilPiPolynomialGaussianSchwartz p)))
  exact (hprime.add tendsto_const_nhds).add tendsto_const_nhds

/-- A finite literature-normalized contour identity with vanishing signed
error yields the exact multiplicity-aware restricted formula.  All p-series
input has already been discharged by xi/Jensen. -/
theorem guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedError
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide : Nat → Real)
    (hfinite :
      ∀ cutoff : Nat,
        GuinandWeilPiMultiplicityPolynomialGaussianFiniteCutoffIdentityWithError
          p exhaustion errorSide cutoff)
    (herror : Tendsto errorSide atTop (nhds 0)) :
    GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula p := by
  have hzero :=
    tendsto_guinandWeilPiMultiplicityPolynomialGaussianLiteratureTruncatedZeroSide
      p exhaustion
  have hzero_as_residual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide
              p cutoff +
            errorSide cutoff)
        atTop
        (nhds
          (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide p)) :=
    hzero.congr'
      (Eventually.of_forall fun cutoff => hfinite cutoff)
  have hresidual_error :
      Tendsto
        (fun cutoff : Nat =>
          guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide
              p cutoff +
            errorSide cutoff)
        atTop
        (nhds
          (guinandWeilPiPolynomialGaussianLiteratureResidualSide p + 0)) :=
    (tendsto_guinandWeilPiPolynomialGaussianLiteratureTruncatedResidualSide p).add
      herror
  have hlimit :
      guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide p =
        guinandWeilPiPolynomialGaussianLiteratureResidualSide p + 0 :=
    tendsto_nhds_unique hzero_as_residual_error hresidual_error
  simpa [GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula] using
    hlimit

/-- Eventual domination by a vanishing nonnegative envelope supplies the
signed-error convergence required by the restricted formula handoff. -/
theorem guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedEventualErrorEnvelope
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    (errorSide errorEnvelope : Nat → Real)
    (hfinite :
      ∀ cutoff : Nat,
        GuinandWeilPiMultiplicityPolynomialGaussianFiniteCutoffIdentityWithError
          p exhaustion errorSide cutoff)
    (herror_bound :
      ∀ᶠ cutoff : Nat in atTop,
        |errorSide cutoff| ≤ errorEnvelope cutoff)
    (henvelope_zero : Tendsto errorEnvelope atTop (nhds 0)) :
    GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula p := by
  apply
    guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedError
      p exhaustion errorSide hfinite
  have habs :
      Tendsto (fun cutoff : Nat => |errorSide cutoff|) atTop (nhds 0) :=
    squeeze_zero'
      (Eventually.of_forall fun cutoff : Nat => abs_nonneg (errorSide cutoff))
      herror_bound henvelope_zero
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

end

end RiemannHypothesisProject
