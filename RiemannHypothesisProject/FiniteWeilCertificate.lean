import RiemannHypothesisProject.ToyPositivity

/-!
# Finite Weil certificates

This file connects the checked finite positivity models to the abstract
Weil-positivity interface.

The point is bookkeeping: if a future restricted Weil quadratic form can be
encoded as a finite positive model, then Lean can transport positivity through
that encoding and apply the RH criterion.
-/

namespace RiemannHypothesisProject

/--
A certificate that an abstract Weil criterion has been reduced to a checked
finite positivity model.

The field `quadraticForm_eq` is the important bridge: it says the criterion's
quadratic form is exactly the finite model's quadratic form after encoding test
functions into finite test functions.
-/
structure FiniteWeilCertificate (criterion : AbstractWeilCriterion) where
  model : FinitePositivityModel
  encode : criterion.TestFunction → FiniteTestFunction model.Index
  quadraticForm_eq :
    ∀ f : criterion.TestFunction,
      criterion.quadraticForm f = model.quadraticForm (encode f)

/-- A bundled abstract Weil criterion together with a finite positivity certificate. -/
structure CertifiedFiniteWeilCriterion where
  criterion : AbstractWeilCriterion
  certificate : FiniteWeilCertificate criterion

/-- Build a finite certificate from a sum-of-squares representation. -/
noncomputable def FiniteWeilCertificate.of_sumSquares
    (criterion : AbstractWeilCriterion)
    (ι : Type) [Fintype ι]
    (encode : criterion.TestFunction → FiniteTestFunction ι)
    (quadraticForm_eq :
      ∀ f : criterion.TestFunction,
        criterion.quadraticForm f = sumSquaresQuadraticForm (encode f)) :
    FiniteWeilCertificate criterion where
  model := sumSquaresPositivityModel ι
  encode := encode
  quadraticForm_eq := quadraticForm_eq

/-- Build a finite certificate from a finite Gram representation. -/
noncomputable def FiniteWeilCertificate.of_finiteGram
    (criterion : AbstractWeilCriterion)
    (ι κ : Type) [Fintype ι] [Fintype κ]
    (feature : κ → ι → ℝ)
    (encode : criterion.TestFunction → FiniteTestFunction ι)
    (quadraticForm_eq :
      ∀ f : criterion.TestFunction,
        criterion.quadraticForm f =
          finiteGramQuadraticForm feature (encode f)) :
    FiniteWeilCertificate criterion where
  model := finiteGramPositivityModel ι κ feature
  encode := encode
  quadraticForm_eq := quadraticForm_eq

/-- A finite Weil certificate proves positivity of the abstract criterion. -/
theorem FiniteWeilCertificate.criterion_nonneg
    {criterion : AbstractWeilCriterion}
    (certificate : FiniteWeilCertificate criterion) :
    ∀ f : criterion.TestFunction, 0 ≤ criterion.quadraticForm f := by
  intro f
  rw [certificate.quadraticForm_eq f]
  exact certificate.model.quadraticForm_nonneg (certificate.encode f)

/-- A finite Weil certificate for an RH criterion implies the project-local RH. -/
theorem RHStatement.of_finiteWeilCertificate
    {criterion : AbstractWeilCriterion}
    (certificate : FiniteWeilCertificate criterion) :
    RHStatement :=
  RHStatement.of_weilCriterion criterion certificate.criterion_nonneg

/-- A finite Weil certificate for an RH criterion implies Mathlib's RH. -/
theorem mathlib_RH_of_finiteWeilCertificate
    {criterion : AbstractWeilCriterion}
    (certificate : FiniteWeilCertificate criterion) :
    RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp
    (RHStatement.of_finiteWeilCertificate certificate)

/-- A bundled certified finite Weil criterion implies the project-local RH. -/
theorem CertifiedFiniteWeilCriterion.RHStatement
    (certified : CertifiedFiniteWeilCriterion) : RHStatement :=
  RHStatement.of_finiteWeilCertificate certified.certificate

/-- A bundled certified finite Weil criterion implies Mathlib's RH. -/
theorem CertifiedFiniteWeilCriterion.mathlib_RH
    (certified : CertifiedFiniteWeilCriterion) : RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp certified.RHStatement

end RiemannHypothesisProject
