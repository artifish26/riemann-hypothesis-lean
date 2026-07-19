import RiemannHypothesisProject.FiniteWeilCertificate

/-!
# Restricted finite Weil criteria

This file introduces a concrete restricted criterion whose test functions are
finite real-valued functions. It is a stepping stone between the fully abstract
`AbstractWeilCriterion` and a future analytic Weil criterion.
-/

namespace RiemannHypothesisProject

/--
A finite restricted Weil criterion.

The analytic work is represented by `positivity_implies_RH`: a proof that
positivity of this restricted quadratic form is strong enough to imply RH. The
finite work is represented by `quadraticForm`, which can be certified using the
finite positivity tools.
-/
structure FiniteWeilCriterion where
  Index : Type
  indexFintype : Fintype Index
  quadraticForm : FiniteTestFunction Index → ℝ
  positivity_implies_RH :
    (∀ f : FiniteTestFunction Index, 0 ≤ quadraticForm f) → RHStatement

attribute [instance] FiniteWeilCriterion.indexFintype

/-- Convert a finite restricted criterion into the abstract interface. -/
def FiniteWeilCriterion.toAbstractWeilCriterion
    (criterion : FiniteWeilCriterion) : AbstractWeilCriterion where
  TestFunction := FiniteTestFunction criterion.Index
  quadraticForm := criterion.quadraticForm
  positivity_implies_RH := criterion.positivity_implies_RH

/-- Positivity of a finite restricted criterion implies the project-local RH. -/
theorem RHStatement.of_finiteWeilCriterion
    (criterion : FiniteWeilCriterion)
    (hpos : ∀ f : FiniteTestFunction criterion.Index, 0 ≤ criterion.quadraticForm f) :
    RHStatement :=
  criterion.positivity_implies_RH hpos

/-- Positivity of a finite restricted criterion implies Mathlib's RH. -/
theorem mathlib_RH_of_finiteWeilCriterion
    (criterion : FiniteWeilCriterion)
    (hpos : ∀ f : FiniteTestFunction criterion.Index, 0 ≤ criterion.quadraticForm f) :
    RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp
    (RHStatement.of_finiteWeilCriterion criterion hpos)

/--
A finite criterion whose quadratic form is certified by a finite positivity
model.
-/
structure CertifiedRestrictedWeilCriterion where
  criterion : FiniteWeilCriterion
  model : FinitePositivityModel
  encode : FiniteTestFunction criterion.Index → FiniteTestFunction model.Index
  quadraticForm_eq :
    ∀ f : FiniteTestFunction criterion.Index,
      criterion.quadraticForm f = model.quadraticForm (encode f)

/-- A certified restricted criterion has a nonnegative quadratic form. -/
theorem CertifiedRestrictedWeilCriterion.quadraticForm_nonneg
    (certified : CertifiedRestrictedWeilCriterion) :
    ∀ f : FiniteTestFunction certified.criterion.Index,
      0 ≤ certified.criterion.quadraticForm f := by
  intro f
  rw [certified.quadraticForm_eq f]
  exact certified.model.quadraticForm_nonneg (certified.encode f)

/-- A certified restricted criterion implies the project-local RH. -/
theorem CertifiedRestrictedWeilCriterion.RHStatement
    (certified : CertifiedRestrictedWeilCriterion) : RHStatement :=
  RHStatement.of_finiteWeilCriterion certified.criterion
    certified.quadraticForm_nonneg

/-- A certified restricted criterion implies Mathlib's RH. -/
theorem CertifiedRestrictedWeilCriterion.mathlib_RH
    (certified : CertifiedRestrictedWeilCriterion) : RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp certified.RHStatement

end RiemannHypothesisProject
