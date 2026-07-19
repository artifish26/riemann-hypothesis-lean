import RiemannHypothesisProject.RestrictedWeilCriterion
import RiemannHypothesisProject.SpectralModel

/-!
# Local Weil criteria

This file gives the positivity route a local form. A restricted or numerical
criterion should usually prove `RHOn family`, not the full RH, unless it carries
a genuinely global implication.
-/

namespace RiemannHypothesisProject

/--
An abstract local Weil-style criterion for a chosen family of complex numbers.

The theorem payload is deliberately local: positivity of the quadratic form
only implies `RHOn family`.
-/
structure AbstractLocalWeilCriterion (family : ℂ → Prop) where
  TestFunction : Type
  quadraticForm : TestFunction → ℝ
  positivity_implies_RHOn :
    (∀ f : TestFunction, 0 ≤ quadraticForm f) → RHOn family

/-- Positivity of a local Weil criterion proves RH on its family. -/
theorem RHOn.of_localWeilCriterion {family : ℂ → Prop}
    (criterion : AbstractLocalWeilCriterion family)
    (hpos : ∀ f : criterion.TestFunction, 0 ≤ criterion.quadraticForm f) :
    RHOn family :=
  criterion.positivity_implies_RHOn hpos

/--
A finite local Weil criterion.

Its test functions are finite real-valued functions, and its positivity
conclusion is local to `family`.
-/
structure FiniteLocalWeilCriterion (family : ℂ → Prop) where
  Index : Type
  indexFintype : Fintype Index
  quadraticForm : FiniteTestFunction Index → ℝ
  positivity_implies_RHOn :
    (∀ f : FiniteTestFunction Index, 0 ≤ quadraticForm f) → RHOn family

attribute [instance] FiniteLocalWeilCriterion.indexFintype

/-- Convert a finite local criterion into the abstract local interface. -/
def FiniteLocalWeilCriterion.toAbstractLocalWeilCriterion
    {family : ℂ → Prop}
    (criterion : FiniteLocalWeilCriterion family) :
    AbstractLocalWeilCriterion family where
  TestFunction := FiniteTestFunction criterion.Index
  quadraticForm := criterion.quadraticForm
  positivity_implies_RHOn := criterion.positivity_implies_RHOn

/-- Positivity of a finite local criterion proves RH on its family. -/
theorem RHOn.of_finiteLocalWeilCriterion {family : ℂ → Prop}
    (criterion : FiniteLocalWeilCriterion family)
    (hpos : ∀ f : FiniteTestFunction criterion.Index, 0 ≤ criterion.quadraticForm f) :
    RHOn family :=
  criterion.positivity_implies_RHOn hpos

/--
A certificate that a finite local Weil criterion has been reduced to a checked
finite positivity model.
-/
structure CertifiedFiniteLocalWeilCriterion (family : ℂ → Prop) where
  criterion : FiniteLocalWeilCriterion family
  model : FinitePositivityModel
  encode : FiniteTestFunction criterion.Index → FiniteTestFunction model.Index
  quadraticForm_eq :
    ∀ f : FiniteTestFunction criterion.Index,
      criterion.quadraticForm f = model.quadraticForm (encode f)

/-- A certified finite local criterion has a nonnegative quadratic form. -/
theorem CertifiedFiniteLocalWeilCriterion.quadraticForm_nonneg
    {family : ℂ → Prop}
    (certified : CertifiedFiniteLocalWeilCriterion family) :
    ∀ f : FiniteTestFunction certified.criterion.Index,
      0 ≤ certified.criterion.quadraticForm f := by
  intro f
  rw [certified.quadraticForm_eq f]
  exact certified.model.quadraticForm_nonneg (certified.encode f)

/-- A certified finite local criterion proves RH on its family. -/
theorem CertifiedFiniteLocalWeilCriterion.RHOn
    {family : ℂ → Prop}
    (certified : CertifiedFiniteLocalWeilCriterion family) :
    RHOn family :=
  RHOn.of_finiteLocalWeilCriterion certified.criterion
    certified.quadraticForm_nonneg

/-- Build a certified finite local criterion from a sum-of-squares representation. -/
noncomputable def CertifiedFiniteLocalWeilCriterion.of_sumSquares
    {family : ℂ → Prop}
    (criterion : FiniteLocalWeilCriterion family)
    (ι : Type) [Fintype ι]
    (encode : FiniteTestFunction criterion.Index → FiniteTestFunction ι)
    (quadraticForm_eq :
      ∀ f : FiniteTestFunction criterion.Index,
        criterion.quadraticForm f = sumSquaresQuadraticForm (encode f)) :
    CertifiedFiniteLocalWeilCriterion family where
  criterion := criterion
  model := sumSquaresPositivityModel ι
  encode := encode
  quadraticForm_eq := quadraticForm_eq

/-- Build a certified finite local criterion from a finite Gram representation. -/
noncomputable def CertifiedFiniteLocalWeilCriterion.of_finiteGram
    {family : ℂ → Prop}
    (criterion : FiniteLocalWeilCriterion family)
    (ι κ : Type) [Fintype ι] [Fintype κ]
    (feature : κ → ι → ℝ)
    (encode : FiniteTestFunction criterion.Index → FiniteTestFunction ι)
    (quadraticForm_eq :
      ∀ f : FiniteTestFunction criterion.Index,
        criterion.quadraticForm f =
          finiteGramQuadraticForm feature (encode f)) :
    CertifiedFiniteLocalWeilCriterion family where
  criterion := criterion
  model := finiteGramPositivityModel ι κ feature
  encode := encode
  quadraticForm_eq := quadraticForm_eq

end RiemannHypothesisProject
