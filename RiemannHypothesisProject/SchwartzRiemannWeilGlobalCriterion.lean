import RiemannHypothesisProject.SchwartzRiemannWeilZeroSide
import RiemannHypothesisProject.LocalRH

/-!
# Global Schwartz Riemann-Weil criterion

This file closes the checked pipeline from the future Riemann-Weil zero-side
specification to the global Riemann Hypothesis statements.

The central structure is a certificate: if future analytic work supplies a
summable zero weight, prime/pole/gamma sides, an explicit-formula identity, a
quadratic-form identification, and positivity strong enough for the universal
family, then Lean derives both the project-local `RHStatement` and Mathlib's
`RiemannHypothesis`.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/--
A complete conditional certificate for the Schwartz Riemann-Weil route to RH.

All analytic content remains explicit in the fields. Theorems below only
transport those fields through the already-checked interfaces.
-/
structure SchwartzRiemannWeilGlobalCriterion where
  zeroSide : SchwartzRiemannWeilZeroSide
  primeSide : SchwartzLineTestFunction → ℝ
  poleSide : SchwartzLineTestFunction → ℝ
  gammaSide : SchwartzLineTestFunction → ℝ
  explicitFormula :
    ∀ f : SchwartzLineTestFunction,
      zeroSide.zeroSide f = primeSide f + poleSide f + gammaSide f
  quadraticForm : SchwartzLineTestFunction → ℝ
  quadraticForm_eq_zeroSide :
    ∀ f : SchwartzLineTestFunction, quadraticForm f = zeroSide.zeroSide f
  positivity :
    ∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f
  positivity_implies_RHOn_univ :
    (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) →
      RHOn (fun _ : ℂ => True)

namespace SchwartzRiemannWeilGlobalCriterion

/-- The global certificate gives a local criterion for the universal family. -/
noncomputable def toLocalCriterion
    (criterion : SchwartzRiemannWeilGlobalCriterion) :
    SchwartzGlobalExplicitFormulaLocalCriterion (fun _ : ℂ => True) :=
  criterion.zeroSide.toGlobalExplicitFormulaLocalCriterion
    criterion.primeSide
    criterion.poleSide
    criterion.gammaSide
    criterion.explicitFormula
    criterion.quadraticForm
    criterion.quadraticForm_eq_zeroSide
    criterion.positivity_implies_RHOn_univ

/-- The global certificate proves `RHOn` for the universal family. -/
theorem RHOn_univ
    (criterion : SchwartzRiemannWeilGlobalCriterion) :
    RHOn (fun _ : ℂ => True) :=
  criterion.zeroSide.RHOn_of_riemannWeilExplicitFormula
    criterion.primeSide
    criterion.poleSide
    criterion.gammaSide
    criterion.explicitFormula
    criterion.quadraticForm
    criterion.quadraticForm_eq_zeroSide
    criterion.positivity_implies_RHOn_univ
    criterion.positivity

/-- The global certificate proves the project-local RH statement. -/
theorem RHStatement
    (criterion : SchwartzRiemannWeilGlobalCriterion) :
    RiemannHypothesisProject.RHStatement :=
  RHStatement_iff_RHOn_univ.mpr criterion.RHOn_univ

/-- The global certificate proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (criterion : SchwartzRiemannWeilGlobalCriterion) :
    RiemannHypothesis :=
  RHStatement_iff_mathlib.mp criterion.RHStatement

/-- Window zero sides for the certificate converge to its quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (criterion : SchwartzRiemannWeilGlobalCriterion)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : ℕ => criterion.zeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (criterion.quadraticForm f)) :=
  criterion.zeroSide.tendsto_windowZeroSide_quadraticForm
    criterion.primeSide
    criterion.poleSide
    criterion.gammaSide
    criterion.explicitFormula
    criterion.quadraticForm
    criterion.quadraticForm_eq_zeroSide
    criterion.positivity_implies_RHOn_univ
    exhaustion
    f

end SchwartzRiemannWeilGlobalCriterion

end RiemannHypothesisProject
