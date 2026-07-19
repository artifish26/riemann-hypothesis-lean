import RiemannHypothesisProject.SchwartzExplicitFormula
import RiemannHypothesisProject.FiniteZeroWindowExamples

/-!
# Schwartz explicit-formula examples

This file gives a toy Schwartz-backed explicit-formula criterion. It is not the
Riemann-Weil explicit formula. Its purpose is to exercise the Phase 5 interfaces
with a concrete analytic test-function class and a concrete nonnegative
quadratic form.
-/

namespace RiemannHypothesisProject

/--
A toy explicit-formula normalization on Schwartz test functions.

This normalization simply puts the L2-energy on the `zeroSide` and `primeSide`
and sets the other sides to zero. It is useful for checking the API shape, not
for zeta mathematics.
-/
noncomputable def schwartzL2ToyNormalization :
    SchwartzExplicitFormulaNormalization where
  zeroSide := schwartzL2Energy
  primeSide := schwartzL2Energy
  poleSide := fun _ => 0
  gammaSide := fun _ => 0
  explicitFormula := by
    intro f
    simp

/--
A toy local explicit-formula criterion for a finite critical-height family,
using Schwartz test functions and the L2-energy quadratic form.
-/
noncomputable def schwartzL2ToyLocalCriterion
    (heights : Finset ℝ) :
    SchwartzExplicitFormulaLocalCriterion (finiteCriticalFamily heights) where
  zeroSide := schwartzL2ToyNormalization.zeroSide
  primeSide := schwartzL2ToyNormalization.primeSide
  poleSide := schwartzL2ToyNormalization.poleSide
  gammaSide := schwartzL2ToyNormalization.gammaSide
  explicitFormula := schwartzL2ToyNormalization.explicitFormula
  quadraticForm := schwartzL2Energy
  quadraticForm_eq_zeroSide := by
    intro f
    rfl
  positivity_implies_RHOn := fun _ => RHOn_finiteCriticalFamily heights

/--
The toy Schwartz explicit-formula criterion proves `RHOn` for finite
critical-height families.
-/
theorem RHOn_finiteCriticalFamily_from_schwartzL2ToyCriterion
    (heights : Finset ℝ) :
    RHOn (finiteCriticalFamily heights) :=
  RHOn.of_schwartzExplicitFormulaLocalCriterion
    (schwartzL2ToyLocalCriterion heights)
    schwartzL2Energy_nonneg

end RiemannHypothesisProject
