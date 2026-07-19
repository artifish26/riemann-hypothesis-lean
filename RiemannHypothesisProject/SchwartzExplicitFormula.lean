import RiemannHypothesisProject.ExplicitFormulaSkeleton
import RiemannHypothesisProject.SchwartzLineTestFunction

/-!
# Schwartz explicit-formula track

This file starts replacing the fully abstract Phase 5 interfaces with a concrete
analytic test-function class: Schwartz functions on the real line.

The explicit-formula sides are still fields, because the actual Riemann-Weil
formula has not been formalized yet. The test-function class and the toy
quadratic form are concrete.
-/

namespace RiemannHypothesisProject

open scoped FourierTransform

/-- Fourier transform on the chosen Schwartz test-function class. -/
noncomputable def SchwartzLineTestFunction.fourier
    (f : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  𝓕 f

/--
At frequency zero, the Fourier transform of a Schwartz line test is its
ordinary integral.  This is the bridge used by the shared-zero obstruction:
zero integral gives a Fourier zero at the origin.
-/
theorem SchwartzLineTestFunction.fourier_zero_eq_integral
    (f : SchwartzLineTestFunction) :
    (SchwartzLineTestFunction.fourier f) (0 : Real) =
      ∫ x : Real, f x := by
  unfold SchwartzLineTestFunction.fourier
  rw [SchwartzMap.fourier_coe]
  rw [Real.fourier_real_eq]
  simp

/-- A zero integral gives a Fourier zero at the origin. -/
theorem SchwartzLineTestFunction.fourier_zero_eq_zero_of_integral_eq_zero
    (f : SchwartzLineTestFunction)
    (h_integral_zero : (∫ x : Real, f x) = 0) :
    (SchwartzLineTestFunction.fourier f) (0 : Real) = 0 := by
  rw [SchwartzLineTestFunction.fourier_zero_eq_integral, h_integral_zero]

/-- Inverse Fourier transform on the chosen Schwartz test-function class. -/
noncomputable def SchwartzLineTestFunction.fourierInv
    (f : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  𝓕⁻ f

/-- The L2-energy quadratic form on Schwartz test functions. -/
noncomputable def schwartzL2Energy (f : SchwartzLineTestFunction) : ℝ :=
  ∫ x : ℝ, ‖f x‖ ^ 2

/-- The L2-energy quadratic form is nonnegative. -/
theorem schwartzL2Energy_nonneg (f : SchwartzLineTestFunction) :
    0 ≤ schwartzL2Energy f := by
  unfold schwartzL2Energy
  exact MeasureTheory.integral_nonneg fun x => sq_nonneg ‖f x‖

/-- Fourier transform preserves the L2-energy of Schwartz functions. -/
theorem schwartzL2Energy_fourier_eq (f : SchwartzLineTestFunction) :
    schwartzL2Energy (SchwartzLineTestFunction.fourier f) =
      schwartzL2Energy f := by
  unfold schwartzL2Energy SchwartzLineTestFunction.fourier
  exact SchwartzMap.integral_norm_sq_fourier f

/--
An explicit-formula normalization whose test functions are Schwartz functions
on the real line.
-/
structure SchwartzExplicitFormulaNormalization where
  zeroSide : SchwartzLineTestFunction → ℝ
  primeSide : SchwartzLineTestFunction → ℝ
  poleSide : SchwartzLineTestFunction → ℝ
  gammaSide : SchwartzLineTestFunction → ℝ
  explicitFormula :
    ∀ f : SchwartzLineTestFunction,
      zeroSide f = primeSide f + poleSide f + gammaSide f

/-- Forget a Schwartz normalization to the general explicit-formula normalization. -/
def SchwartzExplicitFormulaNormalization.toExplicitFormulaNormalization
    (normalization : SchwartzExplicitFormulaNormalization) :
    ExplicitFormulaNormalization where
  TestFunction := SchwartzLineTestFunction
  zeroSide := normalization.zeroSide
  primeSide := normalization.primeSide
  poleSide := normalization.poleSide
  gammaSide := normalization.gammaSide
  explicitFormula := normalization.explicitFormula

/--
A local explicit-formula criterion whose test functions are Schwartz functions
on the real line.
-/
structure SchwartzExplicitFormulaLocalCriterion (family : ℂ → Prop) extends
    SchwartzExplicitFormulaNormalization where
  quadraticForm : SchwartzLineTestFunction → ℝ
  quadraticForm_eq_zeroSide :
    ∀ f : SchwartzLineTestFunction, quadraticForm f = zeroSide f
  positivity_implies_RHOn :
    (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) → RHOn family

/-- Forget a Schwartz local criterion to the general explicit-formula local criterion. -/
def SchwartzExplicitFormulaLocalCriterion.toExplicitFormulaLocalCriterion
    {family : ℂ → Prop}
    (criterion : SchwartzExplicitFormulaLocalCriterion family) :
    ExplicitFormulaLocalCriterion family where
  TestFunction := SchwartzLineTestFunction
  zeroSide := criterion.zeroSide
  primeSide := criterion.primeSide
  poleSide := criterion.poleSide
  gammaSide := criterion.gammaSide
  explicitFormula := criterion.explicitFormula
  quadraticForm := criterion.quadraticForm
  quadraticForm_eq_zeroSide := criterion.quadraticForm_eq_zeroSide
  positivity_implies_RHOn := criterion.positivity_implies_RHOn

/-- Positivity for a Schwartz explicit-formula criterion proves `RHOn`. -/
theorem RHOn.of_schwartzExplicitFormulaLocalCriterion
    {family : ℂ → Prop}
    (criterion : SchwartzExplicitFormulaLocalCriterion family)
    (hpos : ∀ f : SchwartzLineTestFunction, 0 ≤ criterion.quadraticForm f) :
    RHOn family :=
  RHOn.of_explicitFormulaLocalCriterion
    criterion.toExplicitFormulaLocalCriterion hpos

end RiemannHypothesisProject
