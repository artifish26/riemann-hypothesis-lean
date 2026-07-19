import Mathlib.Analysis.Fourier.Convolution
import RiemannHypothesisProject.WeilPositivity.LinearFunctionalGuardrail
import RiemannHypothesisProject.WeilPositivity.SchwartzInvolution

/-!
# Schwartz autocorrelation and the genuine Weil-form interface

The explicit-formula distribution is linear in a formula test.  The associated
Weil form is obtained by evaluating that functional on the autocorrelation
`g * g★`, keeping the base test and formula test as distinct arguments.
-/

namespace RiemannHypothesisProject

open scoped Convolution

namespace SchwartzLineTestFunction

/-- The convolution square `g * g★`, which is again a Schwartz line test. -/
noncomputable def autocorrelation
    (g : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  SchwartzMap.convolution (ContinuousLinearMap.mul Complex Complex) g (star g)

/-- Autocorrelation evaluated through mathlib's function-level convolution. -/
theorem autocorrelation_apply (g : SchwartzLineTestFunction) (x : Real) :
    autocorrelation g x =
      (g ⋆[ContinuousLinearMap.mul Complex Complex] star g) x := by
  exact SchwartzMap.convolution_apply
    (ContinuousLinearMap.mul Complex Complex) g (star g) x

/-- Complex scaling of an autocorrelation produces its squared modulus factor. -/
theorem autocorrelation_smul (c : Complex) (g : SchwartzLineTestFunction) :
    autocorrelation (c • g) =
      (c * (starRingEnd Complex) c) • autocorrelation g := by
  simp only [autocorrelation, star_smul, map_smul]
  change (starRingEnd Complex) c • (c • autocorrelation g) =
    (c * (starRingEnd Complex) c) • autocorrelation g
  rw [smul_smul, mul_comm]

/-- Real scaling displays autocorrelation as a quadratic map. -/
theorem autocorrelation_real_smul (r : Real) (g : SchwartzLineTestFunction) :
    autocorrelation (r • g) = r ^ 2 • autocorrelation g := by
  change autocorrelation ((r : Complex) • g) =
    ((r ^ 2 : Real) : Complex) • autocorrelation g
  rw [autocorrelation_smul]
  simp [pow_two]

end SchwartzLineTestFunction

/--
Data for a genuine Schwartz Weil form.  The stored object is the linear
explicit-formula functional; its quadratic form is derived from
autocorrelation rather than supplied as an unrelated function.
-/
structure SchwartzWeilQuadraticFormData where
  formulaFunctional : SchwartzLineTestFunction →ₗ[Real] Real

namespace SchwartzWeilQuadraticFormData

/-- Raw whole-space positivity would force the formula functional to vanish. -/
theorem formulaFunctional_eq_zero_of_raw_nonnegative
    (data : SchwartzWeilQuadraticFormData)
    (h_nonnegative : ∀ f : SchwartzLineTestFunction,
      0 ≤ data.formulaFunctional f) :
    data.formulaFunctional = 0 :=
  realLinearMap_eq_zero_of_nonnegative data.formulaFunctional h_nonnegative

/-- The base-test-to-formula-test map used by the Weil form. -/
noncomputable def formulaTest
    (_data : SchwartzWeilQuadraticFormData)
    (g : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  SchwartzLineTestFunction.autocorrelation g

/-- The genuine quadratic form `Q(g) = W(g * g★)`. -/
noncomputable def quadraticForm
    (data : SchwartzWeilQuadraticFormData)
    (g : SchwartzLineTestFunction) : Real :=
  data.formulaFunctional (data.formulaTest g)

/-- The Weil form has the expected real quadratic scaling law. -/
theorem quadraticForm_smul
    (data : SchwartzWeilQuadraticFormData)
    (r : Real)
    (g : SchwartzLineTestFunction) :
    data.quadraticForm (r • g) = r ^ 2 * data.quadraticForm g := by
  change data.formulaFunctional
      (SchwartzLineTestFunction.autocorrelation (r • g)) = _
  rw [SchwartzLineTestFunction.autocorrelation_real_smul]
  simp [quadraticForm, formulaTest]

/-- The genuine Weil form vanishes at the zero base test. -/
@[simp]
theorem quadraticForm_zero (data : SchwartzWeilQuadraticFormData) :
    data.quadraticForm 0 = 0 := by
  simp [quadraticForm, formulaTest, SchwartzLineTestFunction.autocorrelation]

end SchwartzWeilQuadraticFormData

end RiemannHypothesisProject
