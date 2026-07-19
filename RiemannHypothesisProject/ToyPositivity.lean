import RiemannHypothesisProject.WeilPositivity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Toy positivity model

This file formalizes a tiny positivity pattern that will be useful when the
Weil-positivity track becomes concrete: a quadratic form can be nonnegative
because it is visibly a finite sum of squares.

The result here is not a theorem about zeta. It is a checked toy model for the
kind of proof shape we want later.
-/

namespace RiemannHypothesisProject

/-- A finite test function is a real-valued function on a finite index type. -/
abbrev FiniteTestFunction (ι : Type) := ι → ℝ

/-- The simplest positive quadratic form: a finite sum of squares. -/
noncomputable def sumSquaresQuadraticForm {ι : Type} [Fintype ι]
    (f : FiniteTestFunction ι) : ℝ :=
  ∑ i, f i ^ 2

/-- The sum-of-squares quadratic form is nonnegative. -/
theorem sumSquaresQuadraticForm_nonneg {ι : Type} [Fintype ι]
    (f : FiniteTestFunction ι) :
    0 ≤ sumSquaresQuadraticForm f := by
  unfold sumSquaresQuadraticForm
  exact Finset.sum_nonneg fun i _ => sq_nonneg (f i)

/--
A finite positivity model packages a finite test-function type together with a
quadratic form whose nonnegativity has been proved.
-/
structure FinitePositivityModel where
  Index : Type
  indexFintype : Fintype Index
  quadraticForm : FiniteTestFunction Index → ℝ
  quadraticForm_nonneg :
    ∀ f : FiniteTestFunction Index, 0 ≤ quadraticForm f

attribute [instance] FinitePositivityModel.indexFintype

/-- The sum-of-squares construction is a finite positivity model. -/
noncomputable def sumSquaresPositivityModel (ι : Type) [Fintype ι] :
    FinitePositivityModel where
  Index := ι
  indexFintype := inferInstance
  quadraticForm := sumSquaresQuadraticForm
  quadraticForm_nonneg := sumSquaresQuadraticForm_nonneg

/--
A finite Gram-style quadratic form.

The `feature` map sends a feature index `κ` and a test-function index `ι` to a
real coefficient. The quadratic form is the sum, over features, of the square of
the pairing with `f`.
-/
noncomputable def finiteGramQuadraticForm {ι κ : Type} [Fintype ι] [Fintype κ]
    (feature : κ → ι → ℝ) (f : FiniteTestFunction ι) : ℝ :=
  ∑ a, (∑ i, feature a i * f i) ^ 2

/-- The matrix kernel associated to a finite Gram-style feature map. -/
noncomputable def finiteGramKernel {ι κ : Type} [Fintype κ]
    (feature : κ → ι → ℝ) (i j : ι) : ℝ :=
  ∑ a, feature a i * feature a j

/--
The finite Gram feature-square form equals the Rayleigh quotient for its
associated matrix kernel.
-/
theorem finiteGramKernel_quadraticForm {ι κ : Type} [Fintype ι] [Fintype κ]
    (feature : κ → ι → ℝ) (f : FiniteTestFunction ι) :
    (∑ i, ∑ j, f i * finiteGramKernel feature i j * f j) =
      finiteGramQuadraticForm feature f := by
  calc
    (∑ i, ∑ j, f i * finiteGramKernel feature i j * f j)
        = ∑ i, ∑ j, ∑ a, f i * (feature a i * feature a j) * f j := by
          simp [finiteGramKernel, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    _ = ∑ i, ∑ a, ∑ j, f i * (feature a i * feature a j) * f j := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, f i * (feature a i * feature a j) * f j := by
          exact Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, (feature a i * f i) * (feature a j * f j) := by
          simp [mul_comm, mul_left_comm]
    _ = ∑ a, ∑ j, ∑ i, (feature a i * f i) * (feature a j * f j) := by
          apply Finset.sum_congr rfl
          intro a _
          exact Finset.sum_comm
    _ = ∑ a, (∑ i, feature a i * f i) * (∑ j, feature a j * f j) := by
          simp [Finset.sum_mul, Finset.mul_sum]
    _ = finiteGramQuadraticForm feature f := by
          simp [finiteGramQuadraticForm, pow_two]

/-- Every finite Gram-style quadratic form is nonnegative. -/
theorem finiteGramQuadraticForm_nonneg {ι κ : Type} [Fintype ι] [Fintype κ]
    (feature : κ → ι → ℝ) (f : FiniteTestFunction ι) :
    0 ≤ finiteGramQuadraticForm feature f := by
  unfold finiteGramQuadraticForm
  exact Finset.sum_nonneg fun a _ => sq_nonneg (∑ i, feature a i * f i)

/-- Any finite feature map gives a finite positivity model. -/
noncomputable def finiteGramPositivityModel (ι κ : Type) [Fintype ι] [Fintype κ]
    (feature : κ → ι → ℝ) : FinitePositivityModel where
  Index := ι
  indexFintype := inferInstance
  quadraticForm := finiteGramQuadraticForm feature
  quadraticForm_nonneg := finiteGramQuadraticForm_nonneg feature

end RiemannHypothesisProject
