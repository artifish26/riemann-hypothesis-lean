import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic

/-!
# Linear-functional positivity guardrail

A real-linear functional that is nonnegative on an entire real vector space
must vanish.  This elementary obstruction prevents the linear distribution in
an explicit formula from being mistaken for Weil's quadratic form.
-/

namespace RiemannHypothesisProject

/-- A real-linear functional nonnegative on its whole domain is the zero map. -/
theorem realLinearMap_eq_zero_of_nonnegative
    {V : Type*} [AddCommGroup V] [Module Real V]
    (functional : V →ₗ[Real] Real)
    (h_nonnegative : ∀ v : V, 0 ≤ functional v) :
    functional = 0 := by
  apply LinearMap.ext
  intro v
  apply le_antisymm
  · have h_neg := h_nonnegative (-v)
    simpa using h_neg
  · exact h_nonnegative v

/-- Whole-space nonnegativity characterizes the zero real-linear functional. -/
theorem realLinearMap_nonnegative_iff_eq_zero
    {V : Type*} [AddCommGroup V] [Module Real V]
    (functional : V →ₗ[Real] Real) :
    (∀ v : V, 0 ≤ functional v) ↔ functional = 0 := by
  constructor
  · exact realLinearMap_eq_zero_of_nonnegative functional
  · rintro rfl
    simp

/-- Every nonzero real-linear functional takes a strictly negative value. -/
theorem realLinearMap_exists_apply_neg_of_ne_zero
    {V : Type*} [AddCommGroup V] [Module Real V]
    (functional : V →ₗ[Real] Real)
    (h_nonzero : functional ≠ 0) :
    ∃ v : V, functional v < 0 := by
  classical
  have h_not_nonnegative : ¬ ∀ v : V, 0 ≤ functional v := fun h =>
    h_nonzero (realLinearMap_eq_zero_of_nonnegative functional h)
  simpa only [not_forall, not_le] using h_not_nonnegative

end RiemannHypothesisProject
