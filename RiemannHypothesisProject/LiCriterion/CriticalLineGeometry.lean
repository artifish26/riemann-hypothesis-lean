import RiemannHypothesisProject.LocalRH
import Mathlib.Analysis.Complex.Basic

/-!
# Critical-line Li geometry

This module contains the elementary critical-line point and Li-ratio geometry
used by the Li criterion positivity helpers.
-/

namespace RiemannHypothesisProject

open ComplexConjugate
/--
The critical-line Li ratio attached to the point `1 / 2 + i t`.

For a zero `rho`, the classical Li summand is built from
`1 - (1 - rho⁻¹)^n`.  On the critical line the ratio `1 - rho⁻¹` has norm
one, which is the elementary positivity mechanism used below.
-/
noncomputable def criticalLineLiRatio (t : Real) : Complex :=
  1 - (criticalLinePoint t)⁻¹

/-- A critical-line point is never zero. -/
theorem criticalLinePoint_ne_zero (t : Real) :
    criticalLinePoint t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [criticalLinePoint] at hre

/-- Negating the critical-line height conjugates the critical-line point. -/
theorem criticalLinePoint_neg_eq_conj (t : Real) :
    criticalLinePoint (-t) = conj (criticalLinePoint t) := by
  apply Complex.ext
  · simp [criticalLinePoint]
  · simp [criticalLinePoint]

/-- On the critical line, `rho - 1` is `-conj rho`. -/
theorem criticalLinePoint_sub_one_eq_neg_conj (t : Real) :
    criticalLinePoint t - 1 = -conj (criticalLinePoint t) := by
  apply Complex.ext
  · simp [criticalLinePoint]
    ring
  · simp [criticalLinePoint]

/--
The critical-line Li ratio is a quotient of conjugates, hence lies on the unit
circle.
-/
theorem criticalLineLiRatio_eq_neg_conj_div (t : Real) :
    criticalLineLiRatio t =
      -conj (criticalLinePoint t) / criticalLinePoint t := by
  have hne : criticalLinePoint t ≠ 0 := criticalLinePoint_ne_zero t
  unfold criticalLineLiRatio
  calc
    1 - (criticalLinePoint t)⁻¹ =
        (criticalLinePoint t - 1) / criticalLinePoint t := by
      field_simp [hne]
    _ = -conj (criticalLinePoint t) / criticalLinePoint t := by
      rw [criticalLinePoint_sub_one_eq_neg_conj]

/-- The critical-line Li ratio has norm one. -/
theorem criticalLineLiRatio_norm (t : Real) :
    ‖criticalLineLiRatio t‖ = 1 := by
  have hnorm_ne :
      ‖criticalLinePoint t‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (criticalLinePoint_ne_zero t)
  rw [criticalLineLiRatio_eq_neg_conj_div, Complex.norm_div, norm_neg,
    Complex.norm_conj]
  exact div_self hnorm_ne

/-- Negating the height conjugates the critical-line Li ratio. -/
theorem criticalLineLiRatio_neg_eq_conj (t : Real) :
    criticalLineLiRatio (-t) = conj (criticalLineLiRatio t) := by
  unfold criticalLineLiRatio
  rw [criticalLinePoint_neg_eq_conj]
  simp
end RiemannHypothesisProject