import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Riemann Hypothesis setup

This file gives the project its preferred vocabulary for the Riemann zeta
function, its nontrivial zeroes, and the critical line. The main theorem in
this file proves that the local statement `RHStatement` is exactly Mathlib's
formal `RiemannHypothesis`.
-/

namespace RiemannHypothesisProject

/-- A complex number lies on the critical line. -/
def IsCriticalLine (s : ℂ) : Prop :=
  s.re = (1 / 2 : ℝ)

/-- A zero of the Riemann zeta function. -/
def IsZetaZero (s : ℂ) : Prop :=
  riemannZeta s = 0

/-- The known trivial zeroes of the Riemann zeta function. -/
def IsTrivialZetaZero (s : ℂ) : Prop :=
  ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)

/-- A nontrivial zero, with the pole at `1` excluded to match Mathlib's statement. -/
def IsNontrivialZetaZero (s : ℂ) : Prop :=
  IsZetaZero s ∧ ¬ IsTrivialZetaZero s ∧ s ≠ 1

/-- The project-local RH statement. -/
def RHStatement : Prop :=
  ∀ s : ℂ, IsNontrivialZetaZero s → IsCriticalLine s

theorem RHStatement_iff_mathlib : RHStatement ↔ RiemannHypothesis := by
  unfold RHStatement RiemannHypothesis IsNontrivialZetaZero IsZetaZero
    IsTrivialZetaZero IsCriticalLine
  constructor
  · intro h s hz hnontrivial hne_one
    exact h s ⟨hz, hnontrivial, hne_one⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

/-- Mathlib's theorem that every negative even integer is a trivial zeta zero. -/
theorem trivialZero_is_zetaZero (n : ℕ) :
    IsZetaZero (-2 * ((n : ℂ) + 1)) := by
  unfold IsZetaZero
  exact riemannZeta_neg_two_mul_nat_add_one n

/--
The Riemann zeta function has no zero in the closed half-plane `1 <= re s`.

This imports Mathlib's nonvanishing theorem into the project vocabulary.  It is
one of the genuine analytic facts used by the zero-counting cleanup route.
-/
theorem not_isZetaZero_of_one_le_re {s : ℂ} (hs : 1 <= s.re) :
    ¬ IsZetaZero s := by
  intro hz
  exact (riemannZeta_ne_zero_of_one_le_re hs) hz

/-- Every zeta zero lies strictly to the left of the line `re s = 1`. -/
theorem IsZetaZero.re_lt_one {s : ℂ} (hz : IsZetaZero s) :
    s.re < 1 := by
  by_contra hnot
  exact not_isZetaZero_of_one_le_re (le_of_not_gt hnot) hz

/-- Nontrivial zeta zeroes also lie strictly to the left of `re s = 1`. -/
theorem IsNontrivialZetaZero.re_lt_one {s : ℂ}
    (hz : IsNontrivialZetaZero s) :
    s.re < 1 :=
  hz.1.re_lt_one

/-- The completed zeta function has the expected `s ↔ 1 - s` symmetry. -/
theorem completedZeta_symmetry (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/--
On the absolutely convergent half-plane, the Riemann zeta function respects
complex conjugation.

This is the checked Dirichlet-series base case for the global conjugation
formula used by the height-counting adapters. Extending this identity across
the analytically continued domain remains the separate continuation step.
-/
theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta ((starRingEnd Complex) s) =
      (starRingEnd Complex) (riemannZeta s) := by
  have hsc : 1 < ((starRingEnd Complex) s).re := by
    simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsc,
    zeta_eq_tsum_one_div_nat_add_one_cpow hs,
    Complex.conj_tsum]
  apply tsum_congr
  intro n
  have harg : Not (Complex.arg ((n : Complex) + 1) = Real.pi) := by
    rw [show (n : Complex) + 1 =
        (((n : Real) + 1 : Real) : Complex) by norm_num]
    rw [Complex.arg_ofReal_of_nonneg]
    exact Real.pi_ne_zero.symm
    positivity
  have hpow : ((n : Complex) + 1) ^ ((starRingEnd Complex) s) =
      (starRingEnd Complex) (((n : Complex) + 1) ^ s) := by
    rw [Complex.cpow_conj _ _ harg]
    simp
  rw [hpow]
  simp

end RiemannHypothesisProject
