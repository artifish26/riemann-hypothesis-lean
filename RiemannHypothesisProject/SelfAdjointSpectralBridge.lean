import RiemannHypothesisProject.LocalRH
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Self-adjoint spectral bridge

This file connects Mathlib's spectral theorem infrastructure to the project's
Hilbert-Polya-style interfaces.

The result here is conditional and structural: if nontrivial zeta zeroes in a
chosen family are parametrized by eigenvalues of a symmetric operator as
`1 / 2 + i * μ`, then those zeroes lie on the critical line because such
eigenvalues are real.
-/

namespace RiemannHypothesisProject

open scoped ComplexConjugate

/-- Eigenvalues of a symmetric complex-linear operator are fixed by conjugation. -/
theorem symmetric_eigenvalue_conj_eq_self
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : Module.End ℂ E} {μ : ℂ}
    (hT : T.IsSymmetric) (hμ : T.HasEigenvalue μ) :
    conj μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

/-- Eigenvalues of a symmetric complex-linear operator are real. -/
theorem symmetric_eigenvalue_eq_ofReal_re
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : Module.End ℂ E} {μ : ℂ}
    (hT : T.IsSymmetric) (hμ : T.HasEigenvalue μ) :
    (μ.re : ℂ) = μ :=
  Complex.conj_eq_iff_re.mp (symmetric_eigenvalue_conj_eq_self hT hμ)

/-- Eigenvalues of a symmetric complex-linear operator have a real height. -/
theorem symmetric_eigenvalue_has_real_height
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : Module.End ℂ E} {μ : ℂ}
    (hT : T.IsSymmetric) (hμ : T.HasEigenvalue μ) :
    ∃ t : ℝ, (t : ℂ) = μ :=
  ⟨μ.re, symmetric_eigenvalue_eq_ofReal_re hT hμ⟩

/--
If a complex number is built as `1 / 2 + i * μ`, where `μ` is an eigenvalue of
a symmetric operator, then it lies on the critical line.
-/
theorem criticalLine_of_symmetric_eigenvalue
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : Module.End ℂ E} {μ s : ℂ}
    (hT : T.IsSymmetric) (hμ : T.HasEigenvalue μ)
    (hs : s = (1 / 2 : ℂ) + μ * Complex.I) :
    IsCriticalLine s := by
  rw [hs]
  rw [← symmetric_eigenvalue_eq_ofReal_re hT hμ]
  exact criticalLinePoint_on_line μ.re

/--
Local RH from a self-adjoint eigenvalue parametrization of the zeroes in a
family.

This is the checked Hilbert-Polya bridge: the hard work is to supply the
operator and prove that the relevant zeta zeroes are parametrized by its
eigenvalues. Once that is supplied, critical-line membership follows from
self-adjointness.
-/
theorem RHOn.of_selfAdjointEigenvalueParametrization
    {family : ℂ → Prop}
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : Module.End ℂ E}
    (hT : T.IsSymmetric)
    (eigenvalue : ∀ s : ℂ, family s → IsNontrivialZetaZero s → ℂ)
    (hasEigenvalue :
      ∀ (s : ℂ) (hs_family : family s) (hs_zero : IsNontrivialZetaZero s),
        T.HasEigenvalue (eigenvalue s hs_family hs_zero))
    (realizes_zeroes :
      ∀ (s : ℂ) (hs_family : family s) (hs_zero : IsNontrivialZetaZero s),
        s = (1 / 2 : ℂ) + eigenvalue s hs_family hs_zero * Complex.I) :
    RHOn family := by
  intro s hs_family hs_zero
  exact criticalLine_of_symmetric_eigenvalue hT
    (hasEigenvalue s hs_family hs_zero)
    (realizes_zeroes s hs_family hs_zero)

end RiemannHypothesisProject
