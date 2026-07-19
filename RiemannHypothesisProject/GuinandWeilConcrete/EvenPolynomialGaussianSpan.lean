import Mathlib.Algebra.Polynomial.Basis
import RiemannHypothesisProject.GuinandWeilConcrete.HermitePolynomialBasis

/-!
# Algebraic span of the even polynomial-Gaussian source

This module isolates the exact algebraic source underlying the intended even
Schwartz density theorem.  Real polynomials are sent to the project Schwartz
test obtained from `p(X^2) exp(-pi X^2)`, and the images of the polynomial
monomial basis span precisely the range of that map.

The theorem is deliberately algebraic.  Density of this range in the real,
even Schwartz subspace remains the separate Hermite spectral theorem.
-/

namespace RiemannHypothesisProject

open Module Submodule

noncomputable section

/-- The real-linear even polynomial-Gaussian source map. -/
noncomputable def guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap :
    Polynomial Real →ₗ[Real] SchwartzLineTestFunction where
  toFun := guinandWeilPiEvenPolynomialGaussianSchwartz
  map_add' p q := by
    ext x
    simp [guinandWeilPiEvenPolynomialGaussianSchwartz,
      guinandWeilPiEvenPolynomial, guinandWeilPiPolynomialGaussianSource]
    ring
  map_smul' c p := by
    ext x
    simp [guinandWeilPiEvenPolynomialGaussianSchwartz,
      guinandWeilPiEvenPolynomial, guinandWeilPiPolynomialGaussianSource]
    ring

/-- The `n`th even monomial-Gaussian Schwartz test. -/
noncomputable def guinandWeilPiEvenMonomialGaussianSchwartz
    (n : Nat) : SchwartzLineTestFunction :=
  guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap
    (Polynomial.basisMonomials Real n)

@[simp]
theorem guinandWeilPiEvenMonomialGaussianSchwartz_apply
    (n : Nat) (x : Real) :
    guinandWeilPiEvenMonomialGaussianSchwartz n x =
      ((x : Complex) ^ (2 * n)) *
        guinandWeilPiGaussianSource (x : Complex) := by
  simp [guinandWeilPiEvenMonomialGaussianSchwartz,
    guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap,
    guinandWeilPiEvenPolynomialGaussianSchwartz,
    guinandWeilPiEvenPolynomial, Polynomial.coe_basisMonomials,
    guinandWeilPiPolynomialGaussianSource, pow_mul]

/--
Finite linear combinations of the even monomial-Gaussians are exactly all
real-coefficient even polynomial-Gaussian Schwartz tests.
-/
theorem span_guinandWeilPiEvenMonomialGaussianSchwartz_eq_range :
    Submodule.span Real
        (Set.range guinandWeilPiEvenMonomialGaussianSchwartz) =
      LinearMap.range guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap := by
  have h := congrArg
    (Submodule.map guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap)
    (Polynomial.basisMonomials Real).span_eq
  rw [Submodule.map_span, Submodule.map_top] at h
  have himage :
      guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap ''
          Set.range (Polynomial.basisMonomials Real) =
        Set.range guinandWeilPiEvenMonomialGaussianSchwartz := by
    ext f
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Polynomial.basisMonomials Real n, ⟨n, rfl⟩, rfl⟩
  rw [himage] at h
  exact h

end

end RiemannHypothesisProject
