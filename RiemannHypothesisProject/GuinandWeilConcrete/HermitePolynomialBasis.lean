import Mathlib.Algebra.Polynomial.Sequence
import RiemannHypothesisProject.GuinandWeilConcrete.EvenPolynomialGaussianSource

/-!
# Hermite basis for the `pi`-Gaussian derivative polynomials

The recursively defined real polynomial factors of the `pi`-Gaussian have
degree exactly `n` and leading coefficient `(-2*pi)^n`.  Consequently they are
a genuine polynomial sequence and form a basis of `Real[X]`.

This identifies the polynomial-Gaussian analytic source family with the
finite Hermite derivative span at the algebraic level.  Topological density in
Schwartz space remains a separate analytic theorem.
-/

namespace RiemannHypothesisProject

open Module Submodule

noncomputable section

/-- Exact degree of the real `pi`-Gaussian derivative polynomial. -/
theorem degree_guinandWeilPiGaussianDerivativeRealPolynomial
    (n : Nat) :
    (guinandWeilPiGaussianDerivativeRealPolynomial n).degree = n := by
  induction n with
  | zero =>
      simp [guinandWeilPiGaussianDerivativeRealPolynomial]
  | succ n ih =>
      let p : Polynomial Real :=
        guinandWeilPiGaussianDerivativeRealPolynomial n
      let a : Real := 2 * Real.pi
      have hp0 : p ≠ 0 := by
        intro hp
        have hbot : p.degree = ⊥ := by rw [hp, Polynomial.degree_zero]
        rw [ih] at hbot
        exact WithBot.coe_ne_bot hbot
      have ha0 : a ≠ 0 := by
        dsimp [a]
        positivity
      have hright :
          (Polynomial.C a * Polynomial.X * p).degree =
            ((n + 1 : Nat) : WithBot Nat) := by
        rw [Polynomial.degree_mul, Polynomial.degree_mul,
          Polynomial.degree_C ha0, Polynomial.degree_X]
        simp [p, ih, add_comm]
      have hderiv_lt :
          p.derivative.degree < ((n + 1 : Nat) : WithBot Nat) := by
        calc
          p.derivative.degree < p.degree :=
            Polynomial.degree_derivative_lt hp0
          _ = (n : Nat) := by simpa [p] using ih
          _ < ((n + 1 : Nat) : WithBot Nat) := by exact_mod_cast Nat.lt_succ_self n
      change
        (guinandWeilPiGaussianDerivativeRealPolynomial (Nat.succ n)).degree =
          ((Nat.succ n : Nat) : WithBot Nat)
      rw [guinandWeilPiGaussianDerivativeRealPolynomial.eq_def]
      change
        (p.derivative - Polynomial.C a * Polynomial.X * p).degree =
          ((n + 1 : Nat) : WithBot Nat)
      rw [Polynomial.degree_sub_eq_right_of_degree_lt
        (by simpa [hright] using hderiv_lt)]
      exact hright

/-- Exact leading coefficient of the real derivative polynomial. -/
theorem leadingCoeff_guinandWeilPiGaussianDerivativeRealPolynomial
    (n : Nat) :
    (guinandWeilPiGaussianDerivativeRealPolynomial n).leadingCoeff =
      (-2 * Real.pi) ^ n := by
  induction n with
  | zero =>
      simp [guinandWeilPiGaussianDerivativeRealPolynomial]
  | succ n ih =>
      let p : Polynomial Real :=
        guinandWeilPiGaussianDerivativeRealPolynomial n
      let a : Real := 2 * Real.pi
      have hp0 : p ≠ 0 := by
        intro hp
        have hbot : p.degree = ⊥ := by rw [hp, Polynomial.degree_zero]
        rw [degree_guinandWeilPiGaussianDerivativeRealPolynomial n] at hbot
        exact WithBot.coe_ne_bot hbot
      have ha0 : a ≠ 0 := by
        dsimp [a]
        positivity
      have hright :
          (Polynomial.C a * Polynomial.X * p).degree =
            ((n + 1 : Nat) : WithBot Nat) := by
        rw [Polynomial.degree_mul, Polynomial.degree_mul,
          Polynomial.degree_C ha0, Polynomial.degree_X]
        simp [p, degree_guinandWeilPiGaussianDerivativeRealPolynomial, add_comm]
      have hderiv_lt :
          p.derivative.degree <
            (Polynomial.C a * Polynomial.X * p).degree := by
        rw [hright]
        calc
          p.derivative.degree < p.degree :=
            Polynomial.degree_derivative_lt hp0
          _ = (n : Nat) := by
            simpa [p] using
              degree_guinandWeilPiGaussianDerivativeRealPolynomial n
          _ < ((n + 1 : Nat) : WithBot Nat) := by exact_mod_cast Nat.lt_succ_self n
      change
        (guinandWeilPiGaussianDerivativeRealPolynomial
          (Nat.succ n)).leadingCoeff =
            (-2 * Real.pi) ^ Nat.succ n
      rw [guinandWeilPiGaussianDerivativeRealPolynomial.eq_def]
      change
        (p.derivative - Polynomial.C a * Polynomial.X * p).leadingCoeff =
          (-2 * Real.pi) ^ (n + 1)
      rw [Polynomial.leadingCoeff_sub_of_degree_lt' hderiv_lt]
      simp [p, a, ih, Polynomial.leadingCoeff_mul]
      rw [pow_succ]
      ring

/-- The real Gaussian derivative factors as a polynomial sequence. -/
noncomputable def guinandWeilPiGaussianDerivativeRealPolynomialSequence :
    Polynomial.Sequence Real where
  elems' := guinandWeilPiGaussianDerivativeRealPolynomial
  degree_eq' := degree_guinandWeilPiGaussianDerivativeRealPolynomial

/-- Every leading coefficient in the Gaussian derivative sequence is a unit. -/
theorem isUnit_leadingCoeff_guinandWeilPiGaussianDerivativeRealPolynomial
    (n : Nat) :
    IsUnit
      (guinandWeilPiGaussianDerivativeRealPolynomialSequence n).leadingCoeff := by
  rw [show
    (guinandWeilPiGaussianDerivativeRealPolynomialSequence n).leadingCoeff =
      (-2 * Real.pi) ^ n by
        exact leadingCoeff_guinandWeilPiGaussianDerivativeRealPolynomial n]
  exact isUnit_iff_ne_zero.mpr
    (pow_ne_zero n (mul_ne_zero (by norm_num) Real.pi_ne_zero))

/-- The Gaussian derivative polynomials form a basis of `Real[X]`. -/
noncomputable def guinandWeilPiGaussianDerivativeRealPolynomialBasis :
    Basis Nat Real (Polynomial Real) :=
  guinandWeilPiGaussianDerivativeRealPolynomialSequence.basis
    isUnit_leadingCoeff_guinandWeilPiGaussianDerivativeRealPolynomial

@[simp]
theorem guinandWeilPiGaussianDerivativeRealPolynomialBasis_apply
    (n : Nat) :
    guinandWeilPiGaussianDerivativeRealPolynomialBasis n =
      guinandWeilPiGaussianDerivativeRealPolynomial n := by
  exact Polynomial.Sequence.basis_eq_self _ _ n

/-- The finite Hermite derivative span is all of `Real[X]`. -/
theorem span_guinandWeilPiGaussianDerivativeRealPolynomial_eq_top :
    Submodule.span Real
        (Set.range guinandWeilPiGaussianDerivativeRealPolynomial) = ⊤ := by
  exact
    guinandWeilPiGaussianDerivativeRealPolynomialSequence.span
      isUnit_leadingCoeff_guinandWeilPiGaussianDerivativeRealPolynomial

/-- Real polynomials mapped to their polynomial-Gaussian Schwartz tests. -/
noncomputable def guinandWeilPiRealPolynomialGaussianSchwartzLinearMap :
    Polynomial Real →ₗ[Real] SchwartzLineTestFunction where
  toFun p :=
    guinandWeilPiPolynomialGaussianSchwartz
      (p.map (algebraMap Real Complex))
  map_add' p q := by
    ext x
    simp [guinandWeilPiPolynomialGaussianSource]
    ring
  map_smul' c p := by
    ext x
    simp [guinandWeilPiPolynomialGaussianSource]
    ring

/-- The `n`th Hermite-Gaussian project Schwartz test. -/
noncomputable def guinandWeilPiGaussianHermiteSchwartz
    (n : Nat) : SchwartzLineTestFunction :=
  guinandWeilPiRealPolynomialGaussianSchwartzLinearMap
    (guinandWeilPiGaussianDerivativeRealPolynomial n)

/-- The general polynomial-Gaussian recurrence agrees with the Gaussian one at `1`. -/
theorem guinandWeilPiPolynomialGaussianDerivativePolynomial_one
    (n : Nat) :
    guinandWeilPiPolynomialGaussianDerivativePolynomial n 1 =
      guinandWeilPiGaussianDerivativePolynomial n := by
  induction n with
  | zero =>
      simp [guinandWeilPiPolynomialGaussianDerivativePolynomial,
        guinandWeilPiGaussianDerivativePolynomial]
  | succ n ih =>
      simp [guinandWeilPiPolynomialGaussianDerivativePolynomial,
        guinandWeilPiPolynomialGaussianDerivativeStep,
        guinandWeilPiGaussianDerivativePolynomial, ih]

@[simp]
theorem guinandWeilPiGaussianHermiteSchwartz_apply
    (n : Nat) (x : Real) :
    guinandWeilPiGaussianHermiteSchwartz n x =
      iteratedDeriv n
        (fun t : Real => guinandWeilPiGaussianSource (t : Complex)) x := by
  change
    guinandWeilPiPolynomialGaussianSchwartz
        ((guinandWeilPiGaussianDerivativeRealPolynomial n).map
          (algebraMap Real Complex)) x = _
  have hfun :
      (fun t : Real => guinandWeilPiGaussianSource (t : Complex)) =
        fun t : Real =>
          guinandWeilPiPolynomialGaussianSource 1 (t : Complex) := by
    funext t
    simp [guinandWeilPiPolynomialGaussianSource]
  rw [hfun,
    iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real,
    guinandWeilPiPolynomialGaussianDerivativePolynomial_one]
  simp [guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiGaussianDerivativePolynomial_eq_map_real]

/--
The finite real Hermite-Gaussian span is exactly the range of all
real-coefficient polynomial-Gaussian Schwartz tests.
-/
theorem span_guinandWeilPiGaussianHermiteSchwartz_eq_range :
    Submodule.span Real (Set.range guinandWeilPiGaussianHermiteSchwartz) =
      LinearMap.range guinandWeilPiRealPolynomialGaussianSchwartzLinearMap := by
  have h := congrArg
    (Submodule.map guinandWeilPiRealPolynomialGaussianSchwartzLinearMap)
    span_guinandWeilPiGaussianDerivativeRealPolynomial_eq_top
  rw [Submodule.map_span, Submodule.map_top] at h
  have himage :
      guinandWeilPiRealPolynomialGaussianSchwartzLinearMap ''
          Set.range guinandWeilPiGaussianDerivativeRealPolynomial =
        Set.range guinandWeilPiGaussianHermiteSchwartz := by
    ext f
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact
        ⟨guinandWeilPiGaussianDerivativeRealPolynomial n, ⟨n, rfl⟩, rfl⟩
  rw [himage] at h
  exact h

end

end RiemannHypothesisProject
