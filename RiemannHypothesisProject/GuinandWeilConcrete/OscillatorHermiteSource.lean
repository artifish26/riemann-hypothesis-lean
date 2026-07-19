import RiemannHypothesisProject.GuinandWeilConcrete.EvenPolynomialGaussianSpan

/-!
# Harmonic-oscillator Hermite source for the `pi`-Gaussian

The Gaussian derivative polynomials give a convenient algebraic basis, but
the topological density theorem is naturally spectral.  This module defines
the correctly scaled creation-operator Hermite polynomials for
`exp (-pi x^2)` and proves their lowering and harmonic-oscillator eigenvalue
identities.
-/

namespace RiemannHypothesisProject

open Module Submodule

noncomputable section

/-- The harmonic-oscillator scale for `exp (-pi x^2)`. -/
noncomputable def guinandWeilPiOscillatorScale : Real :=
  2 * Real.pi

/--
The creation-operator Hermite polynomial for the `pi`-Gaussian.  If `Q_n`
denotes this polynomial, then
`Q_(n+1) = 4*pi*X*Q_n - Q_n'`.
-/
noncomputable def guinandWeilPiOscillatorHermiteRealPolynomial :
    Nat → Polynomial Real
  | 0 => 1
  | n + 1 =>
      Polynomial.C (2 * guinandWeilPiOscillatorScale) * Polynomial.X *
          guinandWeilPiOscillatorHermiteRealPolynomial n -
        (guinandWeilPiOscillatorHermiteRealPolynomial n).derivative

/-- The oscillator Hermite polynomial has exact degree `n`. -/
theorem degree_guinandWeilPiOscillatorHermiteRealPolynomial
    (n : Nat) :
    (guinandWeilPiOscillatorHermiteRealPolynomial n).degree = n := by
  induction n with
  | zero =>
      simp [guinandWeilPiOscillatorHermiteRealPolynomial]
  | succ n ih =>
      let p : Polynomial Real :=
        guinandWeilPiOscillatorHermiteRealPolynomial n
      let a : Real := 2 * guinandWeilPiOscillatorScale
      have hp0 : p ≠ 0 := by
        intro hp
        have hbot : p.degree = ⊥ := by rw [hp, Polynomial.degree_zero]
        rw [ih] at hbot
        exact WithBot.coe_ne_bot hbot
      have ha0 : a ≠ 0 := by
        dsimp [a, guinandWeilPiOscillatorScale]
        positivity
      have hleft :
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
          _ < ((n + 1 : Nat) : WithBot Nat) := by
            exact_mod_cast Nat.lt_succ_self n
      change
        (guinandWeilPiOscillatorHermiteRealPolynomial (Nat.succ n)).degree =
          ((Nat.succ n : Nat) : WithBot Nat)
      rw [guinandWeilPiOscillatorHermiteRealPolynomial.eq_def]
      change (Polynomial.C a * Polynomial.X * p - p.derivative).degree = _
      rw [Polynomial.degree_sub_eq_left_of_degree_lt]
      · exact hleft
      · simpa only [hleft] using hderiv_lt

/-- The oscillator Hermite polynomials form a polynomial sequence. -/
noncomputable def guinandWeilPiOscillatorHermiteRealPolynomialSequence :
    Polynomial.Sequence Real where
  elems' := guinandWeilPiOscillatorHermiteRealPolynomial
  degree_eq' := degree_guinandWeilPiOscillatorHermiteRealPolynomial

/-- Every oscillator Hermite leading coefficient is a unit. -/
theorem isUnit_leadingCoeff_guinandWeilPiOscillatorHermiteRealPolynomial
    (n : Nat) :
    IsUnit
      (guinandWeilPiOscillatorHermiteRealPolynomialSequence n).leadingCoeff := by
  change IsUnit
    (guinandWeilPiOscillatorHermiteRealPolynomial n).leadingCoeff
  apply isUnit_iff_ne_zero.mpr
  apply Polynomial.leadingCoeff_ne_zero.mpr
  intro hzero
  have hbot := degree_guinandWeilPiOscillatorHermiteRealPolynomial n
  rw [hzero, Polynomial.degree_zero] at hbot
  exact WithBot.coe_ne_bot hbot.symm

/-- The oscillator Hermite polynomials form a basis of `Real[X]`. -/
noncomputable def guinandWeilPiOscillatorHermiteRealPolynomialBasis :
    Basis Nat Real (Polynomial Real) :=
  guinandWeilPiOscillatorHermiteRealPolynomialSequence.basis
    isUnit_leadingCoeff_guinandWeilPiOscillatorHermiteRealPolynomial

@[simp]
theorem guinandWeilPiOscillatorHermiteRealPolynomialBasis_apply
    (n : Nat) :
    guinandWeilPiOscillatorHermiteRealPolynomialBasis n =
      guinandWeilPiOscillatorHermiteRealPolynomial n := by
  exact Polynomial.Sequence.basis_eq_self _ _ n

/-- Their finite real span is all of `Real[X]`. -/
theorem span_guinandWeilPiOscillatorHermiteRealPolynomial_eq_top :
    Submodule.span Real
        (Set.range guinandWeilPiOscillatorHermiteRealPolynomial) = ⊤ := by
  exact guinandWeilPiOscillatorHermiteRealPolynomialSequence.span
    isUnit_leadingCoeff_guinandWeilPiOscillatorHermiteRealPolynomial

/-- The creation polynomials satisfy the standard lowering identity. -/
theorem derivative_guinandWeilPiOscillatorHermiteRealPolynomial_succ
    (n : Nat) :
    (guinandWeilPiOscillatorHermiteRealPolynomial (n + 1)).derivative =
      Polynomial.C
          (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) *
        guinandWeilPiOscillatorHermiteRealPolynomial n := by
  induction n with
  | zero =>
      simp [guinandWeilPiOscillatorHermiteRealPolynomial,
        guinandWeilPiOscillatorScale]
  | succ n ih =>
      rw [guinandWeilPiOscillatorHermiteRealPolynomial.eq_def]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_C, zero_mul, Polynomial.derivative_X, zero_add]
      rw [ih]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
        zero_add]
      rw [guinandWeilPiOscillatorHermiteRealPolynomial.eq_def]
      apply Polynomial.funext
      intro x
      simp
      ring

/-- The polynomial part of `-d^2/dx^2 + (2*pi*x)^2` after the Gaussian factor. -/
noncomputable def guinandWeilPiHarmonicOscillatorPolynomial
    (p : Polynomial Real) : Polynomial Real :=
  -p.derivative.derivative +
      Polynomial.C (2 * guinandWeilPiOscillatorScale) * Polynomial.X *
        p.derivative +
    Polynomial.C guinandWeilPiOscillatorScale * p

/-- The real polynomial update induced by differentiating against the Gaussian. -/
noncomputable def guinandWeilPiRealPolynomialGaussianDerivativeStep
    (p : Polynomial Real) : Polynomial Real :=
  p.derivative -
    Polynomial.C guinandWeilPiOscillatorScale * Polynomial.X * p

/-- The real Gaussian derivative step commutes with extension to `Complex`. -/
theorem guinandWeilPiPolynomialGaussianDerivativeStep_map_real
    (p : Polynomial Real) :
    guinandWeilPiPolynomialGaussianDerivativeStep
        (p.map (algebraMap Real Complex)) =
      (guinandWeilPiRealPolynomialGaussianDerivativeStep p).map
        (algebraMap Real Complex) := by
  ext k
  simp [guinandWeilPiPolynomialGaussianDerivativeStep,
    guinandWeilPiRealPolynomialGaussianDerivativeStep,
    guinandWeilPiOscillatorScale]

/-- Two complex source derivatives are the scalar extension of two real steps. -/
theorem guinandWeilPiPolynomialGaussianDerivativePolynomial_two_map_real
    (p : Polynomial Real) :
    guinandWeilPiPolynomialGaussianDerivativePolynomial 2
        (p.map (algebraMap Real Complex)) =
      (guinandWeilPiRealPolynomialGaussianDerivativeStep
          (guinandWeilPiRealPolynomialGaussianDerivativeStep p)).map
        (algebraMap Real Complex) := by
  simp only [guinandWeilPiPolynomialGaussianDerivativePolynomial]
  rw [guinandWeilPiPolynomialGaussianDerivativeStep_map_real,
    guinandWeilPiPolynomialGaussianDerivativeStep_map_real]

/-- Conjugating the oscillator by the `pi`-Gaussian gives the polynomial operator above. -/
theorem guinandWeilPiHarmonicOscillatorPolynomial_eq_step_two
    (p : Polynomial Real) :
    -(guinandWeilPiRealPolynomialGaussianDerivativeStep
        (guinandWeilPiRealPolynomialGaussianDerivativeStep p)) +
        Polynomial.C (guinandWeilPiOscillatorScale ^ 2) *
          Polynomial.X ^ 2 * p =
      guinandWeilPiHarmonicOscillatorPolynomial p := by
  apply Polynomial.funext
  intro x
  simp [guinandWeilPiRealPolynomialGaussianDerivativeStep,
    guinandWeilPiHarmonicOscillatorPolynomial]
  ring

/--
The creation polynomials are eigenpolynomials for the conjugated harmonic
oscillator, with eigenvalue `2*pi*(2*n+1)`.
-/
theorem guinandWeilPiHarmonicOscillatorPolynomial_hermite
    (n : Nat) :
    guinandWeilPiHarmonicOscillatorPolynomial
        (guinandWeilPiOscillatorHermiteRealPolynomial n) =
      Polynomial.C
          (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) *
        guinandWeilPiOscillatorHermiteRealPolynomial n := by
  cases n with
  | zero =>
      simp [guinandWeilPiHarmonicOscillatorPolynomial,
        guinandWeilPiOscillatorHermiteRealPolynomial]
  | succ n =>
      have hrec :
          guinandWeilPiOscillatorHermiteRealPolynomial (n + 1) =
            Polynomial.C (2 * guinandWeilPiOscillatorScale) *
                Polynomial.X *
                guinandWeilPiOscillatorHermiteRealPolynomial n -
              (guinandWeilPiOscillatorHermiteRealPolynomial n).derivative :=
        rfl
      change
        -(guinandWeilPiOscillatorHermiteRealPolynomial (n + 1)).derivative.derivative +
              Polynomial.C (2 * guinandWeilPiOscillatorScale) *
                Polynomial.X *
                (guinandWeilPiOscillatorHermiteRealPolynomial (n + 1)).derivative +
            Polynomial.C guinandWeilPiOscillatorScale *
              guinandWeilPiOscillatorHermiteRealPolynomial (n + 1) =
          Polynomial.C
              (guinandWeilPiOscillatorScale *
                ((2 * (n + 1) + 1 : Nat) : Real)) *
            guinandWeilPiOscillatorHermiteRealPolynomial (n + 1)
      rw [derivative_guinandWeilPiOscillatorHermiteRealPolynomial_succ]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul,
        zero_add]
      rw [hrec]
      apply Polynomial.funext
      intro x
      simp
      ring

/-- The oscillator Hermite polynomials have the expected alternating parity. -/
theorem guinandWeilPiOscillatorHermiteRealPolynomial_eval_neg
    (n : Nat) (x : Real) :
    (guinandWeilPiOscillatorHermiteRealPolynomial n).eval (-x) =
      (-1 : Real) ^ n *
        (guinandWeilPiOscillatorHermiteRealPolynomial n).eval x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [guinandWeilPiOscillatorHermiteRealPolynomial]
      | succ n =>
          rw [guinandWeilPiOscillatorHermiteRealPolynomial.eq_def]
          simp only [Polynomial.eval_sub, Polynomial.eval_mul,
            Polynomial.eval_C, Polynomial.eval_X]
          rw [ih n (Nat.lt_succ_self n)]
          cases n with
          | zero =>
              simp [guinandWeilPiOscillatorHermiteRealPolynomial]
          | succ k =>
              rw [derivative_guinandWeilPiOscillatorHermiteRealPolynomial_succ]
              simp only [Polynomial.eval_mul, Polynomial.eval_C]
              rw [ih k (by omega)]
              push_cast
              ring

/-- The oscillator Hermite polynomial times the `pi`-Gaussian as a project test. -/
noncomputable def guinandWeilPiOscillatorHermiteSchwartz
    (n : Nat) : SchwartzLineTestFunction :=
  guinandWeilPiRealPolynomialGaussianSchwartzLinearMap
    (guinandWeilPiOscillatorHermiteRealPolynomial n)

/-- The finite oscillator-Hermite Schwartz span is the full real
polynomial-Gaussian source range. -/
theorem span_guinandWeilPiOscillatorHermiteSchwartz_eq_range :
    Submodule.span Real (Set.range guinandWeilPiOscillatorHermiteSchwartz) =
      LinearMap.range guinandWeilPiRealPolynomialGaussianSchwartzLinearMap := by
  have h := congrArg
    (Submodule.map guinandWeilPiRealPolynomialGaussianSchwartzLinearMap)
    span_guinandWeilPiOscillatorHermiteRealPolynomial_eq_top
  rw [Submodule.map_span, Submodule.map_top] at h
  have himage :
      guinandWeilPiRealPolynomialGaussianSchwartzLinearMap ''
          Set.range guinandWeilPiOscillatorHermiteRealPolynomial =
        Set.range guinandWeilPiOscillatorHermiteSchwartz := by
    ext g
    constructor
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨guinandWeilPiOscillatorHermiteRealPolynomial n, ⟨n, rfl⟩, rfl⟩
  rw [himage] at h
  exact h

@[simp]
theorem guinandWeilPiOscillatorHermiteSchwartz_apply
    (n : Nat) (x : Real) :
    guinandWeilPiOscillatorHermiteSchwartz n x =
      (guinandWeilPiOscillatorHermiteRealPolynomial n).aeval (x : Complex) *
        guinandWeilPiGaussianSource (x : Complex) := by
  change
    guinandWeilPiPolynomialGaussianSchwartz
        ((guinandWeilPiOscillatorHermiteRealPolynomial n).map
          (algebraMap Real Complex)) x = _
  rw [guinandWeilPiPolynomialGaussianSchwartz_apply,
    guinandWeilPiPolynomialGaussianSource]
  simp [Polynomial.aeval_def]

/-- The oscillator Hermite Schwartz tests have parity `(-1)^n`. -/
theorem guinandWeilPiOscillatorHermiteSchwartz_neg
    (n : Nat) (x : Real) :
    guinandWeilPiOscillatorHermiteSchwartz n (-x) =
      (-1 : Complex) ^ n *
        guinandWeilPiOscillatorHermiteSchwartz n x := by
  rw [guinandWeilPiOscillatorHermiteSchwartz_apply,
    guinandWeilPiOscillatorHermiteSchwartz_apply]
  have hparity :=
    guinandWeilPiOscillatorHermiteRealPolynomial_eval_neg n x
  have hparityC := congrArg (algebraMap Real Complex) hparity
  simp only [map_mul, map_pow, map_neg, map_one] at hparityC
  have hgaussian :
      guinandWeilPiGaussianSource (algebraMap Real Complex (-x)) =
        guinandWeilPiGaussianSource (algebraMap Real Complex x) := by
    simpa using guinandWeilPiGaussianSource_ofReal_neg x
  simp [Polynomial.aeval_def]
  rw [show -(x : Complex) =
      algebraMap Real Complex (-x) by simp,
    Polynomial.eval₂_at_apply]
  rw [show (x : Complex) = algebraMap Real Complex x by rfl,
    Polynomial.eval₂_at_apply,
    hparityC,
    hgaussian]
  ring

/-- The even-indexed oscillator Hermite tests lie in the even source sector. -/
theorem guinandWeilPiOscillatorHermiteSchwartz_even
    (n : Nat) (x : Real) :
    guinandWeilPiOscillatorHermiteSchwartz (2 * n) (-x) =
      guinandWeilPiOscillatorHermiteSchwartz (2 * n) x := by
  rw [guinandWeilPiOscillatorHermiteSchwartz_neg]
  simp [pow_mul]

/-- The real polynomial-Gaussian restriction intertwines the two oscillator operators. -/
theorem guinandWeilPiHarmonicOscillator_polynomialGaussianSource_real
    (p : Polynomial Real) (x : Real) :
    -iteratedDeriv 2
          (fun t : Real =>
            guinandWeilPiPolynomialGaussianSource
              (p.map (algebraMap Real Complex)) (t : Complex)) x +
        (((guinandWeilPiOscillatorScale * x) ^ 2 : Real) : Complex) *
          guinandWeilPiPolynomialGaussianSource
            (p.map (algebraMap Real Complex)) (x : Complex) =
      guinandWeilPiPolynomialGaussianSource
        ((guinandWeilPiHarmonicOscillatorPolynomial p).map
          (algebraMap Real Complex)) (x : Complex) := by
  rw [iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real,
    guinandWeilPiPolynomialGaussianDerivativePolynomial_two_map_real]
  have hpoly := congrArg
    (fun q : Polynomial Real => q.aeval (x : Complex))
    (guinandWeilPiHarmonicOscillatorPolynomial_eq_step_two p)
  simp at hpoly
  simp only [guinandWeilPiPolynomialGaussianSource]
  simp [Polynomial.aeval_def] at hpoly ⊢
  ring_nf at hpoly ⊢
  have hmul := congrArg
    (fun z : Complex => z * guinandWeilPiGaussianSource (x : Complex))
    hpoly
  ring_nf at hmul ⊢
  exact hmul

/--
The correctly scaled Hermite-Gaussian Schwartz tests are genuine eigenfunctions
of `-d^2/dx^2 + (2*pi*x)^2`.
-/
theorem guinandWeilPiOscillatorHermiteSchwartz_eigen
    (n : Nat) (x : Real) :
    -iteratedDeriv 2
          (fun t : Real => guinandWeilPiOscillatorHermiteSchwartz n t) x +
        (((guinandWeilPiOscillatorScale * x) ^ 2 : Real) : Complex) *
          guinandWeilPiOscillatorHermiteSchwartz n x =
      ((guinandWeilPiOscillatorScale *
          ((2 * n + 1 : Nat) : Real) : Real) : Complex) *
        guinandWeilPiOscillatorHermiteSchwartz n x := by
  have hsource (t : Real) :
      guinandWeilPiOscillatorHermiteSchwartz n t =
        guinandWeilPiPolynomialGaussianSource
          ((guinandWeilPiOscillatorHermiteRealPolynomial n).map
            (algebraMap Real Complex)) (t : Complex) := by
    rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
    simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]
  have hfun :
      (fun t : Real => guinandWeilPiOscillatorHermiteSchwartz n t) =
        fun t : Real =>
          guinandWeilPiPolynomialGaussianSource
            ((guinandWeilPiOscillatorHermiteRealPolynomial n).map
              (algebraMap Real Complex)) (t : Complex) := by
    funext t
    exact hsource t
  rw [hfun, hsource x,
    guinandWeilPiHarmonicOscillator_polynomialGaussianSource_real,
    guinandWeilPiHarmonicOscillatorPolynomial_hermite]
  simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]
  ring

end

end RiemannHypothesisProject
