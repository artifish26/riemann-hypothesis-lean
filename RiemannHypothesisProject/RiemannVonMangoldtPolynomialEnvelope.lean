import RiemannHypothesisProject.RiemannVonMangoldtExplicitBoundAdapter

/-!
# Polynomial envelopes for explicit `N(T)` estimates

The explicit `N(T)` adapter expects a coarse polynomial envelope for

`2 * (main(T) + error(T)) + axis(T)`.

In practice, future analytic work is likely to prove this by bounding the main
term, the explicit error term, and the axis/trivial-zero contribution
separately.  This file supplies that elementary arithmetic layer.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

namespace ClassicalExplicitRiemannVonMangoldtBound

/-- The combined constant for two half-plane counts plus the axis contribution. -/
def polynomialEnvelopeConstant
    (mainConstant errorConstant axisConstant : Real) : Real :=
  (mainConstant + errorConstant) +
    (mainConstant + errorConstant) +
    axisConstant

/-- Nonnegative component constants give a nonnegative combined envelope constant. -/
theorem polynomialEnvelopeConstant_nonneg
    {mainConstant errorConstant axisConstant : Real}
    (mainConstant_nonneg : 0 <= mainConstant)
    (errorConstant_nonneg : 0 <= errorConstant)
    (axisConstant_nonneg : 0 <= axisConstant) :
    0 <= polynomialEnvelopeConstant
      mainConstant errorConstant axisConstant :=
  add_nonneg
    (add_nonneg
      (add_nonneg mainConstant_nonneg errorConstant_nonneg)
      (add_nonneg mainConstant_nonneg errorConstant_nonneg))
    axisConstant_nonneg

/--
Separate polynomial bounds for the main, error, and axis terms imply the
combined symmetric closed-ball height envelope needed by the explicit
Riemann-von Mangoldt adapter.
-/
theorem tail_mainErrorEnvelope_le_of_polynomial_bounds
    (cutoff : Nat)
    (mainTerm errorTerm : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (mainConstant errorConstant axisConstant growth : Real)
    (tail_mainTerm_le :
      forall n : Nat,
        mainTerm ((n + cutoff : Nat) : Real) <=
          mainConstant * |(n : Real) + 1| ^ growth)
    (tail_errorTerm_le :
      forall n : Nat,
        errorTerm ((n + cutoff : Nat) : Real) <=
          errorConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth)
    (n : Nat) :
    (mainTerm ((n + cutoff : Nat) : Real) +
        errorTerm ((n + cutoff : Nat) : Real)) +
        (mainTerm ((n + cutoff : Nat) : Real) +
          errorTerm ((n + cutoff : Nat) : Real)) +
        axisOrTrivialBound (n + cutoff) <=
      polynomialEnvelopeConstant mainConstant errorConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
  have hmain := tail_mainTerm_le n
  have herr := tail_errorTerm_le n
  have haxis := tail_axisOrTrivialBound_le n
  calc
    (mainTerm ((n + cutoff : Nat) : Real) +
        errorTerm ((n + cutoff : Nat) : Real)) +
        (mainTerm ((n + cutoff : Nat) : Real) +
          errorTerm ((n + cutoff : Nat) : Real)) +
        axisOrTrivialBound (n + cutoff)
        <=
      (mainConstant * |(n : Real) + 1| ^ growth +
        errorConstant * |(n : Real) + 1| ^ growth) +
        (mainConstant * |(n : Real) + 1| ^ growth +
          errorConstant * |(n : Real) + 1| ^ growth) +
        axisConstant * |(n : Real) + 1| ^ growth := by
        exact add_le_add
          (add_le_add
            (add_le_add hmain herr)
            (add_le_add hmain herr))
          haxis
    _ =
      polynomialEnvelopeConstant mainConstant errorConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
        rw [polynomialEnvelopeConstant]
        ring

/--
Build an explicit `N(T)` target from a published-style absolute-error theorem
and separate polynomial envelopes for the main, error, and axis terms.
-/
noncomputable def ofPolynomialMainErrorAxis
    (cutoff : Nat)
    (heightCount mainTerm errorTerm : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (mainConstant errorConstant axisConstant growth : Real)
    (mainConstant_nonneg : 0 <= mainConstant)
    (errorConstant_nonneg : 0 <= errorConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (explicit_abs_error_le :
      forall T : Real,
        |heightCount T - mainTerm T| <= errorTerm T)
    (positiveFiniteWindowCard_le_heightCount :
      forall s : Finset ZetaZeroSubtype,
        forall T : Real,
          (forall rho : ZetaZeroSubtype,
            rho ∈ s ->
              0 < Complex.im (rho : Complex) ∧
                Complex.im (rho : Complex) <= T) ->
            ((s.card : Nat) : Real) <= heightCount T)
    (negativeFiniteWindowCard_le_heightCount :
      forall s : Finset ZetaZeroSubtype,
        forall T : Real,
          (forall rho : ZetaZeroSubtype,
            rho ∈ s ->
              Complex.im (rho : Complex) < 0 ∧
                -Complex.im (rho : Complex) <= T) ->
            ((s.card : Nat) : Real) <= heightCount T)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_mainTerm_le :
      forall n : Nat,
        mainTerm ((n + cutoff : Nat) : Real) <=
          mainConstant * |(n : Real) + 1| ^ growth)
    (tail_errorTerm_le :
      forall n : Nat,
        errorTerm ((n + cutoff : Nat) : Real) <=
          errorConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    ClassicalExplicitRiemannVonMangoldtBound where
  cutoff := cutoff
  heightCount := heightCount
  mainTerm := mainTerm
  errorTerm := errorTerm
  axisOrTrivialBound := axisOrTrivialBound
  heightEnvelopeConstant :=
    polynomialEnvelopeConstant mainConstant errorConstant axisConstant
  growth := growth
  heightEnvelopeConstant_nonneg :=
    polynomialEnvelopeConstant_nonneg
      mainConstant_nonneg errorConstant_nonneg axisConstant_nonneg
  explicit_abs_error_le := explicit_abs_error_le
  positiveFiniteWindowCard_le_heightCount :=
    positiveFiniteWindowCard_le_heightCount
  negativeFiniteWindowCard_le_heightCount :=
    negativeFiniteWindowCard_le_heightCount
  axisWindowCard_le := axisWindowCard_le
  tail_mainErrorEnvelope_le :=
    tail_mainErrorEnvelope_le_of_polynomial_bounds
      cutoff mainTerm errorTerm axisOrTrivialBound
      mainConstant errorConstant axisConstant growth
      tail_mainTerm_le tail_errorTerm_le tail_axisOrTrivialBound_le

end ClassicalExplicitRiemannVonMangoldtBound

end ComplexCompactExhaustion

end RiemannHypothesisProject
