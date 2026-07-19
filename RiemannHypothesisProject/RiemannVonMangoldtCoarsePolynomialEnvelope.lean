import RiemannHypothesisProject.RiemannVonMangoldtCoarseBoundAdapter

/-!
# Polynomial envelopes for coarse `N(T)` upper bounds

The coarse `N(T)` adapter expects a polynomial envelope for

`B(T) + B(T) + axis(T)`.

This file reduces that combined envelope to two natural estimates: a polynomial
tail bound for the coarse height-count upper bound `B(T)`, and a polynomial
tail bound for the axis/trivial-zero contribution.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

namespace ClassicalCoarseRiemannVonMangoldtBound

/-- The combined constant for two coarse half-plane counts plus the axis contribution. -/
def polynomialEnvelopeConstant
    (countConstant axisConstant : Real) : Real :=
  countConstant + countConstant + axisConstant

/-- Nonnegative component constants give a nonnegative combined envelope constant. -/
theorem polynomialEnvelopeConstant_nonneg
    {countConstant axisConstant : Real}
    (countConstant_nonneg : 0 <= countConstant)
    (axisConstant_nonneg : 0 <= axisConstant) :
    0 <= polynomialEnvelopeConstant countConstant axisConstant :=
  add_nonneg
    (add_nonneg countConstant_nonneg countConstant_nonneg)
    axisConstant_nonneg

/--
Separate polynomial bounds for the coarse `N(T)` upper bound and the axis term
imply the combined symmetric closed-ball height envelope needed by the coarse
Riemann-von Mangoldt adapter.
-/
theorem tail_coarseHeightEnvelope_le_of_polynomial_bounds
    (cutoff : Nat)
    (countBound : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (countConstant axisConstant growth : Real)
    (tail_countBound_le :
      forall n : Nat,
        countBound ((n + cutoff : Nat) : Real) <=
          countConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth)
    (n : Nat) :
    countBound ((n + cutoff : Nat) : Real) +
        countBound ((n + cutoff : Nat) : Real) +
        axisOrTrivialBound (n + cutoff) <=
      polynomialEnvelopeConstant countConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
  have hcount := tail_countBound_le n
  have haxis := tail_axisOrTrivialBound_le n
  calc
    countBound ((n + cutoff : Nat) : Real) +
        countBound ((n + cutoff : Nat) : Real) +
        axisOrTrivialBound (n + cutoff)
        <=
      countConstant * |(n : Real) + 1| ^ growth +
        countConstant * |(n : Real) + 1| ^ growth +
        axisConstant * |(n : Real) + 1| ^ growth := by
        exact add_le_add (add_le_add hcount hcount) haxis
    _ =
      polynomialEnvelopeConstant countConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
        rw [polynomialEnvelopeConstant]
        ring

/--
Build a coarse `N(T)` target from a source upper bound `N(T) <= B(T)` and
separate polynomial envelopes for `B(T)` and the axis contribution.
-/
noncomputable def ofPolynomialCountAxis
    (cutoff : Nat)
    (heightCount countBound : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (countConstant axisConstant growth : Real)
    (countConstant_nonneg : 0 <= countConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (heightCount_le_countBound :
      forall T : Real, heightCount T <= countBound T)
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
    (tail_countBound_le :
      forall n : Nat,
        countBound ((n + cutoff : Nat) : Real) <=
          countConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    ClassicalCoarseRiemannVonMangoldtBound where
  cutoff := cutoff
  heightCount := heightCount
  countBound := countBound
  axisOrTrivialBound := axisOrTrivialBound
  heightEnvelopeConstant :=
    polynomialEnvelopeConstant countConstant axisConstant
  growth := growth
  heightEnvelopeConstant_nonneg :=
    polynomialEnvelopeConstant_nonneg countConstant_nonneg axisConstant_nonneg
  heightCount_le_countBound := heightCount_le_countBound
  positiveFiniteWindowCard_le_heightCount :=
    positiveFiniteWindowCard_le_heightCount
  negativeFiniteWindowCard_le_heightCount :=
    negativeFiniteWindowCard_le_heightCount
  axisWindowCard_le := axisWindowCard_le
  tail_coarseHeightEnvelope_le :=
    tail_coarseHeightEnvelope_le_of_polynomial_bounds
      cutoff countBound axisOrTrivialBound
      countConstant axisConstant growth
      tail_countBound_le tail_axisOrTrivialBound_le

end ClassicalCoarseRiemannVonMangoldtBound

end ComplexCompactExhaustion

end RiemannHypothesisProject
