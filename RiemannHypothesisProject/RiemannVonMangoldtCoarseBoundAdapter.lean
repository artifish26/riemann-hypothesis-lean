import RiemannHypothesisProject.RiemannVonMangoldtClassicalCounting

/-!
# Coarse `N(T)` upper-bound adapter

The sharp explicit-bound adapter consumes a theorem of the form
`|N(T) - main(T)| <= error(T)`.  For the project's zero-counting pipeline, a
much weaker theorem is enough: a coarse published upper bound `N(T) <= B(T)`
with a polynomial tail after converting height windows to closed balls.

This file packages that middle route.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/--
A source-shaped coarse `N(T)` upper-bound theorem for the classical
zero-counting route.

`heightCount` should be read as the positive-ordinate zero-counting function
`N(T)`.  The field `heightCount_le_countBound` is the published or derived
coarse theorem `N(T) <= countBound(T)`.  The finite-window fields say that
`heightCount` controls positive and negative ordinate finite windows; the
negative field is where conjugation symmetry or a lower-half-plane count should
be supplied.
-/
structure ClassicalCoarseRiemannVonMangoldtBound where
  cutoff : Nat
  heightCount : Real -> Real
  countBound : Real -> Real
  axisOrTrivialBound : Nat -> Real
  heightEnvelopeConstant : Real
  growth : Real
  heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant
  heightCount_le_countBound :
    forall T : Real, heightCount T <= countBound T
  positiveFiniteWindowCard_le_heightCount :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= heightCount T
  negativeFiniteWindowCard_le_heightCount :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            Complex.im (rho : Complex) < 0 ∧
              -Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= heightCount T
  axisWindowCard_le :
    forall n : Nat,
      ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
        axisOrTrivialBound n
  tail_coarseHeightEnvelope_le :
    forall n : Nat,
      countBound ((n + cutoff : Nat) : Real) +
          countBound ((n + cutoff : Nat) : Real) +
          axisOrTrivialBound (n + cutoff) <=
        heightEnvelopeConstant * |(n : Real) + 1| ^ growth

namespace ClassicalCoarseRiemannVonMangoldtBound

/-- Positive finite windows are bounded by the coarse `N(T)` upper bound. -/
theorem positiveFiniteWindowCard_le_countBound
    (target : ClassicalCoarseRiemannVonMangoldtBound)
    (s : Finset ZetaZeroSubtype)
    (T : Real)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    ((s.card : Nat) : Real) <= target.countBound T :=
  (target.positiveFiniteWindowCard_le_heightCount s T hs).trans
    (target.heightCount_le_countBound T)

/-- Negative finite windows are bounded by the same coarse `N(T)` upper bound. -/
theorem negativeFiniteWindowCard_le_countBound
    (target : ClassicalCoarseRiemannVonMangoldtBound)
    (s : Finset ZetaZeroSubtype)
    (T : Real)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          Complex.im (rho : Complex) < 0 ∧
            -Complex.im (rho : Complex) <= T) :
    ((s.card : Nat) : Real) <= target.countBound T :=
  (target.negativeFiniteWindowCard_le_heightCount s T hs).trans
    (target.heightCount_le_countBound T)

/--
Convert a coarse `N(T) <= B(T)` theorem into the existing symmetric classical
height-counting target.
-/
noncomputable def toClassicalSymmetricHeightCountingTarget
    (target : ClassicalCoarseRiemannVonMangoldtBound) :
    ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget where
  cutoff := target.cutoff
  positiveCountBound := target.countBound
  axisOrTrivialBound := target.axisOrTrivialBound
  heightEnvelopeConstant := target.heightEnvelopeConstant
  growth := target.growth
  heightEnvelopeConstant_nonneg := target.heightEnvelopeConstant_nonneg
  positiveFiniteWindowCard_le :=
    target.positiveFiniteWindowCard_le_countBound
  negativeFiniteWindowCard_le_positiveBound :=
    target.negativeFiniteWindowCard_le_countBound
  axisWindowCard_le := target.axisWindowCard_le
  tail_symmetricClassicalHeightEnvelope_le :=
    target.tail_coarseHeightEnvelope_le

/-- The coarse bound adapter gives the general height-counting target. -/
noncomputable def toHeightCountingTarget
    (target : ClassicalCoarseRiemannVonMangoldtBound) :
    ClosedBallZeroHeightCountingTarget :=
  target.toClassicalSymmetricHeightCountingTarget.toHeightCountingTarget

/-- The coarse bound adapter gives the preferred cumulative closed-ball count. -/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClassicalCoarseRiemannVonMangoldtBound) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  target.toClassicalSymmetricHeightCountingTarget
    |>.toCumulativeWindowCountingEstimate

/-- The coarse bound adapter gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClassicalCoarseRiemannVonMangoldtBound) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toClassicalSymmetricHeightCountingTarget
    |>.toPolynomialZeroCountingEstimate

/-- The converted cumulative estimate keeps the coarse-bound cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    (target : ClassicalCoarseRiemannVonMangoldtBound) :
    target.toCumulativeWindowCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the coarse-bound growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    (target : ClassicalCoarseRiemannVonMangoldtBound) :
    target.toPolynomialZeroCountingEstimate.growth = target.growth :=
  rfl

end ClassicalCoarseRiemannVonMangoldtBound

end ComplexCompactExhaustion

end RiemannHypothesisProject
