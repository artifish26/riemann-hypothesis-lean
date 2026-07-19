import RiemannHypothesisProject.RiemannVonMangoldtClassicalCounting

/-!
# Explicit `N(T)` bound adapter

Modern explicit Riemann-von Mangoldt estimates are often stated as

`|N(T) - main(T)| <= error(T)`.

The project's zero-counting route needs a coarser object: a positive-ordinate
height-count bound that eventually satisfies a polynomial envelope, plus the
matching negative-ordinate and axis/trivial-zero contributions.  This file
checks the adapter between those shapes.

No explicit estimate for zeta zeroes is proved here.  The record below is a
target for future formalization of Trudgian/Hasanalizade-Shen-Wong/Bellotti-
Wong style theorems, and the checked definitions show exactly how such a
theorem would feed the existing closed-ball counting pipeline.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/--
A source-shaped explicit `N(T)` estimate for the classical zero-counting route.

`heightCount` should be read as the positive-ordinate zero-counting function
`N(T)`.  The field `explicit_abs_error_le` is the published-style theorem
`|N(T) - main(T)| <= error(T)`.  The finite-window fields say that the same
height count controls any finite positive- or negative-ordinate window in the
project's zeta-zero subtype; the negative field is where conjugation symmetry
or an independently stated lower-half-plane count should be supplied.
-/
structure ClassicalExplicitRiemannVonMangoldtBound where
  cutoff : Nat
  heightCount : Real -> Real
  mainTerm : Real -> Real
  errorTerm : Real -> Real
  axisOrTrivialBound : Nat -> Real
  heightEnvelopeConstant : Real
  growth : Real
  heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant
  explicit_abs_error_le :
    forall T : Real,
      |heightCount T - mainTerm T| <= errorTerm T
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
  tail_mainErrorEnvelope_le :
    forall n : Nat,
      (mainTerm ((n + cutoff : Nat) : Real) +
          errorTerm ((n + cutoff : Nat) : Real)) +
          (mainTerm ((n + cutoff : Nat) : Real) +
            errorTerm ((n + cutoff : Nat) : Real)) +
          axisOrTrivialBound (n + cutoff) <=
        heightEnvelopeConstant * |(n : Real) + 1| ^ growth

namespace ClassicalExplicitRiemannVonMangoldtBound

/-- The explicit upper bound extracted from `|N(T) - main(T)| <= error(T)`. -/
noncomputable def countBound
    (target : ClassicalExplicitRiemannVonMangoldtBound) (T : Real) : Real :=
  target.mainTerm T + target.errorTerm T

/-- The absolute-error estimate implies `N(T) <= main(T) + error(T)`. -/
theorem heightCount_le_countBound
    (target : ClassicalExplicitRiemannVonMangoldtBound)
    (T : Real) :
    target.heightCount T <= target.countBound T := by
  have hsub :
      target.heightCount T - target.mainTerm T <= target.errorTerm T :=
    (abs_le.mp (target.explicit_abs_error_le T)).2
  have hle :
      target.heightCount T <= target.errorTerm T + target.mainTerm T :=
    sub_le_iff_le_add.mp hsub
  simpa [countBound, add_comm, add_left_comm, add_assoc] using hle

/-- Positive finite windows are bounded by the explicit `main + error` bound. -/
theorem positiveFiniteWindowCard_le_countBound
    (target : ClassicalExplicitRiemannVonMangoldtBound)
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

/-- Negative finite windows are bounded by the same explicit `main + error` bound. -/
theorem negativeFiniteWindowCard_le_countBound
    (target : ClassicalExplicitRiemannVonMangoldtBound)
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
Convert a published-style explicit `N(T)` estimate into the existing symmetric
classical Riemann-von Mangoldt height-counting target.
-/
noncomputable def toClassicalSymmetricHeightCountingTarget
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
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
  tail_symmetricClassicalHeightEnvelope_le := by
    intro n
    simpa [countBound] using target.tail_mainErrorEnvelope_le n

/-- The explicit bound adapter gives the general height-counting target. -/
noncomputable def toHeightCountingTarget
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
    ClosedBallZeroHeightCountingTarget :=
  target.toClassicalSymmetricHeightCountingTarget.toHeightCountingTarget

/-- The explicit bound adapter gives the preferred cumulative closed-ball count. -/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  target.toClassicalSymmetricHeightCountingTarget
    |>.toCumulativeWindowCountingEstimate

/-- The explicit bound adapter gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toClassicalSymmetricHeightCountingTarget
    |>.toPolynomialZeroCountingEstimate

/-- The converted cumulative estimate keeps the explicit-bound cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
    target.toCumulativeWindowCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the explicit-bound cutoff. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
    target.toPolynomialZeroCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the explicit-bound growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    (target : ClassicalExplicitRiemannVonMangoldtBound) :
    target.toPolynomialZeroCountingEstimate.growth = target.growth :=
  rfl

end ClassicalExplicitRiemannVonMangoldtBound

end ComplexCompactExhaustion

end RiemannHypothesisProject
