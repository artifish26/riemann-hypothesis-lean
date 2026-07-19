import RiemannHypothesisProject.StandardExhaustions

/-!
# Riemann-von Mangoldt zero-counting target

The existing tail pipeline needs a polynomial cumulative count for the standard
closed-ball exhaustion of the zeta-zero subtype.  Classical
Riemann-von Mangoldt estimates give much more precise information than this.

This module records the coarse formal target and checks the connector into the
existing cumulative-window counting package.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/--
A coarse Riemann-von Mangoldt-style bound for the standard closed-ball
exhaustion.

`windowCardBound` is intentionally abstract: a future formalization can fill it
from an explicit `N(T)` theorem, a weaker asymptotic consequence, or a verified
height-counting estimate.  Once it has a polynomial tail, Lean turns it into
the existing cumulative-window counting estimate.
-/
structure ClosedBallZeroRiemannVonMangoldtCountingTarget where
  cutoff : Nat
  windowCardBound : Nat -> Real
  windowCardConstant : Real
  growth : Real
  windowCardConstant_nonneg : 0 <= windowCardConstant
  windowCard_le :
    forall n : Nat,
      ((closedBallZero.zetaZeroSubtypeFinset n).card : Real) <=
        windowCardBound n
  tail_windowCardBound_le :
    forall n : Nat,
      windowCardBound (n + cutoff) <=
        windowCardConstant * |(n : Real) + 1| ^ growth

namespace ClosedBallZeroRiemannVonMangoldtCountingTarget

/--
Convert a coarse Riemann-von Mangoldt target into the project's standard
closed-ball cumulative-window estimate.
-/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClosedBallZeroRiemannVonMangoldtCountingTarget) :
    ClosedBallZeroCumulativeWindowCountingEstimate where
  cutoff := target.cutoff
  windowCardBound := target.windowCardBound
  windowCardConstant := target.windowCardConstant
  growth := target.growth
  windowCardConstant_nonneg := target.windowCardConstant_nonneg
  windowCard_le := target.windowCard_le
  tail_windowCardBound_le := target.tail_windowCardBound_le

/--
Convert a coarse Riemann-von Mangoldt target directly to first-entry shell
counting.
-/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClosedBallZeroRiemannVonMangoldtCountingTarget) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toCumulativeWindowCountingEstimate.toPolynomialZeroCountingEstimate

/-- The converted cumulative estimate keeps the target cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    (target : ClosedBallZeroRiemannVonMangoldtCountingTarget) :
    target.toCumulativeWindowCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the target cutoff. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    (target : ClosedBallZeroRiemannVonMangoldtCountingTarget) :
    target.toPolynomialZeroCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the target growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    (target : ClosedBallZeroRiemannVonMangoldtCountingTarget) :
    target.toPolynomialZeroCountingEstimate.growth = target.growth :=
  rfl

end ClosedBallZeroRiemannVonMangoldtCountingTarget

/--
View any closed-ball cumulative-window counting estimate as the named
Riemann-von-Mangoldt counting target used by the reduced theorem wrappers.
-/
noncomputable def ClosedBallZeroCumulativeWindowCountingEstimate.toRiemannVonMangoldtCountingTarget
    (estimate : ClosedBallZeroCumulativeWindowCountingEstimate) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget where
  cutoff := estimate.cutoff
  windowCardBound := estimate.windowCardBound
  windowCardConstant := estimate.windowCardConstant
  growth := estimate.growth
  windowCardConstant_nonneg := estimate.windowCardConstant_nonneg
  windowCard_le := estimate.windowCard_le
  tail_windowCardBound_le := estimate.tail_windowCardBound_le

/-- The cumulative-to-Riemann-von-Mangoldt adapter preserves the cutoff. -/
theorem ClosedBallZeroCumulativeWindowCountingEstimate.toRiemannVonMangoldtCountingTarget_cutoff
    (estimate : ClosedBallZeroCumulativeWindowCountingEstimate) :
    estimate.toRiemannVonMangoldtCountingTarget.cutoff = estimate.cutoff :=
  rfl

/-- The cumulative-to-Riemann-von-Mangoldt adapter preserves the growth exponent. -/
theorem ClosedBallZeroCumulativeWindowCountingEstimate.toRiemannVonMangoldtCountingTarget_growth
    (estimate : ClosedBallZeroCumulativeWindowCountingEstimate) :
    estimate.toRiemannVonMangoldtCountingTarget.growth = estimate.growth :=
  rfl

/--
Build the Riemann-von Mangoldt target from a direct polynomial bound on
closed-ball window counts.
-/
noncomputable def ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBound
    (cutoff : Nat)
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((closedBallZero.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget where
  cutoff := cutoff
  windowCardBound := fun n =>
    ((closedBallZero.zetaZeroSubtypeFinset n).card : Real)
  windowCardConstant := windowCardConstant
  growth := growth
  windowCardConstant_nonneg := windowCardConstant_nonneg
  windowCard_le := fun _n => le_rfl
  tail_windowCardBound_le := tail_windowCard_le

/--
The direct polynomial closed-ball bound also gives the project's preferred
cumulative-window estimate.
-/
noncomputable def ClosedBallZeroCumulativeWindowCountingEstimate.ofRiemannVonMangoldtWindowBound
    (cutoff : Nat)
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((closedBallZero.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  (ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBound
      cutoff windowCardConstant growth windowCardConstant_nonneg
      tail_windowCard_le).toCumulativeWindowCountingEstimate

/--
Cutoff-2 closed-ball Riemann-von Mangoldt target.

This is the zero-counting companion to the cutoff-2 p-series envelope route:
future analytic work only has to prove the polynomial closed-ball count on
windows `n + 2`.
-/
noncomputable def
    ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBoundCutoffTwo
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((closedBallZero.zetaZeroSubtypeFinset (n + 2)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBound
    2 windowCardConstant growth windowCardConstant_nonneg tail_windowCard_le

/-- The cutoff-2 target has cutoff exactly `2`. -/
theorem
    ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBoundCutoffTwo_cutoff
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((closedBallZero.zetaZeroSubtypeFinset (n + 2)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    (ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBoundCutoffTwo
      windowCardConstant growth windowCardConstant_nonneg
      tail_windowCard_le).cutoff = 2 :=
  rfl

/--
Cutoff-2 direct constructor for the project's preferred cumulative closed-ball
counting estimate.
-/
noncomputable def
    ClosedBallZeroCumulativeWindowCountingEstimate.ofRiemannVonMangoldtWindowBoundCutoffTwo
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((closedBallZero.zetaZeroSubtypeFinset (n + 2)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  (ClosedBallZeroRiemannVonMangoldtCountingTarget.ofWindowCardPolynomialBoundCutoffTwo
      windowCardConstant growth windowCardConstant_nonneg
      tail_windowCard_le).toCumulativeWindowCountingEstimate

/-- The cutoff-2 cumulative counting estimate has cutoff exactly `2`. -/
theorem
    ClosedBallZeroCumulativeWindowCountingEstimate.ofRiemannVonMangoldtWindowBoundCutoffTwo_cutoff
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((closedBallZero.zetaZeroSubtypeFinset (n + 2)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    (ClosedBallZeroCumulativeWindowCountingEstimate.ofRiemannVonMangoldtWindowBoundCutoffTwo
      windowCardConstant growth windowCardConstant_nonneg
      tail_windowCard_le).cutoff = 2 :=
  rfl

end ComplexCompactExhaustion

end RiemannHypothesisProject
