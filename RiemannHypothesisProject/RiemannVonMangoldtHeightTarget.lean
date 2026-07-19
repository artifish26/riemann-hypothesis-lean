import RiemannHypothesisProject.RiemannVonMangoldtCountingTarget

/-!
# Height-counting route to the closed-ball zero count

Classical Riemann-von Mangoldt estimates count non-trivial zeta zeroes by
height, usually with `0 < Im rho <= T`.  The tail pipeline in this project
counts all zeta zeroes in closed balls around zero.  This file names the
intermediate analytic work package connecting those two shapes.

The additional fields are intentional.  Passing from a height count to a
closed-ball count requires accounting for lower half-plane zeroes, symmetry,
and the finite collection of real-axis/trivial zeroes in the closed ball.  None
of those analytic facts is proved here; this module checks how they compose
once supplied.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/-- Zeta zeroes in the standard closed ball with positive ordinate. -/
noncomputable def closedBallZeroPositiveOrdinateFinset
    (n : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact (closedBallZero.zetaZeroSubtypeFinset n).filter
    (fun rho : ZetaZeroSubtype => 0 < Complex.im (rho : Complex))

/-- Zeta zeroes in the standard closed ball with negative ordinate. -/
noncomputable def closedBallZeroNegativeOrdinateFinset
    (n : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact (closedBallZero.zetaZeroSubtypeFinset n).filter
    (fun rho : ZetaZeroSubtype => Complex.im (rho : Complex) < 0)

/-- Zeta zeroes in the standard closed ball on the real axis. -/
noncomputable def closedBallZeroAxisOrdinateFinset
    (n : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact (closedBallZero.zetaZeroSubtypeFinset n).filter
    (fun rho : ZetaZeroSubtype => Complex.im (rho : Complex) = 0)

/-- Membership in the positive-ordinate closed-ball window. -/
theorem mem_closedBallZeroPositiveOrdinateFinset
    (n : Nat) {rho : ZetaZeroSubtype} :
    rho ∈ closedBallZeroPositiveOrdinateFinset n ↔
      rho ∈ closedBallZero.zetaZeroSubtypeFinset n ∧
        0 < Complex.im (rho : Complex) := by
  classical
  simp [closedBallZeroPositiveOrdinateFinset]

/-- Membership in the negative-ordinate closed-ball window. -/
theorem mem_closedBallZeroNegativeOrdinateFinset
    (n : Nat) {rho : ZetaZeroSubtype} :
    rho ∈ closedBallZeroNegativeOrdinateFinset n ↔
      rho ∈ closedBallZero.zetaZeroSubtypeFinset n ∧
        Complex.im (rho : Complex) < 0 := by
  classical
  simp [closedBallZeroNegativeOrdinateFinset]

/-- Membership in the axis-ordinate closed-ball window. -/
theorem mem_closedBallZeroAxisOrdinateFinset
    (n : Nat) {rho : ZetaZeroSubtype} :
    rho ∈ closedBallZeroAxisOrdinateFinset n ↔
      rho ∈ closedBallZero.zetaZeroSubtypeFinset n ∧
        Complex.im (rho : Complex) = 0 := by
  classical
  simp [closedBallZeroAxisOrdinateFinset]

/--
Every closed-ball zero lies in exactly one of the positive, negative, or
axis-ordinate windows.  The theorem is stated as a covering subset because the
cardinality estimate below only needs the upper bound.
-/
theorem closedBallZero_zetaZeroSubtypeFinset_subset_ordinateUnion
    (n : Nat) :
    closedBallZero.zetaZeroSubtypeFinset n ⊆
      closedBallZeroPositiveOrdinateFinset n ∪
        closedBallZeroNegativeOrdinateFinset n ∪
        closedBallZeroAxisOrdinateFinset n := by
  classical
  intro rho hrho
  rcases lt_trichotomy (Complex.im (rho : Complex)) 0 with hneg | haxis | hpos
  · simp [closedBallZeroPositiveOrdinateFinset,
      closedBallZeroNegativeOrdinateFinset,
      closedBallZeroAxisOrdinateFinset, hrho, hneg]
  · simp [closedBallZeroPositiveOrdinateFinset,
      closedBallZeroNegativeOrdinateFinset,
      closedBallZeroAxisOrdinateFinset, hrho, haxis]
  · simp [closedBallZeroPositiveOrdinateFinset,
      closedBallZeroNegativeOrdinateFinset,
      closedBallZeroAxisOrdinateFinset, hrho, hpos]

/--
The closed-ball zero count is bounded by the sum of the three ordinate-window
counts.
-/
theorem closedBallZero_card_le_ordinateWindowCards
    (n : Nat) :
    ((closedBallZero.zetaZeroSubtypeFinset n).card : Real) <=
      ((closedBallZeroPositiveOrdinateFinset n).card : Real) +
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) +
        ((closedBallZeroAxisOrdinateFinset n).card : Real) := by
  classical
  have hsubset :=
    closedBallZero_zetaZeroSubtypeFinset_subset_ordinateUnion n
  have hcard_subset :
      (closedBallZero.zetaZeroSubtypeFinset n).card <=
        (closedBallZeroPositiveOrdinateFinset n ∪
          closedBallZeroNegativeOrdinateFinset n ∪
          closedBallZeroAxisOrdinateFinset n).card :=
    Finset.card_le_card hsubset
  have hcard_union :
      (closedBallZeroPositiveOrdinateFinset n ∪
          closedBallZeroNegativeOrdinateFinset n ∪
          closedBallZeroAxisOrdinateFinset n).card <=
        (closedBallZeroPositiveOrdinateFinset n).card +
          (closedBallZeroNegativeOrdinateFinset n).card +
          (closedBallZeroAxisOrdinateFinset n).card := by
    exact le_trans
      (Finset.card_union_le
        (closedBallZeroPositiveOrdinateFinset n ∪
          closedBallZeroNegativeOrdinateFinset n)
        (closedBallZeroAxisOrdinateFinset n))
      (Nat.add_le_add_right
        (Finset.card_union_le
          (closedBallZeroPositiveOrdinateFinset n)
          (closedBallZeroNegativeOrdinateFinset n))
        (closedBallZeroAxisOrdinateFinset n).card)
  exact_mod_cast le_trans hcard_subset hcard_union

/--
A height-counting envelope for the standard closed-ball exhaustion.

`positiveOrdinateBound` is the Riemann-von-Mangoldt-shaped component.  The
`negativeOrdinateBound` and `axisOrTrivialBound` fields keep the conversion to
closed balls honest: a closed ball contains lower half-plane zeroes and the
trivial/real-axis part, not only the positive-ordinate non-trivial zeroes.
-/
structure ClosedBallZeroHeightCountingTarget where
  cutoff : Nat
  positiveOrdinateBound : Nat -> Real
  negativeOrdinateBound : Nat -> Real
  axisOrTrivialBound : Nat -> Real
  heightEnvelopeConstant : Real
  growth : Real
  heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant
  closedBall_card_le_heightEnvelope :
    forall n : Nat,
      ((closedBallZero.zetaZeroSubtypeFinset n).card : Real) <=
        positiveOrdinateBound n +
          negativeOrdinateBound n +
          axisOrTrivialBound n
  tail_heightEnvelope_le :
    forall n : Nat,
      positiveOrdinateBound (n + cutoff) +
          negativeOrdinateBound (n + cutoff) +
          axisOrTrivialBound (n + cutoff) <=
        heightEnvelopeConstant * |(n : Real) + 1| ^ growth

namespace ClosedBallZeroHeightCountingTarget

/-- The total height envelope used as the closed-ball window-card bound. -/
noncomputable def heightEnvelope
    (target : ClosedBallZeroHeightCountingTarget) (n : Nat) : Real :=
  target.positiveOrdinateBound n +
    target.negativeOrdinateBound n +
    target.axisOrTrivialBound n

/--
Convert a height-counting target into the direct Riemann-von-Mangoldt-style
closed-ball counting target used by the tail pipeline.
-/
noncomputable def toRiemannVonMangoldtCountingTarget
    (target : ClosedBallZeroHeightCountingTarget) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget where
  cutoff := target.cutoff
  windowCardBound := target.heightEnvelope
  windowCardConstant := target.heightEnvelopeConstant
  growth := target.growth
  windowCardConstant_nonneg := target.heightEnvelopeConstant_nonneg
  windowCard_le := target.closedBall_card_le_heightEnvelope
  tail_windowCardBound_le := target.tail_heightEnvelope_le

/-- Height counting gives the preferred cumulative closed-ball count. -/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClosedBallZeroHeightCountingTarget) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  target.toRiemannVonMangoldtCountingTarget
    |>.toCumulativeWindowCountingEstimate

/-- Height counting gives first-entry shell counting for the standard exhaustion. -/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClosedBallZeroHeightCountingTarget) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toRiemannVonMangoldtCountingTarget
    |>.toPolynomialZeroCountingEstimate

/-- The converted Riemann-von-Mangoldt target keeps the height cutoff. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    (target : ClosedBallZeroHeightCountingTarget) :
    target.toRiemannVonMangoldtCountingTarget.cutoff = target.cutoff :=
  rfl

/-- The converted cumulative estimate keeps the height cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    (target : ClosedBallZeroHeightCountingTarget) :
    target.toCumulativeWindowCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the height cutoff. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    (target : ClosedBallZeroHeightCountingTarget) :
    target.toPolynomialZeroCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the height growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    (target : ClosedBallZeroHeightCountingTarget) :
    target.toPolynomialZeroCountingEstimate.growth = target.growth :=
  rfl

end ClosedBallZeroHeightCountingTarget

namespace ClosedBallZeroHeightCountingTarget

/-- The combined constant for positive, negative, and axis/trivial height pieces. -/
def heightEnvelopeConstantFromComponents
    (positiveConstant negativeConstant axisConstant : Real) : Real :=
  positiveConstant + negativeConstant + axisConstant

/-- Nonnegative component constants give a nonnegative height-envelope constant. -/
theorem heightEnvelopeConstantFromComponents_nonneg
    {positiveConstant negativeConstant axisConstant : Real}
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (negativeConstant_nonneg : 0 <= negativeConstant)
    (axisConstant_nonneg : 0 <= axisConstant) :
    0 <= heightEnvelopeConstantFromComponents
      positiveConstant negativeConstant axisConstant :=
  add_nonneg
    (add_nonneg positiveConstant_nonneg negativeConstant_nonneg)
    axisConstant_nonneg

/--
Separate polynomial tails for the positive, negative, and axis/trivial pieces
imply the combined height-envelope tail used by the closed-ball count target.
-/
theorem tail_heightEnvelope_le_of_component_polynomial_bounds
    (cutoff : Nat)
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (positiveConstant negativeConstant axisConstant growth : Real)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + cutoff) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_negativeOrdinateBound_le :
      forall n : Nat,
        negativeOrdinateBound (n + cutoff) <=
          negativeConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth)
    (n : Nat) :
    positiveOrdinateBound (n + cutoff) +
        negativeOrdinateBound (n + cutoff) +
        axisOrTrivialBound (n + cutoff) <=
      heightEnvelopeConstantFromComponents
          positiveConstant negativeConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
  have hpos := tail_positiveOrdinateBound_le n
  have hneg := tail_negativeOrdinateBound_le n
  have haxis := tail_axisOrTrivialBound_le n
  calc
    positiveOrdinateBound (n + cutoff) +
        negativeOrdinateBound (n + cutoff) +
        axisOrTrivialBound (n + cutoff)
        <=
      positiveConstant * |(n : Real) + 1| ^ growth +
        negativeConstant * |(n : Real) + 1| ^ growth +
        axisConstant * |(n : Real) + 1| ^ growth := by
        exact add_le_add (add_le_add hpos hneg) haxis
    _ =
      heightEnvelopeConstantFromComponents
          positiveConstant negativeConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
        rw [heightEnvelopeConstantFromComponents]
        ring

end ClosedBallZeroHeightCountingTarget

/--
Build the height-counting target from separate bounds on the positive,
negative, and axis-ordinate parts of each closed-ball window.
-/
noncomputable def ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBounds
    (cutoff : Nat)
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          negativeOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_heightEnvelope_le :
      forall n : Nat,
        positiveOrdinateBound (n + cutoff) +
            negativeOrdinateBound (n + cutoff) +
            axisOrTrivialBound (n + cutoff) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroHeightCountingTarget where
  cutoff := cutoff
  positiveOrdinateBound := positiveOrdinateBound
  negativeOrdinateBound := negativeOrdinateBound
  axisOrTrivialBound := axisOrTrivialBound
  heightEnvelopeConstant := heightEnvelopeConstant
  growth := growth
  heightEnvelopeConstant_nonneg := heightEnvelopeConstant_nonneg
  closedBall_card_le_heightEnvelope := fun n =>
    le_trans (closedBallZero_card_le_ordinateWindowCards n)
      (add_le_add
        (add_le_add (positiveWindowCard_le n) (negativeWindowCard_le n))
        (axisWindowCard_le n))
  tail_heightEnvelope_le := tail_heightEnvelope_le

/--
Build the height-counting target from separate window bounds and separate
polynomial tails for the positive, negative, and axis/trivial pieces.
-/
noncomputable def ClosedBallZeroHeightCountingTarget.ofOrdinateWindowPolynomialBounds
    (cutoff : Nat)
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (positiveConstant negativeConstant axisConstant growth : Real)
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (negativeConstant_nonneg : 0 <= negativeConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          negativeOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + cutoff) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_negativeOrdinateBound_le :
      forall n : Nat,
        negativeOrdinateBound (n + cutoff) <=
          negativeConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroHeightCountingTarget :=
  ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBounds
    cutoff positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound
    (ClosedBallZeroHeightCountingTarget.heightEnvelopeConstantFromComponents
      positiveConstant negativeConstant axisConstant)
    growth
    (ClosedBallZeroHeightCountingTarget.heightEnvelopeConstantFromComponents_nonneg
      positiveConstant_nonneg negativeConstant_nonneg axisConstant_nonneg)
    positiveWindowCard_le negativeWindowCard_le axisWindowCard_le
    (ClosedBallZeroHeightCountingTarget.tail_heightEnvelope_le_of_component_polynomial_bounds
      cutoff positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound
      positiveConstant negativeConstant axisConstant growth
      tail_positiveOrdinateBound_le tail_negativeOrdinateBound_le
      tail_axisOrTrivialBound_le)

/--
Cutoff-2 height-counting target from separate positive, negative, and
axis-ordinate window bounds.
-/
noncomputable def ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBoundsCutoffTwo
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          negativeOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_heightEnvelope_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) +
            negativeOrdinateBound (n + 2) +
            axisOrTrivialBound (n + 2) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroHeightCountingTarget :=
  ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBounds
    2 positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound
    heightEnvelopeConstant growth heightEnvelopeConstant_nonneg
    positiveWindowCard_le negativeWindowCard_le axisWindowCard_le
    tail_heightEnvelope_le

/-- The cutoff-2 height-counting target has cutoff exactly `2`. -/
theorem ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBoundsCutoffTwo_cutoff
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          negativeOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_heightEnvelope_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) +
            negativeOrdinateBound (n + 2) +
            axisOrTrivialBound (n + 2) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    (ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBoundsCutoffTwo
      positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound
      heightEnvelopeConstant growth heightEnvelopeConstant_nonneg
      positiveWindowCard_le negativeWindowCard_le axisWindowCard_le
      tail_heightEnvelope_le).cutoff = 2 :=
  rfl

/--
Cutoff-2 height-counting target from separate window bounds and separate
polynomial tails for the positive, negative, and axis/trivial pieces.
-/
noncomputable def
    ClosedBallZeroHeightCountingTarget.ofOrdinateWindowPolynomialBoundsCutoffTwo
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (positiveConstant negativeConstant axisConstant growth : Real)
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (negativeConstant_nonneg : 0 <= negativeConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          negativeOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_negativeOrdinateBound_le :
      forall n : Nat,
        negativeOrdinateBound (n + 2) <=
          negativeConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroHeightCountingTarget :=
  ClosedBallZeroHeightCountingTarget.ofOrdinateWindowPolynomialBounds
    2 positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound
    positiveConstant negativeConstant axisConstant growth
    positiveConstant_nonneg negativeConstant_nonneg axisConstant_nonneg
    positiveWindowCard_le negativeWindowCard_le axisWindowCard_le
    tail_positiveOrdinateBound_le tail_negativeOrdinateBound_le
    tail_axisOrTrivialBound_le

/-- The cutoff-2 component-polynomial height-counting target has cutoff exactly `2`. -/
theorem
    ClosedBallZeroHeightCountingTarget.ofOrdinateWindowPolynomialBoundsCutoffTwo_cutoff
    (positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound :
      Nat -> Real)
    (positiveConstant negativeConstant axisConstant growth : Real)
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (negativeConstant_nonneg : 0 <= negativeConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          negativeOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_negativeOrdinateBound_le :
      forall n : Nat,
        negativeOrdinateBound (n + 2) <=
          negativeConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    (ClosedBallZeroHeightCountingTarget.ofOrdinateWindowPolynomialBoundsCutoffTwo
      positiveOrdinateBound negativeOrdinateBound axisOrTrivialBound
      positiveConstant negativeConstant axisConstant growth
      positiveConstant_nonneg negativeConstant_nonneg axisConstant_nonneg
      positiveWindowCard_le negativeWindowCard_le axisWindowCard_le
      tail_positiveOrdinateBound_le tail_negativeOrdinateBound_le
      tail_axisOrTrivialBound_le).cutoff = 2 :=
  rfl

/--
The common symmetric height-counting shape.

In the classical zeta situation, a positive-ordinate count plus conjugation
symmetry should control the negative-ordinate count.  The `axisOrTrivialBound`
field leaves the real-axis/trivial-zero contribution explicit.
-/
structure ClosedBallZeroSymmetricHeightCountingTarget where
  cutoff : Nat
  positiveOrdinateBound : Nat -> Real
  axisOrTrivialBound : Nat -> Real
  heightEnvelopeConstant : Real
  growth : Real
  heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant
  closedBall_card_le_symmetricHeightEnvelope :
    forall n : Nat,
      ((closedBallZero.zetaZeroSubtypeFinset n).card : Real) <=
        positiveOrdinateBound n +
          positiveOrdinateBound n +
          axisOrTrivialBound n
  tail_symmetricHeightEnvelope_le :
    forall n : Nat,
      positiveOrdinateBound (n + cutoff) +
          positiveOrdinateBound (n + cutoff) +
          axisOrTrivialBound (n + cutoff) <=
        heightEnvelopeConstant * |(n : Real) + 1| ^ growth

namespace ClosedBallZeroSymmetricHeightCountingTarget

/-- Forget a symmetric height-counting target to the general height envelope. -/
noncomputable def toHeightCountingTarget
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    ClosedBallZeroHeightCountingTarget where
  cutoff := target.cutoff
  positiveOrdinateBound := target.positiveOrdinateBound
  negativeOrdinateBound := target.positiveOrdinateBound
  axisOrTrivialBound := target.axisOrTrivialBound
  heightEnvelopeConstant := target.heightEnvelopeConstant
  growth := target.growth
  heightEnvelopeConstant_nonneg := target.heightEnvelopeConstant_nonneg
  closedBall_card_le_heightEnvelope :=
    target.closedBall_card_le_symmetricHeightEnvelope
  tail_heightEnvelope_le := target.tail_symmetricHeightEnvelope_le

/-- Symmetric height counting gives the direct closed-ball counting target. -/
noncomputable def toRiemannVonMangoldtCountingTarget
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  target.toHeightCountingTarget.toRiemannVonMangoldtCountingTarget

/-- Symmetric height counting gives the preferred cumulative-window estimate. -/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  target.toHeightCountingTarget.toCumulativeWindowCountingEstimate

/-- Symmetric height counting gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toHeightCountingTarget.toPolynomialZeroCountingEstimate

/-- The converted cumulative estimate keeps the symmetric height cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    target.toCumulativeWindowCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted Riemann-von-Mangoldt target keeps the symmetric height cutoff. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    target.toRiemannVonMangoldtCountingTarget.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the symmetric height cutoff. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    target.toPolynomialZeroCountingEstimate.cutoff = target.cutoff :=
  rfl

/-- The converted shell-counting estimate keeps the symmetric height growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    (target : ClosedBallZeroSymmetricHeightCountingTarget) :
    target.toPolynomialZeroCountingEstimate.growth = target.growth :=
  rfl

end ClosedBallZeroSymmetricHeightCountingTarget

namespace ClosedBallZeroSymmetricHeightCountingTarget

/-- The combined constant for two symmetric half-plane counts plus the axis contribution. -/
def symmetricHeightEnvelopeConstant
    (positiveConstant axisConstant : Real) : Real :=
  positiveConstant + positiveConstant + axisConstant

/-- Nonnegative component constants give a nonnegative symmetric height constant. -/
theorem symmetricHeightEnvelopeConstant_nonneg
    {positiveConstant axisConstant : Real}
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (axisConstant_nonneg : 0 <= axisConstant) :
    0 <= symmetricHeightEnvelopeConstant positiveConstant axisConstant :=
  add_nonneg
    (add_nonneg positiveConstant_nonneg positiveConstant_nonneg)
    axisConstant_nonneg

/--
A polynomial tail for the positive-ordinate envelope, reused for the negative
side, plus an axis/trivial tail gives the symmetric height-envelope tail.
-/
theorem tail_symmetricHeightEnvelope_le_of_component_polynomial_bounds
    (cutoff : Nat)
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (positiveConstant axisConstant growth : Real)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + cutoff) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth)
    (n : Nat) :
    positiveOrdinateBound (n + cutoff) +
        positiveOrdinateBound (n + cutoff) +
        axisOrTrivialBound (n + cutoff) <=
      symmetricHeightEnvelopeConstant positiveConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
  have hpos := tail_positiveOrdinateBound_le n
  have haxis := tail_axisOrTrivialBound_le n
  calc
    positiveOrdinateBound (n + cutoff) +
        positiveOrdinateBound (n + cutoff) +
        axisOrTrivialBound (n + cutoff)
        <=
      positiveConstant * |(n : Real) + 1| ^ growth +
        positiveConstant * |(n : Real) + 1| ^ growth +
        axisConstant * |(n : Real) + 1| ^ growth := by
        exact add_le_add (add_le_add hpos hpos) haxis
    _ =
      symmetricHeightEnvelopeConstant positiveConstant axisConstant *
        |(n : Real) + 1| ^ growth := by
        rw [symmetricHeightEnvelopeConstant]
        ring

end ClosedBallZeroSymmetricHeightCountingTarget

/--
Build the symmetric height-counting target from positive-ordinate and
axis-ordinate bounds, plus an explicit bound showing the negative-ordinate
window is controlled by the same positive-ordinate envelope.
-/
noncomputable def
    ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBounds
    (cutoff : Nat)
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le_positiveBound :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_symmetricHeightEnvelope_le :
      forall n : Nat,
        positiveOrdinateBound (n + cutoff) +
            positiveOrdinateBound (n + cutoff) +
            axisOrTrivialBound (n + cutoff) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroSymmetricHeightCountingTarget where
  cutoff := cutoff
  positiveOrdinateBound := positiveOrdinateBound
  axisOrTrivialBound := axisOrTrivialBound
  heightEnvelopeConstant := heightEnvelopeConstant
  growth := growth
  heightEnvelopeConstant_nonneg := heightEnvelopeConstant_nonneg
  closedBall_card_le_symmetricHeightEnvelope := fun n =>
    le_trans (closedBallZero_card_le_ordinateWindowCards n)
      (add_le_add
        (add_le_add
          (positiveWindowCard_le n)
          (negativeWindowCard_le_positiveBound n))
        (axisWindowCard_le n))
  tail_symmetricHeightEnvelope_le := tail_symmetricHeightEnvelope_le

/--
Build the symmetric height-counting target from window bounds and separate
polynomial tails for the positive-ordinate and axis/trivial pieces.
-/
noncomputable def
    ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisPolynomialBounds
    (cutoff : Nat)
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (positiveConstant axisConstant growth : Real)
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le_positiveBound :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + cutoff) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + cutoff) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroSymmetricHeightCountingTarget :=
  ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBounds
    cutoff positiveOrdinateBound axisOrTrivialBound
    (ClosedBallZeroSymmetricHeightCountingTarget.symmetricHeightEnvelopeConstant
      positiveConstant axisConstant)
    growth
    (ClosedBallZeroSymmetricHeightCountingTarget.symmetricHeightEnvelopeConstant_nonneg
      positiveConstant_nonneg axisConstant_nonneg)
    positiveWindowCard_le negativeWindowCard_le_positiveBound
    axisWindowCard_le
    (ClosedBallZeroSymmetricHeightCountingTarget.tail_symmetricHeightEnvelope_le_of_component_polynomial_bounds
      cutoff positiveOrdinateBound axisOrTrivialBound
      positiveConstant axisConstant growth
      tail_positiveOrdinateBound_le tail_axisOrTrivialBound_le)

/--
Cutoff-2 symmetric height-counting target from a positive-ordinate bound, a
matching negative-side bound, and an axis/trivial contribution.
-/
noncomputable def
    ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBoundsCutoffTwo
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le_positiveBound :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_symmetricHeightEnvelope_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) +
            positiveOrdinateBound (n + 2) +
            axisOrTrivialBound (n + 2) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroSymmetricHeightCountingTarget :=
  ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBounds
    2 positiveOrdinateBound axisOrTrivialBound heightEnvelopeConstant growth
    heightEnvelopeConstant_nonneg positiveWindowCard_le
    negativeWindowCard_le_positiveBound axisWindowCard_le
    tail_symmetricHeightEnvelope_le

/-- The cutoff-2 symmetric height-counting target has cutoff exactly `2`. -/
theorem
    ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBoundsCutoffTwo_cutoff
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le_positiveBound :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_symmetricHeightEnvelope_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) +
            positiveOrdinateBound (n + 2) +
            axisOrTrivialBound (n + 2) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    (ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBoundsCutoffTwo
      positiveOrdinateBound axisOrTrivialBound heightEnvelopeConstant growth
      heightEnvelopeConstant_nonneg positiveWindowCard_le
      negativeWindowCard_le_positiveBound axisWindowCard_le
      tail_symmetricHeightEnvelope_le).cutoff = 2 :=
  rfl

/--
Cutoff-2 symmetric height-counting target from window bounds and separate
polynomial tails for the positive-ordinate and axis/trivial pieces.
-/
noncomputable def
    ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisPolynomialBoundsCutoffTwo
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (positiveConstant axisConstant growth : Real)
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le_positiveBound :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    ClosedBallZeroSymmetricHeightCountingTarget :=
  ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisPolynomialBounds
    2 positiveOrdinateBound axisOrTrivialBound
    positiveConstant axisConstant growth
    positiveConstant_nonneg axisConstant_nonneg
    positiveWindowCard_le negativeWindowCard_le_positiveBound
    axisWindowCard_le tail_positiveOrdinateBound_le
    tail_axisOrTrivialBound_le

/-- The cutoff-2 component-polynomial symmetric height target has cutoff exactly `2`. -/
theorem
    ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisPolynomialBoundsCutoffTwo_cutoff
    (positiveOrdinateBound axisOrTrivialBound : Nat -> Real)
    (positiveConstant axisConstant growth : Real)
    (positiveConstant_nonneg : 0 <= positiveConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (positiveWindowCard_le :
      forall n : Nat,
        ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (negativeWindowCard_le_positiveBound :
      forall n : Nat,
        ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
          positiveOrdinateBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_positiveOrdinateBound_le :
      forall n : Nat,
        positiveOrdinateBound (n + 2) <=
          positiveConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    (ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisPolynomialBoundsCutoffTwo
      positiveOrdinateBound axisOrTrivialBound
      positiveConstant axisConstant growth
      positiveConstant_nonneg axisConstant_nonneg
      positiveWindowCard_le negativeWindowCard_le_positiveBound
      axisWindowCard_le tail_positiveOrdinateBound_le
      tail_axisOrTrivialBound_le).cutoff = 2 :=
  rfl

end ComplexCompactExhaustion

end RiemannHypothesisProject
