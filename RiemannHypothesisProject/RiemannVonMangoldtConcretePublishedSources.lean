import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannHypothesisProject.RiemannVonMangoldtElementaryBounds
import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisEndpoints
import RiemannHypothesisProject.RiemannVonMangoldtPublishedBounds

/-!
# Concrete published `N(T)` source packages

`RiemannVonMangoldtPublishedBounds` gives a general receiving record for
published explicit Riemann-von-Mangoldt estimates.  This file fixes the
published error term for the two concrete sources currently tracked by the
project:

* Bellotti-Wong, with the project-recorded threshold `T >= e`;
* Hasanalizade-Shen-Wong, with the threshold left as an explicit parameter.

The hard analytic theorem, finite-window interpretation, below-domain cleanup,
and polynomial tails remain fields.  The point is to make future instantiation
work fill those fields against the named published constants rather than
restating the normalization each time.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/--
A source package whose published domain threshold and published error term are
fixed by parameters.

This is the common shape behind the Bellotti-Wong and
Hasanalizade-Shen-Wong targets.  It reduces the remaining work to the actual
published estimate, the finite-window interpretation of `N(T)`, the
below-domain all-real extension, and the coarse polynomial tail bounds.
-/
structure FixedErrorExplicitRiemannVonMangoldtSourceInput
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  cutoff : Nat
  heightCount : Real -> Real
  extendedErrorTerm : Real -> Real
  axisOrTrivialBound : Nat -> Real
  mainConstant : Real
  errorConstant : Real
  axisConstant : Real
  growth : Real
  mainConstant_nonneg : 0 <= mainConstant
  errorConstant_nonneg : 0 <= errorConstant
  axisConstant_nonneg : 0 <= axisConstant
  published_abs_error_le :
    forall T : Real,
      validFrom <= T ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          publishedErrorTerm T
  belowDomain_abs_error_le :
    forall T : Real,
      T < validFrom ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          extendedErrorTerm T
  extendedErrorTerm_eq_published :
    forall T : Real,
      validFrom <= T ->
        extendedErrorTerm T = publishedErrorTerm T
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
  tail_mainTerm_le :
    forall n : Nat,
      riemannVonMangoldtMainTerm ((n + cutoff : Nat) : Real) <=
        mainConstant * |(n : Real) + 1| ^ growth
  tail_extendedErrorTerm_le :
    forall n : Nat,
      extendedErrorTerm ((n + cutoff : Nat) : Real) <=
        errorConstant * |(n : Real) + 1| ^ growth
  tail_axisOrTrivialBound_le :
    forall n : Nat,
      axisOrTrivialBound (n + cutoff) <=
        axisConstant * |(n : Real) + 1| ^ growth

namespace FixedErrorExplicitRiemannVonMangoldtSourceInput

/-- Convert a fixed-error source input into the generic published-source record. -/
noncomputable def toPublishedExplicitRiemannVonMangoldtSource
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    PublishedExplicitRiemannVonMangoldtSource where
  cutoff := input.cutoff
  validFrom := validFrom
  heightCount := input.heightCount
  publishedErrorTerm := publishedErrorTerm
  extendedErrorTerm := input.extendedErrorTerm
  axisOrTrivialBound := input.axisOrTrivialBound
  mainConstant := input.mainConstant
  errorConstant := input.errorConstant
  axisConstant := input.axisConstant
  growth := input.growth
  mainConstant_nonneg := input.mainConstant_nonneg
  errorConstant_nonneg := input.errorConstant_nonneg
  axisConstant_nonneg := input.axisConstant_nonneg
  published_abs_error_le := input.published_abs_error_le
  belowDomain_abs_error_le := input.belowDomain_abs_error_le
  extendedErrorTerm_eq_published := input.extendedErrorTerm_eq_published
  positiveFiniteWindowCard_le_heightCount :=
    input.positiveFiniteWindowCard_le_heightCount
  negativeFiniteWindowCard_le_heightCount :=
    input.negativeFiniteWindowCard_le_heightCount
  axisWindowCard_le := input.axisWindowCard_le
  tail_mainTerm_le := input.tail_mainTerm_le
  tail_extendedErrorTerm_le := input.tail_extendedErrorTerm_le
  tail_axisOrTrivialBound_le := input.tail_axisOrTrivialBound_le

/-- The converted source keeps the fixed published threshold. -/
theorem toPublishedExplicitRiemannVonMangoldtSource_validFrom
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toPublishedExplicitRiemannVonMangoldtSource.validFrom =
      validFrom := by
  rfl

/-- The converted source keeps the fixed published error term. -/
theorem toPublishedExplicitRiemannVonMangoldtSource_publishedErrorTerm
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toPublishedExplicitRiemannVonMangoldtSource.publishedErrorTerm =
      publishedErrorTerm := by
  rfl

/-- The converted published source keeps the fixed-error input cutoff. -/
theorem toPublishedExplicitRiemannVonMangoldtSource_cutoff
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toPublishedExplicitRiemannVonMangoldtSource.cutoff =
      input.cutoff := by
  rfl

/-- The fixed-error input gives the existing all-real explicit bound adapter. -/
noncomputable def toClassicalExplicitRiemannVonMangoldtBound
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    ClassicalExplicitRiemannVonMangoldtBound :=
  input.toPublishedExplicitRiemannVonMangoldtSource
    |>.toClassicalExplicitRiemannVonMangoldtBound

/-- The fixed-error input gives the preferred cumulative closed-ball count. -/
noncomputable def toCumulativeWindowCountingEstimate
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  input.toPublishedExplicitRiemannVonMangoldtSource
    |>.toCumulativeWindowCountingEstimate

/-- The fixed-error cumulative count keeps the input cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toCumulativeWindowCountingEstimate.cutoff = input.cutoff := by
  rfl

/-- The fixed-error input gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  input.toPublishedExplicitRiemannVonMangoldtSource
    |>.toPolynomialZeroCountingEstimate

/-- The fixed-error input gives the named closed-ball Riemann-von-Mangoldt target. -/
noncomputable def toRiemannVonMangoldtCountingTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  PublishedExplicitRiemannVonMangoldtSource.toRiemannVonMangoldtCountingTarget
    input.toPublishedExplicitRiemannVonMangoldtSource

/-- The fixed-error shell-counting estimate keeps the input cutoff. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toPolynomialZeroCountingEstimate.cutoff = input.cutoff := by
  rfl

/-- The fixed-error shell-counting estimate keeps the input growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toPolynomialZeroCountingEstimate.growth = input.growth := by
  rfl

/-- The fixed-error Riemann-von-Mangoldt target keeps the input cutoff. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toRiemannVonMangoldtCountingTarget.cutoff = input.cutoff := by
  rw [toRiemannVonMangoldtCountingTarget,
    PublishedExplicitRiemannVonMangoldtSource.toRiemannVonMangoldtCountingTarget_cutoff]
  rfl

/-- The fixed-error Riemann-von-Mangoldt target keeps the input growth exponent. -/
theorem toRiemannVonMangoldtCountingTarget_growth
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm) :
    input.toRiemannVonMangoldtCountingTarget.growth = input.growth := by
  rw [toRiemannVonMangoldtCountingTarget,
    PublishedExplicitRiemannVonMangoldtSource.toRiemannVonMangoldtCountingTarget_growth]
  rfl

/-- If the fixed-error input uses cutoff `2`, so does its cumulative count. -/
theorem toCumulativeWindowCountingEstimate_cutoff_eq_two_of_cutoff_eq_two
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (hcutoff : input.cutoff = 2) :
    input.toCumulativeWindowCountingEstimate.cutoff = 2 := by
  rw [toCumulativeWindowCountingEstimate_cutoff input, hcutoff]

/-- If the fixed-error input uses cutoff `2`, so does its shell-counting estimate. -/
theorem toPolynomialZeroCountingEstimate_cutoff_eq_two_of_cutoff_eq_two
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (hcutoff : input.cutoff = 2) :
    input.toPolynomialZeroCountingEstimate.cutoff = 2 := by
  rw [toPolynomialZeroCountingEstimate_cutoff input, hcutoff]

/-- If the fixed-error input uses cutoff `2`, so does its Riemann-von-Mangoldt target. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff_eq_two_of_cutoff_eq_two
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (input :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (hcutoff : input.cutoff = 2) :
    input.toRiemannVonMangoldtCountingTarget.cutoff = 2 := by
  rw [toRiemannVonMangoldtCountingTarget_cutoff input, hcutoff]

/--
A generic signed below-domain extension for fixed-error sources. Above the
published threshold it is the published error term. Below the threshold,
negative `T` is covered by the absolute Riemann-von-Mangoldt main term, while
nonnegative `T` is controlled by one finite cleanup constant.
-/
def cutoffTwoSignedExtendedErrorTerm
    (validFrom : Real) (publishedErrorTerm : Real -> Real)
    (belowErrorConstant : Real) (T : Real) : Real :=
  if validFrom <= T then publishedErrorTerm T
  else if T < 0 then |riemannVonMangoldtMainTerm T|
  else belowErrorConstant

/-- Above the source threshold, the generic signed extension is the published error term. -/
theorem cutoffTwoSignedExtendedErrorTerm_eq_published
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (belowErrorConstant : Real) {T : Real}
    (hT : validFrom <= T) :
    cutoffTwoSignedExtendedErrorTerm
        validFrom publishedErrorTerm belowErrorConstant T =
      publishedErrorTerm T := by
  dsimp [cutoffTwoSignedExtendedErrorTerm]
  rw [if_pos hT]

/-- The cutoff-2 p-series base satisfies `1 <= |n + 1|^2`. -/
theorem one_le_abs_natCast_add_one_sq (n : Nat) :
    (1 : Real) <= |(n : Real) + 1| ^ (2 : Real) := by
  have hy_nonneg : 0 <= (n : Real) + 1 := by positivity
  have hy_one : 1 <= (n : Real) + 1 := by
    nlinarith [(Nat.cast_nonneg n : (0 : Real) <= (n : Real))]
  have hpow :
      |(n : Real) + 1| ^ (2 : Real) = ((n : Real) + 1) ^ 2 := by
    rw [abs_of_nonneg hy_nonneg]
    exact Real.rpow_natCast ((n : Real) + 1) 2
  rw [hpow]
  nlinarith [hy_one]

/--
The generic signed extension inherits a cutoff-2 quadratic tail from the
published error term, provided the finite nonnegative cleanup constant is no
larger than the same tail constant.
-/
theorem cutoffTwoSignedExtendedErrorTerm_cutoffTwo_le_quadratic
    {validFrom belowErrorConstant errorConstant : Real}
    {publishedErrorTerm : Real -> Real}
    (belowErrorConstant_le : belowErrorConstant <= errorConstant)
    (errorConstant_nonneg : 0 <= errorConstant)
    (published_tail_le :
      forall n : Nat,
        publishedErrorTerm ((n + 2 : Nat) : Real) <=
          errorConstant * |(n : Real) + 1| ^ (2 : Real))
    (n : Nat) :
    cutoffTwoSignedExtendedErrorTerm
        validFrom publishedErrorTerm belowErrorConstant
        ((n + 2 : Nat) : Real) <=
      errorConstant * |(n : Real) + 1| ^ (2 : Real) := by
  by_cases hvalid : validFrom <= ((n + 2 : Nat) : Real)
  · rw [cutoffTwoSignedExtendedErrorTerm_eq_published
      (validFrom := validFrom)
      (publishedErrorTerm := publishedErrorTerm)
      belowErrorConstant hvalid]
    exact published_tail_le n
  · dsimp [cutoffTwoSignedExtendedErrorTerm]
    rw [if_neg hvalid]
    have hnot_neg : ¬ (((n + 2 : Nat) : Real) < 0) := by
      exact not_lt_of_ge (by positivity)
    rw [if_neg hnot_neg]
    have hbase := one_le_abs_natCast_add_one_sq n
    have htail_base :
        errorConstant <=
          errorConstant * |(n : Real) + 1| ^ (2 : Real) := by
      simpa using
        (mul_le_mul_of_nonneg_left hbase errorConstant_nonneg)
    exact belowErrorConstant_le.trans htail_base

/--
For the generic signed extension, below-domain cleanup follows from vanishing
of the height count below the source threshold plus a finite bound for the main
term on the nonnegative part of that interval.
-/
theorem signedBelowDomain_abs_error_le_of_heightCount_eq_zero
    {validFrom belowErrorConstant : Real}
    {publishedErrorTerm heightCount : Real -> Real}
    (heightCount_eq_zero_below :
      forall T : Real,
        T < validFrom ->
          heightCount T = 0)
    (mainTerm_abs_nonneg_below_le :
      forall T : Real,
        0 <= T ->
          T < validFrom ->
            |riemannVonMangoldtMainTerm T| <= belowErrorConstant) :
    forall T : Real,
      T < validFrom ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          cutoffTwoSignedExtendedErrorTerm
            validFrom publishedErrorTerm belowErrorConstant T := by
  intro T hT
  rw [heightCount_eq_zero_below T hT]
  dsimp [cutoffTwoSignedExtendedErrorTerm]
  rw [if_neg (not_le_of_gt hT)]
  by_cases hT_neg : T < 0
  · rw [if_pos hT_neg]
    simp [abs_neg]
  · have hT_nonneg : 0 <= T := le_of_not_gt hT_neg
    rw [if_neg hT_neg]
    simpa [abs_neg] using
      mainTerm_abs_nonneg_below_le T hT_nonneg hT

/--
Build a fixed-error published source input with cutoff fixed to `2`.

The remaining polynomial tails are stated directly at `n + 2`, matching the
cutoff-2 closed-ball counting and p-series route.
-/
noncomputable def ofCutoffTwo
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (heightCount extendedErrorTerm : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (mainConstant errorConstant axisConstant growth : Real)
    (mainConstant_nonneg : 0 <= mainConstant)
    (errorConstant_nonneg : 0 <= errorConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            publishedErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            extendedErrorTerm T)
    (extendedErrorTerm_eq_published :
      forall T : Real,
        validFrom <= T ->
          extendedErrorTerm T = publishedErrorTerm T)
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
        riemannVonMangoldtMainTerm ((n + 2 : Nat) : Real) <=
          mainConstant * |(n : Real) + 1| ^ growth)
    (tail_extendedErrorTerm_le :
      forall n : Nat,
        extendedErrorTerm ((n + 2 : Nat) : Real) <=
          errorConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    FixedErrorExplicitRiemannVonMangoldtSourceInput
      validFrom publishedErrorTerm where
  cutoff := 2
  heightCount := heightCount
  extendedErrorTerm := extendedErrorTerm
  axisOrTrivialBound := axisOrTrivialBound
  mainConstant := mainConstant
  errorConstant := errorConstant
  axisConstant := axisConstant
  growth := growth
  mainConstant_nonneg := mainConstant_nonneg
  errorConstant_nonneg := errorConstant_nonneg
  axisConstant_nonneg := axisConstant_nonneg
  published_abs_error_le := published_abs_error_le
  belowDomain_abs_error_le := belowDomain_abs_error_le
  extendedErrorTerm_eq_published := extendedErrorTerm_eq_published
  positiveFiniteWindowCard_le_heightCount :=
    positiveFiniteWindowCard_le_heightCount
  negativeFiniteWindowCard_le_heightCount :=
    negativeFiniteWindowCard_le_heightCount
  axisWindowCard_le := axisWindowCard_le
  tail_mainTerm_le := tail_mainTerm_le
  tail_extendedErrorTerm_le := tail_extendedErrorTerm_le
  tail_axisOrTrivialBound_le := tail_axisOrTrivialBound_le

/--
Build a fixed-error published source input with cutoff `2` from an exact
positive-ordinate height-count window and a global conjugation-style mirror.
The exact window supplies the positive finite-window field, and conjugation
supplies the negative finite-window field.
-/
noncomputable def ofCutoffTwoWithExactHeightWindowAndConjugation
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (heightCount extendedErrorTerm : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (axisOrTrivialBound : Nat -> Real)
    (mainConstant errorConstant axisConstant growth : Real)
    (mainConstant_nonneg : 0 <= mainConstant)
    (errorConstant_nonneg : 0 <= errorConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            publishedErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            extendedErrorTerm T)
    (extendedErrorTerm_eq_published :
      forall T : Real,
        validFrom <= T ->
          extendedErrorTerm T = publishedErrorTerm T)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_mainTerm_le :
      forall n : Nat,
        riemannVonMangoldtMainTerm ((n + 2 : Nat) : Real) <=
          mainConstant * |(n : Real) + 1| ^ growth)
    (tail_extendedErrorTerm_le :
      forall n : Nat,
        extendedErrorTerm ((n + 2 : Nat) : Real) <=
          errorConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    FixedErrorExplicitRiemannVonMangoldtSourceInput
      validFrom publishedErrorTerm :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwo
    (validFrom := validFrom)
    (publishedErrorTerm := publishedErrorTerm)
    heightCount
    extendedErrorTerm
    axisOrTrivialBound
    mainConstant
    errorConstant
    axisConstant
    growth
    mainConstant_nonneg
    errorConstant_nonneg
    axisConstant_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    extendedErrorTerm_eq_published
    (ExactPositiveOrdinateHeightCountWindow.positiveFiniteWindowCard_le_heightCount
      exactHeightWindow)
    (PositiveOrdinateHeightCountRealization.negativeFiniteWindowCard_le_heightCount_of_mirror
      (ExactPositiveOrdinateHeightCountWindow.toRealization exactHeightWindow)
      (ConjugateOrdinateZetaZeroMirror.toNegativeOrdinateMirrorToPositiveWindow
        conjugationMirror exactHeightWindow))
    axisWindowCard_le
    tail_mainTerm_le
    tail_extendedErrorTerm_le
    tail_axisOrTrivialBound_le

/--
Build the same cutoff-2 fixed-error source input from the theorem-shaped
analytic statement that zeta zeroes are stable under conjugation. Lean turns
that statement into the global ordinate mirror automatically.
-/
noncomputable def ofCutoffTwoWithExactHeightWindowAndZetaZeroConjugationSymmetry
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (heightCount extendedErrorTerm : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (axisOrTrivialBound : Nat -> Real)
    (mainConstant errorConstant axisConstant growth : Real)
    (mainConstant_nonneg : 0 <= mainConstant)
    (errorConstant_nonneg : 0 <= errorConstant)
    (axisConstant_nonneg : 0 <= axisConstant)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            publishedErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            extendedErrorTerm T)
    (extendedErrorTerm_eq_published :
      forall T : Real,
        validFrom <= T ->
          extendedErrorTerm T = publishedErrorTerm T)
    (axisWindowCard_le :
      forall n : Nat,
        ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
          axisOrTrivialBound n)
    (tail_mainTerm_le :
      forall n : Nat,
        riemannVonMangoldtMainTerm ((n + 2 : Nat) : Real) <=
          mainConstant * |(n : Real) + 1| ^ growth)
    (tail_extendedErrorTerm_le :
      forall n : Nat,
        extendedErrorTerm ((n + 2 : Nat) : Real) <=
          errorConstant * |(n : Real) + 1| ^ growth)
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ growth) :
    FixedErrorExplicitRiemannVonMangoldtSourceInput
      validFrom publishedErrorTerm :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwoWithExactHeightWindowAndConjugation
    heightCount
    extendedErrorTerm
    exactHeightWindow
    (conjugateOrdinateZetaZeroMirror_of_zetaZeroConjugationSymmetry
      zetaZeroConjugationSymmetry)
    axisOrTrivialBound
    mainConstant
    errorConstant
    axisConstant
    growth
    mainConstant_nonneg
    errorConstant_nonneg
    axisConstant_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    extendedErrorTerm_eq_published
    axisWindowCard_le
    tail_mainTerm_le
    tail_extendedErrorTerm_le
    tail_axisOrTrivialBound_le

end FixedErrorExplicitRiemannVonMangoldtSourceInput

/--
Bellotti-Wong source input with the project's named error term and threshold
`T >= e`.
-/
abbrev BellottiWongExplicitRiemannVonMangoldtInput :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Bellotti-Wong error term extended below the published threshold by one finite
cleanup constant. For the cutoff-2 route, the only integer tail point below
`e` is `T = 2`.
-/
def bellottiWongCutoffTwoExtendedErrorTerm
    (belowErrorConstant : Real) (T : Real) : Real :=
  if T < bellottiWongValidFrom then belowErrorConstant
  else bellottiWongErrorTerm T

/-- Above the Bellotti-Wong threshold, the cutoff-2 extension is the published error term. -/
theorem bellottiWongCutoffTwoExtendedErrorTerm_eq_published
    (belowErrorConstant : Real) {T : Real}
    (hT : bellottiWongValidFrom <= T) :
    bellottiWongCutoffTwoExtendedErrorTerm belowErrorConstant T =
      bellottiWongErrorTerm T := by
  dsimp [bellottiWongCutoffTwoExtendedErrorTerm]
  simp [not_lt_of_ge hT]

/--
If the one below-threshold Bellotti-Wong cleanup constant is at most `100`, the
extended error term satisfies the same cutoff-2 quadratic tail as the published
logarithmic error term.
-/
theorem bellottiWongCutoffTwoExtendedErrorTerm_cutoffTwo_le_quadratic
    {belowErrorConstant : Real}
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (n : Nat) :
    bellottiWongCutoffTwoExtendedErrorTerm belowErrorConstant
        ((n + 2 : Nat) : Real) <=
      100 * |(n : Real) + 1| ^ (2 : Real) := by
  by_cases hn : n = 0
  · subst n
    dsimp [bellottiWongCutoffTwoExtendedErrorTerm, bellottiWongValidFrom]
    rw [if_pos Real.exp_one_gt_two]
    simpa using belowErrorConstant_le
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_ge_one : 1 <= n := Nat.succ_le_of_lt hnpos
    have hthree_le_nat : 3 <= n + 2 := by
      simpa using Nat.add_le_add_right hn_ge_one 2
    have hvalid : bellottiWongValidFrom <= ((n + 2 : Nat) : Real) := by
      dsimp [bellottiWongValidFrom]
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hthree_le_nat)
    rw [bellottiWongCutoffTwoExtendedErrorTerm_eq_published
      belowErrorConstant hvalid]
    exact bellottiWongErrorTerm_cutoffTwo_le_quadratic n

/--
If the Bellotti-Wong height count vanishes below the published threshold, then
the below-domain cleanup reduces to a bound for the Riemann-von-Mangoldt main
term on that small interval.
-/
theorem bellottiWongBelowDomain_abs_error_le_of_heightCount_eq_zero
    {heightCount : Real -> Real} {belowErrorConstant : Real}
    (heightCount_eq_zero_below :
      forall T : Real,
        T < bellottiWongValidFrom ->
          heightCount T = 0)
    (mainTerm_abs_below_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |riemannVonMangoldtMainTerm T| <= belowErrorConstant) :
    forall T : Real,
      T < bellottiWongValidFrom ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          belowErrorConstant := by
  intro T hT
  rw [heightCount_eq_zero_below T hT]
  simpa [abs_neg] using mainTerm_abs_below_le T hT

/--
On the nonnegative interval below `2*pi*e`, the Riemann-von-Mangoldt main term
is tiny compared with the generous project cleanup constant `100`.
-/
theorem riemannVonMangoldtMainTerm_abs_nonneg_le_twoPiExp_le_hundred
    {T : Real}
    (hT_nonneg : 0 <= T)
    (hT_le : T <= 2 * Real.pi * Real.exp 1) :
    |riemannVonMangoldtMainTerm T| <= 100 := by
  by_cases hT_zero : T = 0
  · subst T
    dsimp [riemannVonMangoldtMainTerm]
    norm_num
  · let x : Real := T / (2 * Real.pi * Real.exp 1)
    have hT_pos : 0 < T :=
      lt_of_le_of_ne hT_nonneg (Ne.symm hT_zero)
    have hden_pos : 0 < 2 * Real.pi * Real.exp 1 := by positivity
    have htwoPi_pos : 0 < 2 * Real.pi := by positivity
    have htwoPi_ne : 2 * Real.pi ≠ 0 := by positivity
    have hden_ne : 2 * Real.pi * Real.exp 1 ≠ 0 := by positivity
    have hexp_ne : Real.exp 1 ≠ 0 := by positivity
    have hx_pos : 0 < x := by
      dsimp [x]
      positivity
    have hx_le_one : x <= 1 := by
      dsimp [x]
      rw [div_le_iff₀ hden_pos]
      simpa using hT_le
    have hsmall : |Real.log x * x| < 1 :=
      Real.abs_log_mul_self_lt x hx_pos hx_le_one
    have hcoef_eq : T / (2 * Real.pi) = Real.exp 1 * x := by
      dsimp [x]
      field_simp [htwoPi_ne, hden_ne, hexp_ne]
    have hmain_abs_eq :
        |riemannVonMangoldtMainTerm T| =
          Real.exp 1 * |Real.log x * x| := by
      dsimp [riemannVonMangoldtMainTerm]
      change |T / (2 * Real.pi) * Real.log x| =
        Real.exp 1 * |Real.log x * x|
      rw [hcoef_eq]
      simp only [abs_mul, abs_of_pos (Real.exp_pos 1), abs_of_pos hx_pos]
      ring
    have hmain_lt_exp : |riemannVonMangoldtMainTerm T| < Real.exp 1 := by
      rw [hmain_abs_eq]
      simpa using mul_lt_mul_of_pos_left hsmall (Real.exp_pos 1)
    exact (le_of_lt hmain_lt_exp).trans (by nlinarith [Real.exp_one_lt_three])

/--
Bellotti-Wong's threshold `e` lies inside the elementary small-main-term
interval `T <= 2*pi*e`.
-/
theorem bellottiWongValidFrom_le_twoPiExp :
    bellottiWongValidFrom <= 2 * Real.pi * Real.exp 1 := by
  dsimp [bellottiWongValidFrom]
  have htwoPi_ge_one : 1 <= 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  simpa using mul_le_mul_of_nonneg_right htwoPi_ge_one
    (le_of_lt (Real.exp_pos 1))

/--
On the actual Bellotti-Wong small nonnegative interval `0 <= T < e`, the
Riemann-von-Mangoldt main term is tiny compared with the generous project
cleanup constant `100`.
-/
theorem riemannVonMangoldtMainTerm_abs_nonneg_lt_bellottiWongValidFrom_le_hundred
    {T : Real} (hT_nonneg : 0 <= T) (hT_lt : T < bellottiWongValidFrom) :
    |riemannVonMangoldtMainTerm T| <= 100 := by
  exact riemannVonMangoldtMainTerm_abs_nonneg_le_twoPiExp_le_hundred
    hT_nonneg ((le_of_lt hT_lt).trans bellottiWongValidFrom_le_twoPiExp)

/--
Bellotti-Wong error term extended below the published threshold in a way that
is realistic on the whole real line: negative `T` is covered by the absolute
main term, while `0 <= T < e` uses one finite cleanup constant.
-/
def bellottiWongCutoffTwoSignedExtendedErrorTerm
    (belowErrorConstant : Real) (T : Real) : Real :=
  if T < 0 then |riemannVonMangoldtMainTerm T|
  else if T < bellottiWongValidFrom then belowErrorConstant
  else bellottiWongErrorTerm T

/-- Above the Bellotti-Wong threshold, the signed extension is the published error term. -/
theorem bellottiWongCutoffTwoSignedExtendedErrorTerm_eq_published
    (belowErrorConstant : Real) {T : Real}
    (hT : bellottiWongValidFrom <= T) :
    bellottiWongCutoffTwoSignedExtendedErrorTerm belowErrorConstant T =
      bellottiWongErrorTerm T := by
  dsimp [bellottiWongCutoffTwoSignedExtendedErrorTerm]
  have hT_nonneg : 0 <= T :=
    (le_of_lt (Real.exp_pos 1)).trans hT
  simp [not_lt_of_ge hT_nonneg, not_lt_of_ge hT]

/--
The signed Bellotti-Wong extension has the same cutoff-2 quadratic tail as the
published error term once the small nonnegative cleanup constant is at most
`100`.
-/
theorem bellottiWongCutoffTwoSignedExtendedErrorTerm_cutoffTwo_le_quadratic
    {belowErrorConstant : Real}
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (n : Nat) :
    bellottiWongCutoffTwoSignedExtendedErrorTerm belowErrorConstant
        ((n + 2 : Nat) : Real) <=
      100 * |(n : Real) + 1| ^ (2 : Real) := by
  by_cases hn : n = 0
  · subst n
    dsimp [bellottiWongCutoffTwoSignedExtendedErrorTerm,
      bellottiWongValidFrom]
    rw [if_neg (by norm_num), if_pos Real.exp_one_gt_two]
    simpa using belowErrorConstant_le
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_ge_one : 1 <= n := Nat.succ_le_of_lt hnpos
    have hthree_le_nat : 3 <= n + 2 := by
      simpa using Nat.add_le_add_right hn_ge_one 2
    have hvalid : bellottiWongValidFrom <= ((n + 2 : Nat) : Real) := by
      dsimp [bellottiWongValidFrom]
      exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hthree_le_nat)
    rw [bellottiWongCutoffTwoSignedExtendedErrorTerm_eq_published
      belowErrorConstant hvalid]
    exact bellottiWongErrorTerm_cutoffTwo_le_quadratic n

/--
For the signed Bellotti-Wong extension, below-domain cleanup follows from
height-count vanishing below `e` plus the checked nonnegative small-main-term
bound.
-/
theorem bellottiWongSignedBelowDomain_abs_error_le_of_heightCount_eq_zero
    {heightCount : Real -> Real} :
    (forall T : Real,
      T < bellottiWongValidFrom ->
        heightCount T = 0) ->
    forall T : Real,
      T < bellottiWongValidFrom ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          bellottiWongCutoffTwoSignedExtendedErrorTerm 100 T := by
  intro heightCount_eq_zero_below T hT
  rw [heightCount_eq_zero_below T hT]
  by_cases hT_neg : T < 0
  · dsimp [bellottiWongCutoffTwoSignedExtendedErrorTerm]
    rw [if_pos hT_neg]
    simp [abs_neg]
  · have hT_nonneg : 0 <= T := le_of_not_gt hT_neg
    dsimp [bellottiWongCutoffTwoSignedExtendedErrorTerm]
    rw [if_neg hT_neg, if_pos hT]
    simpa [abs_neg] using
      riemannVonMangoldtMainTerm_abs_nonneg_lt_bellottiWongValidFrom_le_hundred
        hT_nonneg hT

/--
A finite-window realization of the Bellotti-Wong height count plus a no-positive
zero theorem below `e` supplies the exact vanishing field used by the signed
below-domain cleanup.
-/
theorem bellottiWong_heightCount_eq_zero_below_of_realization_noPositiveOrdinateZetaZerosAtOrBelow
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount)
    (hno :
      NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom) :
    forall T : Real,
      T < bellottiWongValidFrom ->
        heightCount T = 0 :=
  realization.heightCount_eq_zero_below_of_noPositiveOrdinateZetaZerosAtOrBelow
    hno

/--
Build a Bellotti-Wong-shaped cutoff-2 input using the checked elementary
quadratic tails for the standard main term and Bellotti-Wong error term.

The remaining fields are the actual published estimate, the below-threshold
cleanup, finite-window interpretation, and the axis/trivial-zero tail.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTails
    (heightCount : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (axisConstant : Real)
    (axisConstant_nonneg : 0 <= axisConstant)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
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
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ (2 : Real)) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwo
    (validFrom := bellottiWongValidFrom)
    (publishedErrorTerm := bellottiWongErrorTerm)
    heightCount
    bellottiWongErrorTerm
    axisOrTrivialBound
    100
    100
    axisConstant
    2
    (by norm_num)
    (by norm_num)
    axisConstant_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    (fun _ _ => rfl)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic
    bellottiWongErrorTerm_cutoffTwo_le_quadratic
    tail_axisOrTrivialBound_le

/--
Build a Bellotti-Wong cutoff-2 input when the remaining axis/trivial-zero
window has a linear index bound. Lean supplies the corresponding quadratic tail
automatically.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndLinearAxis
    (heightCount : Real -> Real)
    (axisSlope : Real)
    (axisSlope_nonneg : 0 <= axisSlope)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
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
          axisSlope * ((n : Real) + 1)) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTails
    heightCount
    (fun n : Nat => axisSlope * ((n : Real) + 1))
    (3 * axisSlope)
    (by nlinarith)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    (linearIndexBound_cutoffTwo_le_quadratic axisSlope_nonneg)

/--
Build a Bellotti-Wong cutoff-2 input using a finite below-threshold cleanup
constant. The extended error term equals the published Bellotti-Wong error term
above `e`, and the cutoff-2 error tail is checked automatically.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndQuadraticTails
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (axisOrTrivialBound : Nat -> Real)
    (axisConstant : Real)
    (axisConstant_nonneg : 0 <= axisConstant)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ (2 : Real)) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwo
    (validFrom := bellottiWongValidFrom)
    (publishedErrorTerm := bellottiWongErrorTerm)
    heightCount
    (bellottiWongCutoffTwoExtendedErrorTerm belowErrorConstant)
    axisOrTrivialBound
    100
    100
    axisConstant
    2
    (by norm_num)
    (by norm_num)
    axisConstant_nonneg
    published_abs_error_le
    (fun T hT => by
      dsimp [bellottiWongCutoffTwoExtendedErrorTerm]
      rw [if_pos hT]
      exact belowDomain_abs_error_le T hT)
    (fun T hT =>
      bellottiWongCutoffTwoExtendedErrorTerm_eq_published
        belowErrorConstant hT)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic
    (bellottiWongCutoffTwoExtendedErrorTerm_cutoffTwo_le_quadratic
      (belowErrorConstant := belowErrorConstant) belowErrorConstant_le)
    tail_axisOrTrivialBound_le

/--
Build a Bellotti-Wong cutoff-2 input from a finite below-threshold cleanup
constant and a linear axis/trivial-zero window bound. Lean supplies both the
extended-error tail and the axis/trivial quadratic tail.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndLinearAxis
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (axisSlope : Real)
    (axisSlope_nonneg : 0 <= axisSlope)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
          axisSlope * ((n : Real) + 1)) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndQuadraticTails
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    (fun n : Nat => axisSlope * ((n : Real) + 1))
    (3 * axisSlope)
    (by nlinarith)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    (linearIndexBound_cutoffTwo_le_quadratic axisSlope_nonneg)

/--
Build a Bellotti-Wong cutoff-2 input from a finite below-threshold cleanup
constant and split linear bounds for the known-trivial and residual real-axis
windows. This keeps the real nontrivial-axis residue visible.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndSplitLinearAxis
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (knownTrivialSlope residualRealAxisSlope : Real)
    (knownTrivialSlope_nonneg : 0 <= knownTrivialSlope)
    (residualRealAxisSlope_nonneg : 0 <= residualRealAxisSlope)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
    (knownTrivialCard_le :
      forall n : Nat,
        ((closedBallZeroKnownTrivialAxisFinset n).card : Real) <=
          knownTrivialSlope * ((n : Real) + 1))
    (residualRealAxisCard_le :
      forall n : Nat,
        ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
          residualRealAxisSlope * ((n : Real) + 1)) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndLinearAxis
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    (knownTrivialSlope + residualRealAxisSlope)
    (by nlinarith)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    (closedBallZeroAxis_card_le_splitLinearAxisBound
      knownTrivialCard_le residualRealAxisCard_le)

/--
Build a Bellotti-Wong cutoff-2 input from a finite below-threshold cleanup
constant and a linear bound for only the residual real-axis window. The
project-known trivial axis zeroes use the checked linear bound with slope `1`.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndResidualRealAxis
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (residualRealAxisSlope : Real)
    (residualRealAxisSlope_nonneg : 0 <= residualRealAxisSlope)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
    (residualRealAxisCard_le :
      forall n : Nat,
        ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
          residualRealAxisSlope * ((n : Real) + 1)) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndSplitLinearAxis
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    1
    residualRealAxisSlope
    (by norm_num)
    residualRealAxisSlope_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    closedBallZeroKnownTrivialAxis_card_le_linear
    residualRealAxisCard_le

/--
Build a Bellotti-Wong cutoff-2 input from a finite below-threshold cleanup
constant and a no-residual-real-axis theorem. The checked known-trivial axis
bound is then the whole axis contribution.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndNoResidualRealAxis
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (noResidualRealAxis : NoResidualRealAxisZetaZeros)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndResidualRealAxis
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    0
    (by norm_num)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    (closedBallZeroResidualRealAxis_card_le_zero_linear_of_noResidual
      noResidualRealAxis)

/--
Build a Bellotti-Wong cutoff-2 input from a finite below-threshold cleanup
constant and the source-shaped `ZMod 2` checked boundary-value theorem.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndZModTwoBoundaryValue
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (zmodTwoBoundaryValue :
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndNoResidualRealAxis
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    (noResidualRealAxisZetaZeros_of_zmodTwoBoundaryValue
      zmodTwoBoundaryValue)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Bellotti-Wong cutoff-2 input from a finite below-threshold cleanup
constant and the nonendpoint regularized Hurwitz-tail theorem.  The endpoint
residue is supplied by the checked endpoint lemma.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndRegularizedTailHurwitzNonendpoint
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (regularizedTailHurwitz :
      ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndZModTwoBoundaryValue
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitzNonendpoint
      regularizedTailHurwitz)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Bellotti-Wong cutoff-2 input from the classical real-axis zeta-zero
classification. This source-shaped theorem is translated to the project
no-residual-real-axis target internally.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            belowErrorConstant)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndNoResidualRealAxis
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    (noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
      realAxisZeroClassification)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Bellotti-Wong cutoff-2 input from source-shaped small-height data and
the classical real-axis zeta-zero classification.  The below-domain cleanup is
derived from vanishing of the height count below `e` plus a separate bound for
the Riemann-von-Mangoldt main term there.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithZeroBelowDomainAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (heightCount_eq_zero_below :
      forall T : Real,
        T < bellottiWongValidFrom ->
          heightCount T = 0)
    (mainTerm_abs_below_le :
      forall T : Real,
        T < bellottiWongValidFrom ->
          |riemannVonMangoldtMainTerm T| <= belowErrorConstant)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithFiniteBelowDomainAndRealAxisZeroClassification
    heightCount
    belowErrorConstant
    belowErrorConstant_le
    realAxisZeroClassification
    published_abs_error_le
    (bellottiWongBelowDomain_abs_error_le_of_heightCount_eq_zero
      heightCount_eq_zero_below mainTerm_abs_below_le)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Bellotti-Wong cutoff-2 input from zero height count below `e` and the
classical real-axis zeta-zero classification, using the signed all-real
extension.  The nonnegative below-`e` main-term bound is checked in this
module; negative `T` is covered by the extension itself.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (heightCount_eq_zero_below :
      forall T : Real,
        T < bellottiWongValidFrom ->
          heightCount T = 0)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwo
    (validFrom := bellottiWongValidFrom)
    (publishedErrorTerm := bellottiWongErrorTerm)
    heightCount
    (bellottiWongCutoffTwoSignedExtendedErrorTerm 100)
    (fun n : Nat => 1 * ((n : Real) + 1))
    100
    100
    3
    2
    (by norm_num)
    (by norm_num)
    (by norm_num)
    published_abs_error_le
    (bellottiWongSignedBelowDomain_abs_error_le_of_heightCount_eq_zero
      heightCount_eq_zero_below)
    (fun T hT =>
      bellottiWongCutoffTwoSignedExtendedErrorTerm_eq_published 100 hT)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    (closedBallZeroAxis_card_le_noResidualLinearAxisBound
      (noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
        realAxisZeroClassification))
    riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic
    (bellottiWongCutoffTwoSignedExtendedErrorTerm_cutoffTwo_le_quadratic
      (belowErrorConstant := 100) (by norm_num))
    (fun n => by
      simpa using
        (linearIndexBound_cutoffTwo_le_quadratic
          (axisSlope := 1) (by norm_num) n))

/--
Build a Bellotti-Wong cutoff-2 input from a finite-window realization of the
height count, a no-positive-zero theorem below `e`, and the classical real-axis
zeta-zero classification.  Lean derives the signed small-height cleanup field
from the realization plus the no-positive-zero theorem.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedRealizedZeroBelowDomainAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (heightCountRealization :
      PositiveOrdinateHeightCountRealization heightCount)
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassification
    heightCount
    realAxisZeroClassification
    published_abs_error_le
    (bellottiWong_heightCount_eq_zero_below_of_realization_noPositiveOrdinateZetaZerosAtOrBelow
      heightCountRealization noPositiveZerosBelowValidFrom)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Bellotti-Wong cutoff-2 input from exact positive-ordinate window data:
the realizing height-count window both covers all positive-ordinate zeroes up
to `T` and, with the no-positive-zero theorem below `e`, supplies the
small-height cleanup.  The negative-ordinate field remains explicit because it
requires symmetry or a separate lower-half-plane count.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactPositiveWindowDataAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (heightCountRealization :
      PositiveOrdinateHeightCountRealization heightCount)
    (heightCountCoversPositiveZeros :
      heightCountRealization.CoversAllPositiveOrdinateZeros)
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T)
    (negativeFiniteWindowCard_le_heightCount :
      forall s : Finset ZetaZeroSubtype,
        forall T : Real,
          (forall rho : ZetaZeroSubtype,
            rho ∈ s ->
              Complex.im (rho : Complex) < 0 ∧
                -Complex.im (rho : Complex) <= T) ->
            ((s.card : Nat) : Real) <= heightCount T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedRealizedZeroBelowDomainAndRealAxisZeroClassification
    heightCount
    heightCountRealization
    noPositiveZerosBelowValidFrom
    realAxisZeroClassification
    published_abs_error_le
    (PositiveOrdinateHeightCountRealization.positiveFiniteWindowCard_le_heightCount_of_covers
      heightCountRealization heightCountCoversPositiveZeros)
    negativeFiniteWindowCard_le_heightCount

/--
Build a Bellotti-Wong cutoff-2 input from exact positive-window data and an
explicit negative-to-positive mirror. This derives both positive and negative
finite-window interpretation fields from the realized height count, leaving the
published estimate, small-height no-positive-zero theorem, and real-axis
classification as the remaining source-shaped analytic inputs.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactWindowDataAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (heightCountRealization :
      PositiveOrdinateHeightCountRealization heightCount)
    (heightCountCoversPositiveZeros :
      heightCountRealization.CoversAllPositiveOrdinateZeros)
    (negativeMirror :
      PositiveOrdinateHeightCountRealization.NegativeOrdinateMirrorToPositiveWindow
        heightCountRealization)
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactPositiveWindowDataAndRealAxisZeroClassification
    heightCount
    heightCountRealization
    heightCountCoversPositiveZeros
    noPositiveZerosBelowValidFrom
    realAxisZeroClassification
    published_abs_error_le
    (PositiveOrdinateHeightCountRealization.negativeFiniteWindowCard_le_heightCount_of_mirror
      heightCountRealization negativeMirror)

/--
Build a Bellotti-Wong cutoff-2 input from an exact positive-ordinate height
window. Exact membership derives the height-count realization and positive
coverage automatically; an explicit negative-to-positive mirror supplies the
lower-half-plane finite-window interpretation.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (negativeMirror :
      PositiveOrdinateHeightCountRealization.NegativeOrdinateMirrorToPositiveWindow
        (ExactPositiveOrdinateHeightCountWindow.toRealization exactHeightWindow))
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactWindowDataAndRealAxisZeroClassification
    heightCount
    (ExactPositiveOrdinateHeightCountWindow.toRealization exactHeightWindow)
    (ExactPositiveOrdinateHeightCountWindow.coversAllPositiveOrdinateZeros
      exactHeightWindow)
    negativeMirror
    noPositiveZerosBelowValidFrom
    realAxisZeroClassification
    published_abs_error_le

/--
Build a Bellotti-Wong cutoff-2 input from an exact positive-ordinate height
window and a global conjugation-style zero mirror. The global mirror is
specialized to the realized positive window internally.
-/
noncomputable def BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowConjugationAndRealAxisZeroClassification
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowAndRealAxisZeroClassification
    heightCount
    exactHeightWindow
    (ConjugateOrdinateZetaZeroMirror.toNegativeOrdinateMirrorToPositiveWindow
      conjugationMirror exactHeightWindow)
    noPositiveZerosBelowValidFrom
    realAxisZeroClassification
    published_abs_error_le

/--
Preferred Bellotti-Wong exact-source data package.

These are the remaining source-shaped analytic inputs after the checked
cutoff-2 tails, signed below-domain cleanup, exact positive-window realization,
global conjugation mirror, and real-axis decomposition have all been routed
through Lean constructors.
-/
structure BellottiWongExactHeightWindowConjugationSourceData where
  heightCount : Real -> Real
  exactHeightWindow :
    ExactPositiveOrdinateHeightCountWindow heightCount
  conjugationMirror : ConjugateOrdinateZetaZeroMirror
  noPositiveZerosBelowValidFrom :
    NoPositiveOrdinateZetaZerosAtOrBelow bellottiWongValidFrom
  realAxisZeroClassification : RealAxisZetaZeroClassification
  published_abs_error_le :
    forall T : Real,
      bellottiWongValidFrom <= T ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          bellottiWongErrorTerm T

namespace BellottiWongExactHeightWindowConjugationSourceData

/--
Build the preferred Bellotti-Wong exact-source package from a lower bound on
positive-ordinate zeta-zero heights.
-/
def ofPositiveOrdinateZetaZeroLowerBound
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (positiveOrdinateLowerBound :
      PositiveOrdinateZetaZeroLowerBound bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData where
  heightCount := heightCount
  exactHeightWindow := exactHeightWindow
  conjugationMirror := conjugationMirror
  noPositiveZerosBelowValidFrom :=
    noPositiveOrdinateZetaZerosAtOrBelow_of_positiveOrdinateZetaZeroLowerBound
      positiveOrdinateLowerBound
  realAxisZeroClassification := realAxisZeroClassification
  published_abs_error_le := published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the direct
zeta-zero conjugation symmetry theorem. The global mirror field is constructed
inside Lean.
-/
def ofPositiveOrdinateZetaZeroLowerBoundAndZetaZeroConjugationSymmetry
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (positiveOrdinateLowerBound :
      PositiveOrdinateZetaZeroLowerBound bellottiWongValidFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofPositiveOrdinateZetaZeroLowerBound
    heightCount
    exactHeightWindow
    (conjugateOrdinateZetaZeroMirror_of_zetaZeroConjugationSymmetry
      zetaZeroConjugationSymmetry)
    positiveOrdinateLowerBound
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from source-shaped
small-height zero-free data and zeta-zero conjugation symmetry.
-/
def ofZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofPositiveOrdinateZetaZeroLowerBoundAndZetaZeroConjugationSymmetry
    heightCount
    exactHeightWindow
    zetaZeroConjugationSymmetry
    (positiveOrdinateZetaZeroLowerBound_of_zetaZeroFreePositiveOrdinateBand
      zetaZeroFreePositiveOrdinateBand)
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from source-shaped
exact height-window data, source-shaped small-height zero-free data, and
zeta-zero conjugation symmetry.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    heightCount
    (SourceExactPositiveOrdinateHeightCountWindow.toExactPositiveOrdinateHeightCountWindow
      sourceExactHeightWindow)
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from source-shaped
exact height-window data, source-shaped small-height zero-free data, and the
standard function-level zeta conjugation formula.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndRiemannZetaConjugationFormula
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    (zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormula
      riemannZetaConjugationFormula)
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data and the sharpened left-real-axis
classification target.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndLeftRealAxisClassification
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (leftRealAxisZeroClassification : LeftRealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    (realAxisZetaZeroClassification_of_leftRealAxisZetaZeroClassification
      leftRealAxisZeroClassification)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data and the remaining open-unit-interval
real-axis zero-free target.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalRealAxisZeroFree
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (openUnitIntervalRealAxisZeroFree :
      OpenUnitIntervalRealAxisZetaZeroFree)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndLeftRealAxisClassification
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    (leftRealAxisZetaZeroClassification_of_openUnitIntervalRealAxisZetaZeroFree
      openUnitIntervalRealAxisZeroFree)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data and the real-variable nonzero theorem for
zeta on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaNonzero
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (openUnitIntervalZetaNonzero :
      OpenUnitIntervalRiemannZetaNonzero)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalRealAxisZeroFree
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    (openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaNonzero
      openUnitIntervalZetaNonzero)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data and the classical sign-shaped theorem
`Re zeta x < 0` for `0 < x < 1`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaReNegative
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (openUnitIntervalZetaReNegative :
      OpenUnitIntervalRiemannZetaReNegative)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaNonzero
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    (openUnitIntervalRiemannZetaNonzero_of_reNegative
      openUnitIntervalZetaReNegative)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data, the standard function-level zeta conjugation
formula, and the real-variable nonzero theorem for zeta on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaNonzero
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (openUnitIntervalZetaNonzero :
      OpenUnitIntervalRiemannZetaNonzero)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaNonzero
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    (zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormula
      riemannZetaConjugationFormula)
    openUnitIntervalZetaNonzero
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data, the standard function-level zeta conjugation
formula, and the classical sign-shaped theorem `Re zeta x < 0` for
`0 < x < 1`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaReNegative
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (openUnitIntervalZetaReNegative :
      OpenUnitIntervalRiemannZetaReNegative)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaNonzero
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    (openUnitIntervalRiemannZetaNonzero_of_reNegative
      openUnitIntervalZetaReNegative)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data, the standard function-level zeta conjugation
formula, and the eta analytic-continuation formula on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaFormula
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (etaFormula : OpenUnitIntervalRiemannZetaEtaFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaReNegative
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    (openUnitIntervalRiemannZetaReNegative_of_etaFormula etaFormula)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data, the standard function-level zeta conjugation
formula, and the canonical-value eta formula on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaValueFormula
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (etaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaFormula
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    (openUnitIntervalRiemannZetaEtaFormula_of_valueFormula
      etaValueFormula)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data, the standard function-level zeta conjugation
formula, and the source-shaped `ZMod 2` checked boundary-value theorem.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndZModTwoBoundaryValue
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (zmodTwoBoundaryValue :
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaValueFormula
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_zmodTwoBoundaryValue
      zmodTwoBoundaryValue)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the fully
source-shaped zero-counting data, the standard function-level zeta conjugation
formula, and the isolated regularized Hurwitz-tail theorem.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndRegularizedTailHurwitz
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (regularizedTailHurwitz :
      ZModAdditiveCharacterRegularizedTailHurwitzFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndZModTwoBoundaryValue
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      regularizedTailHurwitz)
    published_abs_error_le

/--
Build the preferred Bellotti-Wong exact-source package from the nonendpoint
regularized Hurwitz-tail theorem.  The endpoint residue is automatic.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndRegularizedTailHurwitzNonendpoint
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (regularizedTailHurwitz :
      ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula)
    (published_abs_error_le :
      forall T : Real,
        bellottiWongValidFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongExactHeightWindowConjugationSourceData :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndRegularizedTailHurwitz
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    (zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint
      regularizedTailHurwitz)
    published_abs_error_le

/-- Convert the preferred Bellotti-Wong exact-source package to the checked source input. -/
noncomputable def toInput
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  BellottiWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowConjugationAndRealAxisZeroClassification
    data.heightCount
    data.exactHeightWindow
    data.conjugationMirror
    data.noPositiveZerosBelowValidFrom
    data.realAxisZeroClassification
    data.published_abs_error_le

/-- Convert the preferred Bellotti-Wong exact-source package to the generic published source. -/
noncomputable def toPublishedExplicitRiemannVonMangoldtSource
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    PublishedExplicitRiemannVonMangoldtSource :=
  data.toInput.toPublishedExplicitRiemannVonMangoldtSource

/--
Convert the preferred Bellotti-Wong exact-source package to the named
closed-ball Riemann-von-Mangoldt counting target.
-/
noncomputable def toRiemannVonMangoldtCountingTarget
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  data.toInput.toRiemannVonMangoldtCountingTarget

/-- The preferred Bellotti-Wong exact-source package uses cutoff `2`. -/
theorem toInput_cutoff
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    data.toInput.cutoff = 2 := by
  rfl

/-- The preferred Bellotti-Wong exact-source package has quadratic growth. -/
theorem toInput_growth
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    data.toInput.growth = 2 := by
  rfl

/-- The induced Bellotti-Wong shell-counting package uses cutoff `2`. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    data.toInput.toPolynomialZeroCountingEstimate.cutoff = 2 := by
  rw [FixedErrorExplicitRiemannVonMangoldtSourceInput.toPolynomialZeroCountingEstimate_cutoff,
    toInput_cutoff]

/-- The induced Bellotti-Wong shell-counting package has quadratic growth. -/
theorem toPolynomialZeroCountingEstimate_growth
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    data.toInput.toPolynomialZeroCountingEstimate.growth = 2 := by
  rw [FixedErrorExplicitRiemannVonMangoldtSourceInput.toPolynomialZeroCountingEstimate_growth,
    toInput_growth]

/--
For the preferred Bellotti-Wong exact-source package, the p-series decay margin
is exactly the elementary inequality `3 < decayExponent`.
-/
theorem growth_add_one_lt_decay_of_three_lt
    (data : BellottiWongExactHeightWindowConjugationSourceData)
    {decayExponent : Real}
    (hdecay : (3 : Real) < decayExponent) :
    data.toInput.toPolynomialZeroCountingEstimate.growth + 1 <
      decayExponent := by
  rw [toPolynomialZeroCountingEstimate_growth data]
  norm_num
  exact hdecay

/-- The named Bellotti-Wong counting target uses cutoff `2`. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    data.toRiemannVonMangoldtCountingTarget.cutoff = 2 := by
  rw [toRiemannVonMangoldtCountingTarget,
    FixedErrorExplicitRiemannVonMangoldtSourceInput.toRiemannVonMangoldtCountingTarget_cutoff,
    toInput_cutoff]

/-- The named Bellotti-Wong counting target has quadratic growth. -/
theorem toRiemannVonMangoldtCountingTarget_growth
    (data : BellottiWongExactHeightWindowConjugationSourceData) :
    data.toRiemannVonMangoldtCountingTarget.growth = 2 := by
  rw [toRiemannVonMangoldtCountingTarget,
    FixedErrorExplicitRiemannVonMangoldtSourceInput.toRiemannVonMangoldtCountingTarget_growth,
    toInput_growth]

end BellottiWongExactHeightWindowConjugationSourceData

/--
Source-facing Bellotti-Wong `N(T)` theorem target with exact project constants.

The analytic field is the published estimate on its stated domain
`T >= bellottiWongValidFrom`; the exact source height window records that the
`heightCount` is the positive-ordinate zeta-zero count, not an abstract
majorant.  The lemmas below prove the finite-window and closed-ball
normalization needed by the project counting target.
-/
structure BellottiWongPublishedExactNTTheorem where
  heightCount : Real -> Real
  sourceExactHeightWindow :
    SourceExactPositiveOrdinateHeightCountWindow heightCount
  published_abs_error_le :
    forall T : Real,
      bellottiWongValidFrom <= T ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          bellottiWongErrorTerm T

namespace BellottiWongPublishedExactNTTheorem

/-- The source theorem's complex height window as a project zero-subtype window. -/
noncomputable def exactHeightWindow
    (source : BellottiWongPublishedExactNTTheorem) :
    ExactPositiveOrdinateHeightCountWindow source.heightCount :=
  source.sourceExactHeightWindow.toExactPositiveOrdinateHeightCountWindow

/--
The exact source height window gives the positive finite-window interpretation
required by the Riemann-von-Mangoldt counting adapter.
-/
theorem positiveFiniteWindowCard_le_heightCount
    (source : BellottiWongPublishedExactNTTheorem) :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= source.heightCount T :=
  SourceExactPositiveOrdinateHeightCountWindow.positiveFiniteWindowCard_le_heightCount
    source.sourceExactHeightWindow

/-- The exact Bellotti-Wong source count bounds the positive closed-ball window. -/
theorem positiveClosedBall_card_le_heightCount
    (source : BellottiWongPublishedExactNTTheorem)
    (n : Nat) :
    ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
      source.heightCount (n : Real) :=
  source.positiveFiniteWindowCard_le_heightCount
    (closedBallZeroPositiveOrdinateFinset n)
    (n : Real)
    (fun _rho hrho => closedBallZeroPositiveOrdinate_im_bounds n hrho)

/--
The checked conjugation mirror turns the exact positive Bellotti-Wong window
into the negative finite-window interpretation required for closed balls.
-/
theorem negativeFiniteWindowCard_le_heightCount
    (source : BellottiWongPublishedExactNTTheorem) :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            Complex.im (rho : Complex) < 0 ∧
              -Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= source.heightCount T :=
  PositiveOrdinateHeightCountRealization.negativeFiniteWindowCard_le_heightCount_of_mirror
    (ExactPositiveOrdinateHeightCountWindow.toRealization
      source.exactHeightWindow)
    (ConjugateOrdinateZetaZeroMirror.toNegativeOrdinateMirrorToPositiveWindow
      conjugateOrdinateZetaZeroMirror source.exactHeightWindow)

/-- The exact Bellotti-Wong source count bounds the negative closed-ball window. -/
theorem negativeClosedBall_card_le_heightCount
    (source : BellottiWongPublishedExactNTTheorem)
    (n : Nat) :
    ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
      source.heightCount (n : Real) :=
  source.negativeFiniteWindowCard_le_heightCount
    (closedBallZeroNegativeOrdinateFinset n)
    (n : Real)
    (fun _rho hrho => closedBallZeroNegativeOrdinate_im_bounds n hrho)

/--
A source-shaped zero-free band below Bellotti-Wong's threshold supplies the
below-domain vanishing of the exact height count.
-/
theorem heightCount_eq_zero_below_of_zetaZeroFreePositiveOrdinateBand
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom) :
    forall T : Real,
      T < bellottiWongValidFrom ->
        source.heightCount T = 0 :=
  SourceExactPositiveOrdinateHeightCountWindow.heightCount_eq_zero_below_of_zetaZeroFreePositiveOrdinateBand
    source.sourceExactHeightWindow hfree

/--
The real-axis classification removes the residual real-axis contribution, so
the project-known trivial axis zeros give a linear axis/trivial bound.
-/
theorem axisWindowCard_le_of_realAxisZeroClassification
    (_source : BellottiWongPublishedExactNTTheorem)
    (hrealAxis : RealAxisZetaZeroClassification) :
    forall n : Nat,
      ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
        1 * ((n : Real) + 1) := by
  intro n
  exact
    closedBallZeroAxis_card_le_noResidualLinearAxisBound
      (noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
        hrealAxis)
      n

/--
With the real-axis classification, the residual real-axis subwindow contributes
zero to the Bellotti-Wong axis/trivial count.
-/
theorem residualRealAxisWindowCard_le_zero_linear_of_realAxisZeroClassification
    (_source : BellottiWongPublishedExactNTTheorem)
    (hrealAxis : RealAxisZetaZeroClassification) :
    forall n : Nat,
      ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
        0 * ((n : Real) + 1) := by
  intro n
  exact
    closedBallZeroResidualRealAxis_card_le_zero_linear_of_noResidual
      (noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
        hrealAxis)
      n

/--
The chosen Bellotti-Wong axis/trivial linear bound has the cutoff-2 quadratic
tail used by the downstream Riemann-von-Mangoldt counting input.
-/
theorem axisWindowLinearBound_cutoffTwo_le_quadratic
    (_source : BellottiWongPublishedExactNTTheorem) :
    forall n : Nat,
      1 * (((n + 2 : Nat) : Real) + 1) <=
        3 * |(n : Real) + 1| ^ (2 : Real) := by
  intro n
  simpa using
    (linearIndexBound_cutoffTwo_le_quadratic
      (axisSlope := 1) (by norm_num) n)

/--
Add the remaining source-shaped zero-free and real-axis inputs to the exact
Bellotti-Wong `N(T)` theorem target, yielding the checked project source data.

The conjugation mirror is not an extra hypothesis here: it is the checked zeta
conjugation mirror from `RiemannVonMangoldtClassicalCounting`.
-/
noncomputable def toExactHeightWindowConjugationSourceData
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (hrealAxis : RealAxisZetaZeroClassification) :
    BellottiWongExactHeightWindowConjugationSourceData where
  heightCount := source.heightCount
  exactHeightWindow := source.exactHeightWindow
  conjugationMirror := conjugateOrdinateZetaZeroMirror
  noPositiveZerosBelowValidFrom :=
    noPositiveOrdinateZetaZerosAtOrBelow_of_zetaZeroFreePositiveOrdinateBand
      hfree
  realAxisZeroClassification := hrealAxis
  published_abs_error_le := source.published_abs_error_le

/-- Convert the exact Bellotti-Wong theorem target to the checked source input. -/
noncomputable def toInput
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (hrealAxis : RealAxisZetaZeroClassification) :
    BellottiWongExplicitRiemannVonMangoldtInput :=
  (source.toExactHeightWindowConjugationSourceData hfree hrealAxis).toInput

/-- Convert the exact Bellotti-Wong theorem target to the named closed-ball count. -/
noncomputable def toRiemannVonMangoldtCountingTarget
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (hrealAxis : RealAxisZetaZeroClassification) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  (source.toExactHeightWindowConjugationSourceData hfree hrealAxis)
    |>.toRiemannVonMangoldtCountingTarget

/-- The exact Bellotti-Wong theorem target induces a cutoff-2 project count. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (hrealAxis : RealAxisZetaZeroClassification) :
    (source.toRiemannVonMangoldtCountingTarget hfree hrealAxis).cutoff = 2 := by
  rw [toRiemannVonMangoldtCountingTarget,
    BellottiWongExactHeightWindowConjugationSourceData.toRiemannVonMangoldtCountingTarget_cutoff]

/-- The exact Bellotti-Wong theorem target induces a quadratic-growth project count. -/
theorem toRiemannVonMangoldtCountingTarget_growth
    (source : BellottiWongPublishedExactNTTheorem)
    (hfree : ZetaZeroFreePositiveOrdinateBand bellottiWongValidFrom)
    (hrealAxis : RealAxisZetaZeroClassification) :
    (source.toRiemannVonMangoldtCountingTarget hfree hrealAxis).growth = 2 := by
  rw [toRiemannVonMangoldtCountingTarget,
    BellottiWongExactHeightWindowConjugationSourceData.toRiemannVonMangoldtCountingTarget_growth]

end BellottiWongPublishedExactNTTheorem

/--
Hasanalizade-Shen-Wong source input with the project's named error term.

The validity threshold remains a parameter so a future formalization can match
the exact published domain without changing the receiving API.
-/
abbrev HasanalizadeShenWongExplicitRiemannVonMangoldtInput
    (validFrom : Real) :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput
    validFrom hasanalizadeShenWongErrorTerm

/--
Build a Hasanalizade-Shen-Wong-shaped cutoff-2 input using the checked
elementary quadratic tails for the standard main term and HSW error term.

The remaining fields are the actual published estimate at the chosen threshold,
the below-threshold cleanup, finite-window interpretation, and the
axis/trivial-zero tail.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTails
    (validFrom : Real)
    (heightCount : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (axisConstant : Real)
    (axisConstant_nonneg : 0 <= axisConstant)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ (2 : Real)) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwo
    (validFrom := validFrom)
    (publishedErrorTerm := hasanalizadeShenWongErrorTerm)
    heightCount
    hasanalizadeShenWongErrorTerm
    axisOrTrivialBound
    100
    100
    axisConstant
    2
    (by norm_num)
    (by norm_num)
    axisConstant_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    (fun _ _ => rfl)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic
    hasanalizadeShenWongErrorTerm_cutoffTwo_le_quadratic
    tail_axisOrTrivialBound_le

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input using a signed finite
below-domain extension. This is the HSW analogue of the signed Bellotti-Wong
route: the published HSW error term is used above the threshold, negative
below-threshold `T` is covered by the absolute main term, and nonnegative
below-threshold `T` is covered by one finite cleanup constant.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedFiniteBelowDomainAndQuadraticTails
    (validFrom : Real)
    (heightCount : Real -> Real)
    (axisOrTrivialBound : Nat -> Real)
    (axisConstant : Real)
    (axisConstant_nonneg : 0 <= axisConstant)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            FixedErrorExplicitRiemannVonMangoldtSourceInput.cutoffTwoSignedExtendedErrorTerm
              validFrom hasanalizadeShenWongErrorTerm belowErrorConstant T)
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
    (tail_axisOrTrivialBound_le :
      forall n : Nat,
        axisOrTrivialBound (n + 2) <=
          axisConstant * |(n : Real) + 1| ^ (2 : Real)) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  FixedErrorExplicitRiemannVonMangoldtSourceInput.ofCutoffTwo
    (validFrom := validFrom)
    (publishedErrorTerm := hasanalizadeShenWongErrorTerm)
    heightCount
    (FixedErrorExplicitRiemannVonMangoldtSourceInput.cutoffTwoSignedExtendedErrorTerm
      validFrom hasanalizadeShenWongErrorTerm belowErrorConstant)
    axisOrTrivialBound
    100
    100
    axisConstant
    2
    (by norm_num)
    (by norm_num)
    axisConstant_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    (fun T hT =>
      FixedErrorExplicitRiemannVonMangoldtSourceInput.cutoffTwoSignedExtendedErrorTerm_eq_published
        (validFrom := validFrom)
        (publishedErrorTerm := hasanalizadeShenWongErrorTerm)
        belowErrorConstant hT)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic
    (FixedErrorExplicitRiemannVonMangoldtSourceInput.cutoffTwoSignedExtendedErrorTerm_cutoffTwo_le_quadratic
      (validFrom := validFrom)
      (publishedErrorTerm := hasanalizadeShenWongErrorTerm)
      (belowErrorConstant := belowErrorConstant)
      (errorConstant := 100)
      belowErrorConstant_le
      (by norm_num)
      hasanalizadeShenWongErrorTerm_cutoffTwo_le_quadratic)
    tail_axisOrTrivialBound_le

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input when the remaining
axis/trivial-zero window has a linear index bound. Lean supplies the
corresponding quadratic tail automatically.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndLinearAxis
    (validFrom : Real)
    (heightCount : Real -> Real)
    (axisSlope : Real)
    (axisSlope_nonneg : 0 <= axisSlope)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
          axisSlope * ((n : Real) + 1)) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTails
    validFrom
    heightCount
    (fun n : Nat => axisSlope * ((n : Real) + 1))
    (3 * axisSlope)
    (by nlinarith)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    axisWindowCard_le
    (linearIndexBound_cutoffTwo_le_quadratic axisSlope_nonneg)

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from split linear bounds for the
known-trivial and residual real-axis windows. This keeps the real
nontrivial-axis residue visible while Lean supplies the combined axis tail.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndSplitLinearAxis
    (validFrom : Real)
    (heightCount : Real -> Real)
    (knownTrivialSlope residualRealAxisSlope : Real)
    (knownTrivialSlope_nonneg : 0 <= knownTrivialSlope)
    (residualRealAxisSlope_nonneg : 0 <= residualRealAxisSlope)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
    (knownTrivialCard_le :
      forall n : Nat,
        ((closedBallZeroKnownTrivialAxisFinset n).card : Real) <=
          knownTrivialSlope * ((n : Real) + 1))
    (residualRealAxisCard_le :
      forall n : Nat,
        ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
          residualRealAxisSlope * ((n : Real) + 1)) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndLinearAxis
    validFrom
    heightCount
    (knownTrivialSlope + residualRealAxisSlope)
    (by nlinarith)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    (closedBallZeroAxis_card_le_splitLinearAxisBound
      knownTrivialCard_le residualRealAxisCard_le)

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from a linear bound for only the
residual real-axis window. The project-known trivial axis zeroes use the
checked linear bound with slope `1`.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndResidualRealAxis
    (validFrom : Real)
    (heightCount : Real -> Real)
    (residualRealAxisSlope : Real)
    (residualRealAxisSlope_nonneg : 0 <= residualRealAxisSlope)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
    (residualRealAxisCard_le :
      forall n : Nat,
        ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
          residualRealAxisSlope * ((n : Real) + 1)) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndSplitLinearAxis
    validFrom
    heightCount
    1
    residualRealAxisSlope
    (by norm_num)
    residualRealAxisSlope_nonneg
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    closedBallZeroKnownTrivialAxis_card_le_linear
    residualRealAxisCard_le

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from a no-residual-real-axis
theorem. The checked known-trivial axis bound is then the whole axis
contribution.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndNoResidualRealAxis
    (validFrom : Real)
    (heightCount : Real -> Real)
    (noResidualRealAxis : NoResidualRealAxisZetaZeros)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndResidualRealAxis
    validFrom
    heightCount
    0
    (by norm_num)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    (closedBallZeroResidualRealAxis_card_le_zero_linear_of_noResidual
      noResidualRealAxis)

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from the source-shaped `ZMod 2`
checked boundary-value theorem.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndZModTwoBoundaryValue
    (validFrom : Real)
    (heightCount : Real -> Real)
    (zmodTwoBoundaryValue :
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndNoResidualRealAxis
    validFrom
    heightCount
    (noResidualRealAxisZetaZeros_of_zmodTwoBoundaryValue
      zmodTwoBoundaryValue)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from the nonendpoint regularized
Hurwitz-tail theorem. The endpoint residue is supplied automatically.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndRegularizedTailHurwitzNonendpoint
    (validFrom : Real)
    (heightCount : Real -> Real)
    (regularizedTailHurwitz :
      ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndZModTwoBoundaryValue
    validFrom
    heightCount
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitzNonendpoint
      regularizedTailHurwitz)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from the classical real-axis
zeta-zero classification. This source-shaped theorem is translated to the
project no-residual-real-axis target internally.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndRealAxisZeroClassification
    (validFrom : Real)
    (heightCount : Real -> Real)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndNoResidualRealAxis
    validFrom
    heightCount
    (noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
      realAxisZeroClassification)
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from a signed finite
below-domain cleanup and the classical real-axis zeta-zero classification.
The checked known-trivial axis bound and the no-residual consequence of the
classification supply the axis contribution.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedFiniteBelowDomainAndRealAxisZeroClassification
    (validFrom : Real)
    (heightCount : Real -> Real)
    (belowErrorConstant : Real)
    (belowErrorConstant_le : belowErrorConstant <= 100)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            FixedErrorExplicitRiemannVonMangoldtSourceInput.cutoffTwoSignedExtendedErrorTerm
              validFrom hasanalizadeShenWongErrorTerm belowErrorConstant T)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedFiniteBelowDomainAndQuadraticTails
    validFrom
    heightCount
    (fun n : Nat => 1 * ((n : Real) + 1))
    3
    (by norm_num)
    belowErrorConstant
    belowErrorConstant_le
    published_abs_error_le
    belowDomain_abs_error_le
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount
    (closedBallZeroAxis_card_le_noResidualLinearAxisBound
      (noResidualRealAxisZetaZeros_of_realAxisZetaZeroClassification
        realAxisZeroClassification))
    (fun n => by
      simpa using
        (linearIndexBound_cutoffTwo_le_quadratic
          (axisSlope := 1) (by norm_num) n))

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from zero height count below the
chosen threshold and the classical real-axis zeta-zero classification. The
generic signed extension turns the zero-below-domain theorem plus a main-term
bound on `0 <= T < validFrom` into the required below-domain cleanup.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassification
    (validFrom : Real)
    (heightCount : Real -> Real)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (heightCount_eq_zero_below :
      forall T : Real,
        T < validFrom ->
          heightCount T = 0)
    (mainTerm_abs_nonneg_below_le :
      forall T : Real,
        0 <= T ->
          T < validFrom ->
            |riemannVonMangoldtMainTerm T| <= 100)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedFiniteBelowDomainAndRealAxisZeroClassification
    validFrom
    heightCount
    100
    (by norm_num)
    realAxisZeroClassification
    published_abs_error_le
    (FixedErrorExplicitRiemannVonMangoldtSourceInput.signedBelowDomain_abs_error_le_of_heightCount_eq_zero
      (validFrom := validFrom)
      (belowErrorConstant := 100)
      (publishedErrorTerm := hasanalizadeShenWongErrorTerm)
      heightCount_eq_zero_below
      mainTerm_abs_nonneg_below_le)
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from zero height count below the
chosen threshold when the threshold is at most `2*pi*e`. The checked elementary
main-term bound then supplies the nonnegative small-interval cleanup.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassificationOfValidFromLeTwoPiExp
    (validFrom : Real)
    (heightCount : Real -> Real)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (heightCount_eq_zero_below :
      forall T : Real,
        T < validFrom ->
          heightCount T = 0)
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
            ((s.card : Nat) : Real) <= heightCount T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassification
    validFrom
    heightCount
    realAxisZeroClassification
    published_abs_error_le
    heightCount_eq_zero_below
    (fun _ hT_nonneg hT_lt =>
      riemannVonMangoldtMainTerm_abs_nonneg_le_twoPiExp_le_hundred
        hT_nonneg ((le_of_lt hT_lt).trans validFrom_le_twoPiExp))
    positiveFiniteWindowCard_le_heightCount
    negativeFiniteWindowCard_le_heightCount

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from exact positive-ordinate
height-window data and a global conjugation-style mirror, with the classical
real-axis zeta-zero classification supplying the axis contribution.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithExactHeightWindowConjugationAndRealAxisZeroClassification
    (validFrom : Real)
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T)
    (belowDomain_abs_error_le :
      forall T : Real,
        T < validFrom ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithQuadraticTailsAndRealAxisZeroClassification
    validFrom
    heightCount
    realAxisZeroClassification
    published_abs_error_le
    belowDomain_abs_error_le
    (ExactPositiveOrdinateHeightCountWindow.positiveFiniteWindowCard_le_heightCount
      exactHeightWindow)
    (PositiveOrdinateHeightCountRealization.negativeFiniteWindowCard_le_heightCount_of_mirror
      (ExactPositiveOrdinateHeightCountWindow.toRealization exactHeightWindow)
      (ConjugateOrdinateZetaZeroMirror.toNegativeOrdinateMirrorToPositiveWindow
        conjugationMirror exactHeightWindow))

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from exact positive-ordinate
height-window data, a global conjugation-style mirror, and a no-positive-zero
theorem below the chosen threshold. The signed below-domain extension reduces
the cleanup obligation to a main-term bound on `0 <= T < validFrom`.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowConjugationNoPositiveZerosAndRealAxisZeroClassification
    (validFrom : Real)
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow validFrom)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (mainTerm_abs_nonneg_below_le :
      forall T : Real,
        0 <= T ->
          T < validFrom ->
            |riemannVonMangoldtMainTerm T| <= 100)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassification
    validFrom
    heightCount
    realAxisZeroClassification
    published_abs_error_le
    (ExactPositiveOrdinateHeightCountWindow.heightCount_eq_zero_below_of_noPositiveOrdinateZetaZerosAtOrBelow
      exactHeightWindow noPositiveZerosBelowValidFrom)
    mainTerm_abs_nonneg_below_le
    (ExactPositiveOrdinateHeightCountWindow.positiveFiniteWindowCard_le_heightCount
      exactHeightWindow)
    (PositiveOrdinateHeightCountRealization.negativeFiniteWindowCard_le_heightCount_of_mirror
      (ExactPositiveOrdinateHeightCountWindow.toRealization exactHeightWindow)
      (ConjugateOrdinateZetaZeroMirror.toNegativeOrdinateMirrorToPositiveWindow
        conjugationMirror exactHeightWindow))

/--
Build a Hasanalizade-Shen-Wong cutoff-2 input from exact positive-ordinate
height-window data, a global conjugation-style mirror, and a no-positive-zero
theorem below a threshold `validFrom <= 2*pi*e`. The elementary small-main-term
bound discharges the remaining signed below-domain cleanup field.
-/
noncomputable def HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowConjugationNoPositiveZerosAndRealAxisZeroClassificationOfValidFromLeTwoPiExp
    (validFrom : Real)
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (noPositiveZerosBelowValidFrom :
      NoPositiveOrdinateZetaZerosAtOrBelow validFrom)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedZeroBelowDomainAndRealAxisZeroClassificationOfValidFromLeTwoPiExp
    validFrom
    heightCount
    validFrom_le_twoPiExp
    realAxisZeroClassification
    published_abs_error_le
    (ExactPositiveOrdinateHeightCountWindow.heightCount_eq_zero_below_of_noPositiveOrdinateZetaZerosAtOrBelow
      exactHeightWindow noPositiveZerosBelowValidFrom)
    (ExactPositiveOrdinateHeightCountWindow.positiveFiniteWindowCard_le_heightCount
      exactHeightWindow)
    (PositiveOrdinateHeightCountRealization.negativeFiniteWindowCard_le_heightCount_of_mirror
      (ExactPositiveOrdinateHeightCountWindow.toRealization exactHeightWindow)
      (ConjugateOrdinateZetaZeroMirror.toNegativeOrdinateMirrorToPositiveWindow
        conjugationMirror exactHeightWindow))

/--
Preferred Hasanalizade-Shen-Wong exact-source data package.

The threshold remains explicit, but the package uses the checked
`validFrom <= 2*pi*e` route so the nonnegative below-domain main-term cleanup
is automatic. The remaining fields are the source theorem, exact height-window
interpretation, no-positive-zero theorem below the threshold, global
conjugation mirror, and real-axis classification.
-/
structure HasanalizadeShenWongExactHeightWindowConjugationSourceData
    (validFrom : Real) where
  heightCount : Real -> Real
  exactHeightWindow :
    ExactPositiveOrdinateHeightCountWindow heightCount
  conjugationMirror : ConjugateOrdinateZetaZeroMirror
  noPositiveZerosBelowValidFrom :
    NoPositiveOrdinateZetaZerosAtOrBelow validFrom
  validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1
  realAxisZeroClassification : RealAxisZetaZeroClassification
  published_abs_error_le :
    forall T : Real,
      validFrom <= T ->
        |heightCount T - riemannVonMangoldtMainTerm T| <=
          hasanalizadeShenWongErrorTerm T

namespace HasanalizadeShenWongExactHeightWindowConjugationSourceData

/--
Build the preferred HSW exact-source package from a lower bound on
positive-ordinate zeta-zero heights.
-/
def ofPositiveOrdinateZetaZeroLowerBound
    {validFrom : Real}
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (conjugationMirror : ConjugateOrdinateZetaZeroMirror)
    (positiveOrdinateLowerBound :
      PositiveOrdinateZetaZeroLowerBound validFrom)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom where
  heightCount := heightCount
  exactHeightWindow := exactHeightWindow
  conjugationMirror := conjugationMirror
  noPositiveZerosBelowValidFrom :=
    noPositiveOrdinateZetaZerosAtOrBelow_of_positiveOrdinateZetaZeroLowerBound
      positiveOrdinateLowerBound
  validFrom_le_twoPiExp := validFrom_le_twoPiExp
  realAxisZeroClassification := realAxisZeroClassification
  published_abs_error_le := published_abs_error_le

/--
Build the preferred HSW exact-source package from the direct zeta-zero
conjugation symmetry theorem. The global mirror field is constructed inside
Lean.
-/
def ofPositiveOrdinateZetaZeroLowerBoundAndZetaZeroConjugationSymmetry
    {validFrom : Real}
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (positiveOrdinateLowerBound :
      PositiveOrdinateZetaZeroLowerBound validFrom)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofPositiveOrdinateZetaZeroLowerBound
    heightCount
    exactHeightWindow
    (conjugateOrdinateZetaZeroMirror_of_zetaZeroConjugationSymmetry
      zetaZeroConjugationSymmetry)
    positiveOrdinateLowerBound
    validFrom_le_twoPiExp
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred HSW exact-source package from source-shaped small-height
zero-free data and zeta-zero conjugation symmetry.
-/
def ofZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    {validFrom : Real}
    (heightCount : Real -> Real)
    (exactHeightWindow :
      ExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofPositiveOrdinateZetaZeroLowerBoundAndZetaZeroConjugationSymmetry
    heightCount
    exactHeightWindow
    zetaZeroConjugationSymmetry
    (positiveOrdinateZetaZeroLowerBound_of_zetaZeroFreePositiveOrdinateBand
      zetaZeroFreePositiveOrdinateBand)
    validFrom_le_twoPiExp
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred HSW exact-source package from source-shaped exact
height-window data, source-shaped small-height zero-free data, and zeta-zero
conjugation symmetry.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    heightCount
    (SourceExactPositiveOrdinateHeightCountWindow.toExactPositiveOrdinateHeightCountWindow
      sourceExactHeightWindow)
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    validFrom_le_twoPiExp
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred HSW exact-source package from source-shaped exact
height-window data, source-shaped small-height zero-free data, and the
standard function-level zeta conjugation formula.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndRiemannZetaConjugationFormula
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (realAxisZeroClassification : RealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    (zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormula
      riemannZetaConjugationFormula)
    validFrom_le_twoPiExp
    realAxisZeroClassification
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data and the sharpened left-real-axis classification target.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndLeftRealAxisClassification
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (leftRealAxisZeroClassification : LeftRealAxisZetaZeroClassification)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreePositiveOrdinateBandAndZetaZeroConjugationSymmetry
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    validFrom_le_twoPiExp
    (realAxisZetaZeroClassification_of_leftRealAxisZetaZeroClassification
      leftRealAxisZeroClassification)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data and the remaining open-unit-interval real-axis zero-free
target.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalRealAxisZeroFree
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (openUnitIntervalRealAxisZeroFree :
      OpenUnitIntervalRealAxisZetaZeroFree)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndLeftRealAxisClassification
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    validFrom_le_twoPiExp
    (leftRealAxisZetaZeroClassification_of_openUnitIntervalRealAxisZetaZeroFree
      openUnitIntervalRealAxisZeroFree)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data and the real-variable nonzero theorem for zeta on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaNonzero
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (openUnitIntervalZetaNonzero :
      OpenUnitIntervalRiemannZetaNonzero)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalRealAxisZeroFree
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    validFrom_le_twoPiExp
    (openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaNonzero
      openUnitIntervalZetaNonzero)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data and the classical sign-shaped theorem `Re zeta x < 0` for
`0 < x < 1`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaReNegative
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (zetaZeroConjugationSymmetry : ZetaZeroConjugationSymmetry)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (openUnitIntervalZetaReNegative :
      OpenUnitIntervalRiemannZetaReNegative)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaNonzero
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    zetaZeroConjugationSymmetry
    validFrom_le_twoPiExp
    (openUnitIntervalRiemannZetaNonzero_of_reNegative
      openUnitIntervalZetaReNegative)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data, the standard function-level zeta conjugation formula, and
the real-variable nonzero theorem for zeta on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaNonzero
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (openUnitIntervalZetaNonzero :
      OpenUnitIntervalRiemannZetaNonzero)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandConjugationAndOpenUnitIntervalZetaNonzero
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    (zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormula
      riemannZetaConjugationFormula)
    validFrom_le_twoPiExp
    openUnitIntervalZetaNonzero
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data, the standard function-level zeta conjugation formula, and
the classical sign-shaped theorem `Re zeta x < 0` for `0 < x < 1`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaReNegative
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (openUnitIntervalZetaReNegative :
      OpenUnitIntervalRiemannZetaReNegative)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaNonzero
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    validFrom_le_twoPiExp
    (openUnitIntervalRiemannZetaNonzero_of_reNegative
      openUnitIntervalZetaReNegative)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data, the standard function-level zeta conjugation formula, and
the eta analytic-continuation formula on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaFormula
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (etaFormula : OpenUnitIntervalRiemannZetaEtaFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndOpenUnitIntervalZetaReNegative
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    validFrom_le_twoPiExp
    (openUnitIntervalRiemannZetaReNegative_of_etaFormula etaFormula)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data, the standard function-level zeta conjugation formula, and
the canonical-value eta formula on `(0, 1)`.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaValueFormula
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (etaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaFormula
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    validFrom_le_twoPiExp
    (openUnitIntervalRiemannZetaEtaFormula_of_valueFormula
      etaValueFormula)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data, the standard function-level zeta conjugation formula, and
the source-shaped `ZMod 2` checked boundary-value theorem.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndZModTwoBoundaryValue
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (zmodTwoBoundaryValue :
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndEtaValueFormula
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    validFrom_le_twoPiExp
    (openUnitIntervalRiemannZetaEtaValueFormula_of_zmodTwoBoundaryValue
      zmodTwoBoundaryValue)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the fully source-shaped
zero-counting data, the standard function-level zeta conjugation formula, and
the isolated regularized Hurwitz-tail theorem.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndRegularizedTailHurwitz
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (regularizedTailHurwitz :
      ZModAdditiveCharacterRegularizedTailHurwitzFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndZModTwoBoundaryValue
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    validFrom_le_twoPiExp
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      regularizedTailHurwitz)
    published_abs_error_le

/--
Build the preferred HSW exact-source package from the nonendpoint regularized
Hurwitz-tail theorem.  The endpoint residue is automatic.
-/
noncomputable def ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndRegularizedTailHurwitzNonendpoint
    {validFrom : Real}
    (heightCount : Real -> Real)
    (sourceExactHeightWindow :
      SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (zetaZeroFreePositiveOrdinateBand :
      ZetaZeroFreePositiveOrdinateBand validFrom)
    (riemannZetaConjugationFormula : RiemannZetaConjugationFormula)
    (validFrom_le_twoPiExp : validFrom <= 2 * Real.pi * Real.exp 1)
    (regularizedTailHurwitz :
      ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula)
    (published_abs_error_le :
      forall T : Real,
        validFrom <= T ->
          |heightCount T - riemannVonMangoldtMainTerm T| <=
            hasanalizadeShenWongErrorTerm T) :
    HasanalizadeShenWongExactHeightWindowConjugationSourceData
      validFrom :=
  ofSourceExactHeightWindowZetaZeroFreeBandRiemannZetaConjugationFormulaAndRegularizedTailHurwitz
    heightCount
    sourceExactHeightWindow
    zetaZeroFreePositiveOrdinateBand
    riemannZetaConjugationFormula
    validFrom_le_twoPiExp
    (zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint
      regularizedTailHurwitz)
    published_abs_error_le

/-- Convert the preferred HSW exact-source package to the checked source input. -/
noncomputable def toInput
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    HasanalizadeShenWongExplicitRiemannVonMangoldtInput validFrom :=
  HasanalizadeShenWongExplicitRiemannVonMangoldtInput.ofCutoffTwoWithSignedExactHeightWindowConjugationNoPositiveZerosAndRealAxisZeroClassificationOfValidFromLeTwoPiExp
    validFrom
    data.heightCount
    data.exactHeightWindow
    data.conjugationMirror
    data.noPositiveZerosBelowValidFrom
    data.validFrom_le_twoPiExp
    data.realAxisZeroClassification
    data.published_abs_error_le

/-- Convert the preferred HSW exact-source package to the generic published source. -/
noncomputable def toPublishedExplicitRiemannVonMangoldtSource
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    PublishedExplicitRiemannVonMangoldtSource :=
  data.toInput.toPublishedExplicitRiemannVonMangoldtSource

/--
Convert the preferred HSW exact-source package to the named closed-ball
Riemann-von-Mangoldt counting target.
-/
noncomputable def toRiemannVonMangoldtCountingTarget
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  data.toInput.toRiemannVonMangoldtCountingTarget

/-- The preferred HSW exact-source package uses cutoff `2`. -/
theorem toInput_cutoff
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    data.toInput.cutoff = 2 := by
  rfl

/-- The preferred HSW exact-source package has quadratic growth. -/
theorem toInput_growth
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    data.toInput.growth = 2 := by
  rfl

/-- The induced HSW shell-counting package uses cutoff `2`. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    data.toInput.toPolynomialZeroCountingEstimate.cutoff = 2 := by
  rw [FixedErrorExplicitRiemannVonMangoldtSourceInput.toPolynomialZeroCountingEstimate_cutoff,
    toInput_cutoff]

/-- The induced HSW shell-counting package has quadratic growth. -/
theorem toPolynomialZeroCountingEstimate_growth
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    data.toInput.toPolynomialZeroCountingEstimate.growth = 2 := by
  rw [FixedErrorExplicitRiemannVonMangoldtSourceInput.toPolynomialZeroCountingEstimate_growth,
    toInput_growth]

/--
For the preferred HSW exact-source package, the p-series decay margin is
exactly the elementary inequality `3 < decayExponent`.
-/
theorem growth_add_one_lt_decay_of_three_lt
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom)
    {decayExponent : Real}
    (hdecay : (3 : Real) < decayExponent) :
    data.toInput.toPolynomialZeroCountingEstimate.growth + 1 <
      decayExponent := by
  rw [toPolynomialZeroCountingEstimate_growth data]
  norm_num
  exact hdecay

/-- The named HSW counting target uses cutoff `2`. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    data.toRiemannVonMangoldtCountingTarget.cutoff = 2 := by
  rw [toRiemannVonMangoldtCountingTarget,
    FixedErrorExplicitRiemannVonMangoldtSourceInput.toRiemannVonMangoldtCountingTarget_cutoff,
    toInput_cutoff]

/-- The named HSW counting target has quadratic growth. -/
theorem toRiemannVonMangoldtCountingTarget_growth
    {validFrom : Real}
    (data :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData
        validFrom) :
    data.toRiemannVonMangoldtCountingTarget.growth = 2 := by
  rw [toRiemannVonMangoldtCountingTarget,
    FixedErrorExplicitRiemannVonMangoldtSourceInput.toRiemannVonMangoldtCountingTarget_growth,
    toInput_growth]

end HasanalizadeShenWongExactHeightWindowConjugationSourceData

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
