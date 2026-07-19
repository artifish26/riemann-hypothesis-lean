import RiemannHypothesisProject.RiemannVonMangoldtPolynomialEnvelope

/-!
# Published `N(T)` bound targets

This file records source-shaped targets for published explicit zero-counting
theorems of Riemann-von Mangoldt type.

The project does not prove the analytic estimates here.  Instead, it fixes the
normalization of the main term and common published error terms, and checks the
adapter from a theorem valid only above its published threshold to the existing
all-real `ClassicalExplicitRiemannVonMangoldtBound` package.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/--
The main term in modern explicit Riemann-von Mangoldt estimates:
`T / (2 * pi) * log (T / (2 * pi * e))`.
-/
def riemannVonMangoldtMainTerm (T : Real) : Real :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1))

/-- The Hasanalizade-Shen-Wong 2021 published error term. -/
def hasanalizadeShenWongErrorTerm (T : Real) : Real :=
  ((1038 : Real) / 10000) * Real.log T +
    ((2573 : Real) / 10000) * Real.log (Real.log T) +
    ((93675 : Real) / 10000)

/-- The Bellotti-Wong 2025 published error term, valid for `T >= e`. -/
def bellottiWongErrorTerm (T : Real) : Real :=
  ((10076 : Real) / 100000) * Real.log T +
    ((24460 : Real) / 100000) * Real.log (Real.log T) +
    ((808344 : Real) / 100000)

/-- Bellotti-Wong's published lower threshold for the explicit estimate. -/
def bellottiWongValidFrom : Real :=
  Real.exp 1

/--
A published explicit `N(T)` estimate, separated into the theorem as stated on
its valid domain and an extended all-real error term.

The existing adapter expects an estimate for every real `T`, while papers such
as Bellotti-Wong state the theorem for `T >= e`.  The fields below make the
finite-domain cleanup explicit: prove the published estimate above
`validFrom`, prove any finite/small-height bound below `validFrom`, and prove
that the extended error agrees with the published error on the published
domain.  The polynomial fields are the coarse tail bounds needed by the
closed-ball counting pipeline.
-/
structure PublishedExplicitRiemannVonMangoldtSource where
  cutoff : Nat
  validFrom : Real
  heightCount : Real -> Real
  publishedErrorTerm : Real -> Real
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

namespace PublishedExplicitRiemannVonMangoldtSource

/-- The domain-restricted published estimate plus the below-domain cleanup give an all-real bound. -/
theorem explicit_abs_error_le
    (source : PublishedExplicitRiemannVonMangoldtSource)
    (T : Real) :
    |source.heightCount T - riemannVonMangoldtMainTerm T| <=
      source.extendedErrorTerm T := by
  by_cases hT : source.validFrom <= T
  · have hpub := source.published_abs_error_le T hT
    have heq := source.extendedErrorTerm_eq_published T hT
    simpa [heq] using hpub
  · exact source.belowDomain_abs_error_le T (lt_of_not_ge hT)

/--
Convert a published explicit estimate, with its domain cleanup and polynomial
envelopes, into the existing explicit Riemann-von-Mangoldt adapter.
-/
noncomputable def toClassicalExplicitRiemannVonMangoldtBound
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    ClassicalExplicitRiemannVonMangoldtBound :=
  ClassicalExplicitRiemannVonMangoldtBound.ofPolynomialMainErrorAxis
    source.cutoff
    source.heightCount
    riemannVonMangoldtMainTerm
    source.extendedErrorTerm
    source.axisOrTrivialBound
    source.mainConstant
    source.errorConstant
    source.axisConstant
    source.growth
    source.mainConstant_nonneg
    source.errorConstant_nonneg
    source.axisConstant_nonneg
    source.explicit_abs_error_le
    source.positiveFiniteWindowCard_le_heightCount
    source.negativeFiniteWindowCard_le_heightCount
    source.axisWindowCard_le
    source.tail_mainTerm_le
    source.tail_extendedErrorTerm_le
    source.tail_axisOrTrivialBound_le

/-- The published source gives the preferred cumulative closed-ball count. -/
noncomputable def toCumulativeWindowCountingEstimate
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  source.toClassicalExplicitRiemannVonMangoldtBound
    |>.toCumulativeWindowCountingEstimate

/-- The published source gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  source.toClassicalExplicitRiemannVonMangoldtBound
    |>.toPolynomialZeroCountingEstimate

/-- The published source gives the named closed-ball Riemann-von-Mangoldt target. -/
noncomputable def toRiemannVonMangoldtCountingTarget
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    ClosedBallZeroRiemannVonMangoldtCountingTarget :=
  ClosedBallZeroCumulativeWindowCountingEstimate.toRiemannVonMangoldtCountingTarget
    source.toCumulativeWindowCountingEstimate

/-- The converted cumulative estimate keeps the published-source cutoff. -/
theorem toCumulativeWindowCountingEstimate_cutoff
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    source.toCumulativeWindowCountingEstimate.cutoff = source.cutoff := by
  rfl

/-- The converted shell-counting estimate keeps the published-source cutoff. -/
theorem toPolynomialZeroCountingEstimate_cutoff
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    source.toPolynomialZeroCountingEstimate.cutoff = source.cutoff := by
  rfl

/-- The converted shell-counting estimate keeps the published-source growth exponent. -/
theorem toPolynomialZeroCountingEstimate_growth
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    source.toPolynomialZeroCountingEstimate.growth = source.growth := by
  rfl

/-- The named Riemann-von-Mangoldt target keeps the published-source cutoff. -/
theorem toRiemannVonMangoldtCountingTarget_cutoff
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    source.toRiemannVonMangoldtCountingTarget.cutoff = source.cutoff := by
  rw [toRiemannVonMangoldtCountingTarget,
    ClosedBallZeroCumulativeWindowCountingEstimate.toRiemannVonMangoldtCountingTarget_cutoff,
    toCumulativeWindowCountingEstimate_cutoff]

/-- The named Riemann-von-Mangoldt target keeps the published-source growth exponent. -/
theorem toRiemannVonMangoldtCountingTarget_growth
    (source : PublishedExplicitRiemannVonMangoldtSource) :
    source.toRiemannVonMangoldtCountingTarget.growth = source.growth := by
  rw [toRiemannVonMangoldtCountingTarget,
    ClosedBallZeroCumulativeWindowCountingEstimate.toRiemannVonMangoldtCountingTarget_growth]
  rfl

end PublishedExplicitRiemannVonMangoldtSource

/--
Build a published explicit `N(T)` source with cutoff fixed to `2`.

This is the source-level companion to the cutoff-2 zero-counting and p-series
route: the three polynomial tails are stated directly at `n + 2`.
-/
noncomputable def PublishedExplicitRiemannVonMangoldtSource.ofCutoffTwo
    (validFrom : Real)
    (heightCount publishedErrorTerm extendedErrorTerm : Real -> Real)
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
    PublishedExplicitRiemannVonMangoldtSource where
  cutoff := 2
  validFrom := validFrom
  heightCount := heightCount
  publishedErrorTerm := publishedErrorTerm
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
Bellotti-Wong-shaped source target.  Future analytic work should instantiate
this structure with `publishedErrorTerm = bellottiWongErrorTerm` and
`validFrom = bellottiWongValidFrom`.
-/
abbrev BellottiWongExplicitRiemannVonMangoldtSource :=
  PublishedExplicitRiemannVonMangoldtSource

/--
Hasanalizade-Shen-Wong-shaped source target.  Future analytic work should
instantiate this structure with
`publishedErrorTerm = hasanalizadeShenWongErrorTerm`.
-/
abbrev HasanalizadeShenWongExplicitRiemannVonMangoldtSource :=
  PublishedExplicitRiemannVonMangoldtSource

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
