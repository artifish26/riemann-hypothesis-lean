import RiemannHypothesisProject.RiemannWeilSupportDensityConcreteAssembly
import RiemannHypothesisProject.RiemannWeilConcretePublishedCountingPSeriesAssembly
import RiemannHypothesisProject.RiemannWeilAntitoneRadialSplitPSeriesBridge

/-!
# Split-radial concrete Riemann-Weil assembly

`RiemannWeilAntitoneRadialSplitPSeriesBridge` splits the radial p-series
estimate into finite-prefix and tail pieces.  This file connects that split
radial package to the most concrete published-counting/source-formula/support-
density route.

The resulting endpoint exposes all current preferred analytic work units:

* fixed published `N(T)` source data;
* finite-prefix and tail radial p-series estimates;
* source Guinand-Weil formula data and normalization;
* support-restricted positivity plus a dense core;
* admissible coefficient-test identities for the residual-to-Li step.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion

noncomputable section

/--
Concrete published-counting zero-data package with the radial p-series estimate
split into finite-prefix and tail estimates.
-/
structure RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  publishedCounting :
    FixedErrorExplicitRiemannVonMangoldtSourceInput
      validFrom publishedErrorTerm
  system : SchwartzRiemannWeilExtensionSystem
  growthBound : SchwartzRiemannWeilExtensionGrowthBound system
  cutoff : Nat
  prefixBound : SchwartzLineTestFunction -> Nat -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  radialBound : SchwartzLineTestFunction -> Real -> Real
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  prefixBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n
  envelope_le_radialBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
        radialBound f ‖riemannWeilZeroArgument (rho : Complex)‖
  radialBound_antitone :
    forall f : SchwartzLineTestFunction, Antitone (radialBound f)
  prefix_radialBound_lowerBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      n < cutoff ->
        radialBound f (closedBallZeroArgumentShellLowerBound n) <=
          prefixBound f n
  tail_radialBound_lowerBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      cutoff <= n ->
        radialBound f (closedBallZeroArgumentShellLowerBound n) <=
          zeroConstant f *
            (1 / |((n - cutoff : Nat) : Real) + 1| ^ decayExponent)
  counting_cutoff_eq :
    publishedCounting.toPolynomialZeroCountingEstimate.cutoff = cutoff
  growth_add_one_lt_decay :
    publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
      decayExponent

namespace RiemannWeilFixedErrorPublishedCountingSplitPSeriesData

/-- The generic published source obtained from the fixed-error input. -/
noncomputable def publishedSource
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    PublishedExplicitRiemannVonMangoldtSource :=
  data.publishedCounting.toPublishedExplicitRiemannVonMangoldtSource

/-- The closed-ball first-entry shell count obtained from the fixed-error input. -/
noncomputable def counting
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  data.publishedCounting.toPolynomialZeroCountingEstimate

/-- The cumulative closed-ball count obtained from the fixed-error input. -/
noncomputable def cumulativeCounting
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  data.publishedCounting.toCumulativeWindowCountingEstimate

/-- The induced shell-counting cutoff is the fixed-error source cutoff. -/
theorem counting_cutoff_eq_source
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    data.counting.cutoff = data.publishedCounting.cutoff := by
  rfl

/-- The induced shell-counting growth exponent is the fixed-error source growth. -/
theorem counting_growth_eq_source
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    data.counting.growth = data.publishedCounting.growth := by
  rfl

/--
Build fixed-error published-counting split data from a generic split radial
p-series package whose counting estimate is the one induced by the fixed
published source.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting =
        publishedCounting.toPolynomialZeroCountingEstimate) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm where
  publishedCounting := publishedCounting
  system := splitData.system
  growthBound := splitData.growthBound
  cutoff := splitData.cutoff
  prefixBound := splitData.prefixBound
  zeroConstant := splitData.zeroConstant
  decayExponent := splitData.decayExponent
  radialBound := splitData.radialBound
  zeroConstant_nonneg := splitData.zeroConstant_nonneg
  prefixBound_nonneg := splitData.prefixBound_nonneg
  envelope_le_radialBound := splitData.envelope_le_radialBound
  radialBound_antitone := splitData.radialBound_antitone
  prefix_radialBound_lowerBound_le :=
    splitData.prefix_radialBound_lowerBound_le
  tail_radialBound_lowerBound_le :=
    splitData.tail_radialBound_lowerBound_le
  counting_cutoff_eq := by
    simpa [counting_eq] using splitData.counting_cutoff_eq
  growth_add_one_lt_decay := by
    simpa [counting_eq] using splitData.growth_add_one_lt_decay

/--
Use an automatic-prefix radial target as fixed-error split p-series data when
its counting estimate is the one induced by the fixed published source input.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting =
        publishedCounting.toPolynomialZeroCountingEstimate) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofSplitPSeriesEnvelopeData publishedCounting
    target.toSplitPSeriesEnvelopeData
    (by
      change target.counting =
        publishedCounting.toPolynomialZeroCountingEstimate
      exact counting_eq)

/--
Cutoff-2 closed-ball fixed-error split data from a global exact-norm clipped
p-series decay theorem.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNorm
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            sourceConstant strongDecayExponent f (norm z))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNorm
      system sourceConstant zeroConstant decayExponent strongDecayExponent
      sourceConstant_nonneg sourceConstant_le_zeroConstant
      strongDecayExponent_nonneg extension_norm_le_clippedRadialBound
      hdecay_le_strong publishedCounting.toPolynomialZeroCountingEstimate
      counting_cutoff_eq growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball fixed-error split data from a global exact-norm
shifted-radius p-series decay theorem.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormOfShiftedRadius
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          sourceConstant f *
            (1 / (norm z + 2) ^ strongDecayExponent))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormOfShiftedRadius
      system sourceConstant zeroConstant decayExponent strongDecayExponent
      sourceConstant_nonneg sourceConstant_le_zeroConstant
      strongDecayExponent_nonneg extension_norm_le_shiftedRadialBound
      hdecay_le_strong publishedCounting.toPolynomialZeroCountingEstimate
      counting_cutoff_eq growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball fixed-error split data from a global exact-norm clipped
p-series decay theorem, with matching source/package constant and exponent.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f (norm z))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_clippedRadialBound
      publishedCounting.toPolynomialZeroCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball fixed-error split data from a global exact-norm
shifted-radius p-series decay theorem, with matching source/package constant
and exponent.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_shiftedRadialBound
      publishedCounting.toPolynomialZeroCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Fixed-error split data from the source-shaped cumulative count and a cutoff-2
exact-norm shifted-radius p-series estimate.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toCumulativeWindowCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toCumulativeWindowCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_shiftedRadialBound
      publishedCounting.toCumulativeWindowCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Build the fixed-error split p-series package when the radial tail estimate is
proved in the natural post-cutoff coordinate `m`, i.e. on shell `m + cutoff`.
-/
noncomputable def ofTailCoordinateBounds
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radialBound_lowerBound_le_tail :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (closedBallZeroArgumentShellLowerBound (m + cutoff)) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = cutoff)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm where
  publishedCounting := publishedCounting
  system := system
  growthBound := growthBound
  cutoff := cutoff
  prefixBound := prefixBound
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  radialBound := radialBound
  zeroConstant_nonneg := zeroConstant_nonneg
  prefixBound_nonneg := prefixBound_nonneg
  envelope_le_radialBound := envelope_le_radialBound
  radialBound_antitone := radialBound_antitone
  prefix_radialBound_lowerBound_le := prefix_radialBound_lowerBound_le
  tail_radialBound_lowerBound_le :=
    RiemannWeilAntitoneRadialPSeriesEnvelopeData.tail_radialBound_lowerBound_le_of_tailCoordinate
      cutoff zeroConstant decayExponent radialBound
      tail_radialBound_lowerBound_le_tail
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Build the fixed-error split p-series package when the radial tail estimate is
proved at the plain radius `m`, with shell geometry providing
`m <= lowerBound (m + cutoff)`.
-/
noncomputable def ofNatRadiusTailBounds
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = cutoff)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofTailCoordinateBounds publishedCounting system growthBound cutoff
    prefixBound zeroConstant decayExponent radialBound zeroConstant_nonneg
    prefixBound_nonneg envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.tailCoordinate_lowerBound_le_of_natRadius_tail
      cutoff zeroConstant decayExponent radialBound radialBound_antitone
      tail_radius_le_lowerBound tail_radialBound_natRadius_le)
    counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 fixed-error split p-series package. The checked closed-ball shell
geometry supplies `m <= lowerBound (m + 2)`, so the analytic tail estimate only
needs to be stated at the plain radius `m`.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwo
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < 2 ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofNatRadiusTailBounds publishedCounting system growthBound 2 prefixBound
    zeroConstant decayExponent radialBound zeroConstant_nonneg
    prefixBound_nonneg envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le
    nat_le_closedBallZeroArgumentShellLowerBound_add_two
    tail_radialBound_natRadius_le counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 fixed-error split p-series package where the finite-prefix estimate is
supplied only by the two shell values before the tail.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoPrefixValues
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofNatRadiusTailBoundsCutoffTwo publishedCounting system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
      prefixZero prefixOne)
    zeroConstant decayExponent radialBound zeroConstant_nonneg
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound_nonneg
      prefixZero prefixOne prefixZero_nonneg prefixOne_nonneg)
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
      prefixZero prefixOne radialBound prefixZero_bound prefixOne_bound)
    tail_radialBound_natRadius_le counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 fixed-error split p-series package with source-shaped finite-prefix
and tail constants.  Future analytic estimates may first prove bounds using
source constants at shells `0` and `1`, a source tail constant, and a stronger
source tail exponent; Lean weakens those to the package constants and exponent.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourcePrefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixZero f)
    (sourcePrefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixOne f)
    (sourcePrefixZero_le_prefixZero :
      forall f : SchwartzLineTestFunction, sourcePrefixZero f <= prefixZero f)
    (sourcePrefixOne_le_prefixOne :
      forall f : SchwartzLineTestFunction, sourcePrefixOne f <= prefixOne f)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          sourcePrefixZero f)
    (prefixOne_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          sourcePrefixOne f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofNatRadiusTailBoundsCutoffTwo publishedCounting system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
      prefixZero prefixOne)
    zeroConstant decayExponent radialBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.targetZeroConstant_nonneg_of_sourceConstant_le
      sourceConstant zeroConstant sourceConstant_nonneg
      sourceConstant_le_zeroConstant)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound_nonneg
      prefixZero prefixOne
      (RiemannWeilAntitoneRadialPSeriesEnvelopeData.targetPrefix_nonneg_of_sourcePrefix_le
        sourcePrefixZero prefixZero sourcePrefixZero_nonneg
        sourcePrefixZero_le_prefixZero)
      (RiemannWeilAntitoneRadialPSeriesEnvelopeData.targetPrefix_nonneg_of_sourcePrefix_le
        sourcePrefixOne prefixOne sourcePrefixOne_nonneg
        sourcePrefixOne_le_prefixOne))
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound_of_sourceBounds
      sourcePrefixZero sourcePrefixOne prefixZero prefixOne radialBound
      sourcePrefixZero_le_prefixZero sourcePrefixOne_le_prefixOne
      prefixZero_source_bound prefixOne_source_bound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.tail_radialBound_natRadius_le_of_sourceConstantStrongDecay
      sourceConstant zeroConstant radialBound sourceConstant_nonneg
      sourceConstant_le_zeroConstant hdecay_le_strong
      tail_radialBound_natRadius_le_source)
    counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 fixed-error split p-series package with automatic finite-prefix
constants and source-shaped tail data.  The prefix constants are `max 0` of
the radial majorant at the two finite shells, so future analytic work only
needs the envelope-to-radial estimate, radial antitonicity, and the source-tail
decay theorem.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoAutomaticPrefixOfSourceConstantStrongDecay
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm :=
  ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds
    publishedCounting system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixZero
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixOne
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixZero
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixOne
      radialBound)
    sourceConstant zeroConstant decayExponent strongDecayExponent radialBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixZero_nonneg
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixOne_nonneg
      radialBound)
    (fun _ => le_rfl)
    (fun _ => le_rfl)
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_zero_le_cutoffTwoMaxPrefixZero
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_one_le_cutoffTwoMaxPrefixOne
      radialBound)
    hdecay_le_strong tail_radialBound_natRadius_le_source
    counting_cutoff_eq growth_add_one_lt_decay

/-- The source-shaped fixed-error cutoff-2 constructor has cutoff exactly `2`. -/
theorem ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds_cutoff
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourcePrefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixZero f)
    (sourcePrefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixOne f)
    (sourcePrefixZero_le_prefixZero :
      forall f : SchwartzLineTestFunction, sourcePrefixZero f <= prefixZero f)
    (sourcePrefixOne_le_prefixOne :
      forall f : SchwartzLineTestFunction, sourcePrefixOne f <= prefixOne f)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          sourcePrefixZero f)
    (prefixOne_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          sourcePrefixOne f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    (ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds
      publishedCounting system growthBound sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne sourceConstant zeroConstant decayExponent
      strongDecayExponent radialBound sourcePrefixZero_nonneg
      sourcePrefixOne_nonneg sourcePrefixZero_le_prefixZero
      sourcePrefixOne_le_prefixOne sourceConstant_nonneg
      sourceConstant_le_zeroConstant envelope_le_radialBound
      radialBound_antitone prefixZero_source_bound prefixOne_source_bound
      hdecay_le_strong tail_radialBound_natRadius_le_source
      counting_cutoff_eq growth_add_one_lt_decay).cutoff = 2 := by
  rfl

/--
The source-shaped fixed-error cutoff-2 constructor uses exactly the target
two-value prefix bound.
-/
theorem ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds_prefixBound
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourcePrefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixZero f)
    (sourcePrefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixOne f)
    (sourcePrefixZero_le_prefixZero :
      forall f : SchwartzLineTestFunction, sourcePrefixZero f <= prefixZero f)
    (sourcePrefixOne_le_prefixOne :
      forall f : SchwartzLineTestFunction, sourcePrefixOne f <= prefixOne f)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          sourcePrefixZero f)
    (prefixOne_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          sourcePrefixOne f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    (ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds
      publishedCounting system growthBound sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne sourceConstant zeroConstant decayExponent
      strongDecayExponent radialBound sourcePrefixZero_nonneg
      sourcePrefixOne_nonneg sourcePrefixZero_le_prefixZero
      sourcePrefixOne_le_prefixOne sourceConstant_nonneg
      sourceConstant_le_zeroConstant envelope_le_radialBound
      radialBound_antitone prefixZero_source_bound prefixOne_source_bound
      hdecay_le_strong tail_radialBound_natRadius_le_source
      counting_cutoff_eq growth_add_one_lt_decay).prefixBound =
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
        prefixZero prefixOne := by
  rfl

/-- The fixed-error cutoff-2 prefix-values constructor has cutoff exactly `2`. -/
theorem ofNatRadiusTailBoundsCutoffTwoPrefixValues_cutoff
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    (ofNatRadiusTailBoundsCutoffTwoPrefixValues publishedCounting system
      growthBound prefixZero prefixOne zeroConstant decayExponent radialBound
      zeroConstant_nonneg prefixZero_nonneg prefixOne_nonneg
      envelope_le_radialBound radialBound_antitone prefixZero_bound
      prefixOne_bound tail_radialBound_natRadius_le counting_cutoff_eq
      growth_add_one_lt_decay).cutoff = 2 := by
  rfl

/-- The fixed-error cutoff-2 constructor uses exactly the two-value prefix bound. -/
theorem ofNatRadiusTailBoundsCutoffTwoPrefixValues_prefixBound
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting_cutoff_eq :
      publishedCounting.toPolynomialZeroCountingEstimate.cutoff = 2)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    (ofNatRadiusTailBoundsCutoffTwoPrefixValues publishedCounting system
      growthBound prefixZero prefixOne zeroConstant decayExponent radialBound
      zeroConstant_nonneg prefixZero_nonneg prefixOne_nonneg
      envelope_le_radialBound radialBound_antitone prefixZero_bound
      prefixOne_bound tail_radialBound_natRadius_le counting_cutoff_eq
      growth_add_one_lt_decay).prefixBound =
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
        prefixZero prefixOne := by
  rfl

/-- Convert to the generic split antitone radial p-series package. -/
noncomputable def toAntitoneRadialSplitPSeriesEnvelopeData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData where
  system := data.system
  growthBound := data.growthBound
  cutoff := data.cutoff
  prefixBound := data.prefixBound
  zeroConstant := data.zeroConstant
  decayExponent := data.decayExponent
  radialBound := data.radialBound
  zeroConstant_nonneg := data.zeroConstant_nonneg
  prefixBound_nonneg := data.prefixBound_nonneg
  envelope_le_radialBound := data.envelope_le_radialBound
  radialBound_antitone := data.radialBound_antitone
  prefix_radialBound_lowerBound_le :=
    data.prefix_radialBound_lowerBound_le
  tail_radialBound_lowerBound_le := data.tail_radialBound_lowerBound_le
  counting := data.counting
  counting_cutoff_eq := data.counting_cutoff_eq
  growth_add_one_lt_decay := data.growth_add_one_lt_decay

/-- Convert split radial data to the existing fixed-error antitone package. -/
noncomputable def toFixedErrorPublishedCountingAntitonePSeriesData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
    data.publishedCounting data.toAntitoneRadialSplitPSeriesEnvelopeData rfl

/-- The eventual p-series zero-data package produced from split radial data. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  data.toFixedErrorPublishedCountingAntitonePSeriesData
    |>.toEventualPSeriesEnvelopeZeroData

/-- The induced zero side from fixed published counting and split radial decay. -/
noncomputable def zeroSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

/-- The split-radial zero side uses the candidate extension weight. -/
theorem zeroSide_weight
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide_weight f rho

end RiemannWeilFixedErrorPublishedCountingSplitPSeriesData

/-- Bellotti-Wong specialization of the split radial concrete zero-data package. -/
abbrev RiemannWeilBellottiWongSplitPSeriesData :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization of the split radial concrete zero-data
package, with the validity threshold still explicit.
-/
abbrev RiemannWeilHasanalizadeShenWongSplitPSeriesData
    (validFrom : Real) :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong split data from the preferred exact-source package and the
preferred cutoff-2 exact-norm clipped p-series estimate.  The exact-source
package supplies cutoff `2` and growth `2`, so the p-series margin is the
single field `3 < decayExponent`.
-/
noncomputable def RiemannWeilBellottiWongSplitPSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
    (sourceData : BellottiWongExactHeightWindowConjugationSourceData)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decay_margin : (3 : Real) < decayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f (norm z)) :
    RiemannWeilBellottiWongSplitPSeriesData :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      sourceData.toInput system constant decayExponent constant_nonneg
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 3) decay_margin))
      extension_norm_le_clippedRadialBound
      (BellottiWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (BellottiWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
Bellotti-Wong split data from the preferred exact-source package and a
cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongSplitPSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    (sourceData : BellottiWongExactHeightWindowConjugationSourceData)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decay_margin : (3 : Real) < decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent)) :
    RiemannWeilBellottiWongSplitPSeriesData :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData.toInput system constant decayExponent constant_nonneg
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 3) decay_margin))
      extension_norm_le_shiftedRadialBound
      (BellottiWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (BellottiWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
Bellotti-Wong split data from the exact source's cumulative count and a
cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongSplitPSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
    (sourceData : BellottiWongExactHeightWindowConjugationSourceData)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decay_margin : (3 : Real) < decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent)) :
    RiemannWeilBellottiWongSplitPSeriesData :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      sourceData.toInput system constant decayExponent constant_nonneg
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 3) decay_margin))
      extension_norm_le_shiftedRadialBound
      (FixedErrorExplicitRiemannVonMangoldtSourceInput.toCumulativeWindowCountingEstimate_cutoff_eq_two_of_cutoff_eq_two
        sourceData.toInput sourceData.toInput_cutoff)
      (BellottiWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
HSW split data from the preferred exact-source package and the preferred
cutoff-2 exact-norm clipped p-series estimate.  The exact-source package
supplies cutoff `2` and growth `2`, so the p-series margin is the single field
`3 < decayExponent`.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSplitPSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
    {validFrom : Real}
    (sourceData :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData validFrom)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decay_margin : (3 : Real) < decayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f (norm z)) :
    RiemannWeilHasanalizadeShenWongSplitPSeriesData validFrom :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      sourceData.toInput system constant decayExponent constant_nonneg
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 3) decay_margin))
      extension_norm_le_clippedRadialBound
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
HSW split data from the preferred exact-source package and a cutoff-2 exact-norm
shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSplitPSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    {validFrom : Real}
    (sourceData :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData validFrom)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decay_margin : (3 : Real) < decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent)) :
    RiemannWeilHasanalizadeShenWongSplitPSeriesData validFrom :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData.toInput system constant decayExponent constant_nonneg
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 3) decay_margin))
      extension_norm_le_shiftedRadialBound
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
HSW split data from the exact source's cumulative count and a cutoff-2
exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSplitPSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
    {validFrom : Real}
    (sourceData :
      HasanalizadeShenWongExactHeightWindowConjugationSourceData validFrom)
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decay_margin : (3 : Real) < decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent)) :
    RiemannWeilHasanalizadeShenWongSplitPSeriesData validFrom :=
  RiemannWeilFixedErrorPublishedCountingSplitPSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      sourceData.toInput system constant decayExponent constant_nonneg
      (le_of_lt (lt_trans (by norm_num : (0 : Real) < 3) decay_margin))
      extension_norm_le_shiftedRadialBound
      (FixedErrorExplicitRiemannVonMangoldtSourceInput.toCumulativeWindowCountingEstimate_cutoff_eq_two_of_cutoff_eq_two
        sourceData.toInput sourceData.toInput_cutoff)
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
Most decomposed concrete endpoint using fixed published counting, split radial
p-series estimates, source Guinand-Weil formula data, support-density
positivity, and admissible coefficient-test Li identities.
-/
structure RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  admissible : SchwartzLineTestFunction -> Prop
  restrictedToLi :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData admissible liData
  residual_nonneg_on_admissible :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f
  denseCore :
    SupportRestrictedFormulaResidualDenseCore
      (restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
        residual_nonneg_on_admissible)

namespace RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly

/--
Build the split-radial coefficient-test endpoint from Li coefficient identities
stated against the source Guinand-Weil residual side.
-/
noncomputable def ofSourceResidualCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficientScale : Nat -> Real)
    (coefficientScale_nonneg :
      forall n : Nat, 0 < n -> 0 <= coefficientScale n)
    (coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            coefficientScale n *
              sourcePackage.sourceData.sideData.sourceResidualSide
                (coefficientTest n))
    (residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientTest coefficientTest_admissible coefficientScale
          coefficientScale_nonneg coefficient_eq_scaled_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              residual_nonneg_on_admissible)) :
    RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  admissible := admissible
  restrictedToLi :=
    SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientTest coefficientTest_admissible coefficientScale
      coefficientScale_nonneg coefficient_eq_scaled_sourceResidual
  residual_nonneg_on_admissible := residual_nonneg_on_admissible
  denseCore := denseCore

/--
Build the split-radial coefficient-test endpoint from source-residual
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficientScale : Nat -> Real)
    (coefficientScale_nonneg :
      forall n : Nat, 0 < n -> 0 <= coefficientScale n)
    (coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            coefficientScale n *
              sourcePackage.sourceData.sideData.sourceResidualSide
                (coefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientTest coefficientTest_admissible coefficientScale
          coefficientScale_nonneg coefficient_eq_scaled_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentities zeroData sourcePackage
    normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the split-radial coefficient-test endpoint from unit-scale source-residual
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCoefficientTestsAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficient_eq_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            sourcePackage.sourceData.sideData.sourceResidualSide
              (coefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCoefficientBridge.ofSourceCoefficientTests
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientTest coefficientTest_admissible
          coefficient_eq_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentitiesAndNonnegativity zeroData sourcePackage
    normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible (fun _ => 1)
    (by
      intro _ _
      norm_num)
    (by
      intro n hn
      simp [coefficient_eq_sourceResidual n hn])
    source_residual_nonneg_on_admissible
    (by
      simpa [SupportRestrictedFormulaResidualToLiCoefficientBridge.ofSourceCoefficientTests]
        using denseCore)

/-- Convert to the existing support-density coefficient source-formula endpoint. -/
noncomputable def toSupportDensityCoefficientSourceFormulaAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := assembly.zeroData.toFixedErrorPublishedCountingAntitonePSeriesData
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  admissible := assembly.admissible
  restrictedToLi := assembly.restrictedToLi
  residual_nonneg_on_admissible :=
    assembly.residual_nonneg_on_admissible
  denseCore := assembly.denseCore

/-- The split-radial coefficient-test residual side is the source residual side. -/
theorem formulaResidualSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensityCoefficientSourceFormulaAnalyticAssembly
    |>.formulaResidualSide_eq_sourceResidualSide f

/-- The split-radial coefficient-test zero side is the source residual side. -/
theorem zeroSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensityCoefficientSourceFormulaAnalyticAssembly
    |>.zeroSide_eq_sourceResidualSide f

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSupportDensityCoefficientSourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The split-radial endpoint proves universal local RH, conditionally. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSupportDensityCoefficientSourceFormulaAnalyticAssembly.RHOn_univ

/-- The split-radial endpoint proves the project RH statement, conditionally. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSupportDensityCoefficientSourceFormulaAnalyticAssembly.RHStatement

/-- The split-radial endpoint proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toSupportDensityCoefficientSourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly

/--
Most decomposed concrete endpoint using fixed published counting, split radial
p-series estimates, source Guinand-Weil formula data, support-density
positivity, and cutoff-2 admissible coefficient-test Li identities.
-/
structure RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
      validFrom publishedErrorTerm
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  admissible : SchwartzLineTestFunction -> Prop
  restrictedToLi :
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
      normalizationBridge.toFormulaIdentityData admissible liData
  residual_nonneg_on_admissible :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f
  denseCore :
    SupportRestrictedFormulaResidualDenseCore
      (restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
        residual_nonneg_on_admissible)

namespace RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly

/--
Build the cutoff-2 split-radial endpoint from coefficient `1` and tail
identities stated against the source Guinand-Weil residual side.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale *
          sourcePackage.sourceData.sideData.sourceResidualSide
            coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tailCoefficientScale : Nat -> Real)
    (tailCoefficientScale_nonneg :
      forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n)
    (tail_coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            tailCoefficientScale n *
              sourcePackage.sourceData.sideData.sourceResidualSide
                (tailCoefficientTest n))
    (residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientOneTest coefficientOneTest_admissible
          coefficientOneScale coefficientOneScale_nonneg
          coefficient_one_eq_scaled_sourceResidual
          tailCoefficientTest tailCoefficientTest_admissible
          tailCoefficientScale tailCoefficientScale_nonneg
          tail_coefficient_eq_scaled_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              residual_nonneg_on_admissible)) :
    RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  admissible := admissible
  restrictedToLi :=
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientOneTest coefficientOneTest_admissible
      coefficientOneScale coefficientOneScale_nonneg
      coefficient_one_eq_scaled_sourceResidual
      tailCoefficientTest tailCoefficientTest_admissible
      tailCoefficientScale tailCoefficientScale_nonneg
      tail_coefficient_eq_scaled_sourceResidual
  residual_nonneg_on_admissible := residual_nonneg_on_admissible
  denseCore := denseCore

/--
Build the cutoff-2 split-radial endpoint from source-residual coefficient
identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale *
          sourcePackage.sourceData.sideData.sourceResidualSide
            coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tailCoefficientScale : Nat -> Real)
    (tailCoefficientScale_nonneg :
      forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n)
    (tail_coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            tailCoefficientScale n *
              sourcePackage.sourceData.sideData.sourceResidualSide
                (tailCoefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientOneTest coefficientOneTest_admissible
          coefficientOneScale coefficientOneScale_nonneg
          coefficient_one_eq_scaled_sourceResidual
          tailCoefficientTest tailCoefficientTest_admissible
          tailCoefficientScale tailCoefficientScale_nonneg
          tail_coefficient_eq_scaled_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentities zeroData sourcePackage
    normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the cutoff-2 split-radial endpoint from unit-scale source-residual
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientTestsAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingSplitPSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficient_one_eq_sourceResidual :
      liData.coefficient 1 =
        sourcePackage.sourceData.sideData.sourceResidualSide
          coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tail_coefficient_eq_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            sourcePackage.sourceData.sideData.sourceResidualSide
              (tailCoefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofSourceCoefficientTests
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientOneTest coefficientOneTest_admissible
          coefficient_one_eq_sourceResidual
          tailCoefficientTest tailCoefficientTest_admissible
          tail_coefficient_eq_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity zeroData
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible 1
    (by norm_num)
    (by
      simp [coefficient_one_eq_sourceResidual])
    tailCoefficientTest tailCoefficientTest_admissible (fun _ => 1)
    (by
      intro _ _
      norm_num)
    (by
      intro n hn
      simp [tail_coefficient_eq_sourceResidual n hn])
    source_residual_nonneg_on_admissible
    (by
      simpa [SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofSourceCoefficientTests]
        using denseCore)

/-- Convert to the support-density cutoff-2 coefficient source-formula endpoint. -/
noncomputable def toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := assembly.zeroData.toFixedErrorPublishedCountingAntitonePSeriesData
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  admissible := assembly.admissible
  restrictedToLi := assembly.restrictedToLi
  residual_nonneg_on_admissible :=
    assembly.residual_nonneg_on_admissible
  denseCore := assembly.denseCore

/-- The cutoff-2 split-radial residual side is the source residual side. -/
theorem formulaResidualSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    |>.formulaResidualSide_eq_sourceResidualSide f

/-- The cutoff-2 split-radial zero side is the source residual side. -/
theorem zeroSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    |>.zeroSide_eq_sourceResidualSide f

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The cutoff-2 split-radial endpoint proves universal local RH, conditionally. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.RHOn_univ

/-- The cutoff-2 split-radial endpoint proves the project RH statement, conditionally. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.RHStatement

/-- The cutoff-2 split-radial endpoint proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly

/--
Bellotti-Wong specialization of the most decomposed split-radial concrete
endpoint.
-/
abbrev RiemannWeilBellottiWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization of the most decomposed split-radial
concrete endpoint, with the validity threshold still explicit.
-/
abbrev RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong specialization of the most decomposed split-radial concrete
endpoint with cutoff-2 coefficient tests exposed.
-/
abbrev RiemannWeilBellottiWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization of the most decomposed split-radial
concrete endpoint with cutoff-2 coefficient tests exposed.
-/
abbrev RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
    validFrom hasanalizadeShenWongErrorTerm

namespace RiemannWeilBellottiWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly

/--
Build the Bellotti-Wong split-radial coefficient-test endpoint from unit-scale
source-residual coefficient identities and source-residual nonnegativity.
-/
noncomputable def ofSourceResidualCoefficientTestsAndNonnegativity
    (zeroData : RiemannWeilBellottiWongSplitPSeriesData)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficient_eq_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            sourcePackage.sourceData.sideData.sourceResidualSide
              (coefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCoefficientBridge.ofSourceCoefficientTests
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientTest coefficientTest_admissible
          coefficient_eq_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilBellottiWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly.ofSourceResidualCoefficientTestsAndNonnegativity
      zeroData sourcePackage
      normalizationBridge liData admissible coefficientTest
      coefficientTest_admissible coefficient_eq_sourceResidual
      source_residual_nonneg_on_admissible denseCore

end RiemannWeilBellottiWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly

namespace RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly

/--
Build the Hasanalizade-Shen-Wong split-radial coefficient-test endpoint from
unit-scale source-residual coefficient identities and source-residual
nonnegativity.
-/
noncomputable def ofSourceResidualCoefficientTestsAndNonnegativity
    {validFrom : Real}
    (zeroData : RiemannWeilHasanalizadeShenWongSplitPSeriesData validFrom)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficient_eq_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            sourcePackage.sourceData.sideData.sourceResidualSide
              (coefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCoefficientBridge.ofSourceCoefficientTests
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientTest coefficientTest_admissible
          coefficient_eq_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly
      validFrom :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCoefficientSourceFormulaAssembly.ofSourceResidualCoefficientTestsAndNonnegativity
      zeroData sourcePackage
      normalizationBridge liData admissible coefficientTest
      coefficientTest_admissible coefficient_eq_sourceResidual
      source_residual_nonneg_on_admissible denseCore

end RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCoefficientSourceFormulaAssembly

namespace RiemannWeilBellottiWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly

/--
Build the Bellotti-Wong cutoff-2 split-radial endpoint from unit-scale
source-residual coefficient identities and source-residual nonnegativity.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientTestsAndNonnegativity
    (zeroData : RiemannWeilBellottiWongSplitPSeriesData)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficient_one_eq_sourceResidual :
      liData.coefficient 1 =
        sourcePackage.sourceData.sideData.sourceResidualSide
          coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tail_coefficient_eq_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            sourcePackage.sourceData.sideData.sourceResidualSide
              (tailCoefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofSourceCoefficientTests
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientOneTest coefficientOneTest_admissible
          coefficient_one_eq_sourceResidual
          tailCoefficientTest tailCoefficientTest_admissible
          tail_coefficient_eq_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilBellottiWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly.ofSourceResidualCutoffTwoCoefficientTestsAndNonnegativity
      zeroData
      sourcePackage normalizationBridge liData admissible coefficientOneTest
      coefficientOneTest_admissible coefficient_one_eq_sourceResidual
      tailCoefficientTest tailCoefficientTest_admissible
      tail_coefficient_eq_sourceResidual source_residual_nonneg_on_admissible
      denseCore

end RiemannWeilBellottiWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly

namespace RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly

/--
Build the Hasanalizade-Shen-Wong cutoff-2 split-radial endpoint from unit-scale
source-residual coefficient identities and source-residual nonnegativity.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientTestsAndNonnegativity
    {validFrom : Real}
    (zeroData : RiemannWeilHasanalizadeShenWongSplitPSeriesData validFrom)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficient_one_eq_sourceResidual :
      liData.coefficient 1 =
        sourcePackage.sourceData.sideData.sourceResidualSide
          coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tail_coefficient_eq_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            sourcePackage.sourceData.sideData.sourceResidualSide
              (tailCoefficientTest n))
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofSourceCoefficientTests
          sourcePackage.sourceData.sideData.sourceResidualSide
          (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
          coefficientOneTest coefficientOneTest_admissible
          coefficient_one_eq_sourceResidual
          tailCoefficientTest tailCoefficientTest_admissible
          tail_coefficient_eq_sourceResidual)
            |>.toSupportRestrictedFormulaResidualPositivityData
              (normalizationBridge.residual_nonneg_on_admissible_of_source
                admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly
      validFrom :=
  RiemannWeilFixedErrorSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly.ofSourceResidualCutoffTwoCoefficientTestsAndNonnegativity
      zeroData
      sourcePackage normalizationBridge liData admissible coefficientOneTest
      coefficientOneTest_admissible coefficient_one_eq_sourceResidual
      tailCoefficientTest tailCoefficientTest_admissible
      tail_coefficient_eq_sourceResidual source_residual_nonneg_on_admissible
      denseCore

end RiemannWeilHasanalizadeShenWongSplitRadialSupportDensityCutoffTwoCoefficientSourceFormulaAssembly

end

end RiemannHypothesisProject
