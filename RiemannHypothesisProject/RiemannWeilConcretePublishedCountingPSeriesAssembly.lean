import RiemannHypothesisProject.RiemannWeilPublishedCountingPSeriesAssembly
import RiemannHypothesisProject.RiemannWeilAntitoneRadialSplitPSeriesBridge
import RiemannHypothesisProject.RiemannVonMangoldtConcretePublishedSources

/-!
# Concrete published-counting p-series assembly

This file connects the concrete published `N(T)` source inputs to the
published-counting p-series assembly.

The generic assembly consumes `PublishedExplicitRiemannVonMangoldtSource`.
Here we let future work start one level closer to the papers, from a fixed
published error term such as Bellotti-Wong or Hasanalizade-Shen-Wong.  The
remaining analytic obligations are still explicit fields of the fixed-error
source input and the radial/formula/positivity packages.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion

noncomputable section

/--
Concrete source-guided zero-data package for a fixed published `N(T)` error
term.

This starts with `FixedErrorExplicitRiemannVonMangoldtSourceInput`, converts it
to the generic published source, and then reuses the antitone radial p-series
route.
-/
structure RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
  radialBound_lowerBound_le_eventualPSeries :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      radialBound f (closedBallZeroArgumentShellLowerBound n) <=
        SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
          cutoff prefixBound zeroConstant decayExponent f n
  counting_cutoff_eq :
    publishedCounting.toPolynomialZeroCountingEstimate.cutoff = cutoff
  growth_add_one_lt_decay :
    publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
      decayExponent

namespace RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData

/-- The generic published source obtained from the fixed-error input. -/
noncomputable def publishedSource
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    PublishedExplicitRiemannVonMangoldtSource :=
  data.publishedCounting.toPublishedExplicitRiemannVonMangoldtSource

/-- The closed-ball first-entry shell count obtained from the fixed-error input. -/
noncomputable def counting
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  data.publishedCounting.toPolynomialZeroCountingEstimate

/-- The cumulative closed-ball count obtained from the fixed-error input. -/
noncomputable def cumulativeCounting
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  data.publishedCounting.toCumulativeWindowCountingEstimate

/-- The induced shell-counting cutoff is the fixed-error source cutoff. -/
theorem counting_cutoff_eq_source
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    data.counting.cutoff = data.publishedCounting.cutoff := by
  rfl

/-- The induced shell-counting growth exponent is the fixed-error source growth. -/
theorem counting_growth_eq_source
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    data.counting.growth = data.publishedCounting.growth := by
  rfl

/--
Use a split finite-prefix/tail radial p-series package as fixed-error
published-counting zero data when its counting estimate is the one induced by
the fixed published source input.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate) :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
  radialBound_lowerBound_le_eventualPSeries :=
    splitData.radialBound_lowerBound_le_eventualPSeries
  counting_cutoff_eq := by
    rw [← counting_eq]
    exact splitData.counting_cutoff_eq
  growth_add_one_lt_decay := by
    rw [← counting_eq]
    exact splitData.growth_add_one_lt_decay

/--
Use an automatic-prefix radial target as fixed-error published-counting zero
data when its counting estimate is the one induced by the fixed published
source input.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate) :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm :=
  ofSplitPSeriesEnvelopeData publishedCounting
    target.toSplitPSeriesEnvelopeData
    (by
      change target.counting =
        publishedCounting.toPolynomialZeroCountingEstimate
      exact counting_eq)

/--
Build fixed-error published-counting zero data directly from a global
exact-norm clipped p-series decay theorem for the extension.  The cutoff is the
one induced by the fixed-error counting package.
-/
noncomputable def ofClippedPSeriesRadialMajorantExactNorm
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
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound
          (m + publishedCounting.toPolynomialZeroCountingEstimate.cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (growth_add_one_lt_decay :
      publishedCounting.toPolynomialZeroCountingEstimate.growth + 1 <
        decayExponent) :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofClippedPSeriesRadialMajorantExactNorm
      system publishedCounting.toPolynomialZeroCountingEstimate.cutoff
      sourceConstant zeroConstant decayExponent strongDecayExponent
      sourceConstant_nonneg sourceConstant_le_zeroConstant
      strongDecayExponent_nonneg extension_norm_le_clippedRadialBound
      tail_radius_le_lowerBound hdecay_le_strong
      publishedCounting.toPolynomialZeroCountingEstimate rfl
      growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball fixed-error zero data from a global exact-norm clipped
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
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
Cutoff-2 closed-ball fixed-error zero data from a global exact-norm
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
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
Cutoff-2 closed-ball fixed-error zero data from a global exact-norm clipped
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
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_clippedRadialBound
      publishedCounting.toPolynomialZeroCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball fixed-error zero data from a global exact-norm
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
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_shiftedRadialBound
      publishedCounting.toPolynomialZeroCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Fixed-error zero data from the source-shaped cumulative count and a cutoff-2
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
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_shiftedRadialBound
      publishedCounting.toCumulativeWindowCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/-- Convert fixed-error published counting to the generic published-counting package. -/
noncomputable def toPublishedCountingAntitonePSeriesData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    RiemannWeilPublishedCountingAntitonePSeriesData where
  publishedCounting := data.publishedSource
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
  radialBound_lowerBound_le_eventualPSeries :=
    data.radialBound_lowerBound_le_eventualPSeries
  counting_cutoff_eq := data.counting_cutoff_eq
  growth_add_one_lt_decay := data.growth_add_one_lt_decay

/-- The eventual p-series zero-data package produced from a fixed-error published source. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  data.toPublishedCountingAntitonePSeriesData.toEventualPSeriesEnvelopeZeroData

/-- The zero side produced from fixed-error published counting and antitone radial decay. -/
noncomputable def zeroSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

/-- The fixed-error published-counting zero side uses the candidate extension weight. -/
theorem zeroSide_weight
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (data :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide_weight f rho

end RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData

/-- Bellotti-Wong specialization of the concrete published-counting zero-data package. -/
abbrev RiemannWeilBellottiWongAntitonePSeriesData :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization of the concrete published-counting
zero-data package, with the validity threshold still explicit.
-/
abbrev RiemannWeilHasanalizadeShenWongAntitonePSeriesData
    (validFrom : Real) :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
    validFrom hasanalizadeShenWongErrorTerm

/--
End-to-end assembly for a fixed published error term:
concrete published counting, antitone radial p-series envelope, Guinand-Weil
formula, residual-to-Li coefficient bridge, and residual nonnegativity.
-/
structure RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm
  formulaPackage :
    GuinandWeilProjectFormulaPackage
      zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilFixedErrorPublishedCountingAnalyticAssembly

/--
Build the fixed-error analytic assembly directly from split finite-prefix/tail
p-series data whose counting estimate matches the fixed published source
input.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the fixed-error analytic assembly directly from the automatic-prefix
radial p-series target.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the fixed-error analytic assembly directly from the preferred cutoff-2
exact-norm clipped p-series estimate, with matching source/package constant
and exponent.
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
        decayExponent)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
          publishedCounting system constant decayExponent constant_nonneg
          decayExponent_nonneg extension_norm_le_clippedRadialBound
          counting_cutoff_eq growth_add_one_lt_decay)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      publishedCounting system constant decayExponent constant_nonneg
      decayExponent_nonneg extension_norm_le_clippedRadialBound
      counting_cutoff_eq growth_add_one_lt_decay
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the fixed-error analytic assembly directly from the preferred cutoff-2
exact-norm shifted-radius p-series estimate, with matching source/package
constant and exponent.
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
        decayExponent)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
          publishedCounting system constant decayExponent constant_nonneg
          decayExponent_nonneg extension_norm_le_shiftedRadialBound
          counting_cutoff_eq growth_add_one_lt_decay)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      publishedCounting system constant decayExponent constant_nonneg
      decayExponent_nonneg extension_norm_le_shiftedRadialBound
      counting_cutoff_eq growth_add_one_lt_decay
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/-- Forget the fixed-error origin and use the generic published-counting assembly. -/
noncomputable def toPublishedCountingAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilPublishedCountingAnalyticAssembly where
  zeroData := assembly.zeroData.toPublishedCountingAntitonePSeriesData
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toPublishedCountingAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The concrete source-guided assembly proves universal local RH, conditionally. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toPublishedCountingAnalyticAssembly.RHOn_univ

/-- The concrete source-guided assembly proves the project RH statement, conditionally. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toPublishedCountingAnalyticAssembly.RHStatement

/-- The concrete source-guided assembly proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toPublishedCountingAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorPublishedCountingAnalyticAssembly

/-- Bellotti-Wong specialization of the concrete end-to-end assembly. -/
abbrev RiemannWeilBellottiWongAnalyticAssembly :=
  RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization of the concrete end-to-end assembly,
with the validity threshold still explicit.
-/
abbrev RiemannWeilHasanalizadeShenWongAnalyticAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorPublishedCountingAnalyticAssembly
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong zero data from the preferred exact-source package and the
preferred cutoff-2 exact-norm clipped p-series estimate.  The exact-source
package supplies cutoff `2` and growth `2`, so the p-series margin is the
single field `3 < decayExponent`.
-/
noncomputable def RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
    RiemannWeilBellottiWongAntitonePSeriesData :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      sourceData.toInput system constant decayExponent constant_nonneg
      (by linarith : 0 <= decayExponent)
      extension_norm_le_clippedRadialBound
      (BellottiWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (BellottiWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
Bellotti-Wong zero data from the preferred exact-source package and a
cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    RiemannWeilBellottiWongAntitonePSeriesData :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData.toInput system constant decayExponent constant_nonneg
      (by linarith : 0 <= decayExponent)
      extension_norm_le_shiftedRadialBound
      (BellottiWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (BellottiWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
Bellotti-Wong zero data from the exact source's cumulative count and a
cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
    RiemannWeilBellottiWongAntitonePSeriesData :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      sourceData.toInput system constant decayExponent constant_nonneg
      (by linarith : 0 <= decayExponent)
      extension_norm_le_shiftedRadialBound
      (FixedErrorExplicitRiemannVonMangoldtSourceInput.toCumulativeWindowCountingEstimate_cutoff_eq_two_of_cutoff_eq_two
        sourceData.toInput sourceData.toInput_cutoff)
      (BellottiWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
HSW zero data from the preferred exact-source package and the preferred
cutoff-2 exact-norm clipped p-series estimate.  The exact-source package
supplies cutoff `2` and growth `2`, so the p-series margin is the single field
`3 < decayExponent`.
-/
noncomputable def RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData validFrom :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      sourceData.toInput system constant decayExponent constant_nonneg
      (by linarith : 0 <= decayExponent)
      extension_norm_le_clippedRadialBound
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
HSW zero data from the preferred exact-source package and a cutoff-2 exact-norm
shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData validFrom :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData.toInput system constant decayExponent constant_nonneg
      (by linarith : 0 <= decayExponent)
      extension_norm_le_shiftedRadialBound
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.toPolynomialZeroCountingEstimate_cutoff
        sourceData)
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
HSW zero data from the exact source's cumulative count and a cutoff-2
exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData validFrom :=
  RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      sourceData.toInput system constant decayExponent constant_nonneg
      (by linarith : 0 <= decayExponent)
      extension_norm_le_shiftedRadialBound
      (FixedErrorExplicitRiemannVonMangoldtSourceInput.toCumulativeWindowCountingEstimate_cutoff_eq_two_of_cutoff_eq_two
        sourceData.toInput sourceData.toInput_cutoff)
      (HasanalizadeShenWongExactHeightWindowConjugationSourceData.growth_add_one_lt_decay_of_three_lt
        sourceData decay_margin)

/--
Bellotti-Wong final analytic assembly from the preferred exact-source package,
the preferred cutoff-2 exact-norm clipped p-series estimate, and the remaining
formula/positivity fields.
-/
noncomputable def RiemannWeilBellottiWongAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
            constant decayExponent f (norm z))
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilBellottiWongAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_clippedRadialBound
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Bellotti-Wong final analytic assembly from the preferred exact-source package,
a cutoff-2 exact-norm shifted-radius p-series estimate, and the remaining
formula/positivity fields.
-/
noncomputable def RiemannWeilBellottiWongAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilBellottiWongAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Bellotti-Wong final analytic assembly from the exact source's cumulative
count, a cutoff-2 exact-norm shifted-radius p-series estimate, and the
remaining formula/positivity fields.
-/
noncomputable def RiemannWeilBellottiWongAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilBellottiWongAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
HSW final analytic assembly from the preferred exact-source package, the
preferred cutoff-2 exact-norm clipped p-series estimate, and the remaining
formula/positivity fields.
-/
noncomputable def RiemannWeilHasanalizadeShenWongAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
            constant decayExponent f (norm z))
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilHasanalizadeShenWongAnalyticAssembly validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_clippedRadialBound
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
HSW final analytic assembly from the preferred exact-source package, a
cutoff-2 exact-norm shifted-radius p-series estimate, and the remaining
formula/positivity fields.
-/
noncomputable def RiemannWeilHasanalizadeShenWongAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilHasanalizadeShenWongAnalyticAssembly validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
HSW final analytic assembly from the exact source's cumulative count, a
cutoff-2 exact-norm shifted-radius p-series estimate, and the remaining
formula/positivity fields.
-/
noncomputable def RiemannWeilHasanalizadeShenWongAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilHasanalizadeShenWongAnalyticAssembly validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

end

end RiemannHypothesisProject
