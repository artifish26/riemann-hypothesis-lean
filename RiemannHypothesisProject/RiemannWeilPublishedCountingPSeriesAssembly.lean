import RiemannHypothesisProject.RiemannWeilEventualPSeriesAnalyticAssembly
import RiemannHypothesisProject.RiemannWeilAntitoneRadialSplitPSeriesBridge
import RiemannHypothesisProject.RiemannVonMangoldtPublishedBounds

/-!
# Published-counting p-series assembly

This file connects the published `N(T)` counting target to the antitone radial
p-series route.

The hard analytic fields remain explicit:

* instantiate a Bellotti-Wong or Hasanalizade-Shen-Wong style published
  Riemann-von-Mangoldt source;
* prove the antitone radial envelope estimate for the chosen complex extension;
* supply the Guinand-Weil formula package;
* supply the residual-to-Li bridge and residual nonnegativity.

Once those fields are filled, Lean assembles the existing eventual p-series
analytic endpoint and its RH consequences.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion

noncomputable section

/--
Zero-data package for the preferred route that uses a published explicit
Riemann-von-Mangoldt estimate for counting and an antitone radial p-series
estimate for the extension envelope.
-/
structure RiemannWeilPublishedCountingAntitonePSeriesData where
  publishedCounting : PublishedExplicitRiemannVonMangoldtSource
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

namespace RiemannWeilPublishedCountingAntitonePSeriesData

/-- The closed-ball first-entry shell count obtained from the published source. -/
noncomputable def counting
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  data.publishedCounting.toPolynomialZeroCountingEstimate

/-- The cumulative closed-ball count obtained from the published source. -/
noncomputable def cumulativeCounting
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  data.publishedCounting.toCumulativeWindowCountingEstimate

/-- The induced shell-counting cutoff is the published-source cutoff. -/
theorem counting_cutoff_eq_source
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    data.counting.cutoff = data.publishedCounting.cutoff := by
  rfl

/-- The induced shell-counting growth exponent is the published-source growth. -/
theorem counting_growth_eq_source
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    data.counting.growth = data.publishedCounting.growth := by
  rfl

/--
Use a split finite-prefix/tail radial p-series package as published-counting
zero data when its counting estimate is the one induced by the published
Riemann-von-Mangoldt source.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate) :
    RiemannWeilPublishedCountingAntitonePSeriesData where
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
Use an automatic-prefix radial target as published-counting zero data when its
counting estimate is the one induced by the published Riemann-von-Mangoldt
source.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate) :
    RiemannWeilPublishedCountingAntitonePSeriesData :=
  ofSplitPSeriesEnvelopeData publishedCounting
    target.toSplitPSeriesEnvelopeData
    (by
      change target.counting =
        publishedCounting.toPolynomialZeroCountingEstimate
      exact counting_eq)

/--
Build published-counting zero data directly from a global exact-norm clipped
p-series decay theorem for the extension.  The cutoff is the one induced by the
published counting package.
-/
noncomputable def ofClippedPSeriesRadialMajorantExactNorm
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
    RiemannWeilPublishedCountingAntitonePSeriesData :=
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
Cutoff-2 closed-ball published-counting zero data from a global exact-norm
clipped p-series decay theorem.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNorm
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
    RiemannWeilPublishedCountingAntitonePSeriesData :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNorm
      system sourceConstant zeroConstant decayExponent strongDecayExponent
      sourceConstant_nonneg sourceConstant_le_zeroConstant
      strongDecayExponent_nonneg extension_norm_le_clippedRadialBound
      hdecay_le_strong publishedCounting.toPolynomialZeroCountingEstimate
      counting_cutoff_eq growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball published-counting zero data from a global exact-norm
shifted-radius p-series decay theorem.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormOfShiftedRadius
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
    RiemannWeilPublishedCountingAntitonePSeriesData :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormOfShiftedRadius
      system sourceConstant zeroConstant decayExponent strongDecayExponent
      sourceConstant_nonneg sourceConstant_le_zeroConstant
      strongDecayExponent_nonneg extension_norm_le_shiftedRadialBound
      hdecay_le_strong publishedCounting.toPolynomialZeroCountingEstimate
      counting_cutoff_eq growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball published-counting zero data from a global exact-norm
clipped p-series decay theorem, with matching source/package constant and
exponent.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
    RiemannWeilPublishedCountingAntitonePSeriesData :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_clippedRadialBound
      publishedCounting.toPolynomialZeroCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Cutoff-2 closed-ball published-counting zero data from a global exact-norm
shifted-radius p-series decay theorem, with matching source/package constant
and exponent.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
    RiemannWeilPublishedCountingAntitonePSeriesData :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_shiftedRadialBound
      publishedCounting.toPolynomialZeroCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Published-counting zero data from the source-shaped cumulative count and a
cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
    RiemannWeilPublishedCountingAntitonePSeriesData :=
  ofAutomaticPrefixRadialTarget publishedCounting
    (RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
      system constant decayExponent constant_nonneg decayExponent_nonneg
      extension_norm_le_shiftedRadialBound
      publishedCounting.toCumulativeWindowCountingEstimate counting_cutoff_eq
      growth_add_one_lt_decay)
    rfl

/--
Convert published counting plus antitone radial envelope estimates into the
existing antitone radial p-series zero-data package.
-/
noncomputable def toAntitoneRadialPSeriesEnvelopeData
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    RiemannWeilAntitoneRadialPSeriesEnvelopeData where
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
  counting := data.counting
  counting_cutoff_eq := data.counting_cutoff_eq
  growth_add_one_lt_decay := data.growth_add_one_lt_decay

/-- The eventual p-series zero-data package produced by the published-counting route. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  data.toAntitoneRadialPSeriesEnvelopeData.toEventualPSeriesEnvelopeZeroData

/-- The zero side produced by published counting and antitone radial decay. -/
noncomputable def zeroSide
    (data : RiemannWeilPublishedCountingAntitonePSeriesData) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

/-- The induced zero side uses the candidate Riemann-Weil extension weight. -/
theorem zeroSide_weight
    (data : RiemannWeilPublishedCountingAntitonePSeriesData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide_weight f rho

end RiemannWeilPublishedCountingAntitonePSeriesData

/--
End-to-end assembly for the preferred source-guided route:
published zero counting, antitone radial p-series envelope, Guinand-Weil
formula, residual-to-Li coefficient bridge, and residual nonnegativity.
-/
structure RiemannWeilPublishedCountingAnalyticAssembly where
  zeroData : RiemannWeilPublishedCountingAntitonePSeriesData
  formulaPackage :
    GuinandWeilProjectFormulaPackage
      zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilPublishedCountingAnalyticAssembly

/--
Build the published-counting analytic assembly directly from split
finite-prefix/tail p-series data whose counting estimate matches the published
source. This keeps the split p-series obligation visible at the final assembly
boundary.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilPublishedCountingAnalyticAssembly where
  zeroData :=
    RiemannWeilPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the published-counting analytic assembly directly from the
automatic-prefix radial p-series target.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        ((RiemannWeilPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilPublishedCountingAnalyticAssembly where
  zeroData :=
    RiemannWeilPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the published-counting analytic assembly directly from the preferred
cutoff-2 exact-norm clipped p-series estimate, with matching source/package
constant and exponent.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
        ((RiemannWeilPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
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
    RiemannWeilPublishedCountingAnalyticAssembly where
  zeroData :=
    RiemannWeilPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
      publishedCounting system constant decayExponent constant_nonneg
      decayExponent_nonneg extension_norm_le_clippedRadialBound
      counting_cutoff_eq growth_add_one_lt_decay
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the published-counting analytic assembly directly from the preferred
cutoff-2 exact-norm shifted-radius p-series estimate, with matching
source/package constant and exponent.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    (publishedCounting : PublishedExplicitRiemannVonMangoldtSource)
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
        ((RiemannWeilPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    RiemannWeilPublishedCountingAnalyticAssembly where
  zeroData :=
    RiemannWeilPublishedCountingAntitonePSeriesData.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      publishedCounting system constant decayExponent constant_nonneg
      decayExponent_nonneg extension_norm_le_shiftedRadialBound
      counting_cutoff_eq growth_add_one_lt_decay
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/-- Forget the published-counting origin and use the generic antitone radial assembly. -/
noncomputable def toAntitoneRadialAnalyticAssembly
    (assembly : RiemannWeilPublishedCountingAnalyticAssembly) :
    RiemannWeilAntitoneRadialAnalyticAssembly where
  zeroPackage := assembly.zeroData.toAntitoneRadialPSeriesEnvelopeData
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Convert to the generic eventual p-series analytic assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly : RiemannWeilPublishedCountingAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly :=
  assembly.toAntitoneRadialAnalyticAssembly.toEventualPSeriesAnalyticAssembly

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly : RiemannWeilPublishedCountingAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The preferred source-guided assembly proves universal local RH, conditionally. -/
theorem RHOn_univ
    (assembly : RiemannWeilPublishedCountingAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toEventualPSeriesAnalyticAssembly.RHOn_univ

/-- The preferred source-guided assembly proves the project RH statement, conditionally. -/
theorem RHStatement
    (assembly : RiemannWeilPublishedCountingAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toEventualPSeriesAnalyticAssembly.RHStatement

/-- The preferred source-guided assembly proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    (assembly : RiemannWeilPublishedCountingAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toEventualPSeriesAnalyticAssembly.mathlib_RH

end RiemannWeilPublishedCountingAnalyticAssembly

end

end RiemannHypothesisProject
