import RiemannHypothesisProject.RiemannWeilSourceFormulaConcreteAssembly
import RiemannHypothesisProject.LocalizedWeilQuadraticFormTarget
import RiemannHypothesisProject.SupportRestrictedWeilDensityConstructors
import RiemannHypothesisProject.SupportRestrictedLiCoefficientBridge

/-!
# Support-density concrete Riemann-Weil assembly

`RiemannWeilSourceFormulaConcreteAssembly` exposes the source Guinand-Weil
formula and normalization bridge but still asks for full residual
nonnegativity.

This file replaces that all-tests residual nonnegativity field with the
standard density route:

* prove residual nonnegativity on an admissible support-restricted class;
* prove a concrete dense core is contained in that admissible class;
* use the residual continuity obtained from the source Guinand-Weil formula
  package to close the residual-nonnegative locus.

The global positivity theorem is therefore still an explicit analytic
obligation, but it is split into support-restricted positivity, density, and
continuity pieces.

The final section gives an even sharper coefficient-test variant: prove that
the Li coefficients are nonnegative scalar multiples of residuals evaluated at
admissible test functions, and Lean builds the restricted positivity package.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion

noncomputable section

/--
Concrete source-formula assembly whose full residual nonnegativity is obtained
from support-restricted positivity and density.
-/
structure RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData liData
  restrictedData :
    SupportRestrictedFormulaResidualPositivityData
      normalizationBridge.toFormulaIdentityData
  denseCore :
    SupportRestrictedFormulaResidualDenseCore restrictedData

namespace RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly

/--
Build the support-density source-formula assembly from a localized Weil
quadratic-form target. The localized target supplies restricted residual
positivity; the dense-core field remains the explicit density obligation.
-/
noncomputable def ofLocalizedQuadraticFormTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    localizedTarget.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the support-density source-formula assembly directly from split
finite-prefix/tail p-series data whose counting estimate matches the fixed
published source input.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the support-density source-formula assembly directly from split
finite-prefix/tail p-series data and a localized Weil quadratic-form target.
This keeps the split p-series and localized positivity obligations visible at
the same concrete boundary.
-/
noncomputable def ofSplitPSeriesEnvelopeDataAndLocalizedQuadraticFormTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofLocalizedQuadraticFormTarget
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
Build the support-density source-formula assembly directly from an
automatic-prefix radial target whose counting estimate matches the fixed
published source input.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the support-density source-formula assembly directly from an
automatic-prefix radial target and a localized Weil quadratic-form target.
-/
noncomputable def ofAutomaticPrefixRadialTargetAndLocalizedQuadraticFormTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofLocalizedQuadraticFormTarget
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/-- Assemble the project-level Guinand-Weil formula package from source data. -/
noncomputable def formulaPackage
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    GuinandWeilProjectFormulaPackage
      assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide where
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge

/-- Source formula data gives residual continuity for the project-normalized formula. -/
noncomputable def residualContinuityData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilFormulaResidualContinuityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.formulaPackage.residualContinuityData

/-- The support-density assembly's project residual side is the source residual side. -/
theorem formulaResidualSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.formulaData_residualSide_eq_sourceResidualSide f

/-- The support-density assembly's zero side is the source residual side. -/
theorem zeroSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.explicitFormula_sourceResidualSide f

/-- The dense-core route gives the support-restricted density bridge. -/
noncomputable def supportDensityBridge
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SupportRestrictedFormulaResidualDensityBridge assembly.restrictedData :=
  assembly.denseCore.toSupportRestrictedDensityBridgeOfResidualContinuity
    assembly.residualContinuityData

/-- Support-restricted positivity plus density promotes to full residual nonnegativity. -/
theorem residual_nonneg
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    forall f : SchwartzLineTestFunction,
      0 <= assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f :=
  assembly.supportDensityBridge.residual_nonneg

/-- Build the source-formula concrete assembly with full residual nonnegativity supplied by density. -/
noncomputable def toSourceFormulaAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := assembly.zeroData
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/--
The formula residual positivity package obtained through the coefficient-level
residual-to-Li bridge after density has promoted restricted positivity.
-/
noncomputable def formulaResidualDataFromLi
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilFormulaResidualPositivityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.residualToLi.toFormulaResidualPositivityData
    assembly.residual_nonneg

/-- The density bridge itself also yields formula residual positivity data. -/
noncomputable def formulaResidualDataFromDensity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilFormulaResidualPositivityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.supportDensityBridge.toFormulaResidualPositivityData

/-- The support-density source-formula assembly proves universal local RH, conditionally. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSourceFormulaAnalyticAssembly.RHOn_univ

/-- The support-density source-formula assembly proves the project RH statement, conditionally. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSourceFormulaAnalyticAssembly.RHStatement

/-- The support-density source-formula assembly proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toSourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly

/--
Concrete componentwise source-formula assembly whose full residual
nonnegativity is obtained from support-restricted positivity and density.

This is the support-density companion to
`RiemannWeilFixedErrorComponentwiseSourceFormulaAnalyticAssembly`: prime, pole,
and gamma side normalizations remain componentwise, while restricted positivity
is promoted through the dense-core/continuity route before entering the final
p-series formula-residual endpoint.
-/
structure RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
      validFrom publishedErrorTerm
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge
      sourcePackage.sourceData
      zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData liData
  restrictedData :
    SupportRestrictedFormulaResidualPositivityData
      normalizationBridge.toFormulaIdentityData
  denseCore :
    SupportRestrictedFormulaResidualDenseCore restrictedData

namespace RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly

/--
Build the componentwise support-density source-formula assembly from a
localized Weil quadratic-form target. The localized target supplies restricted
residual positivity; the dense-core field remains the explicit density
obligation.
-/
noncomputable def ofLocalizedQuadraticFormTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    localizedTarget.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the localized quadratic-form target used by the componentwise
support-density endpoint from identities stated against the source residual
side.
-/
noncomputable def sourceResidualLocalizedQuadraticFormTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilQuadraticFormTarget normalizationBridge.toFormulaIdentityData :=
  (({
    sourcePackage := sourcePackage
    normalizationBridge := normalizationBridge
  } : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    |>.sourceResidualLocalizedQuadraticFormTarget admissible localQuadraticForm
      localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ)

/--
Build the componentwise support-density endpoint directly from a localized
quadratic-form identity stated against the source residual side.

The equality and nonnegativity hypotheses are source-side analytic inputs; the
constructor transports them through componentwise normalization and leaves the
dense-core promotion as the explicit density obligation.
-/
noncomputable def ofSourceResidualLocalizedQuadraticForm
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((sourceResidualLocalizedQuadraticFormTarget sourcePackage
          normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofLocalizedQuadraticFormTarget zeroData sourcePackage normalizationBridge
    liData residualToLi
    (sourceResidualLocalizedQuadraticFormTarget sourcePackage
      normalizationBridge admissible localQuadraticForm
      localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ)
    denseCore

/--
Build the finite-model target used by the componentwise support-density
endpoint from an identity stated against the source residual side.
-/
noncomputable def sourceResidualFinitePositivityModelTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget
      normalizationBridge.toFormulaIdentityData :=
  (({
    sourcePackage := sourcePackage
    normalizationBridge := normalizationBridge
  } : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    |>.sourceResidualFinitePositivityModelTarget admissible model encode
      encodedQuadratic_eq_sourceResidualSide_on_admissible
      restricted_source_positivity_implies_RHOn_univ)

/--
Build the componentwise support-density endpoint directly from a finite
positive model identity stated against the source residual side.
-/
noncomputable def ofSourceResidualFinitePositivityModel
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((sourceResidualFinitePositivityModelTarget sourcePackage
          normalizationBridge admissible model encode
          encodedQuadratic_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    (sourceResidualFinitePositivityModelTarget sourcePackage
      normalizationBridge admissible model encode
      encodedQuadratic_eq_sourceResidualSide_on_admissible
      restricted_source_positivity_implies_RHOn_univ)
        |>.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the finite-Gram target used by the componentwise support-density endpoint
from an identity stated against the source residual side.
-/
noncomputable def sourceResidualFiniteGramTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData zeroSide)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget
      normalizationBridge.toFormulaIdentityData :=
  (({
    sourcePackage := sourcePackage
    normalizationBridge := normalizationBridge
  } : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    |>.sourceResidualFiniteGramTarget Index Feature feature admissible encode
      finiteGram_eq_sourceResidualSide_on_admissible
      restricted_source_positivity_implies_RHOn_univ)

/--
Build the componentwise support-density endpoint directly from a finite Gram
identity stated against the source residual side.
-/
noncomputable def ofSourceResidualFiniteGram
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((sourceResidualFiniteGramTarget sourcePackage normalizationBridge
          Index Feature feature admissible encode
          finiteGram_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    (sourceResidualFiniteGramTarget sourcePackage normalizationBridge
      Index Feature feature admissible encode
      finiteGram_eq_sourceResidualSide_on_admissible
      restricted_source_positivity_implies_RHOn_univ)
        |>.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the finite-Rayleigh target used by the componentwise support-density
endpoint from an identity stated against the source residual side.
-/
noncomputable def sourceResidualFiniteRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData zeroSide)
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget normalizationBridge.toFormulaIdentityData
      Index :=
  (({
    sourcePackage := sourcePackage
    normalizationBridge := normalizationBridge
  } : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    |>.sourceResidualFiniteRayleighTarget Index admissible rayleighData
      rayleighQuadratic_eq_sourceResidualSide_on_admissible
      restricted_source_positivity_implies_RHOn_univ)

/--
Build the componentwise support-density endpoint directly from a finite
Rayleigh identity stated against the source residual side.
-/
noncomputable def ofSourceResidualFiniteRayleigh
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((sourceResidualFiniteRayleighTarget sourcePackage normalizationBridge
          Index admissible rayleighData
          rayleighQuadratic_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    (sourceResidualFiniteRayleighTarget sourcePackage normalizationBridge
      Index admissible rayleighData
      rayleighQuadratic_eq_sourceResidualSide_on_admissible
      restricted_source_positivity_implies_RHOn_univ)
        |>.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the componentwise support-density source-formula assembly directly from
split finite-prefix/tail p-series data whose counting estimate matches the
fixed published source input.
-/
noncomputable def ofSplitPSeriesEnvelopeData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the componentwise support-density source-formula assembly directly from
split finite-prefix/tail p-series data and a localized Weil quadratic-form
target.
-/
noncomputable def ofSplitPSeriesEnvelopeDataAndLocalizedQuadraticFormTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofLocalizedQuadraticFormTarget
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
Build the componentwise support-density source-formula assembly directly from
split finite-prefix/tail p-series data and a localized quadratic-form identity
stated against the source residual side.
-/
noncomputable def ofSplitPSeriesSourceResidualLocalizedQuadraticForm
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((sourceResidualLocalizedQuadraticFormTarget sourcePackage
          normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualLocalizedQuadraticForm
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData residualToLi admissible
    localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
    localQuadraticForm_nonneg_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
Build the componentwise support-density source-formula assembly directly from
an automatic-prefix radial target whose counting estimate matches the fixed
published source input.
-/
noncomputable def ofAutomaticPrefixRadialTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData :=
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the componentwise support-density source-formula assembly directly from
an automatic-prefix radial target and a localized Weil quadratic-form target.
-/
noncomputable def ofAutomaticPrefixRadialTargetAndLocalizedQuadraticFormTarget
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofLocalizedQuadraticFormTarget
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
Build the componentwise support-density source-formula assembly directly from
an automatic-prefix radial target and a localized quadratic-form identity
stated against the source residual side.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualLocalizedQuadraticForm
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((sourceResidualLocalizedQuadraticFormTarget sourcePackage
          normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualLocalizedQuadraticForm
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData residualToLi admissible
    localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
    localQuadraticForm_nonneg_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
Build the componentwise support-density endpoint from a support-restricted
coefficient bridge and source-residual nonnegativity on admissible tests.

The coefficient bridge may itself be built from source-residual identities via
`GuinandWeilComponentwiseProjectFormulaPackage.sourceResidualSupportRestrictedToLiCoefficientBridge`.
-/
noncomputable def ofSupportRestrictedCoefficientBridgeAndSourceResidualNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (restrictedToLi :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        (restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
          (normalizationBridge.residual_nonneg_on_admissible_of_source
            admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := restrictedToLi.toFormulaResidualToLiCoefficientBridge
  restrictedData :=
    restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
      (normalizationBridge.residual_nonneg_on_admissible_of_source
        admissible source_residual_nonneg_on_admissible)
  denseCore := denseCore

/--
Build the componentwise support-density endpoint from source-residual
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
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
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSupportRestrictedCoefficientBridgeAndSourceResidualNonnegativity
    zeroData sourcePackage normalizationBridge liData admissible
    (SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientTest coefficientTest_admissible coefficientScale
      coefficientScale_nonneg coefficient_eq_scaled_sourceResidual)
    source_residual_nonneg_on_admissible denseCore

/--
Build the componentwise support-density endpoint directly from split
finite-prefix/tail p-series data, source-residual coefficient identities, and
source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSplitPSeriesSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual source_residual_nonneg_on_admissible
    denseCore

/--
Build the componentwise support-density endpoint directly from an
automatic-prefix radial target, source-residual coefficient identities, and
source-residual nonnegativity on admissible tests.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual source_residual_nonneg_on_admissible
    denseCore

/--
Build the componentwise support-density endpoint from a cutoff-2
support-restricted coefficient bridge and source-residual nonnegativity on
admissible tests.

This is the componentwise endpoint for the common split Li-coefficient route:
coefficient `1` and the tail `2 <= n` may be proved by different source
residual identities.
-/
noncomputable def ofSupportRestrictedCutoffTwoCoefficientBridgeAndSourceResidualNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (restrictedToLi :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        normalizationBridge.toFormulaIdentityData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        (restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
          (normalizationBridge.residual_nonneg_on_admissible_of_source
            admissible source_residual_nonneg_on_admissible))) :
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := zeroData
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi :=
    restrictedToLi.toFormulaResidualToLiCutoffTwoCoefficientBridge
      |>.toFormulaResidualToLiCoefficientBridge
  restrictedData :=
    restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
      (normalizationBridge.residual_nonneg_on_admissible_of_source
        admissible source_residual_nonneg_on_admissible)
  denseCore := denseCore

/--
Build the componentwise support-density endpoint from source-residual
coefficient `1` and tail identities, plus source-residual nonnegativity on
admissible tests.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
        validFrom publishedErrorTerm)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
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
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSupportRestrictedCutoffTwoCoefficientBridgeAndSourceResidualNonnegativity
    zeroData sourcePackage normalizationBridge liData admissible
    (SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientOneTest coefficientOneTest_admissible coefficientOneScale
      coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
      tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
      tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual)
    source_residual_nonneg_on_admissible denseCore

/--
Build the componentwise support-density endpoint directly from split
finite-prefix/tail p-series data, source-residual coefficient `1` and tail
identities, and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSplitPSeriesSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual tailCoefficientTest
    tailCoefficientTest_admissible tailCoefficientScale tailCoefficientScale_nonneg
    tail_coefficient_eq_scaled_sourceResidual source_residual_nonneg_on_admissible
    denseCore

/--
Build the componentwise support-density endpoint directly from an
automatic-prefix radial target, source-residual coefficient `1` and tail
identities, and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual tailCoefficientTest
    tailCoefficientTest_admissible tailCoefficientScale tailCoefficientScale_nonneg
    tail_coefficient_eq_scaled_sourceResidual source_residual_nonneg_on_admissible
    denseCore

/-- Assemble the componentwise project-level Guinand-Weil formula package. -/
noncomputable def formulaPackage
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    GuinandWeilComponentwiseProjectFormulaPackage
      assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide where
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge

/-- Componentwise source formula data gives residual continuity after normalization. -/
noncomputable def residualContinuityData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilFormulaResidualContinuityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.formulaPackage.residualContinuityData

/-- The componentwise support-density residual side is the source residual side. -/
theorem formulaResidualSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.formulaData_residualSide_eq_sourceResidualSide f

/-- The componentwise support-density zero side is the source residual side. -/
theorem zeroSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.explicitFormula_sourceResidualSide f

/-- The dense-core route gives the componentwise support-restricted density bridge. -/
noncomputable def supportDensityBridge
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SupportRestrictedFormulaResidualDensityBridge assembly.restrictedData :=
  assembly.denseCore.toSupportRestrictedDensityBridgeOfResidualContinuity
    assembly.residualContinuityData

/-- Support-restricted positivity plus density promotes to full residual nonnegativity. -/
theorem residual_nonneg
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    forall f : SchwartzLineTestFunction,
      0 <= assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f :=
  assembly.supportDensityBridge.residual_nonneg

/--
Build the componentwise source-formula concrete assembly with full residual
nonnegativity supplied by density.
-/
noncomputable def toComponentwiseSourceFormulaAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorComponentwiseSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := assembly.zeroData
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toComponentwiseSourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/--
The formula residual positivity package obtained through the coefficient-level
residual-to-Li bridge after density has promoted restricted positivity.
-/
noncomputable def formulaResidualDataFromLi
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilFormulaResidualPositivityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.residualToLi.toFormulaResidualPositivityData
    assembly.residual_nonneg

/-- The componentwise density bridge itself also yields formula residual positivity data. -/
noncomputable def formulaResidualDataFromDensity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilFormulaResidualPositivityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.supportDensityBridge.toFormulaResidualPositivityData

/-- The componentwise support-density assembly proves universal local RH, conditionally. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toComponentwiseSourceFormulaAnalyticAssembly.RHOn_univ

/-- The componentwise support-density assembly proves the project RH statement. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toComponentwiseSourceFormulaAnalyticAssembly.RHStatement

/-- The componentwise support-density assembly proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toComponentwiseSourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly

/--
Bellotti-Wong specialization with source formula and support-density positivity
fields exposed.
-/
abbrev RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization with source formula and support-density
positivity fields exposed and the validity threshold still explicit.
-/
abbrev RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong specialization with componentwise source formula normalization
and support-density positivity fields exposed.
-/
abbrev RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization with componentwise source formula
normalization, support-density positivity fields exposed, and the validity
threshold still explicit.
-/
abbrev RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong support-density assembly from the preferred exact-source package
and the preferred cutoff-2 exact-norm clipped p-series estimate.  The
remaining positivity work is exposed as support-restricted residual
positivity plus dense-core promotion.
-/
noncomputable def RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong support-density assembly from the preferred exact-source package
and a cutoff-2 exact-norm shifted-radius p-series estimate.  Support-restricted
positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong support-density assembly from the exact source's cumulative count
and a cutoff-2 exact-norm shifted-radius p-series estimate.
Support-restricted positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong localized support-density assembly from the preferred
exact-source package.  The localized target supplies restricted residual
positivity; the dense-core field remains explicit.
-/
noncomputable def RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfAndLocalizedQuadraticFormTarget
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
Bellotti-Wong localized support-density assembly from the preferred exact-source
package and a cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusAndLocalizedQuadraticFormTarget
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
Bellotti-Wong localized support-density assembly from the exact source's
cumulative count and a cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndLocalizedQuadraticFormTarget
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilBellottiWongSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
HSW support-density assembly from the preferred exact-source package and the
preferred cutoff-2 exact-norm clipped p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
      validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
HSW support-density assembly from the preferred exact-source package and a
cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
      validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
HSW support-density assembly from the exact source's cumulative count and a
cutoff-2 exact-norm shifted-radius p-series estimate. Support-restricted
positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
      validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong componentwise support-density assembly from the preferred
exact-source package and the preferred cutoff-2 exact-norm clipped p-series
estimate. Support-restricted positivity and dense-core promotion remain
explicit.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong componentwise support-density assembly from the preferred
exact-source package and a cutoff-2 exact-norm shifted-radius p-series
estimate. Support-restricted positivity and dense-core promotion remain
explicit.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong componentwise support-density assembly from the exact source's
cumulative count and a cutoff-2 exact-norm shifted-radius p-series estimate.
Support-restricted positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly where
  zeroData :=
    RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
HSW componentwise support-density assembly from the preferred exact-source
package and the preferred cutoff-2 exact-norm clipped p-series estimate.
Support-restricted positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
HSW componentwise support-density assembly from the preferred exact-source
package and a cutoff-2 exact-norm shifted-radius p-series estimate.
Support-restricted positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
HSW componentwise support-density assembly from the exact source's cumulative
count and a cutoff-2 exact-norm shifted-radius p-series estimate.
Support-restricted positivity and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom where
  zeroData :=
    RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Bellotti-Wong componentwise localized support-density assembly from the
preferred exact-source package and the preferred cutoff-2 exact-norm clipped
p-series estimate.

The localized quadratic-form identity is stated against the componentwise
source residual side and transported to project residual positivity here.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfAndSourceResidualLocalizedQuadraticForm
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualLocalizedQuadraticFormTarget
          sourcePackage normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualLocalizedQuadraticForm
      (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_clippedRadialBound)
      sourcePackage normalizationBridge liData residualToLi admissible
      localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ denseCore

/--
Bellotti-Wong componentwise localized support-density assembly from the
preferred exact-source package and a cutoff-2 exact-norm shifted-radius
p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusAndSourceResidualLocalizedQuadraticForm
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualLocalizedQuadraticFormTarget
          sourcePackage normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualLocalizedQuadraticForm
      (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound)
      sourcePackage normalizationBridge liData residualToLi admissible
      localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ denseCore

/--
Bellotti-Wong componentwise localized support-density assembly from the exact
source's cumulative count and a cutoff-2 exact-norm shifted-radius p-series
estimate.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualLocalizedQuadraticForm
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualLocalizedQuadraticFormTarget
          sourcePackage normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualLocalizedQuadraticForm
      (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound)
      sourcePackage normalizationBridge liData residualToLi admissible
      localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW componentwise localized support-density assembly from the preferred
exact-source package and the preferred cutoff-2 exact-norm clipped p-series
estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfAndSourceResidualLocalizedQuadraticForm
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualLocalizedQuadraticFormTarget
          sourcePackage normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualLocalizedQuadraticForm
      (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_clippedRadialBound)
      sourcePackage normalizationBridge liData residualToLi admissible
      localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW componentwise localized support-density assembly from the preferred
exact-source package and a cutoff-2 exact-norm shifted-radius p-series
estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusAndSourceResidualLocalizedQuadraticForm
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualLocalizedQuadraticFormTarget
          sourcePackage normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualLocalizedQuadraticForm
      (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound)
      sourcePackage normalizationBridge liData residualToLi admissible
      localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW componentwise localized support-density assembly from the exact source's
cumulative count and a cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualLocalizedQuadraticForm
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualLocalizedQuadraticFormTarget
          sourcePackage normalizationBridge admissible localQuadraticForm
          localQuadraticForm_eq_sourceResidualSide_on_admissible
          localQuadraticForm_nonneg_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualLocalizedQuadraticForm
      (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
        sourceData system constant decayExponent constant_nonneg decay_margin
        extension_norm_le_shiftedRadialBound)
      sourcePackage normalizationBridge liData residualToLi admissible
      localQuadraticForm localQuadraticForm_eq_sourceResidualSide_on_admissible
      localQuadraticForm_nonneg_on_admissible
      restricted_source_positivity_implies_RHOn_univ denseCore

/--
Bellotti-Wong componentwise finite-model support-density assembly from the
exact source's cumulative count and a cutoff-2 exact-norm shifted-radius
p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualFinitePositivityModel
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualFinitePositivityModelTarget
          sourcePackage normalizationBridge admissible model encode
          encodedQuadratic_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualFinitePositivityModel
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi admissible model
    encode encodedQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
Bellotti-Wong componentwise finite-Gram support-density assembly from the
exact source's cumulative count and a cutoff-2 exact-norm shifted-radius
p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualFiniteGram
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualFiniteGramTarget
          sourcePackage normalizationBridge Index Feature feature admissible
          encode finiteGram_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualFiniteGram
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi Index Feature
    feature admissible encode finiteGram_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
Bellotti-Wong componentwise finite-Rayleigh support-density assembly from the
exact source's cumulative count and a cutoff-2 exact-norm shifted-radius
p-series estimate.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualFiniteRayleigh
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualFiniteRayleighTarget
          sourcePackage normalizationBridge Index admissible rayleighData
          rayleighQuadratic_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualFiniteRayleigh
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi Index admissible
    rayleighData rayleighQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW componentwise finite-model support-density assembly from the exact
source's cumulative count and a cutoff-2 exact-norm shifted-radius p-series
estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualFinitePositivityModel
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualFinitePositivityModelTarget
          sourcePackage normalizationBridge admissible model encode
          encodedQuadratic_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualFinitePositivityModel
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi admissible model
    encode encodedQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW componentwise finite-Gram support-density assembly from the exact source's
cumulative count and a cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualFiniteGram
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualFiniteGramTarget
          sourcePackage normalizationBridge Index Feature feature admissible
          encode finiteGram_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualFiniteGram
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi Index Feature
    feature admissible encode finiteGram_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW componentwise finite-Rayleigh support-density assembly from the exact
source's cumulative count and a cutoff-2 exact-norm shifted-radius p-series
estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualFiniteRayleigh
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f =
            sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True))
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        ((RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.sourceResidualFiniteRayleighTarget
          sourcePackage normalizationBridge Index admissible rayleighData
          rayleighQuadratic_eq_sourceResidualSide_on_admissible
          restricted_source_positivity_implies_RHOn_univ)
            |>.toSupportRestrictedFormulaResidualPositivityData)) :
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualFiniteRayleigh
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi Index admissible
    rayleighData rayleighQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ denseCore

/--
HSW localized support-density assembly from the preferred exact-source package.
The real localized positivity theorem and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfAndLocalizedQuadraticFormTarget
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
HSW localized support-density assembly from the preferred exact-source package
and a cutoff-2 exact-norm shifted-radius p-series estimate.  The localized
positivity theorem and dense-core promotion remain explicit.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusAndLocalizedQuadraticFormTarget
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
HSW localized support-density assembly from the exact source's cumulative count
and a cutoff-2 exact-norm shifted-radius p-series estimate.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndLocalizedQuadraticFormTarget
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (localizedTarget :
      LocalizedWeilQuadraticFormTarget
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore
        localizedTarget.toSupportRestrictedFormulaResidualPositivityData) :
    RiemannWeilHasanalizadeShenWongSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData residualToLi localizedTarget
    denseCore

/--
Concrete support-density assembly where the restricted positivity-to-RH
criterion is supplied by admissible coefficient tests.
-/
structure RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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

namespace RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly

/-- The restricted positivity package built from coefficient tests. -/
noncomputable def restrictedData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SupportRestrictedFormulaResidualPositivityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
    assembly.residual_nonneg_on_admissible

/--
Build the coefficient-test support-density endpoint from Li coefficient
identities stated against the source Guinand-Weil residual side.
-/
noncomputable def ofSourceResidualCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
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
Build the coefficient-test support-density endpoint from source-residual
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentities zeroData sourcePackage
    normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the coefficient-test support-density endpoint directly from split
finite-prefix/tail p-series data and source-residual coefficient identities,
while residual nonnegativity is supplied on the normalized formula side.
-/
noncomputable def ofSplitPSeriesSourceResidualCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentities
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual residual_nonneg_on_admissible denseCore

/--
Build the coefficient-test support-density endpoint directly from split
finite-prefix/tail p-series data, source-residual coefficient identities, and
source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSplitPSeriesSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual source_residual_nonneg_on_admissible
    denseCore

/--
Build the coefficient-test support-density endpoint directly from an
automatic-prefix radial target and source-residual coefficient identities,
while residual nonnegativity is supplied on the normalized formula side.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentities
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual residual_nonneg_on_admissible denseCore

/--
Build the coefficient-test support-density endpoint directly from an
automatic-prefix radial target, source-residual coefficient identities, and
source-residual nonnegativity on admissible tests.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual source_residual_nonneg_on_admissible
    denseCore

/-- Convert to the support-density source-formula assembly. -/
noncomputable def toSupportDensitySourceFormulaAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := assembly.zeroData
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  residualToLi := assembly.restrictedToLi.toFormulaResidualToLiCoefficientBridge
  restrictedData := assembly.restrictedData
  denseCore := assembly.denseCore

/-- The coefficient-test support-density residual side is the source residual side. -/
theorem formulaResidualSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly
    |>.formulaResidualSide_eq_sourceResidualSide f

/-- The coefficient-test support-density zero side is the source residual side. -/
theorem zeroSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly
    |>.zeroSide_eq_sourceResidualSide f

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The coefficient-test support-density assembly proves universal local RH, conditionally. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly.RHOn_univ

/-- The coefficient-test support-density assembly proves the project RH statement. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly.RHStatement

/-- The coefficient-test support-density assembly proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly

/--
Concrete support-density assembly where the restricted positivity-to-RH
criterion is supplied by cutoff-2 admissible coefficient tests: coefficient `1`
and the tail family `2 <= n` are separate fields of the bridge.
-/
structure RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    (validFrom : Real) (publishedErrorTerm : Real -> Real) where
  zeroData :
    RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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

namespace RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly

/-- The restricted positivity package built from cutoff-2 coefficient tests. -/
noncomputable def restrictedData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SupportRestrictedFormulaResidualPositivityData
      assembly.normalizationBridge.toFormulaIdentityData :=
  assembly.restrictedToLi.toSupportRestrictedFormulaResidualPositivityData
    assembly.residual_nonneg_on_admissible

/--
Build the cutoff-2 coefficient-test support-density endpoint from coefficient
`1` and tail identities stated against the source Guinand-Weil residual side.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
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
Build the cutoff-2 coefficient-test support-density endpoint from source
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (zeroData :
      RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData
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
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
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
Build the cutoff-2 coefficient-test support-density endpoint directly from
split finite-prefix/tail p-series data and source-residual coefficient
identities, while residual nonnegativity is supplied on the normalized formula
side.
-/
noncomputable def ofSplitPSeriesSourceResidualCutoffTwoCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentities
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    residual_nonneg_on_admissible denseCore

/--
Build the cutoff-2 coefficient-test support-density endpoint directly from
split finite-prefix/tail p-series data, source-residual coefficient identities,
and source-residual nonnegativity on admissible tests.
-/
noncomputable def ofSplitPSeriesSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (splitData : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (counting_eq :
      splitData.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
          publishedCounting splitData counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofSplitPSeriesEnvelopeData
      publishedCounting splitData counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
Build the cutoff-2 coefficient-test support-density endpoint directly from an
automatic-prefix radial target and source-residual coefficient identities,
while residual nonnegativity is supplied on the normalized formula side.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualCutoffTwoCoefficientIdentities
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentities
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    residual_nonneg_on_admissible denseCore

/--
Build the cutoff-2 coefficient-test support-density endpoint directly from an
automatic-prefix radial target, source-residual coefficient identities, and
source-residual nonnegativity on admissible tests.
-/
noncomputable def ofAutomaticPrefixRadialTargetSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (publishedCounting :
      FixedErrorExplicitRiemannVonMangoldtSourceInput
        validFrom publishedErrorTerm)
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget)
    (counting_eq :
      target.counting = publishedCounting.toPolynomialZeroCountingEstimate)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
          publishedCounting target counting_eq)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm :=
  ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilFixedErrorPublishedCountingAntitonePSeriesData.ofAutomaticPrefixRadialTarget
      publishedCounting target counting_eq)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/-- Convert to the support-density source-formula assembly. -/
noncomputable def toSupportDensitySourceFormulaAnalyticAssembly
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannWeilFixedErrorSupportDensitySourceFormulaAnalyticAssembly
      validFrom publishedErrorTerm where
  zeroData := assembly.zeroData
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  residualToLi :=
    assembly.restrictedToLi
      |>.toFormulaResidualToLiCutoffTwoCoefficientBridge
      |>.toFormulaResidualToLiCoefficientBridge
  restrictedData := assembly.restrictedData
  denseCore := assembly.denseCore

/-- The cutoff-2 coefficient-test support-density residual side is the source residual side. -/
theorem formulaResidualSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.normalizationBridge.toFormulaIdentityData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly
    |>.formulaResidualSide_eq_sourceResidualSide f

/-- The cutoff-2 coefficient-test support-density zero side is the source residual side. -/
theorem zeroSide_eq_sourceResidualSide
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.toEventualPSeriesEnvelopeZeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly
    |>.zeroSide_eq_sourceResidualSide f

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The cutoff-2 coefficient-test support-density assembly proves universal local RH. -/
theorem RHOn_univ
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly.RHOn_univ

/-- The cutoff-2 coefficient-test support-density assembly proves the project RH statement. -/
theorem RHStatement
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly.RHStatement

/-- The cutoff-2 coefficient-test support-density assembly proves Mathlib RH. -/
theorem mathlib_RH
    {validFrom : Real} {publishedErrorTerm : Real -> Real}
    (assembly :
      RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
        validFrom publishedErrorTerm) :
    RiemannHypothesis :=
  assembly.toSupportDensitySourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly

/--
Bellotti-Wong specialization with source formula, support-density positivity,
and admissible coefficient tests exposed.
-/
abbrev RiemannWeilBellottiWongSupportDensityCoefficientSourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization with source formula, support-density
positivity, and admissible coefficient tests exposed.
-/
abbrev RiemannWeilHasanalizadeShenWongSupportDensityCoefficientSourceFormulaAnalyticAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorSupportDensityCoefficientSourceFormulaAnalyticAssembly
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong specialization with source formula, support-density positivity,
and cutoff-2 admissible coefficient tests exposed.
-/
abbrev RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    bellottiWongValidFrom bellottiWongErrorTerm

/--
Hasanalizade-Shen-Wong specialization with source formula, support-density
positivity, and cutoff-2 admissible coefficient tests exposed.
-/
abbrev RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    (validFrom : Real) :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
    validFrom hasanalizadeShenWongErrorTerm

/--
Bellotti-Wong cutoff-2 coefficient-test endpoint from the preferred
exact-source package, the cutoff-2 exact-norm clipped p-series estimate,
source-residual coefficient identities, and source-residual nonnegativity on
admissible tests.
-/
noncomputable def RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
Bellotti-Wong cutoff-2 coefficient-test endpoint from the preferred
exact-source package, a cutoff-2 exact-norm shifted-radius p-series estimate,
source-residual coefficient identities, and source-residual nonnegativity on
admissible tests.
-/
noncomputable def RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
Bellotti-Wong cutoff-2 coefficient-test endpoint from the exact source's
cumulative count, a cutoff-2 exact-norm shifted-radius p-series estimate,
source-residual coefficient identities, and source-residual nonnegativity on
admissible tests.
-/
noncomputable def RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilBellottiWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
HSW cutoff-2 coefficient-test endpoint from the preferred exact-source
package, the cutoff-2 exact-norm clipped p-series estimate, source-residual
coefficient identities, and source-residual nonnegativity on admissible tests.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_clippedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_clippedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
HSW cutoff-2 coefficient-test endpoint from the preferred exact-source package,
a cutoff-2 exact-norm shifted-radius p-series estimate, source-residual
coefficient identities, and source-residual nonnegativity on admissible tests.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCutoffTwoClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
HSW cutoff-2 coefficient-test endpoint from the exact source's cumulative
count, a cutoff-2 exact-norm shifted-radius p-series estimate, source-residual
coefficient identities, and source-residual nonnegativity on admissible tests.
-/
noncomputable def RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilHasanalizadeShenWongSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorSupportDensityCutoffTwoCoefficientSourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
Bellotti-Wong componentwise support-density endpoint from the exact source's
cumulative count, a cutoff-2 exact-norm shifted-radius p-series estimate,
source-residual coefficient identities, and source-residual nonnegativity on
admissible tests.
-/
noncomputable def RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilBellottiWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilBellottiWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

/--
HSW componentwise support-density endpoint from the exact source's cumulative
count, a cutoff-2 exact-norm shifted-radius p-series estimate,
source-residual coefficient identities, and source-residual nonnegativity on
admissible tests.
-/
noncomputable def RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelfAndSourceResidualCutoffTwoCoefficientIdentities
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
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilComponentwiseNormalizationBridge
        sourcePackage.sourceData
        ((RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
            sourceData system constant decayExponent constant_nonneg
            decay_margin extension_norm_le_shiftedRadialBound)
          |>.toEventualPSeriesEnvelopeZeroData
          |>.zeroSide))
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
    RiemannWeilHasanalizadeShenWongComponentwiseSupportDensitySourceFormulaAnalyticAssembly
      validFrom :=
  RiemannWeilFixedErrorComponentwiseSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
    (RiemannWeilHasanalizadeShenWongAntitonePSeriesData.ofExactSourceCumulativeCutoffTwoShiftedRadiusExactNormSelf
      sourceData system constant decayExponent constant_nonneg decay_margin
      extension_norm_le_shiftedRadialBound)
    sourcePackage normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    source_residual_nonneg_on_admissible denseCore

end

end RiemannHypothesisProject
