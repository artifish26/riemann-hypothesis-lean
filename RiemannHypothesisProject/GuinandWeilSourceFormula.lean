import RiemannHypothesisProject.GuinandWeilDensityFormulaBridge
import RiemannHypothesisProject.LocalizedWeilQuadraticFormTarget
import RiemannHypothesisProject.SupportRestrictedLiCoefficientBridge

/-!
# Guinand-Weil source formula package

The existing Guinand-Weil modules separate the source test-function class, the
restricted source formula, density promotion, normalization, and continuity
transport.  This file assembles those pieces into source-facing work packages.

No analytic Guinand-Weil formula is proved here.  The point is to make the
future source proof target crisp: fill the restricted formula, side bridges,
density, continuity, and normalization fields, and Lean exposes the project
formula identity plus the residual-continuity/closedness data used by the
positivity route.
-/

namespace RiemannHypothesisProject

noncomputable section

/--
A source-level Guinand-Weil package before choosing the project zero-side
normalization.

Future analytic work should instantiate this by proving the restricted source
formula on the admissible source class, the source-to-Schwartz side identities,
density of the admissible image, and continuity of the four source sides.
-/
structure GuinandWeilSourceFormulaPackage where
  testData : GuinandWeilSourceTestFunctionClass
  restrictedData : GuinandWeilRestrictedFormulaIdentityData testData
  globalSideData : GuinandWeilFormulaSideData
  densityBridge :
    GuinandWeilRestrictedFormulaDensityBridge restrictedData globalSideData

namespace GuinandWeilSourceFormulaPackage

/-- The density-promoted global source formula data. -/
noncomputable def sourceData
    (pkg : GuinandWeilSourceFormulaPackage) :
    GuinandWeilFormulaIdentityData :=
  pkg.densityBridge.toGlobalFormulaIdentityData

/-- The source formula equality after density promotion. -/
theorem sourceExplicitFormula
    (pkg : GuinandWeilSourceFormulaPackage)
    (f : SchwartzLineTestFunction) :
    pkg.globalSideData.sourceZeroSide f =
      pkg.globalSideData.sourceResidualSide f :=
  pkg.densityBridge.sourceExplicitFormula f

/-- The promoted source formula keeps the package's global side data. -/
theorem sourceData_sideData
    (pkg : GuinandWeilSourceFormulaPackage) :
    pkg.sourceData.sideData = pkg.globalSideData :=
  rfl

/-- Source prime/pole/gamma continuity extracted from the full density package. -/
noncomputable def sideContinuityData
    (pkg : GuinandWeilSourceFormulaPackage) :
    GuinandWeilFormulaSideContinuityData pkg.sourceData :=
  pkg.densityBridge.continuity.toSideContinuityData

/-- Source residual-side continuity extracted from the full density package. -/
theorem continuous_sourceResidualSide
    (pkg : GuinandWeilSourceFormulaPackage) :
    Continuous pkg.sourceData.sideData.sourceResidualSide :=
  pkg.densityBridge.continuity.continuous_sourceResidualSide

/-- The source formula equality locus is closed for the package's source sides. -/
theorem sourceFormulaEqualitySet_closed
    (pkg : GuinandWeilSourceFormulaPackage) :
    IsClosed (guinandWeilSourceFormulaEqualitySet pkg.sourceData.sideData) :=
  pkg.densityBridge.continuity.sourceFormulaEqualitySet_closed

end GuinandWeilSourceFormulaPackage

/--
A project-level Guinand-Weil package after choosing and normalizing the
project Riemann-Weil zero side.
-/
structure GuinandWeilProjectFormulaPackage
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge sourcePackage.sourceData zeroSide

namespace GuinandWeilProjectFormulaPackage

/-- The project-normalized formula identity data. -/
noncomputable def formulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  pkg.normalizationBridge.toFormulaIdentityData

/-- The project formula identity obtained from the source package and normalization bridge. -/
theorem explicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = pkg.formulaData.sideData.residualSide f :=
  pkg.formulaData.explicitFormula f

/-- The project residual side is the source residual side after normalization. -/
theorem formulaData_residualSide_eq_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.residualSide f =
      pkg.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  pkg.normalizationBridge.toFormulaIdentityData_residualSide f

/--
Build the residual-to-Li coefficient bridge from identities stated in source
Guinand-Weil residual notation.

The normalization projection `formulaData_residualSide_eq_sourceResidualSide`
transports the identities to the formula-residual side used by the RH endpoint.
-/
noncomputable def sourceResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientScale : Nat -> Real)
    (coefficientScale_nonneg :
      forall n : Nat, 0 < n -> 0 <= coefficientScale n)
    (coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            coefficientScale n *
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (coefficientTest n)) :
    FormulaResidualToLiCoefficientBridge pkg.formulaData liData :=
  FormulaResidualToLiCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientTest coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual

/--
Build the cutoff-2 residual-to-Li bridge from coefficient `1` and tail
identities stated in source Guinand-Weil residual notation.
-/
noncomputable def sourceResidualToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale *
          pkg.sourcePackage.sourceData.sideData.sourceResidualSide
            coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientScale : Nat -> Real)
    (tailCoefficientScale_nonneg :
      forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n)
    (tail_coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            tailCoefficientScale n *
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (tailCoefficientTest n)) :
    FormulaResidualToLiCutoffTwoCoefficientBridge pkg.formulaData liData :=
  FormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientOneTest coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientScale tailCoefficientScale_nonneg
    tail_coefficient_eq_scaled_sourceResidual

/--
Build the support-restricted coefficient bridge from admissible coefficient
tests and identities stated in source Guinand-Weil residual notation.
-/
noncomputable def sourceResidualSupportRestrictedToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
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
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (coefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      pkg.formulaData admissible liData :=
  SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientTest coefficientTest_admissible coefficientScale
    coefficientScale_nonneg coefficient_eq_scaled_sourceResidual

/--
Build the cutoff-2 support-restricted coefficient bridge from admissible
coefficient `1` and tail identities stated in source residual notation.
-/
noncomputable def sourceResidualSupportRestrictedToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale *
          pkg.sourcePackage.sourceData.sideData.sourceResidualSide
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
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (tailCoefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
      pkg.formulaData admissible liData :=
  SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientOneTest coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual

/--
Package support-restricted residual positivity from nonnegativity proved
directly for the source Guinand-Weil residual side.
-/
noncomputable def sourceResidualSupportRestrictedPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    {admissible : SchwartzLineTestFunction -> Prop}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        pkg.formulaData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  bridge.toSupportRestrictedFormulaResidualPositivityDataOfResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    source_residual_nonneg_on_admissible

/--
Package support-restricted residual positivity from a source-residual
coefficient bridge and source-residual nonnegativity on admissible tests.
-/
noncomputable def sourceResidualCoefficientPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    {admissible : SchwartzLineTestFunction -> Prop}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        pkg.formulaData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  pkg.sourceResidualSupportRestrictedPositivityData
    bridge.toSupportRestrictedFormulaResidualToLiBridge
    source_residual_nonneg_on_admissible

/--
Package support-restricted residual positivity from a cutoff-2 source-residual
coefficient bridge and source-residual nonnegativity on admissible tests.
-/
noncomputable def sourceResidualCutoffTwoCoefficientPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    {admissible : SchwartzLineTestFunction -> Prop}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        pkg.formulaData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  pkg.sourceResidualSupportRestrictedPositivityData
    bridge.toSupportRestrictedFormulaResidualToLiBridge
    source_residual_nonneg_on_admissible

/--
The project zero-side formula can be read directly as the source residual-side
formula transported by the normalization bridge.
-/
theorem explicitFormula_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      pkg.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  pkg.normalizationBridge.zeroSide_eq_sourceResidualSide f

/-- Project side-continuity data transported from source side continuity. -/
noncomputable def formulaSideContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide) :
    SchwartzRiemannWeilFormulaSideContinuityData pkg.formulaData :=
  pkg.sourcePackage.sideContinuityData
    |>.toSchwartzFormulaSideContinuityData pkg.normalizationBridge

/-- Project residual-continuity data transported from source side continuity. -/
noncomputable def residualContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide) :
    SchwartzRiemannWeilFormulaResidualContinuityData pkg.formulaData :=
  pkg.formulaSideContinuityData.toResidualContinuityData

/-- The residual-nonnegative locus is closed for the project-normalized formula. -/
theorem residual_nonnegativeSet_closed
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide) :
    IsClosed (formulaResidualNonnegativeSet pkg.formulaData) :=
  pkg.formulaSideContinuityData.residual_nonnegativeSet_closed

end GuinandWeilProjectFormulaPackage

/--
A project-level Guinand-Weil package with componentwise normalization of the
zero, prime, pole, and gamma sides.
-/
structure GuinandWeilComponentwiseProjectFormulaPackage
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge sourcePackage.sourceData zeroSide

namespace GuinandWeilComponentwiseProjectFormulaPackage

/-- The project-normalized formula identity data from componentwise normalization. -/
noncomputable def formulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  pkg.normalizationBridge.toFormulaIdentityData

/-- The project formula identity obtained from componentwise source normalization. -/
theorem explicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = pkg.formulaData.sideData.residualSide f :=
  pkg.formulaData.explicitFormula f

/-- The componentwise-normalized residual side is the source residual side. -/
theorem formulaData_residualSide_eq_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.residualSide f =
      pkg.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  pkg.normalizationBridge.toFormulaIdentityData_residualSide f

/-- The componentwise-normalized prime side is the source prime side. -/
theorem formulaData_primeSide_eq_sourcePrimeSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.primeSide f =
      pkg.sourcePackage.sourceData.sideData.sourcePrimeSide f :=
  pkg.normalizationBridge.toFormulaIdentityData_primeSide f

/-- The componentwise-normalized pole side is the source pole side. -/
theorem formulaData_poleSide_eq_sourcePoleSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.poleSide f =
      pkg.sourcePackage.sourceData.sideData.sourcePoleSide f :=
  pkg.normalizationBridge.toFormulaIdentityData_poleSide f

/-- The componentwise-normalized gamma side is the source gamma side. -/
theorem formulaData_gammaSide_eq_sourceGammaSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.gammaSide f =
      pkg.sourcePackage.sourceData.sideData.sourceGammaSide f :=
  pkg.normalizationBridge.toFormulaIdentityData_gammaSide f

/--
The project zero-side formula can be read directly as the source residual-side
formula transported by the componentwise normalization bridge.
-/
theorem explicitFormula_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      pkg.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  pkg.normalizationBridge.zeroSide_eq_sourceResidualSide f

/--
Build the residual-to-Li coefficient bridge from identities stated in source
Guinand-Weil residual notation, using the componentwise normalization package.
-/
noncomputable def sourceResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientScale : Nat -> Real)
    (coefficientScale_nonneg :
      forall n : Nat, 0 < n -> 0 <= coefficientScale n)
    (coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            coefficientScale n *
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (coefficientTest n)) :
    FormulaResidualToLiCoefficientBridge pkg.formulaData liData :=
  FormulaResidualToLiCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientTest coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual

/--
Build the cutoff-2 residual-to-Li bridge from coefficient `1` and tail
identities stated in source Guinand-Weil residual notation, using the
componentwise normalization package.
-/
noncomputable def sourceResidualToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale *
          pkg.sourcePackage.sourceData.sideData.sourceResidualSide
            coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientScale : Nat -> Real)
    (tailCoefficientScale_nonneg :
      forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n)
    (tail_coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            tailCoefficientScale n *
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (tailCoefficientTest n)) :
    FormulaResidualToLiCutoffTwoCoefficientBridge pkg.formulaData liData :=
  FormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientOneTest coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientScale tailCoefficientScale_nonneg
    tail_coefficient_eq_scaled_sourceResidual

/--
Build the support-restricted coefficient bridge from admissible coefficient
tests and identities stated in source residual notation, using the componentwise
normalization package.
-/
noncomputable def sourceResidualSupportRestrictedToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
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
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (coefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      pkg.formulaData admissible liData :=
  SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientTest coefficientTest_admissible coefficientScale
    coefficientScale_nonneg coefficient_eq_scaled_sourceResidual

/--
Build the cutoff-2 support-restricted coefficient bridge from admissible
coefficient `1` and tail identities stated in source residual notation, using
the componentwise normalization package.
-/
noncomputable def sourceResidualSupportRestrictedToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (admissible : SchwartzLineTestFunction -> Prop)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale *
          pkg.sourcePackage.sourceData.sideData.sourceResidualSide
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
              pkg.sourcePackage.sourceData.sideData.sourceResidualSide
                (tailCoefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
      pkg.formulaData admissible liData :=
  SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    coefficientOneTest coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual

/--
Package support-restricted residual positivity from nonnegativity proved
directly for the source Guinand-Weil residual side, using the componentwise
normalization package.
-/
noncomputable def sourceResidualSupportRestrictedPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    {admissible : SchwartzLineTestFunction -> Prop}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        pkg.formulaData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  bridge.toSupportRestrictedFormulaResidualPositivityDataOfResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    source_residual_nonneg_on_admissible

/--
Package support-restricted residual positivity from a source-residual
coefficient bridge and source-residual nonnegativity on admissible tests, using
the componentwise normalization package.
-/
noncomputable def sourceResidualCoefficientPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    {admissible : SchwartzLineTestFunction -> Prop}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        pkg.formulaData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  pkg.sourceResidualSupportRestrictedPositivityData
    bridge.toSupportRestrictedFormulaResidualToLiBridge
    source_residual_nonneg_on_admissible

/--
Package support-restricted residual positivity from a cutoff-2 source-residual
coefficient bridge and source-residual nonnegativity on admissible tests, using
the componentwise normalization package.
-/
noncomputable def sourceResidualCutoffTwoCoefficientPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    {admissible : SchwartzLineTestFunction -> Prop}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        pkg.formulaData admissible liData)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  pkg.sourceResidualSupportRestrictedPositivityData
    bridge.toSupportRestrictedFormulaResidualToLiBridge
    source_residual_nonneg_on_admissible

/--
Build a localized quadratic-form target from identities stated in the
componentwise source residual notation.

This is the localized-positivity analogue of the source-residual coefficient
bridges above: the analytic proof may identify a local quadratic form with the
source residual side, and the componentwise normalization package transports
that identity to the project formula residual side.
-/
noncomputable def sourceResidualLocalizedQuadraticFormTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilQuadraticFormTarget pkg.formulaData :=
  LocalizedWeilQuadraticFormTarget.ofResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    admissible localQuadraticForm
    localQuadraticForm_eq_sourceResidualSide_on_admissible
    localQuadraticForm_nonneg_on_admissible
    restricted_source_positivity_implies_RHOn_univ

/--
Package source-residual localized quadratic-form positivity as
support-restricted project residual positivity.
-/
noncomputable def sourceResidualLocalizedSupportRestrictedPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          localQuadraticForm f =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  (pkg.sourceResidualLocalizedQuadraticFormTarget admissible localQuadraticForm
    localQuadraticForm_eq_sourceResidualSide_on_admissible
    localQuadraticForm_nonneg_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
      |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build a finite positivity-model target from a componentwise source-residual
identity.

This is the finite-model version of
`sourceResidualLocalizedQuadraticFormTarget`: the analytic proof identifies a
finite positive quadratic model with the source residual side on an admissible
class, and the componentwise normalization package transports it to the
project formula residual side.
-/
noncomputable def sourceResidualFinitePositivityModelTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget pkg.formulaData :=
  LocalizedWeilFinitePositivityModelTarget.ofSourceResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    admissible model encode
    encodedQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ

/--
Package componentwise source-residual finite-model positivity as
support-restricted project residual positivity.
-/
noncomputable def sourceResidualFinitePositivityModelSupportRestrictedPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  (pkg.sourceResidualFinitePositivityModelTarget admissible model encode
    encodedQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
      |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build a finite Gram positivity-model target from a componentwise
source-residual identity.
-/
noncomputable def sourceResidualFiniteGramTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget pkg.formulaData :=
  LocalizedWeilFinitePositivityModelTarget.ofSourceFiniteGram
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    Index Feature feature admissible encode
    finiteGram_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ

/--
Package componentwise source-residual finite Gram positivity as
support-restricted project residual positivity.
-/
noncomputable def sourceResidualFiniteGramSupportRestrictedPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  (pkg.sourceResidualFiniteGramTarget Index Feature feature admissible encode
    finiteGram_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
      |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build a finite Rayleigh target from a componentwise source-residual identity.
-/
noncomputable def sourceResidualFiniteRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget pkg.formulaData Index :=
  LocalizedWeilFiniteRayleighTarget.ofSourceResidualSideEq
    pkg.sourcePackage.sourceData.sideData.sourceResidualSide
    pkg.formulaData_residualSide_eq_sourceResidualSide
    admissible rayleighData
    rayleighQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ

/--
Package componentwise source-residual finite Rayleigh positivity as
support-restricted project residual positivity.
-/
noncomputable def sourceResidualFiniteRayleighSupportRestrictedPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide)
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f =
            pkg.sourcePackage.sourceData.sideData.sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f ->
          0 <= pkg.sourcePackage.sourceData.sideData.sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SupportRestrictedFormulaResidualPositivityData pkg.formulaData :=
  (pkg.sourceResidualFiniteRayleighTarget Index admissible rayleighData
    rayleighQuadratic_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ)
      |>.toSupportRestrictedFormulaResidualPositivityData

/-- Project side-continuity data transported from componentwise source continuity. -/
noncomputable def formulaSideContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide) :
    SchwartzRiemannWeilFormulaSideContinuityData pkg.formulaData :=
  pkg.normalizationBridge.toSchwartzFormulaSideContinuityData
    pkg.sourcePackage.sideContinuityData

/-- Project residual-continuity data transported from componentwise source continuity. -/
noncomputable def residualContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide) :
    SchwartzRiemannWeilFormulaResidualContinuityData pkg.formulaData :=
  pkg.formulaSideContinuityData.toResidualContinuityData

/-- The residual-nonnegative locus is closed for the componentwise-normalized formula. -/
theorem residual_nonnegativeSet_closed
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseProjectFormulaPackage zeroSide) :
    IsClosed (formulaResidualNonnegativeSet pkg.formulaData) :=
  pkg.normalizationBridge.residual_nonnegativeSet_closed
    pkg.sourcePackage.sideContinuityData

/--
Every older zero-side-normalized project package gives a componentwise package
by taking project prime, pole, and gamma sides to be the source sides.
-/
noncomputable def ofProjectFormulaPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilProjectFormulaPackage zeroSide) :
    GuinandWeilComponentwiseProjectFormulaPackage zeroSide where
  sourcePackage := pkg.sourcePackage
  normalizationBridge :=
    GuinandWeilComponentwiseNormalizationBridge.ofZeroSideNormalizationBridge
      pkg.normalizationBridge

end GuinandWeilComponentwiseProjectFormulaPackage

end

end RiemannHypothesisProject
