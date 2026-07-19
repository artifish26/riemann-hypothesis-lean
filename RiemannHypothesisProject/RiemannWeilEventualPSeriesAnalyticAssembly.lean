import RiemannHypothesisProject.RiemannWeilAntitoneRadialSplitPSeriesBridge
import RiemannHypothesisProject.RiemannWeilShiftedRadius.CertificateEndpoints
import RiemannHypothesisProject.GuinandWeilSourceFormula
import RiemannHypothesisProject.ResidualToLiCoefficientBridge
import RiemannHypothesisProject.LocalizedWeilQuadraticFormTarget

/-!
# End-to-end eventual p-series analytic assembly

This file connects the current analytic work packages:

* eventual p-series zero-data;
* the source-normalized Guinand-Weil formula package and normalization bridge;
* the residual-to-Li coefficient bridge;
* residual nonnegativity.

The hard analytic theorems are still explicit fields.  Once those fields are
filled, Lean assembles the final
`SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData` target and
all of its checked RH endpoint consequences.
-/

namespace RiemannHypothesisProject

noncomputable section

open Filter
open scoped Topology

/--
The generic end-to-end analytic package for the current eventual p-series
route.

The package is deliberately conditional: it assumes already-built zero data,
a normalized Guinand-Weil formula package for that zero side, a Li criterion,
coefficient identities relating residuals to Li coefficients, and residual
nonnegativity.
-/
structure RiemannWeilEventualPSeriesAnalyticAssembly where
  zeroData : SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData
  formulaPackage : GuinandWeilProjectFormulaPackage zeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilEventualPSeriesAnalyticAssembly

/-- The project-normalized formula identity data. -/
noncomputable def formulaData
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.formulaPackage.formulaData

/-- The formula residual positivity data obtained through coefficient identities. -/
noncomputable def formulaResidualData
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualPositivityData assembly.formulaData :=
  assembly.residualToLi.toFormulaResidualPositivityData
    assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData where
  zeroData := assembly.zeroData
  formulaData := assembly.formulaData
  formulaResidualData := assembly.formulaResidualData

/-- Convert the assembly into the preferred profiled shell formula-residual target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toEventualPSeriesFormulaResidualInputData
    |>.toProfiledShellFormulaResidualInputData

/-- The assembly exposes residual-side continuity from the Guinand-Weil package. -/
noncomputable def residualContinuityData
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualContinuityData assembly.formulaData :=
  assembly.formulaPackage.residualContinuityData

/-- The residual-nonnegative locus is closed for the assembled formula. -/
theorem residual_nonnegativeSet_closed
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.formulaPackage.residual_nonnegativeSet_closed

/-- The assembled zero side agrees with the formula residual side. -/
theorem zeroSide_eq_formulaResidualSide
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.toEventualPSeriesFormulaResidualInputData.toProfiledTailCertificateData.zeroSide.zeroSide f =
      assembly.formulaData.sideData.residualSide f :=
  assembly.toEventualPSeriesFormulaResidualInputData
    |>.zeroSide_eq_formulaResidualSide f

/-- Window zero-side sums converge to the formula residual side. -/
theorem tendsto_windowZeroSide_formulaResidualSide
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        assembly.toEventualPSeriesFormulaResidualInputData.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop (nhds (assembly.formulaData.sideData.residualSide f)) :=
  assembly.toEventualPSeriesFormulaResidualInputData
    |>.tendsto_windowZeroSide_formulaResidualSide windowExhaustion f

/-- The assembled package proves universal local RH, conditionally on the supplied fields. -/
theorem RHOn_univ
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toEventualPSeriesFormulaResidualInputData.RHOn_univ

/-- The assembled package proves the project RH statement, conditionally on the supplied fields. -/
theorem RHStatement
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toEventualPSeriesFormulaResidualInputData.RHStatement

/-- The assembled package proves Mathlib RH, conditionally on the supplied fields. -/
theorem mathlib_RH
    (assembly : RiemannWeilEventualPSeriesAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toEventualPSeriesFormulaResidualInputData.mathlib_RH

end RiemannWeilEventualPSeriesAnalyticAssembly

/--
Specialization of the end-to-end assembly where the eventual p-series zero data
comes from the antitone radial route.
-/
structure RiemannWeilAntitoneRadialAnalyticAssembly where
  zeroPackage : RiemannWeilAntitoneRadialPSeriesEnvelopeData
  formulaPackage :
    GuinandWeilProjectFormulaPackage
      zeroPackage.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilAntitoneRadialAnalyticAssembly

/-- Convert the antitone radial assembly to the generic eventual p-series assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly : RiemannWeilAntitoneRadialAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly where
  zeroData := assembly.zeroPackage.toEventualPSeriesEnvelopeZeroData
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly : RiemannWeilAntitoneRadialAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- The antitone radial assembly proves Mathlib RH, conditionally on the supplied fields. -/
theorem mathlib_RH
    (assembly : RiemannWeilAntitoneRadialAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toEventualPSeriesAnalyticAssembly.mathlib_RH

end RiemannWeilAntitoneRadialAnalyticAssembly

/--
Specialization of the end-to-end assembly where the eventual p-series zero data
comes from the automatic-prefix radial target.
-/
structure RiemannWeilAutomaticPrefixRadialAnalyticAssembly where
  zeroTarget : RiemannWeilAutomaticPrefixRadialPSeriesTarget
  formulaPackage :
    GuinandWeilProjectFormulaPackage
      zeroTarget.toEventualPSeriesEnvelopeZeroData.zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilAutomaticPrefixRadialAnalyticAssembly

/-- Convert the automatic-prefix radial assembly to the generic eventual package. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly where
  zeroData := assembly.zeroTarget.toEventualPSeriesEnvelopeZeroData
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the assembly into the preferred profiled shell formula-residual target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/-- The automatic-prefix radial assembly exposes the formula identity data. -/
noncomputable def formulaData
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData
      assembly.zeroTarget.toEventualPSeriesEnvelopeZeroData.zeroSide :=
  assembly.toEventualPSeriesAnalyticAssembly.formulaData

/-- The residual-nonnegative locus is closed for the assembled formula. -/
theorem residual_nonnegativeSet_closed
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.toEventualPSeriesAnalyticAssembly.residual_nonnegativeSet_closed

/-- Window zero-side sums converge to the formula residual side. -/
theorem tendsto_windowZeroSide_formulaResidualSide
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        assembly.toEventualPSeriesFormulaResidualInputData.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop (nhds (assembly.formulaData.sideData.residualSide f)) :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.tendsto_windowZeroSide_formulaResidualSide windowExhaustion f

/-- The automatic-prefix radial assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toEventualPSeriesAnalyticAssembly.RHOn_univ

/-- The automatic-prefix radial assembly proves the project RH statement. -/
theorem RHStatement
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toEventualPSeriesAnalyticAssembly.RHStatement

/-- The automatic-prefix radial assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly : RiemannWeilAutomaticPrefixRadialAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toEventualPSeriesAnalyticAssembly.mathlib_RH

end RiemannWeilAutomaticPrefixRadialAnalyticAssembly

/--
The cutoff-1 zero-data package obtained from a shifted-radius exact-norm
extension estimate.

This names the most direct analytic p-series input currently checked for the
closed-ball exhaustion: prove `norm (extension f z) <= C_f / (norm z + 2)^q`,
prove a compatible cutoff-1 zero-counting estimate, and Lean assembles the
eventual p-series zero side.
-/
noncomputable def shiftedRadiusCutoffOneExactNormZeroData
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofClosedBallShiftedRadiusExactNormCutoffOneSelf
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Shifted-radius exact-norm zero data from a cutoff-2 counting estimate plus one
explicit shell-1 bound.

This is the bridge from the project's preferred cutoff-2 published-counting
packages to the sharper cutoff-1 shifted-radius p-series route.
-/
noncomputable def shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  shiftedRadiusCutoffOneExactNormZeroData
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    (counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
      growth_nonneg shell_one_le)
    rfl
    growth_add_one_lt_decay

/--
Shifted-radius exact-norm zero data from a cutoff-2 cumulative-window counting
estimate plus one explicit window-1 bound.

This is the cumulative-window version of
`shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting`, matching the
shape of many height-counting or `N(T)` inputs before they are converted to
first-entry shell counting.
-/
noncomputable def shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  shiftedRadiusCutoffOneExactNormZeroData
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    ((counting.lowerCutoffTwoToOne counting_cutoff_eq_two
        newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
        growth_nonneg window_one_le).toPolynomialZeroCountingEstimate)
    rfl
    growth_add_one_lt_decay

/--
End-to-end assembly for the shifted-radius exact-norm cutoff-1 p-series route.

The real analytic inputs remain explicit: shifted-radius extension decay,
cutoff-1 closed-ball zero counting, the Guinand-Weil formula package for the
resulting zero side, coefficient identities, and residual nonnegativity.
-/
structure RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly where
  system : SchwartzRiemannWeilExtensionSystem
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  extension_norm_le_shiftedRadialBound :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      norm (system.extension f z) <=
        constant f * (1 / (norm z + 2) ^ decayExponent)
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate
      ComplexCompactExhaustion.closedBallZero
  counting_cutoff_eq : counting.cutoff = 1
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent
  formulaPackage :
    GuinandWeilProjectFormulaPackage
      (shiftedRadiusCutoffOneExactNormZeroData
        system constant decayExponent constant_nonneg decayExponent_nonneg
        extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
        growth_add_one_lt_decay).zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly

/-- The cutoff-1 shifted-radius zero data assembled from the analytic fields. -/
noncomputable def zeroData
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  shiftedRadiusCutoffOneExactNormZeroData
    assembly.system assembly.constant assembly.decayExponent
    assembly.constant_nonneg assembly.decayExponent_nonneg
    assembly.extension_norm_le_shiftedRadialBound assembly.counting
    assembly.counting_cutoff_eq assembly.growth_add_one_lt_decay

/-- Convert the shifted-radius cutoff-1 route to the generic eventual assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly where
  zeroData := assembly.zeroData
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the shifted-radius route into the preferred profiled shell target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/-- The shifted-radius cutoff-1 assembly exposes the formula identity data. -/
noncomputable def formulaData
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.toEventualPSeriesAnalyticAssembly.formulaData

/-- The residual-nonnegative locus is closed for the assembled formula. -/
theorem residual_nonnegativeSet_closed
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.toEventualPSeriesAnalyticAssembly.residual_nonnegativeSet_closed

/-- The shifted-radius cutoff-1 assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toEventualPSeriesAnalyticAssembly.RHOn_univ

/-- The shifted-radius cutoff-1 assembly proves the project RH statement. -/
theorem RHStatement
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toEventualPSeriesAnalyticAssembly.RHStatement

/-- The shifted-radius cutoff-1 assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly : RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toEventualPSeriesAnalyticAssembly.mathlib_RH

end RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly

/--
Source-formula version of the shifted-radius cutoff-1 p-series route.

This is the same analytic zero-data boundary as
`RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly`, but it keeps the
source-normalized Guinand-Weil package and normalization bridge visible. This
is the preferred receiving shape when the formula proof is being developed in
source notation.
-/
structure RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system : SchwartzRiemannWeilExtensionSystem
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  extension_norm_le_shiftedRadialBound :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      norm (system.extension f z) <=
        constant f * (1 / (norm z + 2) ^ decayExponent)
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate
      ComplexCompactExhaustion.closedBallZero
  counting_cutoff_eq : counting.cutoff = 1
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      (shiftedRadiusCutoffOneExactNormZeroData
        system constant decayExponent constant_nonneg decayExponent_nonneg
        extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
        growth_add_one_lt_decay).zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f

namespace RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly

/-- The cutoff-1 shifted-radius zero data assembled from the analytic fields. -/
noncomputable def zeroData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  shiftedRadiusCutoffOneExactNormZeroData
    assembly.system assembly.constant assembly.decayExponent
    assembly.constant_nonneg assembly.decayExponent_nonneg
    assembly.extension_norm_le_shiftedRadialBound assembly.counting
    assembly.counting_cutoff_eq assembly.growth_add_one_lt_decay

/-- Assemble the project-level formula package from the source package. -/
noncomputable def formulaPackage
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    GuinandWeilProjectFormulaPackage assembly.zeroData.zeroSide where
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge

/--
Forget the source-formula decomposition and use the project-normalized
shifted-radius cutoff-1 assembly.
-/
noncomputable def toShiftedRadiusCutoffOneAnalyticAssembly
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly where
  system := assembly.system
  constant := assembly.constant
  decayExponent := assembly.decayExponent
  constant_nonneg := assembly.constant_nonneg
  decayExponent_nonneg := assembly.decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    assembly.extension_norm_le_shiftedRadialBound
  counting := assembly.counting
  counting_cutoff_eq := assembly.counting_cutoff_eq
  growth_add_one_lt_decay := assembly.growth_add_one_lt_decay
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Convert the source-formula route to the generic eventual p-series assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly :=
  assembly.toShiftedRadiusCutoffOneAnalyticAssembly
    |>.toEventualPSeriesAnalyticAssembly

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toShiftedRadiusCutoffOneAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the source-formula route into the preferred profiled shell target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toShiftedRadiusCutoffOneAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/-- The source-formula assembly exposes the project-normalized formula data. -/
noncomputable def formulaData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.formulaPackage.formulaData

/-- Source formula data gives residual continuity for the project formula. -/
noncomputable def residualContinuityData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualContinuityData assembly.formulaData :=
  assembly.formulaPackage.residualContinuityData

/-- The project residual side is the source residual side after normalization. -/
theorem formulaResidualSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.formulaData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.formulaData_residualSide_eq_sourceResidualSide f

/-- The shifted-radius zero side is the source residual side after normalization. -/
theorem zeroSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.explicitFormula_sourceResidualSide f

/-- The residual-nonnegative locus is closed for the source-formula assembly. -/
theorem residual_nonnegativeSet_closed
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.formulaPackage.residual_nonnegativeSet_closed

/-- The source-formula cutoff-1 assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toShiftedRadiusCutoffOneAnalyticAssembly.RHOn_univ

/-- The source-formula cutoff-1 assembly proves the project RH statement. -/
theorem RHStatement
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toShiftedRadiusCutoffOneAnalyticAssembly.RHStatement

/-- The source-formula cutoff-1 assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toShiftedRadiusCutoffOneAnalyticAssembly.mathlib_RH

end RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly

/--
End-to-end assembly for the repaired zero-argument weighted shifted-radius
cutoff-1 p-series route.

Unlike `RiemannWeilShiftedRadiusCutoffOneAnalyticAssembly`, this package only
requires shifted-radius decay at the actual Riemann-Weil zero arguments.  This
is the analytically viable replacement for the old all-plane entire-extension
decay assumption.
-/
structure RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly where
  system : SchwartzRiemannWeilExtensionSystem
  certificate :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate
      ComplexCompactExhaustion.closedBallZero
  counting_cutoff_eq : counting.cutoff = 1
  growth_add_one_lt_decay :
    counting.growth + 1 < certificate.decayExponent
  formulaPackage :
    GuinandWeilProjectFormulaPackage
      (certificate.toCutoffOneClosedBallZeroData
        counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaPackage.formulaData.sideData.residualSide f

namespace RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly

/-- The cutoff-1 zero-argument weighted zero data assembled from the certificate. -/
noncomputable def zeroData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  assembly.certificate.toCutoffOneClosedBallZeroData
    assembly.counting assembly.counting_cutoff_eq
    assembly.growth_add_one_lt_decay

/-- Convert the zero-argument weighted route to the generic eventual assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly where
  zeroData := assembly.zeroData
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the zero-argument weighted route into the profiled shell target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toEventualPSeriesAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/-- The zero-argument weighted assembly exposes the formula identity data. -/
noncomputable def formulaData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.toEventualPSeriesAnalyticAssembly.formulaData

/-- The residual-nonnegative locus is closed for the assembled formula. -/
theorem residual_nonnegativeSet_closed
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.toEventualPSeriesAnalyticAssembly.residual_nonnegativeSet_closed

/-- The zero-argument weighted cutoff-1 assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toEventualPSeriesAnalyticAssembly.RHOn_univ

/-- The zero-argument weighted cutoff-1 assembly proves the project RH statement. -/
theorem RHStatement
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toEventualPSeriesAnalyticAssembly.RHStatement

/-- The zero-argument weighted cutoff-1 assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toEventualPSeriesAnalyticAssembly.mathlib_RH

end RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly

/--
Build the zero-argument weighted cutoff-1 assembly directly from the named
dense-core zero-locus p-series target.

This keeps the restricted dense-core source/core route visible at the final
assembly boundary instead of asking callers to first extract the weighted
certificate by hand.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.ofDenseCoreZeroLocusPSeriesTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (denseCoreTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilDenseCoreZeroLocusPSeriesTarget
        system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < denseCoreTarget.decayExponent)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        (denseCoreTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly where
  system := system
  certificate := denseCoreTarget.toWeightedDecayCertificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the zero-argument weighted cutoff-1 assembly directly from the named
source-image zero-locus p-series target.

This is the same closedness/source-image route as the dense-core constructor,
but with a genuine Guinand-Weil source class at the boundary.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.ofSourceImageZeroLocusPSeriesTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (sourceImageTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilSourceImageZeroLocusPSeriesTarget
        system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < sourceImageTarget.decayExponent)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        (sourceImageTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly where
  system := system
  certificate := sourceImageTarget.toWeightedDecayCertificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  formulaPackage := formulaPackage
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the zero-argument weighted cutoff-1 assembly directly from the named
actual-source finite-component strip/positive-axis p-series target.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.ofSourceImageFiniteComponentStripAxisPSeriesTarget
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (finiteComponentTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < finiteComponentTarget.decayExponent)
    (formulaPackage :
      GuinandWeilProjectFormulaPackage
        (finiteComponentTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge formulaPackage.formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaPackage.formulaData.sideData.residualSide f) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly :=
  RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.ofSourceImageZeroLocusPSeriesTarget
    finiteComponentTarget.toSourceImageZeroLocusPSeriesTarget counting
    counting_cutoff_eq growth_add_one_lt_decay formulaPackage liData
    residualToLi residual_nonneg

/--
Source-formula version of the zero-argument weighted shifted-radius cutoff-1
p-series route.

This is the preferred receiving shape for the Guinand-Weil formula proof: the
zero data now depends on the zero-locus certificate rather than on global
entire-extension decay.
-/
structure RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system : SchwartzRiemannWeilExtensionSystem
  certificate :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate
      ComplexCompactExhaustion.closedBallZero
  counting_cutoff_eq : counting.cutoff = 1
  growth_add_one_lt_decay :
    counting.growth + 1 < certificate.decayExponent
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      (certificate.toCutoffOneClosedBallZeroData
        counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData liData
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f

namespace RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly

/-- The cutoff-1 zero-argument weighted zero data assembled from the certificate. -/
noncomputable def zeroData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  assembly.certificate.toCutoffOneClosedBallZeroData
    assembly.counting assembly.counting_cutoff_eq
    assembly.growth_add_one_lt_decay

/-- Assemble the project-level formula package from the source package. -/
noncomputable def formulaPackage
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    GuinandWeilProjectFormulaPackage assembly.zeroData.zeroSide where
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge

/--
Forget the source-formula decomposition and use the project-normalized
zero-argument weighted cutoff-1 assembly.
-/
noncomputable def toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly where
  system := assembly.system
  certificate := assembly.certificate
  counting := assembly.counting
  counting_cutoff_eq := assembly.counting_cutoff_eq
  growth_add_one_lt_decay := assembly.growth_add_one_lt_decay
  formulaPackage := assembly.formulaPackage
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Convert the source-formula route to the generic eventual p-series assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly :=
  assembly.toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly
    |>.toEventualPSeriesAnalyticAssembly

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the source-formula route into the preferred profiled shell target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/-- The source-formula assembly exposes the project-normalized formula data. -/
noncomputable def formulaData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.formulaPackage.formulaData

/-- Source formula data gives residual continuity for the project formula. -/
noncomputable def residualContinuityData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualContinuityData assembly.formulaData :=
  assembly.formulaPackage.residualContinuityData

/-- The project residual side is the source residual side after normalization. -/
theorem formulaResidualSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.formulaData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.formulaData_residualSide_eq_sourceResidualSide f

/-- The zero-argument weighted zero side is the source residual side after normalization. -/
theorem zeroSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.explicitFormula_sourceResidualSide f

/-- The residual-nonnegative locus is closed for the source-formula assembly. -/
theorem residual_nonnegativeSet_closed
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.formulaPackage.residual_nonnegativeSet_closed

/-- The source-formula zero-argument weighted assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.RHOn_univ

/-- The source-formula zero-argument weighted assembly proves the project RH statement. -/
theorem RHStatement
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.RHStatement

/-- The source-formula zero-argument weighted assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toZeroArgumentWeightedShiftedRadiusCutoffOneAnalyticAssembly.mathlib_RH

end RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly

/--
Build the source-formula zero-argument weighted cutoff-1 assembly directly from
the named dense-core zero-locus p-series target.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly.ofDenseCoreZeroLocusPSeriesTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (denseCoreTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilDenseCoreZeroLocusPSeriesTarget
        system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < denseCoreTarget.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (denseCoreTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system := system
  certificate := denseCoreTarget.toWeightedDecayCertificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the source-formula zero-argument weighted cutoff-1 assembly directly from
the named source-image zero-locus p-series target.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly.ofSourceImageZeroLocusPSeriesTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (sourceImageTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilSourceImageZeroLocusPSeriesTarget
        system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < sourceImageTarget.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (sourceImageTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system := system
  certificate := sourceImageTarget.toWeightedDecayCertificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the source-formula zero-argument weighted cutoff-1 assembly directly from
the actual-source finite-component strip/positive-axis p-series target.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly.ofSourceImageFiniteComponentStripAxisPSeriesTarget
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (finiteComponentTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < finiteComponentTarget.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (finiteComponentTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly :=
  RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly.ofSourceImageZeroLocusPSeriesTarget
    finiteComponentTarget.toSourceImageZeroLocusPSeriesTarget counting
    counting_cutoff_eq growth_add_one_lt_decay sourcePackage
    normalizationBridge liData residualToLi residual_nonneg

/--
Support-density version of the zero-argument weighted source-formula route.

This is the downstream target for the residual positivity blocker: restricted
positivity and dense-core promotion can now be combined with the repaired
zero-locus p-series decay hypothesis.
-/
structure RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system : SchwartzRiemannWeilExtensionSystem
  certificate :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate
      ComplexCompactExhaustion.closedBallZero
  counting_cutoff_eq : counting.cutoff = 1
  growth_add_one_lt_decay :
    counting.growth + 1 < certificate.decayExponent
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      (certificate.toCutoffOneClosedBallZeroData
        counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData liData
  restrictedData :
    SupportRestrictedFormulaResidualPositivityData
      normalizationBridge.toFormulaIdentityData
  denseCore :
    SupportRestrictedFormulaResidualDenseCore restrictedData

namespace RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly

/-- The cutoff-1 zero-argument weighted zero data assembled from the certificate. -/
noncomputable def zeroData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  assembly.certificate.toCutoffOneClosedBallZeroData
    assembly.counting assembly.counting_cutoff_eq
    assembly.growth_add_one_lt_decay

/-- Assemble the project-level formula package from the source package. -/
noncomputable def formulaPackage
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    GuinandWeilProjectFormulaPackage assembly.zeroData.zeroSide where
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge

/-- The project-normalized formula identity data. -/
noncomputable def formulaData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.formulaPackage.formulaData

/-- Source formula data gives residual continuity for the project formula. -/
noncomputable def residualContinuityData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualContinuityData assembly.formulaData :=
  assembly.formulaPackage.residualContinuityData

/-- Dense-core promotion gives the support-restricted density bridge. -/
noncomputable def supportDensityBridge
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SupportRestrictedFormulaResidualDensityBridge assembly.restrictedData :=
  assembly.denseCore.toSupportRestrictedDensityBridgeOfResidualContinuity
    assembly.residualContinuityData

/-- Support-restricted positivity plus density promotes to full residual nonnegativity. -/
theorem residual_nonneg
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    forall f : SchwartzLineTestFunction,
      0 <= assembly.formulaData.sideData.residualSide f :=
  assembly.supportDensityBridge.residual_nonneg

/--
Build the source-formula cutoff-1 assembly with full residual nonnegativity
supplied by support-density promotion.
-/
noncomputable def toSourceFormulaAnalyticAssembly
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system := assembly.system
  certificate := assembly.certificate
  counting := assembly.counting
  counting_cutoff_eq := assembly.counting_cutoff_eq
  growth_add_one_lt_decay := assembly.growth_add_one_lt_decay
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Convert the support-density route to the generic eventual p-series assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly :=
  assembly.toSourceFormulaAnalyticAssembly.toEventualPSeriesAnalyticAssembly

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the support-density route into the preferred profiled shell target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toSourceFormulaAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/--
The formula residual positivity package obtained through the coefficient-level
residual-to-Li bridge after density has promoted restricted positivity.
-/
noncomputable def formulaResidualDataFromLi
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualPositivityData assembly.formulaData :=
  assembly.residualToLi.toFormulaResidualPositivityData
    assembly.residual_nonneg

/-- The density bridge itself also yields formula residual positivity data. -/
noncomputable def formulaResidualDataFromDensity
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualPositivityData assembly.formulaData :=
  assembly.supportDensityBridge.toFormulaResidualPositivityData

/-- The project residual side is the source residual side after normalization. -/
theorem formulaResidualSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.formulaData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.formulaData_residualSide_eq_sourceResidualSide f

/-- The zero-argument weighted zero side is the source residual side after normalization. -/
theorem zeroSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.explicitFormula_sourceResidualSide f

/-- The residual-nonnegative locus is closed for the support-density assembly. -/
theorem residual_nonnegativeSet_closed
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.formulaPackage.residual_nonnegativeSet_closed

/-- The support-density zero-argument weighted assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSourceFormulaAnalyticAssembly.RHOn_univ

/-- The support-density zero-argument weighted assembly proves the project RH statement. -/
theorem RHStatement
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSourceFormulaAnalyticAssembly.RHStatement

/-- The support-density zero-argument weighted assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly :
      RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toSourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly

/--
Build the support-density zero-argument weighted cutoff-1 assembly directly
from the named dense-core zero-locus p-series target.

This is the theorem-facing handoff for the restricted dense-core p-series
route plus source formula, Li bridge, support-restricted positivity, and
density promotion.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofDenseCoreZeroLocusPSeriesTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (denseCoreTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilDenseCoreZeroLocusPSeriesTarget
        system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < denseCoreTarget.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (denseCoreTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  certificate := denseCoreTarget.toWeightedDecayCertificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the support-density zero-argument weighted cutoff-1 assembly directly
from the named source-image zero-locus p-series target.

This is the theorem-facing handoff for a genuine dense admissible source image,
source formula, Li bridge, support-restricted positivity, and density
promotion.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceImageZeroLocusPSeriesTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (sourceImageTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilSourceImageZeroLocusPSeriesTarget
        system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < sourceImageTarget.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (sourceImageTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  certificate := sourceImageTarget.toWeightedDecayCertificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the support-density zero-argument weighted cutoff-1 assembly directly
from the actual-source finite-component strip/positive-axis p-series target.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceImageFiniteComponentStripAxisPSeriesTarget
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (finiteComponentTarget :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate.RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < finiteComponentTarget.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (finiteComponentTarget.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceImageZeroLocusPSeriesTarget
    finiteComponentTarget.toSourceImageZeroLocusPSeriesTarget counting
    counting_cutoff_eq growth_add_one_lt_decay sourcePackage
    normalizationBridge liData residualToLi restrictedData denseCore

/--
Build the support-density zero-argument weighted cutoff-1 assembly from a
localized Weil quadratic-form target.  This constructor keeps the hard
positivity proof separated from the repaired p-series decay hypothesis.
-/
noncomputable def RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
    (system : SchwartzRiemannWeilExtensionSystem)
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (certificate.toCutoffOneClosedBallZeroData
          counting counting_cutoff_eq growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilZeroArgumentWeightedShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  certificate := certificate
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    localizedTarget.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the source-formula shifted-radius cutoff-1 assembly from a cutoff-2
first-entry shell counting estimate plus an explicit shell-1 bound.

This is the source-formula companion to
`shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting`.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly.ofCutoffTwoCounting
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
          growth_nonneg shell_one_le growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f) :
    RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting :=
    counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
      growth_nonneg shell_one_le
  counting_cutoff_eq := rfl
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Build the source-formula shifted-radius cutoff-1 assembly from a cutoff-2
cumulative-window counting estimate plus an explicit window-1 bound.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly.ofCutoffTwoCumulativeCounting
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
          growth_nonneg window_one_le growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= normalizationBridge.toFormulaIdentityData.sideData.residualSide f) :
    RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting :=
    (counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
      growth_nonneg window_one_le).toPolynomialZeroCountingEstimate
  counting_cutoff_eq := rfl
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  residual_nonneg := residual_nonneg

/--
Support-density version of the shifted-radius cutoff-1 source-formula route.

This replaces the full residual-nonnegativity field by the standard restricted
positivity plus dense-core promotion package. The real analytic obligations are
therefore: shifted-radius extension decay, compatible zero counting, source
Guinand-Weil formula and normalization, residual-to-Li identities,
support-restricted residual positivity, and dense-core/continuity promotion.
-/
structure RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system : SchwartzRiemannWeilExtensionSystem
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  extension_norm_le_shiftedRadialBound :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      norm (system.extension f z) <=
        constant f * (1 / (norm z + 2) ^ decayExponent)
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate
      ComplexCompactExhaustion.closedBallZero
  counting_cutoff_eq : counting.cutoff = 1
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent
  sourcePackage : GuinandWeilSourceFormulaPackage
  normalizationBridge :
    GuinandWeilNormalizationBridge
      sourcePackage.sourceData
      (shiftedRadiusCutoffOneExactNormZeroData
        system constant decayExponent constant_nonneg decayExponent_nonneg
        extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
        growth_add_one_lt_decay).zeroSide
  liData : AbstractLiCriterionData (fun _ : Complex => True)
  residualToLi :
    FormulaResidualToLiCoefficientBridge
      normalizationBridge.toFormulaIdentityData liData
  restrictedData :
    SupportRestrictedFormulaResidualPositivityData
      normalizationBridge.toFormulaIdentityData
  denseCore :
    SupportRestrictedFormulaResidualDenseCore restrictedData

namespace RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly

/-- The cutoff-1 shifted-radius zero data assembled from the analytic fields. -/
noncomputable def zeroData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  shiftedRadiusCutoffOneExactNormZeroData
    assembly.system assembly.constant assembly.decayExponent
    assembly.constant_nonneg assembly.decayExponent_nonneg
    assembly.extension_norm_le_shiftedRadialBound assembly.counting
    assembly.counting_cutoff_eq assembly.growth_add_one_lt_decay

/-- Assemble the project-level formula package from the source package. -/
noncomputable def formulaPackage
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    GuinandWeilProjectFormulaPackage assembly.zeroData.zeroSide where
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge

/-- The project-normalized formula identity data. -/
noncomputable def formulaData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaIdentityData assembly.zeroData.zeroSide :=
  assembly.formulaPackage.formulaData

/-- Source formula data gives residual continuity for the project formula. -/
noncomputable def residualContinuityData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualContinuityData assembly.formulaData :=
  assembly.formulaPackage.residualContinuityData

/-- Dense-core promotion gives the support-restricted density bridge. -/
noncomputable def supportDensityBridge
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SupportRestrictedFormulaResidualDensityBridge assembly.restrictedData :=
  assembly.denseCore.toSupportRestrictedDensityBridgeOfResidualContinuity
    assembly.residualContinuityData

/-- Support-restricted positivity plus density promotes to full residual nonnegativity. -/
theorem residual_nonneg
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    forall f : SchwartzLineTestFunction,
      0 <= assembly.formulaData.sideData.residualSide f :=
  assembly.supportDensityBridge.residual_nonneg

/--
Build the source-formula cutoff-1 assembly with full residual nonnegativity
supplied by support-density promotion.
-/
noncomputable def toSourceFormulaAnalyticAssembly
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannWeilShiftedRadiusCutoffOneSourceFormulaAnalyticAssembly where
  system := assembly.system
  constant := assembly.constant
  decayExponent := assembly.decayExponent
  constant_nonneg := assembly.constant_nonneg
  decayExponent_nonneg := assembly.decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    assembly.extension_norm_le_shiftedRadialBound
  counting := assembly.counting
  counting_cutoff_eq := assembly.counting_cutoff_eq
  growth_add_one_lt_decay := assembly.growth_add_one_lt_decay
  sourcePackage := assembly.sourcePackage
  normalizationBridge := assembly.normalizationBridge
  liData := assembly.liData
  residualToLi := assembly.residualToLi
  residual_nonneg := assembly.residual_nonneg

/-- Convert the support-density route to the generic eventual p-series assembly. -/
noncomputable def toEventualPSeriesAnalyticAssembly
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannWeilEventualPSeriesAnalyticAssembly :=
  assembly.toSourceFormulaAnalyticAssembly.toEventualPSeriesAnalyticAssembly

/-- Assemble the final eventual p-series formula-residual input package. -/
noncomputable def toEventualPSeriesFormulaResidualInputData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeFormulaResidualInputData :=
  assembly.toSourceFormulaAnalyticAssembly
    |>.toEventualPSeriesFormulaResidualInputData

/-- Convert the support-density route into the preferred profiled shell target. -/
noncomputable def toProfiledShellFormulaResidualInputData
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData :=
  assembly.toSourceFormulaAnalyticAssembly
    |>.toProfiledShellFormulaResidualInputData

/--
The formula residual positivity package obtained through the coefficient-level
residual-to-Li bridge after density has promoted restricted positivity.
-/
noncomputable def formulaResidualDataFromLi
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualPositivityData assembly.formulaData :=
  assembly.residualToLi.toFormulaResidualPositivityData
    assembly.residual_nonneg

/-- The density bridge itself also yields formula residual positivity data. -/
noncomputable def formulaResidualDataFromDensity
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    SchwartzRiemannWeilFormulaResidualPositivityData assembly.formulaData :=
  assembly.supportDensityBridge.toFormulaResidualPositivityData

/-- The project residual side is the source residual side after normalization. -/
theorem formulaResidualSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.formulaData.sideData.residualSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.formulaData_residualSide_eq_sourceResidualSide f

/-- The shifted-radius zero side is the source residual side after normalization. -/
theorem zeroSide_eq_sourceResidualSide
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly)
    (f : SchwartzLineTestFunction) :
    assembly.zeroData.zeroSide.zeroSide f =
      assembly.sourcePackage.sourceData.sideData.sourceResidualSide f :=
  assembly.formulaPackage.explicitFormula_sourceResidualSide f

/-- The residual-nonnegative locus is closed for the support-density assembly. -/
theorem residual_nonnegativeSet_closed
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    IsClosed (formulaResidualNonnegativeSet assembly.formulaData) :=
  assembly.formulaPackage.residual_nonnegativeSet_closed

/-- The support-density cutoff-1 assembly proves universal local RH. -/
theorem RHOn_univ
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RHOn (fun _ : Complex => True) :=
  assembly.toSourceFormulaAnalyticAssembly.RHOn_univ

/-- The support-density cutoff-1 assembly proves the project RH statement. -/
theorem RHStatement
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannHypothesisProject.RHStatement :=
  assembly.toSourceFormulaAnalyticAssembly.RHStatement

/-- The support-density cutoff-1 assembly proves Mathlib RH. -/
theorem mathlib_RH
    (assembly :
      RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly) :
    RiemannHypothesis :=
  assembly.toSourceFormulaAnalyticAssembly.mathlib_RH

end RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly

/--
Build the support-density shifted-radius cutoff-1 assembly from a localized
Weil quadratic-form target. The localized target supplies restricted residual
positivity; the dense-core field remains explicit.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofLocalizedQuadraticFormTarget
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroData
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
          growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData :=
    localizedTarget.toSupportRestrictedFormulaResidualPositivityData
  denseCore := denseCore

/--
Build the support-density shifted-radius cutoff-1 assembly from source-residual
Li coefficient identities and formula-side residual nonnegativity on
admissible coefficient tests.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualCoefficientIdentities
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroData
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
          growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi :=
    (SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientTest coefficientTest_admissible coefficientScale
      coefficientScale_nonneg coefficient_eq_scaled_sourceResidual)
        |>.toFormulaResidualToLiCoefficientBridge
  restrictedData :=
    (SupportRestrictedFormulaResidualToLiCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientTest coefficientTest_admissible coefficientScale
      coefficientScale_nonneg coefficient_eq_scaled_sourceResidual)
        |>.toSupportRestrictedFormulaResidualPositivityData
          residual_nonneg_on_admissible
  denseCore := denseCore

/--
Build the support-density shifted-radius cutoff-1 assembly from source-residual
coefficient identities and source-residual nonnegativity on admissible tests.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualCoefficientIdentitiesAndNonnegativity
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroData
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
          growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofSourceResidualCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
    growth_add_one_lt_decay sourcePackage normalizationBridge liData
    admissible coefficientTest coefficientTest_admissible coefficientScale
    coefficientScale_nonneg coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the support-density shifted-radius cutoff-1 assembly from cutoff-2
source-residual Li coefficient identities and formula-side residual
nonnegativity on admissible coefficient tests.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentities
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroData
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
          growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi :=
    (SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientOneTest coefficientOneTest_admissible
      coefficientOneScale coefficientOneScale_nonneg
      coefficient_one_eq_scaled_sourceResidual
      tailCoefficientTest tailCoefficientTest_admissible
      tailCoefficientScale tailCoefficientScale_nonneg
      tail_coefficient_eq_scaled_sourceResidual)
        |>.toSupportRestrictedFormulaResidualToLiCoefficientBridge
        |>.toFormulaResidualToLiCoefficientBridge
  restrictedData :=
    (SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge.ofResidualSideEq
      sourcePackage.sourceData.sideData.sourceResidualSide
      (fun f => normalizationBridge.toFormulaIdentityData_residualSide f)
      coefficientOneTest coefficientOneTest_admissible
      coefficientOneScale coefficientOneScale_nonneg
      coefficient_one_eq_scaled_sourceResidual
      tailCoefficientTest tailCoefficientTest_admissible
      tailCoefficientScale tailCoefficientScale_nonneg
      tail_coefficient_eq_scaled_sourceResidual)
        |>.toSupportRestrictedFormulaResidualPositivityData
          residual_nonneg_on_admissible
  denseCore := denseCore

/--
Build the support-density shifted-radius cutoff-1 assembly from cutoff-2
source-residual coefficient identities and source-residual nonnegativity on
admissible tests.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroData
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
          growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofSourceResidualCutoffTwoCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq
    growth_add_one_lt_decay sourcePackage normalizationBridge liData
    admissible coefficientOneTest coefficientOneTest_admissible
    coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual tailCoefficientTest
    tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the coefficient-test support-density shifted-radius assembly from a
cutoff-2 first-entry shell counting estimate plus an explicit shell-1 bound.

This combines the published-counting lowering step with source-residual Li
coefficient identities, so future Bellotti-Wong/HSW-style counting inputs can
enter the Li/coefficient route without manually constructing the cutoff-1
counting package first.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCountingSourceResidualCoefficientIdentities
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
          growth_nonneg shell_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofSourceResidualCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    (counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
      growth_nonneg shell_one_le)
    rfl growth_add_one_lt_decay sourcePackage normalizationBridge liData
    admissible coefficientTest coefficientTest_admissible coefficientScale
    coefficientScale_nonneg coefficient_eq_scaled_sourceResidual
    residual_nonneg_on_admissible denseCore

/--
Build the coefficient-test support-density shifted-radius assembly from a
cutoff-2 cumulative-window counting estimate plus an explicit window-1 bound.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCumulativeCountingSourceResidualCoefficientIdentities
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
          growth_nonneg window_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofSourceResidualCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    ((counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
      growth_nonneg window_one_le).toPolynomialZeroCountingEstimate)
    rfl growth_add_one_lt_decay sourcePackage normalizationBridge liData
    admissible coefficientTest coefficientTest_admissible coefficientScale
    coefficientScale_nonneg coefficient_eq_scaled_sourceResidual
    residual_nonneg_on_admissible denseCore

/--
Build the coefficient-test support-density shifted-radius assembly from a
cutoff-2 first-entry shell counting estimate and source-residual nonnegativity.

This is the source-side nonnegativity variant of
`ofCutoffTwoCountingSourceResidualCoefficientIdentities`: the normalization
bridge transports positivity on the source residual to the formula residual.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCountingSourceResidualCoefficientIdentitiesAndNonnegativity
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
          growth_nonneg shell_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofCutoffTwoCountingSourceResidualCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
    newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
    growth_nonneg shell_one_le growth_add_one_lt_decay sourcePackage
    normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the coefficient-test support-density shifted-radius assembly from a
cutoff-2 cumulative-window counting estimate and source-residual nonnegativity.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCumulativeCountingSourceResidualCoefficientIdentitiesAndNonnegativity
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
          growth_nonneg window_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofCutoffTwoCumulativeCountingSourceResidualCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
    newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
    growth_nonneg window_one_le growth_add_one_lt_decay sourcePackage
    normalizationBridge liData admissible coefficientTest
    coefficientTest_admissible coefficientScale coefficientScale_nonneg
    coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the cutoff-2 coefficient-test support-density shifted-radius assembly
from a cutoff-2 first-entry shell counting estimate plus an explicit shell-1
bound.

This is the most decomposed published-counting/Li route in the generic
shifted-radius cutoff-1 assembly: counting is lowered from cutoff `2` to
cutoff `1`, while Li coefficient `1` and the `2 <= n` tail keep separate
admissible test families.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCountingSourceResidualCutoffTwoCoefficientIdentities
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
          growth_nonneg shell_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofSourceResidualCutoffTwoCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    (counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
      growth_nonneg shell_one_le)
    rfl growth_add_one_lt_decay sourcePackage normalizationBridge liData
    admissible coefficientOneTest coefficientOneTest_admissible
    coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual tailCoefficientTest
    tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    residual_nonneg_on_admissible denseCore

/--
Build the cutoff-2 coefficient-test support-density shifted-radius assembly
from a cutoff-2 cumulative-window counting estimate plus an explicit window-1
bound.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCumulativeCountingSourceResidualCutoffTwoCoefficientIdentities
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
          growth_nonneg window_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofSourceResidualCutoffTwoCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    ((counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
      growth_nonneg window_one_le).toPolynomialZeroCountingEstimate)
    rfl growth_add_one_lt_decay sourcePackage normalizationBridge liData
    admissible coefficientOneTest coefficientOneTest_admissible
    coefficientOneScale coefficientOneScale_nonneg
    coefficient_one_eq_scaled_sourceResidual tailCoefficientTest
    tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    residual_nonneg_on_admissible denseCore

/--
Build the cutoff-2 coefficient-test support-density shifted-radius assembly
from a cutoff-2 first-entry shell counting estimate and source-residual
nonnegativity on admissible tests.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCountingSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
          growth_nonneg shell_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofCutoffTwoCountingSourceResidualCutoffTwoCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
    newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
    growth_nonneg shell_one_le growth_add_one_lt_decay sourcePackage
    normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the cutoff-2 coefficient-test support-density shifted-radius assembly
from a cutoff-2 cumulative-window counting estimate and source-residual
nonnegativity on admissible tests.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCumulativeCountingSourceResidualCutoffTwoCoefficientIdentitiesAndNonnegativity
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
          growth_nonneg window_one_le growth_add_one_lt_decay).zeroSide)
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
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly :=
  ofCutoffTwoCumulativeCountingSourceResidualCutoffTwoCoefficientIdentities
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
    newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
    growth_nonneg window_one_le growth_add_one_lt_decay sourcePackage
    normalizationBridge liData admissible coefficientOneTest
    coefficientOneTest_admissible coefficientOneScale
    coefficientOneScale_nonneg coefficient_one_eq_scaled_sourceResidual
    tailCoefficientTest tailCoefficientTest_admissible tailCoefficientScale
    tailCoefficientScale_nonneg tail_coefficient_eq_scaled_sourceResidual
    (normalizationBridge.residual_nonneg_on_admissible_of_source
      admissible source_residual_nonneg_on_admissible)
    denseCore

/--
Build the support-density shifted-radius cutoff-1 assembly from a cutoff-2
first-entry shell counting estimate plus an explicit shell-1 bound.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCounting
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      counting.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (shell_one_le :
      counting.shellCardBound 1 <= newShellCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
          growth_nonneg shell_one_le growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting :=
    counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newShellCardConstant newShellCardConstant_nonneg oldConstant_le_new
      growth_nonneg shell_one_le
  counting_cutoff_eq := rfl
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

/--
Build the support-density shifted-radius cutoff-1 assembly from a cutoff-2
cumulative-window counting estimate plus an explicit window-1 bound.
-/
noncomputable def RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly.ofCutoffTwoCumulativeCounting
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
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq_two : counting.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      counting.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= counting.growth)
    (window_one_le :
      counting.windowCardBound 1 <= newWindowCardConstant)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent)
    (sourcePackage : GuinandWeilSourceFormulaPackage)
    (normalizationBridge :
      GuinandWeilNormalizationBridge
        sourcePackage.sourceData
        (shiftedRadiusCutoffOneExactNormZeroDataOfCutoffTwoCumulativeCounting
          system constant decayExponent constant_nonneg decayExponent_nonneg
          extension_norm_le_shiftedRadialBound counting counting_cutoff_eq_two
          newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
          growth_nonneg window_one_le growth_add_one_lt_decay).zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (residualToLi :
      FormulaResidualToLiCoefficientBridge
        normalizationBridge.toFormulaIdentityData liData)
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData
        normalizationBridge.toFormulaIdentityData)
    (denseCore :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    RiemannWeilShiftedRadiusCutoffOneSupportDensitySourceFormulaAnalyticAssembly where
  system := system
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  extension_norm_le_shiftedRadialBound :=
    extension_norm_le_shiftedRadialBound
  counting :=
    (counting.lowerCutoffTwoToOne counting_cutoff_eq_two
      newWindowCardConstant newWindowCardConstant_nonneg oldConstant_le_new
      growth_nonneg window_one_le).toPolynomialZeroCountingEstimate
  counting_cutoff_eq := rfl
  growth_add_one_lt_decay := growth_add_one_lt_decay
  sourcePackage := sourcePackage
  normalizationBridge := normalizationBridge
  liData := liData
  residualToLi := residualToLi
  restrictedData := restrictedData
  denseCore := denseCore

end

end RiemannHypothesisProject
