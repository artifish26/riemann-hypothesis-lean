import RiemannHypothesisProject.SchwartzRiemannWeilProfiledTailCertificateData

/-!
# Final analytic input packages for the Schwartz Riemann-Weil route

The lower-level files split the route into tail estimates, formula-side data,
and positivity packages. This file names the combined targets that remain for
the analytic project:

* a tail-estimate input package; and
* a profiled tail-estimate input package keeping the extension profile visible.

Both packages contain only the remaining mathematical inputs. Lean then
assembles the existing certificates, global criterion, project RH statement,
and Mathlib `RiemannHypothesis` consequence.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/--
Formula identity data relative to an abstract p-series zero side.

This is the formula-facing work package for restricted-source p-series routes:
the zero side is produced by a direct abstract weight summability certificate,
not by a global all-Schwartz extension system.
-/
structure SchwartzRiemannWeilAbstractPSeriesFormulaData
    {exhaustion : ComplexCompactExhaustion}
    (zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion) where
  formulaData :
    SchwartzRiemannWeilFormulaIdentityData zeroData.toZeroSide

namespace SchwartzRiemannWeilAbstractPSeriesFormulaData

/-- Build abstract p-series formula data directly from raw formula sides. -/
noncomputable def ofRawSides
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        zeroData.toZeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f) :
    SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData where
  formulaData :=
    SchwartzRiemannWeilFormulaIdentityData.ofRawSides
      primeSide poleSide gammaSide explicitFormula

/-- Compact-exhaustion sums converge to the formula-side residual expression. -/
theorem tendsto_windowZeroSide_formulaResidualSide
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    (formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => zeroData.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (formulaData.formulaData.sideData.residualSide f)) := by
  rw [← formulaData.formulaData.explicitFormula f]
  exact zeroData.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractPSeriesFormulaData

/-- Formula-side residual positivity relative to abstract p-series formula data. -/
structure SchwartzRiemannWeilAbstractPSeriesResidualPositivityData
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    (formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData) where
  formulaResidualData :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData.formulaData

namespace SchwartzRiemannWeilAbstractPSeriesResidualPositivityData

/-- Build abstract p-series residual positivity from raw residual-side data. -/
noncomputable def ofRawResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    {formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData}
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.formulaData.sideData.residualSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= formulaData.formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilAbstractPSeriesResidualPositivityData
      formulaData where
  formulaResidualData :=
    SchwartzRiemannWeilFormulaResidualPositivityData.ofRawResidualPositivity
      residual_nonneg residual_positivity_implies_RHOn_univ

/-- The packaged formula residual side is nonnegative. -/
theorem formulaResidual_nonneg
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    {formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData}
    (positivityData :
      SchwartzRiemannWeilAbstractPSeriesResidualPositivityData
        formulaData)
    (f : SchwartzLineTestFunction) :
    0 <= formulaData.formulaData.sideData.residualSide f :=
  positivityData.formulaResidualData.residual_nonneg f

/-- Formula-side residual positivity proves universal local RH. -/
theorem formulaResidual_positivity_implies_RHOn_univ
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    {formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData}
    (positivityData :
      SchwartzRiemannWeilAbstractPSeriesResidualPositivityData
        formulaData) :
    (forall f : SchwartzLineTestFunction,
      0 <= formulaData.formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True) :=
  positivityData.formulaResidualData.residual_positivity_implies_RHOn_univ

end SchwartzRiemannWeilAbstractPSeriesResidualPositivityData

/--
The combined abstract p-series analytic input package.

This is the theorem-facing endpoint for restricted-source p-series work when
the zero-side weight is supplied directly: prove first-entry shell counting,
direct weight p-series decay, the explicit formula, and residual positivity;
Lean then assembles the existing decomposed Riemann-Weil certificate.
-/
structure SchwartzRiemannWeilAbstractPSeriesAnalyticInputData where
  exhaustion : ComplexCompactExhaustion
  zeroData :
    SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion
  formulaData :
    SchwartzRiemannWeilFormulaIdentityData zeroData.toZeroSide
  formulaResidualData :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData

namespace SchwartzRiemannWeilAbstractPSeriesAnalyticInputData

/-- Build the combined package from the split abstract p-series work packages. -/
noncomputable def ofWorkPackages
    {exhaustion : ComplexCompactExhaustion}
    {zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion}
    {formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData}
    (positivityData :
      SchwartzRiemannWeilAbstractPSeriesResidualPositivityData
        formulaData) :
    SchwartzRiemannWeilAbstractPSeriesAnalyticInputData where
  exhaustion := exhaustion
  zeroData := zeroData
  formulaData := formulaData.formulaData
  formulaResidualData := positivityData.formulaResidualData

/--
Build the full abstract p-series endpoint from zero data, raw formula sides,
and raw residual positivity.
-/
noncomputable def ofZeroDataAndRawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    (zeroData :
      SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        zeroData.toZeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilAbstractPSeriesAnalyticInputData := by
  let formulaData :
      SchwartzRiemannWeilAbstractPSeriesFormulaData zeroData :=
    SchwartzRiemannWeilAbstractPSeriesFormulaData.ofRawSides
      primeSide poleSide gammaSide explicitFormula
  let positivityData :
      SchwartzRiemannWeilAbstractPSeriesResidualPositivityData
        formulaData :=
    { formulaResidualData :=
        { residual_nonneg := fun f => by
            change 0 <= primeSide f + poleSide f + gammaSide f
            exact residual_nonneg f
          residual_positivity_implies_RHOn_univ := fun hres =>
            residual_positivity_implies_RHOn_univ <| fun f => by
              have hf := hres f
              change 0 <= primeSide f + poleSide f + gammaSide f at hf
              exact hf } }
  exact ofWorkPackages positivityData

/--
Build the full abstract p-series endpoint from polynomial-cardinality zero
data, raw formula sides, and raw residual positivity.
-/
noncomputable def ofPolynomialCardZeroDataAndRawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    (zeroData :
      SchwartzRiemannWeilAbstractEventualPolynomialCardPSeriesTailMajorant
        exhaustion)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        zeroData.toZeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilAbstractPSeriesAnalyticInputData :=
  ofZeroDataAndRawFormulaResidual
    zeroData.toEventualPSeriesTailMajorant
    primeSide poleSide gammaSide
    explicitFormula
    residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Build the full abstract p-series endpoint from polynomial-cardinality decay
zero data, raw formula sides, and raw residual positivity.
-/
noncomputable def ofPolynomialCardDecayZeroDataAndRawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    (zeroData :
      SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
        exhaustion)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        zeroData.toZeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilAbstractPSeriesAnalyticInputData :=
  ofZeroDataAndRawFormulaResidual
    zeroData.toEventualPSeriesTailMajorant
    primeSide poleSide gammaSide
    explicitFormula
    residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Build the full abstract p-series endpoint from separated polynomial counting
and direct weight-decay data, raw formula sides, and raw residual positivity.
-/
noncomputable def ofAbstractSeparatedPolynomialDecayAndRawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    (zeroData :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        zeroData.toZeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilAbstractPSeriesAnalyticInputData :=
  ofZeroDataAndRawFormulaResidual
    zeroData.toEventualPSeriesTailMajorant
    primeSide poleSide gammaSide
    explicitFormula
    residual_nonneg
    residual_positivity_implies_RHOn_univ

/--
Build the full abstract p-series endpoint from packaged polynomial counting, a
cutoff-zero direct global p-series bound for the supplied weight, raw formula
sides, and raw residual positivity.
-/
noncomputable def ofAbstractCountingAndGlobalPSeriesWeightBoundAndRawFormulaResidual
    {exhaustion : ComplexCompactExhaustion}
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (norm_weight_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq_zero : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndGlobalPSeriesWeightBound
          weight zeroConstant decayExponent zeroConstant_nonneg
          norm_weight_le_pseries counting counting_cutoff_eq_zero
          growth_add_one_lt_decay).toZeroSide.zeroSide f =
          primeSide f + poleSide f + gammaSide f)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= primeSide f + poleSide f + gammaSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilAbstractPSeriesAnalyticInputData :=
  ofAbstractSeparatedPolynomialDecayAndRawFormulaResidual
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndGlobalPSeriesWeightBound
      weight zeroConstant decayExponent zeroConstant_nonneg
      norm_weight_le_pseries counting counting_cutoff_eq_zero
      growth_add_one_lt_decay)
    primeSide poleSide gammaSide
    explicitFormula
    residual_nonneg
    residual_positivity_implies_RHOn_univ

/-- The zero side produced by the abstract p-series estimate. -/
noncomputable def zeroSide
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    SchwartzRiemannWeilZeroSide :=
  data.zeroData.toZeroSide

/-- The abstract p-series zero side uses the supplied direct weight. -/
theorem zeroSide_weight
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.zeroData.weight f rho := by
  simpa [zeroSide] using data.zeroData.toZeroSide_weight f rho

/-- Compact-exhaustion sums converge for the abstract p-series zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.zeroSide.zeroSide f)) := by
  simpa [zeroSide] using
    data.zeroData.tendsto_windowZeroSide windowExhaustion f

/-- Export the abstract package as decomposed explicit-formula data. -/
noncomputable def toExplicitFormulaData
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    SchwartzRiemannWeilExplicitFormulaData :=
  data.formulaData.toExplicitFormulaData

/-- Export formula-side residual positivity as packaged positivity data. -/
noncomputable def toPackagedPositivityData
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    SchwartzRiemannWeilPackagedPositivityData
      data.formulaData.toExplicitFormulaData :=
  SchwartzRiemannWeilPackagedPositivityData.ofFormulaResidualPositivityData
    data.formulaResidualData

/-- Assemble the abstract p-series inputs into the decomposed certificate. -/
noncomputable def toCertificateData
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    SchwartzRiemannWeilCertificateData where
  formulaData := data.toExplicitFormulaData
  positivityData := data.toPackagedPositivityData.toPositivityData

/-- Assemble the abstract p-series inputs into the global criterion. -/
noncomputable def toGlobalCriterion
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    SchwartzRiemannWeilGlobalCriterion :=
  data.toCertificateData.toGlobalCriterion

/-- The abstract p-series residual side is nonnegative. -/
theorem formulaResidual_nonneg
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData)
    (f : SchwartzLineTestFunction) :
    0 <= data.formulaData.sideData.residualSide f :=
  data.formulaResidualData.residual_nonneg f

/-- The abstract p-series zero side equals the formula residual side. -/
theorem zeroSide_eq_formulaResidualSide
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData)
    (f : SchwartzLineTestFunction) :
    data.zeroSide.zeroSide f = data.formulaData.sideData.residualSide f := by
  simpa [zeroSide] using data.formulaData.explicitFormula f

/-- Abstract p-series zero-window sums converge to the formula residual side. -/
theorem tendsto_windowZeroSide_formulaResidualSide
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.formulaData.sideData.residualSide f)) := by
  rw [← data.zeroSide_eq_formulaResidualSide f]
  exact data.tendsto_windowZeroSide windowExhaustion f

/-- The abstract p-series inputs prove universal local RH. -/
theorem RHOn_univ
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    RHOn (fun _ : Complex => True) :=
  data.toGlobalCriterion.RHOn_univ

/-- The abstract p-series inputs prove the project-local RH statement. -/
theorem RHStatement
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    RiemannHypothesisProject.RHStatement :=
  data.toGlobalCriterion.RHStatement

/-- The abstract p-series inputs prove Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData) :
    RiemannHypothesis :=
  data.toGlobalCriterion.mathlib_RH

/-- Abstract p-series zero-window sums converge to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (data : SchwartzRiemannWeilAbstractPSeriesAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop
      (nhds
        (data.toPackagedPositivityData.identification.quadraticData.quadraticForm f)) := by
  have hconv :=
    data.tendsto_windowZeroSide_formulaResidualSide windowExhaustion f
  have hquad :
      data.formulaData.sideData.residualSide f =
        data.toPackagedPositivityData.identification.quadraticData.quadraticForm f := by
    simp [toPackagedPositivityData,
      SchwartzRiemannWeilPackagedPositivityData.ofFormulaResidualPositivityData,
      SchwartzRiemannWeilPackagedPositivityData.ofResidualPositivityData,
      SchwartzRiemannWeilResidualPositivityData.toQuadraticFormIdentification,
      SchwartzRiemannWeilResidualPositivityData.toQuadraticFormData,
      SchwartzRiemannWeilFormulaIdentityData.toExplicitFormulaData,
      SchwartzRiemannWeilExplicitFormulaData.toGlobalExplicitFormulaNormalization,
      SchwartzRiemannWeilZeroSide.toGlobalExplicitFormulaNormalization,
      SchwartzExplicitFormulaNormalization.residualSide,
      SchwartzRiemannWeilFormulaSideData.residualSide]
  simpa [hquad] using hconv

end SchwartzRiemannWeilAbstractPSeriesAnalyticInputData

/--
The combined analytic input target for the separated tail-estimate route.

Supplying this record means supplying:
* a compact exhaustion and extension system;
* a separated polynomial decay tail estimate for the candidate zero side;
* a formula-side identity for that zero side; and
* packaged positivity data for the resulting explicit formula.
-/
structure SchwartzRiemannWeilTailAnalyticInputData where
  exhaustion : ComplexCompactExhaustion
  system : SchwartzRiemannWeilExtensionSystem
  tailEstimate :
    SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system
  formulaData :
    SchwartzRiemannWeilFormulaIdentityData tailEstimate.toZeroSide
  packagedPositivityData :
    SchwartzRiemannWeilPackagedPositivityData formulaData.toExplicitFormulaData

namespace SchwartzRiemannWeilTailAnalyticInputData

/-- Bundle separated zero-counting and zero-decay estimates into a tail estimate. -/
def separatedTailEstimateOfCountingAndDecay
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (decay : SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system)
    (cutoff_eq : counting.cutoff = decay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decay.decayExponent f) :
    SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system where
  counting := counting
  decay := decay
  cutoff_eq := cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Build final tail analytic inputs directly from separated zero-counting and
zero-decay estimates, plus the formula and positivity packages.
-/
noncomputable def ofCountingAndDecay
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (decay : SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system)
    (cutoff_eq : counting.cutoff = decay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (separatedTailEstimateOfCountingAndDecay
          counting decay cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (packagedPositivityData :
      SchwartzRiemannWeilPackagedPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilTailAnalyticInputData where
  exhaustion := exhaustion
  system := system
  tailEstimate :=
    separatedTailEstimateOfCountingAndDecay
      counting decay cutoff_eq growth_add_one_lt_decay
  formulaData := formulaData
  packagedPositivityData := packagedPositivityData

/--
Build tail analytic inputs from a tail estimate, formula identity, and
residual-side positivity data.
-/
noncomputable def ofTailEstimateAndResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (tailEstimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData tailEstimate.toZeroSide)
    (residualData :
      SchwartzRiemannWeilResidualPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilTailAnalyticInputData where
  exhaustion := exhaustion
  system := system
  tailEstimate := tailEstimate
  formulaData := formulaData
  packagedPositivityData :=
    SchwartzRiemannWeilPackagedPositivityData.ofResidualPositivityData
      residualData

/--
Build tail analytic inputs from a tail estimate, formula identity, and
formula-side residual positivity data.
-/
noncomputable def ofTailEstimateAndFormulaResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (tailEstimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData tailEstimate.toZeroSide)
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilTailAnalyticInputData :=
  ofTailEstimateAndResidualPositivity tailEstimate formulaData
    formulaResidualData.toResidualPositivityData

/--
Build tail analytic inputs directly from separated zero-counting and zero-decay
estimates, plus formula identity and residual-side positivity data.
-/
noncomputable def ofCountingAndDecayAndResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (decay : SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system)
    (cutoff_eq : counting.cutoff = decay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (separatedTailEstimateOfCountingAndDecay
          counting decay cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (residualData :
      SchwartzRiemannWeilResidualPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilTailAnalyticInputData :=
  ofCountingAndDecay counting decay cutoff_eq growth_add_one_lt_decay
    formulaData
    (SchwartzRiemannWeilPackagedPositivityData.ofResidualPositivityData
      residualData)

/--
Build tail analytic inputs directly from separated zero-counting and zero-decay
estimates, plus formula identity and formula-side residual positivity data.
-/
noncomputable def ofCountingAndDecayAndFormulaResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (decay : SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system)
    (cutoff_eq : counting.cutoff = decay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (separatedTailEstimateOfCountingAndDecay
          counting decay cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilTailAnalyticInputData :=
  ofCountingAndDecayAndResidualPositivity
    counting decay cutoff_eq growth_add_one_lt_decay formulaData
    formulaResidualData.toResidualPositivityData

/-- Assemble the tail analytic inputs into the concrete tail certificate. -/
noncomputable def toTailCertificateData
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    SchwartzRiemannWeilTailCertificateData :=
  SchwartzRiemannWeilTailCertificateData.ofFormulaIdentityAndPackagedPositivityData
    data.tailEstimate data.formulaData data.packagedPositivityData

/-- Assemble the tail analytic inputs into the decomposed certificate. -/
noncomputable def toCertificateData
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    SchwartzRiemannWeilCertificateData :=
  data.toTailCertificateData.toCertificateData

/-- Assemble the tail analytic inputs into the global criterion. -/
noncomputable def toGlobalCriterion
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    SchwartzRiemannWeilGlobalCriterion :=
  data.toTailCertificateData.toGlobalCriterion

/-- The zero side produced by the analytic inputs uses the extension-system weight. -/
theorem zeroSide_weight
    (data : SchwartzRiemannWeilTailAnalyticInputData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.toTailCertificateData.zeroSide.weight f rho =
      data.toTailCertificateData.system.weight f rho :=
  data.toTailCertificateData.zeroSide_weight f rho

/-- Compact-exhaustion sums converge for the tail analytic zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilTailAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toTailCertificateData.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.toTailCertificateData.zeroSide.zeroSide f)) :=
  data.toTailCertificateData.tendsto_windowZeroSide windowExhaustion f

/-- The tail analytic quadratic form is the residual side of its explicit formula. -/
theorem quadraticForm_eq_residualSide
    (data : SchwartzRiemannWeilTailAnalyticInputData)
    (f : SchwartzLineTestFunction) :
    data.toTailCertificateData.quadraticForm f =
      (data.toTailCertificateData.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  data.toTailCertificateData.quadraticForm_eq_residualSide f

/-- The tail analytic inputs prove universal local RH. -/
theorem RHOn_univ
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    RHOn (fun _ : Complex => True) :=
  data.toTailCertificateData.RHOn_univ

/-- The tail analytic inputs prove the project-local RH statement. -/
theorem RHStatement
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    RiemannHypothesisProject.RHStatement :=
  data.toTailCertificateData.RHStatement

/-- The tail analytic inputs prove Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    RiemannHypothesis :=
  data.toTailCertificateData.mathlib_RH

/-- Tail analytic zero-window sums converge to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (data : SchwartzRiemannWeilTailAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toTailCertificateData.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.toTailCertificateData.quadraticForm f)) :=
  data.toTailCertificateData.tendsto_windowZeroSide_quadraticForm
    windowExhaustion f

end SchwartzRiemannWeilTailAnalyticInputData

/--
The combined analytic input target for the profiled tail-estimate route.

This is the preferred final work package when the complex extension profile is
part of the construction: the profile supplies the separated tail estimate,
then formula-side identity and packaged positivity complete the route.
-/
structure SchwartzRiemannWeilProfiledAnalyticInputData where
  exhaustion : ComplexCompactExhaustion
  system : SchwartzRiemannWeilExtensionSystem
  profiledTailEstimate :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system
  formulaData :
    SchwartzRiemannWeilFormulaIdentityData profiledTailEstimate.toZeroSide
  packagedPositivityData :
    SchwartzRiemannWeilPackagedPositivityData formulaData.toExplicitFormulaData

namespace SchwartzRiemannWeilProfiledAnalyticInputData

/-- Bundle an extension profile and zero-counting estimate into a profiled tail estimate. -/
def profiledTailEstimateOfProfileAndCounting
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profile :
      SchwartzRiemannWeilExtensionAnalyticProfile exhaustion system)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = profile.shellDecay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < profile.shellDecay.decayExponent f) :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system where
  profile := profile
  counting := counting
  cutoff_eq := cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Build final profiled analytic inputs directly from an extension profile and
zero-counting estimate, plus the formula and positivity packages.
-/
noncomputable def ofProfileAndCounting
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profile :
      SchwartzRiemannWeilExtensionAnalyticProfile exhaustion system)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = profile.shellDecay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < profile.shellDecay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (profiledTailEstimateOfProfileAndCounting
          profile counting cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (packagedPositivityData :
      SchwartzRiemannWeilPackagedPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilProfiledAnalyticInputData where
  exhaustion := exhaustion
  system := system
  profiledTailEstimate :=
    profiledTailEstimateOfProfileAndCounting
      profile counting cutoff_eq growth_add_one_lt_decay
  formulaData := formulaData
  packagedPositivityData := packagedPositivityData

/--
Build final profiled analytic inputs directly from extension shell-decay data
and zero-counting estimates, plus the formula and positivity packages.
-/
noncomputable def ofShellDecayAndCounting
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellDecay :
      SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = shellDecay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < shellDecay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofShellDecayAndCounting
          shellDecay counting cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (packagedPositivityData :
      SchwartzRiemannWeilPackagedPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilProfiledAnalyticInputData where
  exhaustion := exhaustion
  system := system
  profiledTailEstimate :=
    SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofShellDecayAndCounting
      shellDecay counting cutoff_eq growth_add_one_lt_decay
  formulaData := formulaData
  packagedPositivityData := packagedPositivityData

/--
Build profiled analytic inputs from a profiled tail estimate, formula identity,
and residual-side positivity data.
-/
noncomputable def ofProfiledTailEstimateAndResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profiledTailEstimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData profiledTailEstimate.toZeroSide)
    (residualData :
      SchwartzRiemannWeilResidualPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilProfiledAnalyticInputData where
  exhaustion := exhaustion
  system := system
  profiledTailEstimate := profiledTailEstimate
  formulaData := formulaData
  packagedPositivityData :=
    SchwartzRiemannWeilPackagedPositivityData.ofResidualPositivityData
      residualData

/--
Build profiled analytic inputs from a profiled tail estimate, formula identity,
and formula-side residual positivity data.
-/
noncomputable def ofProfiledTailEstimateAndFormulaResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profiledTailEstimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData profiledTailEstimate.toZeroSide)
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilProfiledAnalyticInputData :=
  ofProfiledTailEstimateAndResidualPositivity
    profiledTailEstimate formulaData
    formulaResidualData.toResidualPositivityData

/--
Build final profiled analytic inputs directly from extension shell-decay data,
zero-counting estimates, formula identity, and residual-side positivity data.
-/
noncomputable def ofShellDecayAndCountingAndResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellDecay :
      SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = shellDecay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < shellDecay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofShellDecayAndCounting
          shellDecay counting cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (residualData :
      SchwartzRiemannWeilResidualPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilProfiledAnalyticInputData :=
  ofShellDecayAndCounting shellDecay counting cutoff_eq
    growth_add_one_lt_decay formulaData
    (SchwartzRiemannWeilPackagedPositivityData.ofResidualPositivityData
      residualData)

/--
Build final profiled analytic inputs directly from extension shell-decay data,
zero-counting estimates, formula identity, and formula-side residual positivity
data.
-/
noncomputable def ofShellDecayAndCountingAndFormulaResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (shellDecay :
      SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system)
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = shellDecay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < shellDecay.decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofShellDecayAndCounting
          shellDecay counting cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilProfiledAnalyticInputData :=
  ofShellDecayAndCountingAndResidualPositivity
    shellDecay counting cutoff_eq growth_add_one_lt_decay formulaData
    formulaResidualData.toResidualPositivityData

/--
Lift generic tail analytic inputs into the profiled target using the
conservative exact-norm profile.
-/
noncomputable def ofTailAnalyticInputData
    (data : SchwartzRiemannWeilTailAnalyticInputData) :
    SchwartzRiemannWeilProfiledAnalyticInputData where
  exhaustion := data.exhaustion
  system := data.system
  profiledTailEstimate :=
    SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofSeparatedPolynomialDecayEstimate
      data.tailEstimate
  formulaData := data.formulaData
  packagedPositivityData := data.packagedPositivityData

/-- Assemble the profiled analytic inputs into the profiled certificate. -/
noncomputable def toProfiledTailCertificateData
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    SchwartzRiemannWeilProfiledTailCertificateData :=
  SchwartzRiemannWeilProfiledTailCertificateData.ofFormulaIdentityAndPackagedPositivityData
    data.profiledTailEstimate data.formulaData data.packagedPositivityData

/-- Forget profiled analytic inputs to the generic tail certificate. -/
noncomputable def toTailCertificateData
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    SchwartzRiemannWeilTailCertificateData :=
  data.toProfiledTailCertificateData.toTailCertificateData

/-- Assemble the profiled analytic inputs into the decomposed certificate. -/
noncomputable def toCertificateData
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    SchwartzRiemannWeilCertificateData :=
  data.toProfiledTailCertificateData.toCertificateData

/-- Assemble the profiled analytic inputs into the global criterion. -/
noncomputable def toGlobalCriterion
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    SchwartzRiemannWeilGlobalCriterion :=
  data.toProfiledTailCertificateData.toGlobalCriterion

/-- The profiled analytic zero side uses the extension-system weight. -/
theorem zeroSide_weight
    (data : SchwartzRiemannWeilProfiledAnalyticInputData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.toProfiledTailCertificateData.zeroSide.weight f rho =
      data.toProfiledTailCertificateData.system.weight f rho :=
  data.toProfiledTailCertificateData.zeroSide_weight f rho

/-- Compact-exhaustion sums converge for the profiled analytic zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilProfiledAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop
        (nhds (data.toProfiledTailCertificateData.zeroSide.zeroSide f)) :=
  data.toProfiledTailCertificateData.tendsto_windowZeroSide
    windowExhaustion f

/-- The profiled analytic quadratic form is the residual side of its formula. -/
theorem quadraticForm_eq_residualSide
    (data : SchwartzRiemannWeilProfiledAnalyticInputData)
    (f : SchwartzLineTestFunction) :
    data.toProfiledTailCertificateData.quadraticForm f =
      (data.toProfiledTailCertificateData.toTailCertificateData.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  data.toProfiledTailCertificateData.quadraticForm_eq_residualSide f

/-- The profiled analytic inputs prove universal local RH. -/
theorem RHOn_univ
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    RHOn (fun _ : Complex => True) :=
  data.toProfiledTailCertificateData.RHOn_univ

/-- The profiled analytic inputs prove the project-local RH statement. -/
theorem RHStatement
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    RiemannHypothesisProject.RHStatement :=
  data.toProfiledTailCertificateData.RHStatement

/-- The profiled analytic inputs prove Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (data : SchwartzRiemannWeilProfiledAnalyticInputData) :
    RiemannHypothesis :=
  data.toProfiledTailCertificateData.mathlib_RH

/-- Profiled analytic zero-window sums converge to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (data : SchwartzRiemannWeilProfiledAnalyticInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop (nhds (data.toProfiledTailCertificateData.quadraticForm f)) :=
  data.toProfiledTailCertificateData.tendsto_windowZeroSide_quadraticForm
    windowExhaustion f

end SchwartzRiemannWeilProfiledAnalyticInputData

/--
Preferred final input target for the current profiled Riemann-Weil route.

This record states the remaining analytic work directly:
* extension shell decay;
* first-entry shell zero counting;
* the decay margin after zero counting;
* the explicit formula for the resulting zero side; and
* nonnegativity of the packaged formula residual side.
-/
structure SchwartzRiemannWeilProfiledShellFormulaResidualInputData where
  exhaustion : ComplexCompactExhaustion
  system : SchwartzRiemannWeilExtensionSystem
  shellDecay :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system
  counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion
  cutoff_eq : counting.cutoff = shellDecay.cutoff
  growth_add_one_lt_decay :
    forall f : SchwartzLineTestFunction,
      counting.growth + 1 < shellDecay.decayExponent f
  formulaData :
    SchwartzRiemannWeilFormulaIdentityData
      (SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofShellDecayAndCounting
        shellDecay counting cutoff_eq growth_add_one_lt_decay).toZeroSide
  formulaResidualData :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData

namespace SchwartzRiemannWeilProfiledShellFormulaResidualInputData

/--
Build shell-decay data for the final endpoint from a direct p-series envelope
bound on the extension at zero arguments.
-/
noncomputable def shellDecayOfGlobalPSeriesEnvelopeBound
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f)) :
    SchwartzRiemannWeilExtensionShellDecayEstimate exhaustion system :=
  SchwartzRiemannWeilExtensionShellDecayEstimate.ofGlobalPSeriesEnvelopeBound
    growthBound zeroConstant decayExponent zeroConstant_nonneg
    pseriesBound_nonneg envelope_zeroArgument_le_pseries

/--
Assemble the profiled tail estimate used by the final endpoint from a direct
p-series envelope bound and zero-counting data.
-/
noncomputable def profiledTailEstimateOfGlobalPSeriesEnvelopeAndCounting
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f) :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system :=
  SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofShellDecayAndCounting
    (shellDecayOfGlobalPSeriesEnvelopeBound
      growthBound zeroConstant decayExponent zeroConstant_nonneg
      pseriesBound_nonneg envelope_zeroArgument_le_pseries)
    counting cutoff_eq growth_add_one_lt_decay

/--
Build the preferred final input target from direct p-series envelope decay,
zero-counting data, formula identity, and formula-side residual positivity.
-/
noncomputable def ofGlobalPSeriesEnvelopeAndCountingAndFormulaResidualPositivity
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (envelope_zeroArgument_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData
        (profiledTailEstimateOfGlobalPSeriesEnvelopeAndCounting
          growthBound zeroConstant decayExponent zeroConstant_nonneg
          pseriesBound_nonneg envelope_zeroArgument_le_pseries
          counting cutoff_eq growth_add_one_lt_decay).toZeroSide)
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilProfiledShellFormulaResidualInputData where
  exhaustion := exhaustion
  system := system
  shellDecay :=
    shellDecayOfGlobalPSeriesEnvelopeBound
      growthBound zeroConstant decayExponent zeroConstant_nonneg
      pseriesBound_nonneg envelope_zeroArgument_le_pseries
  counting := counting
  cutoff_eq := cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay
  formulaData := formulaData
  formulaResidualData := formulaResidualData

/-- Convert the preferred final input target to the existing profiled analytic target. -/
noncomputable def toProfiledAnalyticInputData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilProfiledAnalyticInputData :=
  SchwartzRiemannWeilProfiledAnalyticInputData.ofShellDecayAndCountingAndFormulaResidualPositivity
    data.shellDecay data.counting data.cutoff_eq
    data.growth_add_one_lt_decay data.formulaData data.formulaResidualData

/-- The profiled separated tail estimate assembled from the final input target. -/
noncomputable def profiledTailEstimate
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate
      data.exhaustion data.system :=
  data.toProfiledAnalyticInputData.profiledTailEstimate

/-- Export the final target's formula identity data. -/
noncomputable def toFormulaIdentityData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilFormulaIdentityData
      data.toProfiledAnalyticInputData.profiledTailEstimate.toZeroSide :=
  data.toProfiledAnalyticInputData.formulaData

/-- Export the final target's formula-side residual positivity data. -/
noncomputable def toFormulaResidualPositivityData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilFormulaResidualPositivityData data.formulaData :=
  data.formulaResidualData

/-- Export the final target's normalized residual positivity data. -/
noncomputable def toResidualPositivityData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilResidualPositivityData
      data.formulaData.toExplicitFormulaData :=
  data.formulaResidualData.toResidualPositivityData

/-- Export the final target's packaged positivity data. -/
noncomputable def toPackagedPositivityData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilPackagedPositivityData
      data.formulaData.toExplicitFormulaData :=
  SchwartzRiemannWeilPackagedPositivityData.ofFormulaResidualPositivityData
    data.formulaResidualData

/-- The packaged formula residual side in the final target is nonnegative. -/
theorem formulaResidual_nonneg
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (f : SchwartzLineTestFunction) :
    0 <= data.formulaData.sideData.residualSide f :=
  data.formulaResidualData.residual_nonneg f

/-- The final target's formula-side residual positivity criterion proves universal RH. -/
theorem formulaResidual_positivity_implies_RHOn_univ
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    (forall f : SchwartzLineTestFunction,
      0 <= data.formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True) :=
  data.formulaResidualData.residual_positivity_implies_RHOn_univ

/-- Assemble the final input target into the profiled certificate. -/
noncomputable def toProfiledTailCertificateData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilProfiledTailCertificateData :=
  data.toProfiledAnalyticInputData.toProfiledTailCertificateData

/-- The final target's zero side is the packaged formula residual side. -/
theorem zeroSide_eq_formulaResidualSide
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (f : SchwartzLineTestFunction) :
    data.toProfiledTailCertificateData.zeroSide.zeroSide f =
      data.formulaData.sideData.residualSide f :=
  data.formulaData.explicitFormula f

/-- Forget the final input target to the generic tail certificate. -/
noncomputable def toTailCertificateData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilTailCertificateData :=
  data.toProfiledAnalyticInputData.toTailCertificateData

/-- Assemble the final input target into the decomposed certificate. -/
noncomputable def toCertificateData
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilCertificateData :=
  data.toProfiledAnalyticInputData.toCertificateData

/-- Assemble the final input target into the global criterion. -/
noncomputable def toGlobalCriterion
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    SchwartzRiemannWeilGlobalCriterion :=
  data.toProfiledAnalyticInputData.toGlobalCriterion

/-- The final input target's zero side uses the extension-system weight. -/
theorem zeroSide_weight
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.toProfiledTailCertificateData.zeroSide.weight f rho =
      data.toProfiledTailCertificateData.system.weight f rho :=
  data.toProfiledAnalyticInputData.zeroSide_weight f rho

/-- Compact-exhaustion sums converge for the final target's zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop
        (nhds (data.toProfiledTailCertificateData.zeroSide.zeroSide f)) :=
  data.toProfiledAnalyticInputData.tendsto_windowZeroSide
    windowExhaustion f

/-- Compact-exhaustion sums converge to the packaged formula residual side. -/
theorem tendsto_windowZeroSide_formulaResidualSide
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop (nhds (data.formulaData.sideData.residualSide f)) := by
  rw [← data.zeroSide_eq_formulaResidualSide f]
  exact data.tendsto_windowZeroSide windowExhaustion f

/-- The final target's quadratic form is the residual side of its formula. -/
theorem quadraticForm_eq_residualSide
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (f : SchwartzLineTestFunction) :
    data.toProfiledTailCertificateData.quadraticForm f =
      (data.toProfiledTailCertificateData.toTailCertificateData.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  data.toProfiledAnalyticInputData.quadraticForm_eq_residualSide f

/-- The final target's quadratic form is the packaged formula residual side. -/
theorem quadraticForm_eq_formulaResidualSide
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (f : SchwartzLineTestFunction) :
    data.toProfiledTailCertificateData.quadraticForm f =
      data.formulaData.sideData.residualSide f := by
  rw [data.toProfiledTailCertificateData.quadraticForm_eq_zeroSide f]
  exact data.zeroSide_eq_formulaResidualSide f

/-- The packaged formula residual side is the final target's quadratic form. -/
theorem formulaResidualSide_eq_quadraticForm
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (f : SchwartzLineTestFunction) :
    data.formulaData.sideData.residualSide f =
      data.toProfiledTailCertificateData.quadraticForm f :=
  (data.quadraticForm_eq_formulaResidualSide f).symm

/-- The final input target proves universal local RH. -/
theorem RHOn_univ
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    RHOn (fun _ : Complex => True) :=
  data.toProfiledAnalyticInputData.RHOn_univ

/-- The final input target proves the project-local RH statement. -/
theorem RHStatement
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    RiemannHypothesisProject.RHStatement :=
  data.toProfiledAnalyticInputData.RHStatement

/-- The final input target proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData) :
    RiemannHypothesis :=
  data.toProfiledAnalyticInputData.mathlib_RH

/-- Final-target zero-window sums converge to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (data : SchwartzRiemannWeilProfiledShellFormulaResidualInputData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat =>
        data.toProfiledTailCertificateData.zeroSide.windowZeroSide
          windowExhaustion n f)
      atTop (nhds (data.toProfiledTailCertificateData.quadraticForm f)) :=
  data.toProfiledAnalyticInputData.tendsto_windowZeroSide_quadraticForm
    windowExhaustion f

end SchwartzRiemannWeilProfiledShellFormulaResidualInputData

end RiemannHypothesisProject
