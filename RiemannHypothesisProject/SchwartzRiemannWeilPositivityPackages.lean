import RiemannHypothesisProject.SchwartzRiemannWeilFormulaSides

/-!
# Positivity packages for the Schwartz Riemann-Weil route

The decomposed Riemann-Weil certificate contains a positivity component:
a quadratic form, its identification with the zero side, a nonnegativity proof,
and a theorem that such nonnegativity proves universal `RHOn`.

This module splits that component into smaller reusable packages. The combined
package converts back to the existing `SchwartzRiemannWeilPositivityData`, so
all downstream global criterion and RH consequences remain unchanged.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/-- A quadratic form on Schwartz test functions for the Riemann-Weil route. -/
structure SchwartzRiemannWeilQuadraticFormData where
  quadraticForm : SchwartzLineTestFunction -> Real

namespace SchwartzRiemannWeilQuadraticFormData

/-- Evaluate the packaged quadratic form. -/
noncomputable def value
    (quadraticData : SchwartzRiemannWeilQuadraticFormData)
    (f : SchwartzLineTestFunction) : Real :=
  quadraticData.quadraticForm f

/-- The value notation is definitionally the packaged quadratic form. -/
theorem value_eq
    (quadraticData : SchwartzRiemannWeilQuadraticFormData)
    (f : SchwartzLineTestFunction) :
    quadraticData.value f = quadraticData.quadraticForm f :=
  rfl

end SchwartzRiemannWeilQuadraticFormData

/--
Identification of a quadratic form with the zero side of explicit-formula data.

This isolates the equality that turns zero-side convergence into convergence to
the quadratic form.
-/
structure SchwartzRiemannWeilQuadraticFormIdentification
    (formulaData : SchwartzRiemannWeilExplicitFormulaData) where
  quadraticData : SchwartzRiemannWeilQuadraticFormData
  quadraticForm_eq_zeroSide :
    forall f : SchwartzLineTestFunction,
      quadraticData.quadraticForm f = formulaData.zeroSide.zeroSide f

namespace SchwartzRiemannWeilQuadraticFormIdentification

/-- The identified quadratic form is the residual side of the explicit formula. -/
theorem quadraticForm_eq_residualSide
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (identification :
      SchwartzRiemannWeilQuadraticFormIdentification formulaData)
    (f : SchwartzLineTestFunction) :
    identification.quadraticData.quadraticForm f =
      (formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f := by
  rw [identification.quadraticForm_eq_zeroSide f]
  exact formulaData.zeroSide_eq_residualSide f

/-- The residual side of the explicit formula is the identified quadratic form. -/
theorem residualSide_eq_quadraticForm
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (identification :
      SchwartzRiemannWeilQuadraticFormIdentification formulaData)
    (f : SchwartzLineTestFunction) :
    (formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f =
      identification.quadraticData.quadraticForm f :=
  (identification.quadraticForm_eq_residualSide f).symm

end SchwartzRiemannWeilQuadraticFormIdentification

/-- A nonnegativity proof for a packaged quadratic form. -/
structure SchwartzRiemannWeilQuadraticFormPositivity
    (quadraticData : SchwartzRiemannWeilQuadraticFormData) where
  positivity :
    forall f : SchwartzLineTestFunction, 0 <= quadraticData.quadraticForm f

/--
A positivity-to-RH criterion for a packaged quadratic form.

This is still a hypothesis package, not the final analytic theorem. It isolates
the field that should eventually be replaced by a genuine Weil positivity
criterion.
-/
structure SchwartzRiemannWeilPositivityCriterionData
    (quadraticData : SchwartzRiemannWeilQuadraticFormData) where
  positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction, 0 <= quadraticData.quadraticForm f) ->
      RHOn (fun _ : Complex => True)

/--
Residual-side positivity data for explicit-formula data.

This is the smallest positivity target once the explicit formula has been
fixed: take the quadratic form to be the residual side itself, prove it is
nonnegative, and supply the positivity-to-RH criterion for that residual side.
-/
structure SchwartzRiemannWeilResidualPositivityData
    (formulaData : SchwartzRiemannWeilExplicitFormulaData) where
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <=
        (formulaData.toGlobalExplicitFormulaNormalization
          |>.toSchwartzExplicitFormulaNormalization).residualSide f
  residual_positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction,
      0 <=
        (formulaData.toGlobalExplicitFormulaNormalization
          |>.toSchwartzExplicitFormulaNormalization).residualSide f) ->
      RHOn (fun _ : Complex => True)

namespace SchwartzRiemannWeilResidualPositivityData

/-- The residual side viewed as the packaged quadratic form. -/
noncomputable def toQuadraticFormData
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (_residualData :
      SchwartzRiemannWeilResidualPositivityData formulaData) :
    SchwartzRiemannWeilQuadraticFormData where
  quadraticForm := fun f =>
    (formulaData.toGlobalExplicitFormulaNormalization
      |>.toSchwartzExplicitFormulaNormalization).residualSide f

/-- Identify the residual-side quadratic form with the zero side. -/
noncomputable def toQuadraticFormIdentification
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (residualData :
      SchwartzRiemannWeilResidualPositivityData formulaData) :
    SchwartzRiemannWeilQuadraticFormIdentification formulaData where
  quadraticData := residualData.toQuadraticFormData
  quadraticForm_eq_zeroSide := fun f =>
    formulaData.residualSide_eq_zeroSide f

/-- Convert residual-side positivity into positivity of the packaged quadratic form. -/
noncomputable def toQuadraticFormPositivity
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (residualData :
      SchwartzRiemannWeilResidualPositivityData formulaData) :
    SchwartzRiemannWeilQuadraticFormPositivity
      residualData.toQuadraticFormData where
  positivity := residualData.residual_nonneg

/-- Convert the residual-side positivity-to-RH implication to criterion data. -/
noncomputable def toPositivityCriterionData
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (residualData :
      SchwartzRiemannWeilResidualPositivityData formulaData) :
    SchwartzRiemannWeilPositivityCriterionData
      residualData.toQuadraticFormData where
  positivity_implies_RHOn_univ :=
    residualData.residual_positivity_implies_RHOn_univ

end SchwartzRiemannWeilResidualPositivityData

/--
Residual-side positivity stated directly for packaged formula-side data.

This is the formula-author-facing version of residual positivity: prove
nonnegativity of the packaged `prime + pole + gamma` residual side, then supply
the positivity-to-RH criterion for that same residual side.
-/
structure SchwartzRiemannWeilFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) where
  residual_nonneg :
    forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f
  residual_positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True)

namespace SchwartzRiemannWeilFormulaResidualPositivityData

/--
Build formula-side residual positivity directly from nonnegativity of the
packaged residual expression and the corresponding positivity-to-RH criterion.
-/
noncomputable def ofRawResidualPositivity
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f)
    (residual_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData where
  residual_nonneg := residual_nonneg
  residual_positivity_implies_RHOn_univ :=
    residual_positivity_implies_RHOn_univ

/-- Convert formula-side residual positivity to normalized residual positivity. -/
noncomputable def toResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilResidualPositivityData
      formulaData.toExplicitFormulaData where
  residual_nonneg := fun f => by
    simpa [SchwartzRiemannWeilFormulaIdentityData.toExplicitFormulaData,
      SchwartzRiemannWeilExplicitFormulaData.toGlobalExplicitFormulaNormalization,
      SchwartzRiemannWeilZeroSide.toGlobalExplicitFormulaNormalization,
      SchwartzExplicitFormulaNormalization.residualSide,
      SchwartzRiemannWeilFormulaSideData.residualSide]
      using formulaResidualData.residual_nonneg f
  residual_positivity_implies_RHOn_univ := fun hres =>
    formulaResidualData.residual_positivity_implies_RHOn_univ <| fun f => by
      simpa [SchwartzRiemannWeilFormulaIdentityData.toExplicitFormulaData,
        SchwartzRiemannWeilExplicitFormulaData.toGlobalExplicitFormulaNormalization,
        SchwartzRiemannWeilZeroSide.toGlobalExplicitFormulaNormalization,
        SchwartzExplicitFormulaNormalization.residualSide,
        SchwartzRiemannWeilFormulaSideData.residualSide]
        using hres f

end SchwartzRiemannWeilFormulaResidualPositivityData

/--
Packaged positivity data relative to explicit-formula data.

This is the smaller replacement target for the positivity component of the
decomposed certificate.
-/
structure SchwartzRiemannWeilPackagedPositivityData
    (formulaData : SchwartzRiemannWeilExplicitFormulaData) where
  identification :
    SchwartzRiemannWeilQuadraticFormIdentification formulaData
  positivity :
    SchwartzRiemannWeilQuadraticFormPositivity identification.quadraticData
  criterion :
    SchwartzRiemannWeilPositivityCriterionData identification.quadraticData

namespace SchwartzRiemannWeilPackagedPositivityData

/-- Convert packaged positivity data to the existing decomposed positivity data. -/
noncomputable def toPositivityData
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData) :
    SchwartzRiemannWeilPositivityData formulaData where
  quadraticForm := packagedData.identification.quadraticData.quadraticForm
  quadraticForm_eq_zeroSide :=
    packagedData.identification.quadraticForm_eq_zeroSide
  positivity := packagedData.positivity.positivity
  positivity_implies_RHOn_univ :=
    packagedData.criterion.positivity_implies_RHOn_univ

/-- Build packaged positivity data from the existing decomposed positivity data. -/
noncomputable def ofPositivityData
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData) :
    SchwartzRiemannWeilPackagedPositivityData formulaData := by
  let quadraticData : SchwartzRiemannWeilQuadraticFormData :=
    { quadraticForm := positivityData.quadraticForm }
  let identification :
      SchwartzRiemannWeilQuadraticFormIdentification formulaData :=
    { quadraticData := quadraticData
      quadraticForm_eq_zeroSide :=
        positivityData.quadraticForm_eq_zeroSide }
  exact
    { identification := identification
      positivity :=
        { positivity := positivityData.positivity }
      criterion :=
        { positivity_implies_RHOn_univ :=
            positivityData.positivity_implies_RHOn_univ } }

/-- Build packaged positivity data by using the residual side as the quadratic form. -/
noncomputable def ofResidualPositivityData
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (residualData :
      SchwartzRiemannWeilResidualPositivityData formulaData) :
    SchwartzRiemannWeilPackagedPositivityData formulaData where
  identification := residualData.toQuadraticFormIdentification
  positivity := residualData.toQuadraticFormPositivity
  criterion := residualData.toPositivityCriterionData

/-- Build packaged positivity data from formula-side residual positivity. -/
noncomputable def ofFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (formulaResidualData :
      SchwartzRiemannWeilFormulaResidualPositivityData formulaData) :
    SchwartzRiemannWeilPackagedPositivityData
      formulaData.toExplicitFormulaData :=
  ofResidualPositivityData formulaResidualData.toResidualPositivityData

/-- Packaged positivity data assembles the global criterion. -/
noncomputable def toGlobalCriterion
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData) :
    SchwartzRiemannWeilGlobalCriterion :=
  packagedData.toPositivityData.toGlobalCriterion

/-- Packaged positivity data proves universal local RH. -/
theorem RHOn_univ
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData) :
    RHOn (fun _ : Complex => True) :=
  packagedData.toPositivityData.RHOn_univ

/-- Packaged positivity data proves the project-local RH statement. -/
theorem RHStatement
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData) :
    RiemannHypothesisProject.RHStatement :=
  packagedData.toPositivityData.RHStatement

/-- Packaged positivity data proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData) :
    RiemannHypothesis :=
  packagedData.toPositivityData.mathlib_RH

/-- The packaged quadratic form is the residual side of the explicit formula. -/
theorem quadraticForm_eq_residualSide
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData)
    (f : SchwartzLineTestFunction) :
    packagedData.identification.quadraticData.quadraticForm f =
      (formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  packagedData.identification.quadraticForm_eq_residualSide f

/-- Compact-exhaustion zero-window sums converge to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData formulaData)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => formulaData.zeroSide.windowZeroSide exhaustion n f)
      atTop
      (nhds (packagedData.identification.quadraticData.quadraticForm f)) :=
  packagedData.toPositivityData.tendsto_windowZeroSide_quadraticForm
    exhaustion f

end SchwartzRiemannWeilPackagedPositivityData

end RiemannHypothesisProject
