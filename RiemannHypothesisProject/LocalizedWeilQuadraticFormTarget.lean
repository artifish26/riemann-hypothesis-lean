import RiemannHypothesisProject.SupportRestrictedWeilDensityConstructors
import RiemannHypothesisProject.ToyPositivity

/-!
# Localized Weil quadratic-form targets

Connes-Consani-style compressed trace formulae and Suzuki-style local
quadratic-form models suggest finite or localized positivity checks before one
attempts a full Weil positivity theorem. This file packages that intermediate
target without asserting global residual positivity.

The main route is:

1. prove a finite Rayleigh quotient is nonnegative;
2. identify that local quadratic form with the formula residual on an
   admissible test-function class;
3. hand the resulting restricted residual positivity to the existing
   `SupportRestrictedFormulaResidualPositivityData` API.
-/

namespace RiemannHypothesisProject

open scoped BigOperators

/--
Finite Rayleigh-quotient data for a localized Weil quadratic form.

The field `quadratic_nonneg` is the finite-dimensional positivity certificate.
In concrete Connes-Consani-style experiments, `kernel` may be a finite Toeplitz
or compressed-trace matrix and `coordinate` may be a projection of a test
function to a finite-dimensional model.
-/
structure LocalizedWeilFiniteRayleighData (Index : Type) [Fintype Index] where
  coordinate : SchwartzLineTestFunction -> Index -> Real
  kernel : Index -> Index -> Real
  quadratic_nonneg :
    forall x : Index -> Real,
      0 <= ∑ i : Index, ∑ j : Index, x i * kernel i j * x j

namespace LocalizedWeilFiniteRayleighData

/-- The finite Rayleigh quotient attached to a test function. -/
noncomputable def quadraticForm
    {Index : Type} [Fintype Index]
    (data : LocalizedWeilFiniteRayleighData Index)
    (f : SchwartzLineTestFunction) : Real :=
  ∑ i : Index, ∑ j : Index,
    data.coordinate f i * data.kernel i j * data.coordinate f j

/-- The finite Rayleigh quotient is nonnegative by the packaged certificate. -/
theorem quadraticForm_nonneg
    {Index : Type} [Fintype Index]
    (data : LocalizedWeilFiniteRayleighData Index)
    (f : SchwartzLineTestFunction) :
    0 <= data.quadraticForm f := by
  simpa [quadraticForm] using data.quadratic_nonneg (data.coordinate f)

end LocalizedWeilFiniteRayleighData

/--
A localized quadratic-form target for a formula residual.

This is intentionally support-restricted: the hard analytic work is to choose
`admissible`, prove local positivity there, and identify the local quadratic
form with the normalized formula residual on that class.
-/
structure LocalizedWeilQuadraticFormTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) where
  admissible : SchwartzLineTestFunction -> Prop
  localQuadraticForm : SchwartzLineTestFunction -> Real
  localQuadraticForm_eq_residualSide_on_admissible :
    forall f : SchwartzLineTestFunction,
      admissible f -> localQuadraticForm f = formulaData.sideData.residualSide f
  localQuadraticForm_nonneg_on_admissible :
    forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f
  restricted_positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True)

namespace LocalizedWeilQuadraticFormTarget

/--
Build a localized target from a quadratic-form identity stated against a
source residual side.  This keeps the analytic localized-form proof in source
notation while transporting it to the normalized formula residual.
-/
noncomputable def ofResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (admissible : SchwartzLineTestFunction -> Prop)
    (localQuadraticForm : SchwartzLineTestFunction -> Real)
    (localQuadraticForm_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> localQuadraticForm f = sourceResidualSide f)
    (localQuadraticForm_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction, admissible f -> 0 <= localQuadraticForm f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilQuadraticFormTarget formulaData where
  admissible := admissible
  localQuadraticForm := localQuadraticForm
  localQuadraticForm_eq_residualSide_on_admissible := by
    intro f hf
    rw [localQuadraticForm_eq_sourceResidualSide_on_admissible f hf,
      ← residualSide_eq_source f]
  localQuadraticForm_nonneg_on_admissible :=
    localQuadraticForm_nonneg_on_admissible
  restricted_positivity_implies_RHOn_univ := by
    intro residual_nonneg_on_admissible
    exact restricted_source_positivity_implies_RHOn_univ
      (fun f hf => by
        rw [← residualSide_eq_source f]
        exact residual_nonneg_on_admissible f hf)

/--
The localized quadratic-form certificate gives formula-side residual
nonnegativity on the admissible class.
-/
theorem residual_nonneg_on_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData)
    (f : SchwartzLineTestFunction)
    (hf : target.admissible f) :
    0 <= formulaData.sideData.residualSide f := by
  simpa [target.localQuadraticForm_eq_residualSide_on_admissible f hf] using
    target.localQuadraticForm_nonneg_on_admissible f hf

/-- Convert a localized quadratic-form certificate to support-restricted positivity. -/
noncomputable def toSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData) :
    SupportRestrictedFormulaResidualPositivityData formulaData where
  admissible := target.admissible
  residual_nonneg_on_admissible := target.residual_nonneg_on_admissible
  restricted_positivity_implies_RHOn_univ :=
    target.restricted_positivity_implies_RHOn_univ

/--
Promote localized positivity to full formula-side residual positivity using a
supplied density/closedness bridge.
-/
noncomputable def toFormulaResidualPositivityDataOfDensityBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData)
    (bridge :
      SupportRestrictedFormulaResidualDensityBridge
        target.toSupportRestrictedFormulaResidualPositivityData) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  bridge.toFormulaResidualPositivityData

/--
Promote localized positivity to full formula-side residual positivity from a
dense admissible core and closedness of the residual-nonnegative locus.
-/
noncomputable def toFormulaResidualPositivityDataOfDenseCoreAndClosed
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData)
    (coreData :
      SupportRestrictedFormulaResidualDenseCore
        target.toSupportRestrictedFormulaResidualPositivityData)
    (residual_nonnegativeSet_closed :
      IsClosed (formulaResidualNonnegativeSet formulaData)) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  (coreData.toSupportRestrictedDensityBridgeOfClosed
    residual_nonnegativeSet_closed).toFormulaResidualPositivityData

/--
Promote localized positivity to full formula-side residual positivity from a
dense admissible core and continuity of the formula residual side.
-/
noncomputable def toFormulaResidualPositivityDataOfDenseCoreAndResidualContinuity
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData)
    (coreData :
      SupportRestrictedFormulaResidualDenseCore
        target.toSupportRestrictedFormulaResidualPositivityData)
    (continuity :
      SchwartzRiemannWeilFormulaResidualContinuityData formulaData) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  (coreData.toSupportRestrictedDensityBridgeOfResidualContinuity
    continuity).toFormulaResidualPositivityData

/--
Promote localized positivity to full formula-side residual positivity from a
dense admissible core and separate continuity of the prime, pole, and gamma
sides.
-/
noncomputable def toFormulaResidualPositivityDataOfDenseCoreAndSideContinuity
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData)
    (coreData :
      SupportRestrictedFormulaResidualDenseCore
        target.toSupportRestrictedFormulaResidualPositivityData)
    (continuity :
      SchwartzRiemannWeilFormulaSideContinuityData formulaData) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  (coreData.toSupportRestrictedDensityBridgeOfSideContinuity
    continuity).toFormulaResidualPositivityData

/-- The localized target proves universal local RH, conditionally. -/
theorem RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData) :
    RHOn (fun _ : Complex => True) :=
  target.toSupportRestrictedFormulaResidualPositivityData.RHOn_univ

/-- The localized target proves the project RH statement, conditionally. -/
theorem RHStatement
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData) :
    RiemannHypothesisProject.RHStatement :=
  target.toSupportRestrictedFormulaResidualPositivityData.RHStatement

/-- The localized target proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilQuadraticFormTarget formulaData) :
    RiemannHypothesis :=
  target.toSupportRestrictedFormulaResidualPositivityData.mathlib_RH

end LocalizedWeilQuadraticFormTarget

/--
A localized Weil target whose quadratic form is supplied by an existing finite
positivity model.

This reuses the sum-of-squares and finite Gram certificates from
`ToyPositivity.lean`. The analytic work remains the residual-identification
field on the chosen admissible test class.
-/
structure LocalizedWeilFinitePositivityModelTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) where
  admissible : SchwartzLineTestFunction -> Prop
  model : FinitePositivityModel
  encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index
  encodedQuadratic_eq_residualSide_on_admissible :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        model.quadraticForm (encode f) = formulaData.sideData.residualSide f
  restricted_positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True)

namespace LocalizedWeilFinitePositivityModelTarget

/-- View a finite positivity model target as a localized quadratic-form target. -/
noncomputable def toLocalizedWeilQuadraticFormTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilFinitePositivityModelTarget formulaData) :
    LocalizedWeilQuadraticFormTarget formulaData where
  admissible := target.admissible
  localQuadraticForm := fun f => target.model.quadraticForm (target.encode f)
  localQuadraticForm_eq_residualSide_on_admissible :=
    target.encodedQuadratic_eq_residualSide_on_admissible
  localQuadraticForm_nonneg_on_admissible :=
    fun f _hf => target.model.quadraticForm_nonneg (target.encode f)
  restricted_positivity_implies_RHOn_univ :=
    target.restricted_positivity_implies_RHOn_univ

/-- Convert a finite positivity model target to support-restricted residual positivity. -/
noncomputable def toSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilFinitePositivityModelTarget formulaData) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  target.toLocalizedWeilQuadraticFormTarget
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build a finite positivity model target from a residual identity stated in
source notation.

This is the finite-model analogue of
`LocalizedWeilQuadraticFormTarget.ofResidualSideEq`: the analytic input may
identify a finite positive model with the source residual side, while the
normalization equality transports it to the formula residual side.
-/
noncomputable def ofSourceResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (admissible : SchwartzLineTestFunction -> Prop)
    (model : FinitePositivityModel)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction model.Index)
    (encodedQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          model.quadraticForm (encode f) = sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget formulaData where
  admissible := admissible
  model := model
  encode := encode
  encodedQuadratic_eq_residualSide_on_admissible := by
    intro f hf
    rw [encodedQuadratic_eq_sourceResidualSide_on_admissible f hf,
      ← residualSide_eq_source f]
  restricted_positivity_implies_RHOn_univ := by
    intro residual_nonneg_on_admissible
    exact restricted_source_positivity_implies_RHOn_univ
      (fun f hf => by
        rw [← residualSide_eq_source f]
        exact residual_nonneg_on_admissible f hf)

/-- Build a localized target from a sum-of-squares finite positivity model. -/
noncomputable def ofSumSquares
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (Index : Type) [Fintype Index]
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (sumSquares_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          sumSquaresQuadraticForm (encode f) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget formulaData where
  admissible := admissible
  model := sumSquaresPositivityModel Index
  encode := encode
  encodedQuadratic_eq_residualSide_on_admissible :=
    sumSquares_eq_residualSide_on_admissible
  restricted_positivity_implies_RHOn_univ :=
    restricted_positivity_implies_RHOn_univ

/-- Build a localized target from a finite Gram positivity model. -/
noncomputable def ofFiniteGram
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_residualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            formulaData.sideData.residualSide f)
    (restricted_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget formulaData where
  admissible := admissible
  model := finiteGramPositivityModel Index Feature feature
  encode := encode
  encodedQuadratic_eq_residualSide_on_admissible :=
    finiteGram_eq_residualSide_on_admissible
  restricted_positivity_implies_RHOn_univ :=
    restricted_positivity_implies_RHOn_univ

/--
Build a localized target from a finite Gram positivity model whose
identification is stated against a source residual side.
-/
noncomputable def ofSourceFiniteGram
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (Index Feature : Type) [Fintype Index] [Fintype Feature]
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (encode : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (finiteGram_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          finiteGramQuadraticForm feature (encode f) =
            sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFinitePositivityModelTarget formulaData :=
  ofSourceResidualSideEq
    sourceResidualSide residualSide_eq_source admissible
    (finiteGramPositivityModel Index Feature feature)
    encode
    finiteGram_eq_sourceResidualSide_on_admissible
    restricted_source_positivity_implies_RHOn_univ

/-- The finite positivity model target proves universal local RH, conditionally. -/
theorem RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilFinitePositivityModelTarget formulaData) :
    RHOn (fun _ : Complex => True) :=
  target.toLocalizedWeilQuadraticFormTarget.RHOn_univ

/-- The finite positivity model target proves the project RH statement, conditionally. -/
theorem RHStatement
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilFinitePositivityModelTarget formulaData) :
    RiemannHypothesisProject.RHStatement :=
  target.toLocalizedWeilQuadraticFormTarget.RHStatement

/-- The finite positivity model target proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (target : LocalizedWeilFinitePositivityModelTarget formulaData) :
    RiemannHypothesis :=
  target.toLocalizedWeilQuadraticFormTarget.mathlib_RH

end LocalizedWeilFinitePositivityModelTarget

/--
A localized Weil target whose quadratic form is supplied by a finite Rayleigh
quotient. The residual identification remains explicit and restricted to the
chosen admissible test class.
-/
structure LocalizedWeilFiniteRayleighTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (Index : Type) [Fintype Index] where
  admissible : SchwartzLineTestFunction -> Prop
  rayleighData : LocalizedWeilFiniteRayleighData Index
  rayleighQuadratic_eq_residualSide_on_admissible :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        rayleighData.quadraticForm f = formulaData.sideData.residualSide f
  restricted_positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True)

namespace LocalizedWeilFiniteRayleighTarget

/-- View a finite Rayleigh target as a localized quadratic-form target. -/
noncomputable def toLocalizedWeilQuadraticFormTarget
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index]
    (target : LocalizedWeilFiniteRayleighTarget formulaData Index) :
    LocalizedWeilQuadraticFormTarget formulaData where
  admissible := target.admissible
  localQuadraticForm := target.rayleighData.quadraticForm
  localQuadraticForm_eq_residualSide_on_admissible :=
    target.rayleighQuadratic_eq_residualSide_on_admissible
  localQuadraticForm_nonneg_on_admissible :=
    fun f _hf => target.rayleighData.quadraticForm_nonneg f
  restricted_positivity_implies_RHOn_univ :=
    target.restricted_positivity_implies_RHOn_univ

/-- Convert a finite Rayleigh target to support-restricted residual positivity. -/
noncomputable def toSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index]
    (target : LocalizedWeilFiniteRayleighTarget formulaData Index) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  target.toLocalizedWeilQuadraticFormTarget
    |>.toSupportRestrictedFormulaResidualPositivityData

/--
Build a finite Rayleigh target from a Rayleigh/residual identity stated in
source notation.

This lets finite-matrix or compressed-trace experiments stay source-facing
until the final normalization rewrite to the formula residual side.
-/
noncomputable def ofSourceResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index]
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (admissible : SchwartzLineTestFunction -> Prop)
    (rayleighData : LocalizedWeilFiniteRayleighData Index)
    (rayleighQuadratic_eq_sourceResidualSide_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          rayleighData.quadraticForm f = sourceResidualSide f)
    (restricted_source_positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) ->
        RHOn (fun _ : Complex => True)) :
    LocalizedWeilFiniteRayleighTarget formulaData Index where
  admissible := admissible
  rayleighData := rayleighData
  rayleighQuadratic_eq_residualSide_on_admissible := by
    intro f hf
    rw [rayleighQuadratic_eq_sourceResidualSide_on_admissible f hf,
      ← residualSide_eq_source f]
  restricted_positivity_implies_RHOn_univ := by
    intro residual_nonneg_on_admissible
    exact restricted_source_positivity_implies_RHOn_univ
      (fun f hf => by
        rw [← residualSide_eq_source f]
        exact residual_nonneg_on_admissible f hf)

/-- The finite Rayleigh target proves universal local RH, conditionally. -/
theorem RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index]
    (target : LocalizedWeilFiniteRayleighTarget formulaData Index) :
    RHOn (fun _ : Complex => True) :=
  target.toLocalizedWeilQuadraticFormTarget.RHOn_univ

/-- The finite Rayleigh target proves the project RH statement, conditionally. -/
theorem RHStatement
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index]
    (target : LocalizedWeilFiniteRayleighTarget formulaData Index) :
    RiemannHypothesisProject.RHStatement :=
  target.toLocalizedWeilQuadraticFormTarget.RHStatement

/-- The finite Rayleigh target proves Mathlib RH, conditionally. -/
theorem mathlib_RH
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {Index : Type} [Fintype Index]
    (target : LocalizedWeilFiniteRayleighTarget formulaData Index) :
    RiemannHypothesis :=
  target.toLocalizedWeilQuadraticFormTarget.mathlib_RH

end LocalizedWeilFiniteRayleighTarget

end RiemannHypothesisProject
