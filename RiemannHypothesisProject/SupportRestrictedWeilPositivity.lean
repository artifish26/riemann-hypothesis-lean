import RiemannHypothesisProject.LiCriterion.ResidualBridgeInput

/-!
# Support-restricted Weil positivity target

Burnol-style support restrictions and Connes-Consani-style finite/compressed
positivity arguments are useful partial targets for the Riemann-Weil route.
This file packages that idea without claiming full residual positivity.

The core object is an admissible predicate on Schwartz test functions.  A
future analytic theorem may prove residual nonnegativity only on that class, and
then prove that this restricted positivity is already enough to force RH, or
that it implies Li-coefficient positivity.
-/

namespace RiemannHypothesisProject

/--
Formula-side residual positivity on a restricted class of test functions.

The field `restricted_positivity_implies_RHOn_univ` is the future analytic
criterion: it says that nonnegativity on the admissible class is sufficient for
universal `RHOn`.  This lets support-restricted or compact-support positivity
be developed without coercing it into a full-all-tests positivity theorem.
-/
structure SupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) where
  admissible : SchwartzLineTestFunction -> Prop
  residual_nonneg_on_admissible :
    forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= formulaData.sideData.residualSide f
  restricted_positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= formulaData.sideData.residualSide f) ->
      RHOn (fun _ : Complex => True)

namespace SupportRestrictedFormulaResidualPositivityData

/-- The packaged restricted positivity theorem proves universal local RH. -/
theorem RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData) :
    RHOn (fun _ : Complex => True) :=
  restrictedData.restricted_positivity_implies_RHOn_univ
    restrictedData.residual_nonneg_on_admissible

/-- The packaged restricted positivity theorem proves the project RH statement. -/
theorem RHStatement
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData) :
    RiemannHypothesisProject.RHStatement :=
  RHStatement_iff_RHOn_univ.mpr restrictedData.RHOn_univ

/-- The packaged restricted positivity theorem proves Mathlib RH. -/
theorem mathlib_RH
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData) :
    RiemannHypothesis :=
  RHStatement_iff_mathlib.mp restrictedData.RHStatement

/--
If the admissible class contains every test function, a support-restricted
package becomes ordinary formula-side residual positivity data.
-/
noncomputable def toFormulaResidualPositivityDataOfAllTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData)
    (all_admissible :
      forall f : SchwartzLineTestFunction, restrictedData.admissible f) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  SchwartzRiemannWeilFormulaResidualPositivityData.ofRawResidualPositivity
    (fun f =>
      restrictedData.residual_nonneg_on_admissible f (all_admissible f))
    (fun hres =>
      restrictedData.restricted_positivity_implies_RHOn_univ
        (fun f _hf => hres f))

end SupportRestrictedFormulaResidualPositivityData

/--
A bridge from support-restricted residual positivity to Li-coefficient
positivity.

This is the support-restricted analogue of
`FormulaResidualToLiPositivityBridge`.  Future work can try to prove Li
coefficient positivity from a smaller admissible class of test functions before
attempting full residual positivity.
-/
structure SupportRestrictedFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  restricted_residual_nonneg_implies_li_nonneg :
    (forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= formulaData.sideData.residualSide f) ->
      forall n : Nat, 0 < n -> 0 <= liData.coefficient n

namespace SupportRestrictedFormulaResidualToLiBridge

/--
Restricted residual positivity proves universal local RH through the packaged
Li criterion.
-/
theorem restricted_residual_nonneg_implies_RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        formulaData admissible liData)
    (hres :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    RHOn (fun _ : Complex => True) :=
  liData.RHOn_of_li_nonneg
    (bridge.restricted_residual_nonneg_implies_li_nonneg hres)

/--
Restricted residual positivity proves Mathlib RH through the packaged Li
criterion.
-/
theorem mathlib_RH_of_restricted_residual_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        formulaData admissible liData)
    (hres :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    RiemannHypothesis :=
  liData.mathlib_RH_of_li_nonneg_univ
    (bridge.restricted_residual_nonneg_implies_li_nonneg hres)

/--
Package a restricted residual-to-Li bridge together with an actual restricted
nonnegativity proof as support-restricted residual positivity data.
-/
noncomputable def toSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        formulaData admissible liData)
    (residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    SupportRestrictedFormulaResidualPositivityData formulaData where
  admissible := admissible
  residual_nonneg_on_admissible := residual_nonneg_on_admissible
  restricted_positivity_implies_RHOn_univ :=
    fun hres => bridge.restricted_residual_nonneg_implies_RHOn_univ hres

/--
Package support-restricted positivity when nonnegativity is proved for another
residual-side normalization equal to the formula residual side.

This is the generic transport used by the source Guinand-Weil route: prove
nonnegativity in source residual notation, then rewrite to the normalized
formula residual side used by the RH endpoint.
-/
noncomputable def toSupportRestrictedFormulaResidualPositivityDataOfResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        formulaData admissible liData)
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceResidualSide f) :
    SupportRestrictedFormulaResidualPositivityData formulaData :=
  bridge.toSupportRestrictedFormulaResidualPositivityData
    (fun f hf => by
      rw [residualSide_eq_source f]
      exact source_residual_nonneg_on_admissible f hf)

/--
A restricted residual-to-Li bridge becomes the full residual-to-Li bridge used
by the existing pipeline, since full residual nonnegativity immediately implies
restricted residual nonnegativity.
-/
noncomputable def toFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        formulaData admissible liData) :
    FormulaResidualToLiPositivityBridge formulaData liData where
  residual_nonneg_implies_li_nonneg := fun hres =>
    bridge.restricted_residual_nonneg_implies_li_nonneg
      (fun f _hf => hres f)

end SupportRestrictedFormulaResidualToLiBridge

end RiemannHypothesisProject
