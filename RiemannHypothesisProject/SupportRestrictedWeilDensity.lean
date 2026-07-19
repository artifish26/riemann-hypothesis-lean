import RiemannHypothesisProject.SupportRestrictedWeilPositivity

/-!
# Density bridge for support-restricted positivity

Support-restricted Weil positivity is useful only if it can be connected to the
full residual positivity package.  One standard route is density: prove
positivity on an admissible class, prove that class is dense in the test
function topology, and prove that the residual-nonnegative locus is closed.

This file checks that abstract route.  It does not prove the Burnol-style
density theorem or residual continuity; those remain explicit fields.
-/

namespace RiemannHypothesisProject

/-- The set of test functions where the packaged formula residual side is nonnegative. -/
def formulaResidualNonnegativeSet
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) :
    Set SchwartzLineTestFunction :=
  {f : SchwartzLineTestFunction | 0 <= formulaData.sideData.residualSide f}

/--
A density/closedness bridge for a support-restricted residual positivity
package.

Future analytic work should supply `dense_admissible` from a support/density
theorem and `residual_nonnegativeSet_closed` from continuity of the chosen
formula residual side.
-/
structure SupportRestrictedFormulaResidualDensityBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData) where
  dense_admissible :
    closure {f : SchwartzLineTestFunction | restrictedData.admissible f} =
      Set.univ
  residual_nonnegativeSet_closed :
    IsClosed (formulaResidualNonnegativeSet formulaData)

namespace SupportRestrictedFormulaResidualDensityBridge

/--
Restricted residual nonnegativity promotes to full residual nonnegativity
across a dense admissible class when the nonnegative locus is closed.
-/
theorem residual_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (bridge :
      SupportRestrictedFormulaResidualDensityBridge restrictedData) :
    forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f := by
  intro f
  have hadmissible_subset :
      {g : SchwartzLineTestFunction | restrictedData.admissible g} ⊆
        formulaResidualNonnegativeSet formulaData := by
    intro g hg
    exact restrictedData.residual_nonneg_on_admissible g hg
  have hclosure_subset :
      closure {g : SchwartzLineTestFunction | restrictedData.admissible g} ⊆
        formulaResidualNonnegativeSet formulaData :=
    closure_minimal hadmissible_subset bridge.residual_nonnegativeSet_closed
  have hf_closure :
      f ∈ closure {g : SchwartzLineTestFunction | restrictedData.admissible g} := by
    rw [bridge.dense_admissible]
    exact Set.mem_univ f
  exact hclosure_subset hf_closure

/--
Turn support-restricted positivity into ordinary formula-side residual
positivity using density and closedness.
-/
noncomputable def toFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (bridge :
      SupportRestrictedFormulaResidualDensityBridge restrictedData) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  SchwartzRiemannWeilFormulaResidualPositivityData.ofRawResidualPositivity
    bridge.residual_nonneg
    (fun hres =>
      restrictedData.restricted_positivity_implies_RHOn_univ
        (fun f _hf => hres f))

/-- The density bridge plus restricted positivity proves universal local RH. -/
theorem RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (bridge :
      SupportRestrictedFormulaResidualDensityBridge restrictedData) :
    RHOn (fun _ : Complex => True) :=
  bridge.toFormulaResidualPositivityData
    |>.residual_positivity_implies_RHOn_univ bridge.residual_nonneg

/-- The density bridge plus restricted positivity proves the project RH statement. -/
theorem RHStatement
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (bridge :
      SupportRestrictedFormulaResidualDensityBridge restrictedData) :
    RiemannHypothesisProject.RHStatement :=
  RHStatement_iff_RHOn_univ.mpr bridge.RHOn_univ

/-- The density bridge plus restricted positivity proves Mathlib RH. -/
theorem mathlib_RH
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (bridge :
      SupportRestrictedFormulaResidualDensityBridge restrictedData) :
    RiemannHypothesis :=
  RHStatement_iff_mathlib.mp bridge.RHStatement

end SupportRestrictedFormulaResidualDensityBridge

end RiemannHypothesisProject
