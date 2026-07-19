import RiemannHypothesisProject.SchwartzRiemannWeilResidualContinuity

/-!
# Constructors for support-restricted density bridges

The support-restricted positivity route asks for density of the admissible test
class.  In applications, one usually proves density of a smaller concrete core
class, then proves that this core is admissible.  This file checks that
standard move and connects it to the residual-continuity bridge.
-/

namespace RiemannHypothesisProject

/--
A dense core inside the admissible class of a support-restricted positivity
package.

Future analytic work can instantiate `core` with compactly supported tests,
bandlimited approximants, Paley-Wiener functions, or another concrete dense
subclass, then prove the two displayed fields.
-/
structure SupportRestrictedFormulaResidualDenseCore
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData) where
  core : Set SchwartzLineTestFunction
  core_subset_admissible :
    core ⊆ {f : SchwartzLineTestFunction | restrictedData.admissible f}
  dense_core :
    closure core = Set.univ

namespace SupportRestrictedFormulaResidualDenseCore

/-- A dense admissible core proves density of the whole admissible class. -/
theorem dense_admissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (coreData :
      SupportRestrictedFormulaResidualDenseCore restrictedData) :
    closure {f : SchwartzLineTestFunction | restrictedData.admissible f} =
      Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro f
  have hf_core : f ∈ closure coreData.core := by
    rw [coreData.dense_core]
    exact Set.mem_univ f
  exact (closure_mono coreData.core_subset_admissible) hf_core

/--
Build the full density bridge from a dense core and closedness of the
residual-nonnegative locus.
-/
noncomputable def toSupportRestrictedDensityBridgeOfClosed
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (coreData :
      SupportRestrictedFormulaResidualDenseCore restrictedData)
    (residual_nonnegativeSet_closed :
      IsClosed (formulaResidualNonnegativeSet formulaData)) :
    SupportRestrictedFormulaResidualDensityBridge restrictedData where
  dense_admissible := coreData.dense_admissible
  residual_nonnegativeSet_closed := residual_nonnegativeSet_closed

/-- Build the full density bridge from a dense core and residual-side continuity. -/
noncomputable def toSupportRestrictedDensityBridgeOfResidualContinuity
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (coreData :
      SupportRestrictedFormulaResidualDenseCore restrictedData)
    (continuity :
      SchwartzRiemannWeilFormulaResidualContinuityData formulaData) :
    SupportRestrictedFormulaResidualDensityBridge restrictedData :=
  continuity.toSupportRestrictedDensityBridge coreData.dense_admissible

/-- Build the full density bridge from a dense core and separate side continuity. -/
noncomputable def toSupportRestrictedDensityBridgeOfSideContinuity
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (coreData :
      SupportRestrictedFormulaResidualDenseCore restrictedData)
    (continuity :
      SchwartzRiemannWeilFormulaSideContinuityData formulaData) :
    SupportRestrictedFormulaResidualDensityBridge restrictedData :=
  continuity.toSupportRestrictedDensityBridge coreData.dense_admissible

end SupportRestrictedFormulaResidualDenseCore

/--
The special case where every test function is admissible.  This is mostly a
sanity check and a bridge for unrestricted positivity packages.
-/
noncomputable def SupportRestrictedFormulaResidualDenseCore.ofAllAdmissible
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData)
    (all_admissible :
      forall f : SchwartzLineTestFunction, restrictedData.admissible f) :
    SupportRestrictedFormulaResidualDenseCore restrictedData where
  core := Set.univ
  core_subset_admissible := by
    intro f _hf
    exact all_admissible f
  dense_core := by
    rw [closure_univ]

end RiemannHypothesisProject
