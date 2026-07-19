import RiemannHypothesisProject.LiCriterion.ShellCoefficient
import RiemannHypothesisProject.SchwartzRiemannWeilPositivityPackages

/-!
# Residual-to-Li bridge input surfaces

This module contains the abstract Li criterion package and the theorem surfaces
connecting formula-side residual positivity to Li-coefficient positivity and RH
endpoints.
-/

namespace RiemannHypothesisProject

open ComplexConjugate
/--
An abstract Li-style criterion for a chosen zero family.

The field `li_nonneg_implies_RHOn` is the formal theorem to be supplied by a
future Bombieri-Lagarias/Li formalization for the chosen coefficient sequence.
-/
structure AbstractLiCriterionData (family : Complex -> Prop) where
  coefficient : Nat -> Real
  li_nonneg_implies_RHOn :
    (forall n : Nat, 0 < n -> 0 <= coefficient n) -> RHOn family

namespace AbstractLiCriterionData

/-- Coefficient nonnegativity proves local RH for the packaged family. -/
theorem RHOn_of_li_nonneg
    {family : Complex -> Prop}
    (liData : AbstractLiCriterionData family)
    (hli : forall n : Nat, 0 < n -> 0 <= liData.coefficient n) :
    RHOn family :=
  liData.li_nonneg_implies_RHOn hli

/-- A universal Li criterion plus coefficient nonnegativity proves project RH. -/
theorem RHStatement_of_li_nonneg_univ
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (hli : forall n : Nat, 0 < n -> 0 <= liData.coefficient n) :
    RHStatement :=
  RHStatement_iff_RHOn_univ.mpr (liData.RHOn_of_li_nonneg hli)

/-- A universal Li criterion plus coefficient nonnegativity proves Mathlib RH. -/
theorem mathlib_RH_of_li_nonneg_univ
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (hli : forall n : Nat, 0 < n -> 0 <= liData.coefficient n) :
    RiemannHypothesis :=
  RHStatement_iff_mathlib.mp
    (liData.RHStatement_of_li_nonneg_univ hli)

end AbstractLiCriterionData

/--
A bridge from formula-side residual positivity to Li-coefficient positivity.

This is the non-tautological place future work should target: prove that the
chosen residual positivity statement implies the positivity of an independently
defined Li/Bombieri-Lagarias coefficient sequence.
-/
structure FormulaResidualToLiPositivityBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  residual_nonneg_implies_li_nonneg :
    (forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f) ->
      forall n : Nat, 0 < n -> 0 <= liData.coefficient n

namespace FormulaResidualToLiPositivityBridge

/--
Residual positivity proves universal local RH via the packaged Li criterion.
-/
theorem residual_nonneg_implies_RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiPositivityBridge formulaData liData)
    (hres :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    RHOn (fun _ : Complex => True) :=
  liData.RHOn_of_li_nonneg
    (bridge.residual_nonneg_implies_li_nonneg hres)

/--
Build formula-side residual positivity data from a residual-to-Li bridge and a
residual nonnegativity theorem.
-/
noncomputable def toFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  SchwartzRiemannWeilFormulaResidualPositivityData.ofRawResidualPositivity
    residual_nonneg
    (fun hres => bridge.residual_nonneg_implies_RHOn_univ hres)

/--
The residual-to-Li bridge gives Mathlib RH once residual nonnegativity is
proved for the packaged formula.
-/
theorem mathlib_RH_of_residual_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    RiemannHypothesis :=
  liData.mathlib_RH_of_li_nonneg_univ
    (bridge.residual_nonneg_implies_li_nonneg residual_nonneg)

end FormulaResidualToLiPositivityBridge
end RiemannHypothesisProject