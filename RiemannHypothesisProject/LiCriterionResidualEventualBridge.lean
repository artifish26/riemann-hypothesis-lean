import RiemannHypothesisProject.LiCriterionEventualPositivity

/-!
# Residual-to-eventual Li positivity bridge

`FormulaResidualToLiPositivityBridge` asks future work to prove all
Li-coefficient inequalities directly from formula-side residual positivity.
In practice, that proof may split into a finite prefix and an eventual tail.

This file checks that split route and converts it back to the existing
residual-to-Li pipeline.
-/

namespace RiemannHypothesisProject

/--
A bridge from formula-side residual positivity to finite-prefix plus eventual
Li-coefficient positivity.

The two fields are deliberately separate so future work can combine finite
certificates for `0 < n < cutoff` with an analytic tail theorem for
`cutoff <= n`.
-/
structure FormulaResidualToLiEventualPositivityBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  cutoff : Nat
  residual_nonneg_implies_prefix_nonneg :
    (forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f) ->
      forall n : Nat, 0 < n -> n < cutoff -> 0 <= liData.coefficient n
  residual_nonneg_implies_tail_nonneg :
    (forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f) ->
      forall n : Nat, cutoff <= n -> 0 <= liData.coefficient n

namespace FormulaResidualToLiEventualPositivityBridge

/-- Residual nonnegativity packages as eventual Li positivity. -/
noncomputable def toEventualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiEventualPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    AbstractLiEventualPositivityData liData where
  cutoff := bridge.cutoff
  prefix_nonneg :=
    bridge.residual_nonneg_implies_prefix_nonneg residual_nonneg
  tail_nonneg :=
    bridge.residual_nonneg_implies_tail_nonneg residual_nonneg

/-- Residual nonnegativity gives all positive-index Li-coefficient inequalities. -/
theorem residual_nonneg_implies_li_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiEventualPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    forall n : Nat, 0 < n -> 0 <= liData.coefficient n :=
  (bridge.toEventualPositivityData residual_nonneg).li_nonneg

/-- Convert the eventual bridge into the existing all-coefficients residual-to-Li bridge. -/
noncomputable def toFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiEventualPositivityBridge formulaData liData) :
    FormulaResidualToLiPositivityBridge formulaData liData where
  residual_nonneg_implies_li_nonneg :=
    bridge.residual_nonneg_implies_li_nonneg

/-- Residual positivity proves universal local RH through the eventual Li split. -/
theorem residual_nonneg_implies_RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiEventualPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    RHOn (fun _ : Complex => True) :=
  (bridge.toEventualPositivityData residual_nonneg).RHOn

/--
Build formula-side residual positivity data from an eventual residual-to-Li
bridge and a residual nonnegativity theorem.
-/
noncomputable def toFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiEventualPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  bridge.toFormulaResidualToLiBridge.toFormulaResidualPositivityData
    residual_nonneg

/-- The eventual residual-to-Li bridge gives Mathlib RH once residual nonnegativity is proved. -/
theorem mathlib_RH_of_residual_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiEventualPositivityBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    RiemannHypothesis :=
  bridge.toFormulaResidualToLiBridge.mathlib_RH_of_residual_nonneg
    residual_nonneg

end FormulaResidualToLiEventualPositivityBridge

/--
Build a residual-to-eventual-Li bridge with cutoff `2`.

The finite-prefix residual-to-Li obligation is reduced to the single
coefficient `1`; the remaining analytic theorem is the tail for `2 <= n`.
-/
noncomputable def FormulaResidualToLiEventualPositivityBridge.ofCutoffTwo
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (residual_nonneg_implies_one_nonneg :
      (forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) ->
        0 <= liData.coefficient 1)
    (residual_nonneg_implies_tail_nonneg :
      (forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) ->
        forall n : Nat, 2 <= n -> 0 <= liData.coefficient n) :
    FormulaResidualToLiEventualPositivityBridge formulaData liData where
  cutoff := 2
  residual_nonneg_implies_prefix_nonneg := by
    intro residual_nonneg
    exact
      AbstractLiEventualPositivityData.prefix_nonneg_cutoffTwo_of_one_nonneg
        (residual_nonneg_implies_one_nonneg residual_nonneg)
  residual_nonneg_implies_tail_nonneg :=
    residual_nonneg_implies_tail_nonneg

end RiemannHypothesisProject
