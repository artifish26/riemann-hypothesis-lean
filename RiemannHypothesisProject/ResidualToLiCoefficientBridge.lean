import RiemannHypothesisProject.LiCriterionResidualEventualBridge

/-!
# Residual-to-Li coefficient bridge

`FormulaResidualToLiPositivityBridge` is intentionally broad: it asks future
work to prove that formula-side residual nonnegativity implies all Li
coefficient inequalities.

This file records a more concrete Lagarias-style route.  If each positive-index
Li coefficient is identified with a nonnegative scalar multiple of the formula
residual evaluated at a designated test function, then residual nonnegativity
implies Li coefficient nonnegativity automatically.

No coefficient identity is proved here; those identities are the analytic
content of a future residual-to-Li theorem.
-/

namespace RiemannHypothesisProject

noncomputable section

/--
A coefficient-level bridge from formula residual positivity to Li positivity.

For each positive index `n`, future analytic work supplies a test function and
a nonnegative scale factor such that the chosen Li coefficient is exactly that
scale times the formula residual of the test.  This isolates the coefficient
identity from the final RH implication.
-/
structure FormulaResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  coefficientTest : Nat -> SchwartzLineTestFunction
  coefficientScale : Nat -> Real
  coefficientScale_nonneg :
    forall n : Nat, 0 < n -> 0 <= coefficientScale n
  coefficient_eq_scaled_residual :
    forall n : Nat,
      0 < n ->
        liData.coefficient n =
          coefficientScale n *
            formulaData.sideData.residualSide (coefficientTest n)

namespace FormulaResidualToLiCoefficientBridge

/-- Residual nonnegativity gives all positive-index Li coefficient inequalities. -/
theorem residual_nonneg_implies_li_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiCoefficientBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    forall n : Nat, 0 < n -> 0 <= liData.coefficient n := by
  intro n hn
  rw [bridge.coefficient_eq_scaled_residual n hn]
  exact mul_nonneg (bridge.coefficientScale_nonneg n hn)
    (residual_nonneg (bridge.coefficientTest n))

/-- Convert the coefficient bridge into the existing residual-to-Li bridge. -/
noncomputable def toFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiCoefficientBridge formulaData liData) :
    FormulaResidualToLiPositivityBridge formulaData liData where
  residual_nonneg_implies_li_nonneg :=
    bridge.residual_nonneg_implies_li_nonneg

/--
Convert the coefficient bridge into the finite-prefix/eventual-tail bridge, for
any positive cutoff.
-/
noncomputable def toEventualBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiCoefficientBridge formulaData liData)
    (cutoff : Nat)
    (cutoff_pos : 0 < cutoff) :
    FormulaResidualToLiEventualPositivityBridge formulaData liData where
  cutoff := cutoff
  residual_nonneg_implies_prefix_nonneg := by
    intro residual_nonneg n hn _hn_cutoff
    exact bridge.residual_nonneg_implies_li_nonneg residual_nonneg n hn
  residual_nonneg_implies_tail_nonneg := by
    intro residual_nonneg n hcutoff
    have hn : 0 < n := lt_of_lt_of_le cutoff_pos hcutoff
    exact bridge.residual_nonneg_implies_li_nonneg residual_nonneg n hn

/--
Build formula-side residual positivity data from coefficient identities and a
residual nonnegativity theorem.
-/
noncomputable def toFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiCoefficientBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  bridge.toFormulaResidualToLiBridge.toFormulaResidualPositivityData
    residual_nonneg

/--
Transport coefficient identities across an equality of residual-side
normalizations.

This lets future analytic work state Li coefficient identities in source
Guinand-Weil residual notation, then use the checked normalization projection
to obtain the formula-residual bridge required by the RH endpoint.
-/
noncomputable def ofResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientScale : Nat -> Real)
    (coefficientScale_nonneg :
      forall n : Nat, 0 < n -> 0 <= coefficientScale n)
    (coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            coefficientScale n * sourceResidualSide (coefficientTest n)) :
    FormulaResidualToLiCoefficientBridge formulaData liData where
  coefficientTest := coefficientTest
  coefficientScale := coefficientScale
  coefficientScale_nonneg := coefficientScale_nonneg
  coefficient_eq_scaled_residual := by
    intro n hn
    rw [coefficient_eq_scaled_sourceResidual n hn,
      residualSide_eq_source (coefficientTest n)]

/--
Unit-scale source-residual constructor: future analytic work may state each Li
coefficient directly as the source residual of a chosen test, then transport it
through the normalization projection.
-/
noncomputable def ofSourceCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficient_eq_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n = sourceResidualSide (coefficientTest n)) :
    FormulaResidualToLiCoefficientBridge formulaData liData :=
  ofResidualSideEq sourceResidualSide residualSide_eq_source
    coefficientTest (fun _ => 1)
    (by
      intro _ _
      norm_num)
    (by
      intro n hn
      simp [coefficient_eq_sourceResidual n hn])

/-- The coefficient bridge gives Mathlib RH once residual nonnegativity is proved. -/
theorem mathlib_RH_of_residual_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge : FormulaResidualToLiCoefficientBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    RiemannHypothesis :=
  bridge.toFormulaResidualToLiBridge.mathlib_RH_of_residual_nonneg
    residual_nonneg

/--
Unit-scale constructor: if each coefficient is literally the residual side of
a chosen test function, it is a special case of the scaled bridge.
-/
noncomputable def ofCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficient_eq_residual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            formulaData.sideData.residualSide (coefficientTest n)) :
    FormulaResidualToLiCoefficientBridge formulaData liData where
  coefficientTest := coefficientTest
  coefficientScale := fun _ => 1
  coefficientScale_nonneg := by
    intro _ _
    norm_num
  coefficient_eq_scaled_residual := by
    intro n hn
    simp [coefficient_eq_residual n hn]

end FormulaResidualToLiCoefficientBridge

/--
Cutoff-2 coefficient-level bridge from formula residual positivity to Li
positivity.

This is the coefficient-identity companion to
`FormulaResidualToLiEventualPositivityBridge.ofCutoffTwo`: prove one scaled
residual identity for coefficient `1`, then prove a separate scaled residual
identity family only for the tail `2 <= n`.
-/
structure FormulaResidualToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  coefficientOneTest : SchwartzLineTestFunction
  coefficientOneScale : Real
  coefficientOneScale_nonneg : 0 <= coefficientOneScale
  coefficient_one_eq_scaled_residual :
    liData.coefficient 1 =
      coefficientOneScale *
        formulaData.sideData.residualSide coefficientOneTest
  tailCoefficientTest : Nat -> SchwartzLineTestFunction
  tailCoefficientScale : Nat -> Real
  tailCoefficientScale_nonneg :
    forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n
  tail_coefficient_eq_scaled_residual :
    forall n : Nat,
      2 <= n ->
        liData.coefficient n =
          tailCoefficientScale n *
            formulaData.sideData.residualSide (tailCoefficientTest n)

namespace FormulaResidualToLiCutoffTwoCoefficientBridge

/-- A positive natural number different from `1` is in the cutoff-2 tail. -/
theorem two_le_of_pos_ne_one
    {n : Nat} (hn : 0 < n) (hn_one : n ≠ 1) :
    2 <= n := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ n =>
      cases n with
      | zero =>
          exact (hn_one rfl).elim
      | succ n =>
          exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))

/-- Residual nonnegativity gives nonnegativity of coefficient `1`. -/
theorem residual_nonneg_implies_one_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    0 <= liData.coefficient 1 := by
  rw [bridge.coefficient_one_eq_scaled_residual]
  exact mul_nonneg bridge.coefficientOneScale_nonneg
    (residual_nonneg bridge.coefficientOneTest)

/-- Residual nonnegativity gives tail Li-coefficient nonnegativity. -/
theorem residual_nonneg_implies_tail_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    forall n : Nat, 2 <= n -> 0 <= liData.coefficient n := by
  intro n hn
  rw [bridge.tail_coefficient_eq_scaled_residual n hn]
  exact mul_nonneg (bridge.tailCoefficientScale_nonneg n hn)
    (residual_nonneg (bridge.tailCoefficientTest n))

/-- Convert cutoff-2 coefficient identities to the cutoff-2 eventual bridge. -/
noncomputable def toEventualBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData) :
    FormulaResidualToLiEventualPositivityBridge formulaData liData :=
  FormulaResidualToLiEventualPositivityBridge.ofCutoffTwo
    bridge.residual_nonneg_implies_one_nonneg
    bridge.residual_nonneg_implies_tail_nonneg

/-- Convert cutoff-2 coefficient identities to the broad residual-to-Li bridge. -/
noncomputable def toFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData) :
    FormulaResidualToLiPositivityBridge formulaData liData :=
  bridge.toEventualBridge.toFormulaResidualToLiBridge

/--
Convert cutoff-2 coefficient identities to the existing all-positive-index
coefficient bridge shape.
-/
noncomputable def toFormulaResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData) :
    FormulaResidualToLiCoefficientBridge formulaData liData where
  coefficientTest := fun n =>
    if n = 1 then bridge.coefficientOneTest else bridge.tailCoefficientTest n
  coefficientScale := fun n =>
    if n = 1 then bridge.coefficientOneScale else bridge.tailCoefficientScale n
  coefficientScale_nonneg := by
    intro n hn
    by_cases hn_one : n = 1
    · simpa [hn_one] using bridge.coefficientOneScale_nonneg
    · have htail : 2 <= n := two_le_of_pos_ne_one hn hn_one
      simpa [hn_one] using bridge.tailCoefficientScale_nonneg n htail
  coefficient_eq_scaled_residual := by
    intro n hn
    by_cases hn_one : n = 1
    · subst n
      simp [bridge.coefficient_one_eq_scaled_residual]
    · have htail : 2 <= n := two_le_of_pos_ne_one hn hn_one
      simp [hn_one, bridge.tail_coefficient_eq_scaled_residual n htail]

/--
Build formula-side residual positivity data from cutoff-2 coefficient
identities and a residual nonnegativity theorem.
-/
noncomputable def toFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData)
    (residual_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= formulaData.sideData.residualSide f) :
    SchwartzRiemannWeilFormulaResidualPositivityData formulaData :=
  bridge.toFormulaResidualToLiBridge.toFormulaResidualPositivityData
    residual_nonneg

/--
Transport cutoff-2 coefficient identities across an equality of residual-side
normalizations.

The coefficient `1` identity and the `2 <= n` tail family can be proved in
source residual notation and then converted to the normalized formula side.
-/
noncomputable def ofResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale * sourceResidualSide coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientScale : Nat -> Real)
    (tailCoefficientScale_nonneg :
      forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n)
    (tail_coefficient_eq_scaled_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            tailCoefficientScale n * sourceResidualSide (tailCoefficientTest n)) :
    FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData where
  coefficientOneTest := coefficientOneTest
  coefficientOneScale := coefficientOneScale
  coefficientOneScale_nonneg := coefficientOneScale_nonneg
  coefficient_one_eq_scaled_residual := by
    rw [coefficient_one_eq_scaled_sourceResidual,
      residualSide_eq_source coefficientOneTest]
  tailCoefficientTest := tailCoefficientTest
  tailCoefficientScale := tailCoefficientScale
  tailCoefficientScale_nonneg := tailCoefficientScale_nonneg
  tail_coefficient_eq_scaled_residual := by
    intro n hn
    rw [tail_coefficient_eq_scaled_sourceResidual n hn,
      residualSide_eq_source (tailCoefficientTest n)]

/--
Unit-scale source-residual constructor for the cutoff-2 bridge.  The coefficient
`1` and the tail identities may be proved directly against a source residual
normalization, then transported to the formula residual side.
-/
noncomputable def ofSourceCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficient_one_eq_sourceResidual :
      liData.coefficient 1 = sourceResidualSide coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tail_coefficient_eq_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n = sourceResidualSide (tailCoefficientTest n)) :
    FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData :=
  ofResidualSideEq sourceResidualSide residualSide_eq_source
    coefficientOneTest 1
    (by norm_num)
    (by
      simp [coefficient_one_eq_sourceResidual])
    tailCoefficientTest (fun _ => 1)
    (by
      intro _ _
      norm_num)
    (by
      intro n hn
      simp [tail_coefficient_eq_sourceResidual n hn])

/--
Unit-scale constructor for the cutoff-2 coefficient bridge: coefficient `1`
and each tail coefficient are literally formula residual values.
-/
noncomputable def ofCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficient_one_eq_residual :
      liData.coefficient 1 =
        formulaData.sideData.residualSide coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tail_coefficient_eq_residual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            formulaData.sideData.residualSide (tailCoefficientTest n)) :
    FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData where
  coefficientOneTest := coefficientOneTest
  coefficientOneScale := 1
  coefficientOneScale_nonneg := by norm_num
  coefficient_one_eq_scaled_residual := by
    simp [coefficient_one_eq_residual]
  tailCoefficientTest := tailCoefficientTest
  tailCoefficientScale := fun _ => 1
  tailCoefficientScale_nonneg := by
    intro _ _
    norm_num
  tail_coefficient_eq_scaled_residual := by
    intro n hn
    simp [tail_coefficient_eq_residual n hn]

end FormulaResidualToLiCutoffTwoCoefficientBridge

end

end RiemannHypothesisProject
