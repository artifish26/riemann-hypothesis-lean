import RiemannHypothesisProject.ResidualToLiCoefficientBridge
import RiemannHypothesisProject.SupportRestrictedWeilPositivity

/-!
# Support-restricted residual-to-Li coefficient bridge

`ResidualToLiCoefficientBridge` handles the full residual-positivity route:
each Li coefficient is a nonnegative scalar multiple of the formula residual
evaluated at a designated test function.

For support-restricted positivity, those designated tests must also be
admissible.  This file records that sharper target.  Future analytic work can
prove coefficient identities and admissibility of the coefficient-test family,
then Lean derives the support-restricted residual-to-Li bridge automatically.
-/

namespace RiemannHypothesisProject

noncomputable section

/--
A coefficient-level bridge from support-restricted formula residual positivity
to Li positivity.

For each positive index `n`, the test function used to represent the `n`th Li
coefficient must belong to the admissible class.
-/
structure SupportRestrictedFormulaResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  coefficientTest : Nat -> SchwartzLineTestFunction
  coefficientTest_admissible :
    forall n : Nat, 0 < n -> admissible (coefficientTest n)
  coefficientScale : Nat -> Real
  coefficientScale_nonneg :
    forall n : Nat, 0 < n -> 0 <= coefficientScale n
  coefficient_eq_scaled_residual :
    forall n : Nat,
      0 < n ->
        liData.coefficient n =
          coefficientScale n *
            formulaData.sideData.residualSide (coefficientTest n)

namespace SupportRestrictedFormulaResidualToLiCoefficientBridge

/-- Restricted residual nonnegativity gives all positive-index Li inequalities. -/
theorem restricted_residual_nonneg_implies_li_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        formulaData admissible liData)
    (restricted_residual_nonneg :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    forall n : Nat, 0 < n -> 0 <= liData.coefficient n := by
  intro n hn
  rw [bridge.coefficient_eq_scaled_residual n hn]
  exact mul_nonneg (bridge.coefficientScale_nonneg n hn)
    (restricted_residual_nonneg
      (bridge.coefficientTest n)
      (bridge.coefficientTest_admissible n hn))

/-- Convert to the broad support-restricted residual-to-Li bridge. -/
noncomputable def toSupportRestrictedFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        formulaData admissible liData) :
    SupportRestrictedFormulaResidualToLiBridge formulaData admissible liData where
  restricted_residual_nonneg_implies_li_nonneg :=
    bridge.restricted_residual_nonneg_implies_li_nonneg

/--
Forget admissibility and convert to the full residual-to-Li coefficient bridge.

This is useful after density has promoted restricted residual positivity to
full residual nonnegativity.
-/
noncomputable def toFormulaResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        formulaData admissible liData) :
    FormulaResidualToLiCoefficientBridge formulaData liData where
  coefficientTest := bridge.coefficientTest
  coefficientScale := bridge.coefficientScale
  coefficientScale_nonneg := bridge.coefficientScale_nonneg
  coefficient_eq_scaled_residual := bridge.coefficient_eq_scaled_residual

/-- Restricted residual nonnegativity proves universal local RH through Li. -/
theorem restricted_residual_nonneg_implies_RHOn_univ
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        formulaData admissible liData)
    (restricted_residual_nonneg :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    RHOn (fun _ : Complex => True) :=
  liData.RHOn_of_li_nonneg
    (bridge.restricted_residual_nonneg_implies_li_nonneg
      restricted_residual_nonneg)

/-- Restricted residual nonnegativity proves Mathlib RH through Li. -/
theorem mathlib_RH_of_restricted_residual_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
        formulaData admissible liData)
    (restricted_residual_nonneg :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    RiemannHypothesis :=
  liData.mathlib_RH_of_li_nonneg_univ
    (bridge.restricted_residual_nonneg_implies_li_nonneg
      restricted_residual_nonneg)

/--
Package a coefficient bridge and a restricted residual nonnegativity proof as
support-restricted residual positivity data.
-/
noncomputable def toSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCoefficientBridge
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
Transport support-restricted coefficient identities across an equality of
residual-side normalizations.

This is the source-residual version of the support-restricted coefficient
target: future work may prove admissibility and Li coefficient identities for
tests written against the source Guinand-Weil residual, then Lean rewrites
them to the normalized formula residual side.
-/
noncomputable def ofResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
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
            coefficientScale n * sourceResidualSide (coefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      formulaData admissible liData where
  coefficientTest := coefficientTest
  coefficientTest_admissible := coefficientTest_admissible
  coefficientScale := coefficientScale
  coefficientScale_nonneg := coefficientScale_nonneg
  coefficient_eq_scaled_residual := by
    intro n hn
    rw [coefficient_eq_scaled_sourceResidual n hn,
      residualSide_eq_source (coefficientTest n)]

/--
Unit-scale source-residual constructor: future analytic work may state each Li
coefficient directly as the source residual of an admissible test, then
transport it through the normalization projection.
-/
noncomputable def ofSourceCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficient_eq_sourceResidual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n = sourceResidualSide (coefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      formulaData admissible liData :=
  ofResidualSideEq sourceResidualSide residualSide_eq_source
    coefficientTest coefficientTest_admissible (fun _ => 1)
    (by
      intro _ _
      norm_num)
    (by
      intro n hn
      simp [coefficient_eq_sourceResidual n hn])

/--
Unit-scale constructor: if each coefficient is literally the residual side of
an admissible test function, it is a special case of the scaled bridge.
-/
noncomputable def ofCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (coefficientTest : Nat -> SchwartzLineTestFunction)
    (coefficientTest_admissible :
      forall n : Nat, 0 < n -> admissible (coefficientTest n))
    (coefficient_eq_residual :
      forall n : Nat,
        0 < n ->
          liData.coefficient n =
            formulaData.sideData.residualSide (coefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      formulaData admissible liData where
  coefficientTest := coefficientTest
  coefficientTest_admissible := coefficientTest_admissible
  coefficientScale := fun _ => 1
  coefficientScale_nonneg := by
    intro _ _
    norm_num
  coefficient_eq_scaled_residual := by
    intro n hn
    simp [coefficient_eq_residual n hn]

end SupportRestrictedFormulaResidualToLiCoefficientBridge

/--
Cutoff-2 support-restricted coefficient bridge.

The support-restricted route can now prove admissibility and the coefficient
identity for coefficient `1` separately from the admissible tail family
`2 <= n`.
-/
structure SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (liData : AbstractLiCriterionData (fun _ : Complex => True)) where
  coefficientOneTest : SchwartzLineTestFunction
  coefficientOneTest_admissible : admissible coefficientOneTest
  coefficientOneScale : Real
  coefficientOneScale_nonneg : 0 <= coefficientOneScale
  coefficient_one_eq_scaled_residual :
    liData.coefficient 1 =
      coefficientOneScale *
        formulaData.sideData.residualSide coefficientOneTest
  tailCoefficientTest : Nat -> SchwartzLineTestFunction
  tailCoefficientTest_admissible :
    forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n)
  tailCoefficientScale : Nat -> Real
  tailCoefficientScale_nonneg :
    forall n : Nat, 2 <= n -> 0 <= tailCoefficientScale n
  tail_coefficient_eq_scaled_residual :
    forall n : Nat,
      2 <= n ->
        liData.coefficient n =
          tailCoefficientScale n *
            formulaData.sideData.residualSide (tailCoefficientTest n)

namespace SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge

/-- Restricted residual nonnegativity gives nonnegativity of coefficient `1`. -/
theorem restricted_residual_nonneg_implies_one_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData)
    (restricted_residual_nonneg :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    0 <= liData.coefficient 1 := by
  rw [bridge.coefficient_one_eq_scaled_residual]
  exact mul_nonneg bridge.coefficientOneScale_nonneg
    (restricted_residual_nonneg bridge.coefficientOneTest
      bridge.coefficientOneTest_admissible)

/-- Restricted residual nonnegativity gives tail Li-coefficient nonnegativity. -/
theorem restricted_residual_nonneg_implies_tail_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData)
    (restricted_residual_nonneg :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    forall n : Nat, 2 <= n -> 0 <= liData.coefficient n := by
  intro n hn
  rw [bridge.tail_coefficient_eq_scaled_residual n hn]
  exact mul_nonneg (bridge.tailCoefficientScale_nonneg n hn)
    (restricted_residual_nonneg (bridge.tailCoefficientTest n)
      (bridge.tailCoefficientTest_admissible n hn))

/-- Restricted residual nonnegativity gives all positive-index Li inequalities. -/
theorem restricted_residual_nonneg_implies_li_nonneg
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData)
    (restricted_residual_nonneg :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    forall n : Nat, 0 < n -> 0 <= liData.coefficient n := by
  intro n hn
  by_cases htail : 2 <= n
  · exact bridge.restricted_residual_nonneg_implies_tail_nonneg
      restricted_residual_nonneg n htail
  · have hnlt : n < 2 := Nat.lt_of_not_ge htail
    cases n with
    | zero =>
        exact (Nat.not_lt_zero 0 hn).elim
    | succ n =>
        cases n with
        | zero =>
            simpa using
              bridge.restricted_residual_nonneg_implies_one_nonneg
                restricted_residual_nonneg
        | succ n =>
            have htwo : 2 <= Nat.succ (Nat.succ n) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
            exact (not_lt_of_ge htwo hnlt).elim

/-- Convert to the broad support-restricted residual-to-Li bridge. -/
noncomputable def toSupportRestrictedFormulaResidualToLiBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData) :
    SupportRestrictedFormulaResidualToLiBridge formulaData admissible liData where
  restricted_residual_nonneg_implies_li_nonneg :=
    bridge.restricted_residual_nonneg_implies_li_nonneg

/--
Convert cutoff-2 support-restricted coefficient identities to the existing
all-positive-index support-restricted coefficient bridge shape.
-/
noncomputable def toSupportRestrictedFormulaResidualToLiCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData) :
    SupportRestrictedFormulaResidualToLiCoefficientBridge
      formulaData admissible liData where
  coefficientTest := fun n =>
    if n = 1 then bridge.coefficientOneTest else bridge.tailCoefficientTest n
  coefficientTest_admissible := by
    intro n hn
    by_cases hn_one : n = 1
    · simpa [hn_one] using bridge.coefficientOneTest_admissible
    · have htail : 2 <= n :=
        FormulaResidualToLiCutoffTwoCoefficientBridge.two_le_of_pos_ne_one
          hn hn_one
      simpa [hn_one] using bridge.tailCoefficientTest_admissible n htail
  coefficientScale := fun n =>
    if n = 1 then bridge.coefficientOneScale else bridge.tailCoefficientScale n
  coefficientScale_nonneg := by
    intro n hn
    by_cases hn_one : n = 1
    · simpa [hn_one] using bridge.coefficientOneScale_nonneg
    · have htail : 2 <= n :=
        FormulaResidualToLiCutoffTwoCoefficientBridge.two_le_of_pos_ne_one
          hn hn_one
      simpa [hn_one] using bridge.tailCoefficientScale_nonneg n htail
  coefficient_eq_scaled_residual := by
    intro n hn
    by_cases hn_one : n = 1
    · subst n
      simp [bridge.coefficient_one_eq_scaled_residual]
    · have htail : 2 <= n :=
        FormulaResidualToLiCutoffTwoCoefficientBridge.two_le_of_pos_ne_one
          hn hn_one
      simp [hn_one, bridge.tail_coefficient_eq_scaled_residual n htail]

/--
Forget admissibility and convert to the full cutoff-2 coefficient bridge.

This is useful after density has promoted restricted residual positivity to
full residual nonnegativity.
-/
noncomputable def toFormulaResidualToLiCutoffTwoCoefficientBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData) :
    FormulaResidualToLiCutoffTwoCoefficientBridge formulaData liData where
  coefficientOneTest := bridge.coefficientOneTest
  coefficientOneScale := bridge.coefficientOneScale
  coefficientOneScale_nonneg := bridge.coefficientOneScale_nonneg
  coefficient_one_eq_scaled_residual :=
    bridge.coefficient_one_eq_scaled_residual
  tailCoefficientTest := bridge.tailCoefficientTest
  tailCoefficientScale := bridge.tailCoefficientScale
  tailCoefficientScale_nonneg := bridge.tailCoefficientScale_nonneg
  tail_coefficient_eq_scaled_residual :=
    bridge.tail_coefficient_eq_scaled_residual

/--
Package a cutoff-2 coefficient bridge and a restricted residual nonnegativity
proof as support-restricted residual positivity data.
-/
noncomputable def toSupportRestrictedFormulaResidualPositivityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (bridge :
      SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
        formulaData admissible liData)
    (residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= formulaData.sideData.residualSide f) :
    SupportRestrictedFormulaResidualPositivityData formulaData where
  admissible := admissible
  residual_nonneg_on_admissible := residual_nonneg_on_admissible
  restricted_positivity_implies_RHOn_univ := by
    intro hres
    exact liData.RHOn_of_li_nonneg
      (bridge.restricted_residual_nonneg_implies_li_nonneg hres)

/--
Transport cutoff-2 support-restricted coefficient identities across an equality
of residual-side normalizations.

This lets the coefficient `1` test and the `2 <= n` admissible tail family be
proved against the source residual side before conversion to the formula side.
-/
noncomputable def ofResidualSideEq
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficientOneScale : Real)
    (coefficientOneScale_nonneg : 0 <= coefficientOneScale)
    (coefficient_one_eq_scaled_sourceResidual :
      liData.coefficient 1 =
        coefficientOneScale * sourceResidualSide coefficientOneTest)
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
            tailCoefficientScale n * sourceResidualSide (tailCoefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
      formulaData admissible liData where
  coefficientOneTest := coefficientOneTest
  coefficientOneTest_admissible := coefficientOneTest_admissible
  coefficientOneScale := coefficientOneScale
  coefficientOneScale_nonneg := coefficientOneScale_nonneg
  coefficient_one_eq_scaled_residual := by
    rw [coefficient_one_eq_scaled_sourceResidual,
      residualSide_eq_source coefficientOneTest]
  tailCoefficientTest := tailCoefficientTest
  tailCoefficientTest_admissible := tailCoefficientTest_admissible
  tailCoefficientScale := tailCoefficientScale
  tailCoefficientScale_nonneg := tailCoefficientScale_nonneg
  tail_coefficient_eq_scaled_residual := by
    intro n hn
    rw [tail_coefficient_eq_scaled_sourceResidual n hn,
      residualSide_eq_source (tailCoefficientTest n)]

/--
Unit-scale source-residual constructor for the cutoff-2 support-restricted
coefficient bridge.  The coefficient `1` and the admissible tail identities may
be proved directly against a source residual normalization, then transported to
the formula residual side.
-/
noncomputable def ofSourceCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (sourceResidualSide : SchwartzLineTestFunction -> Real)
    (residualSide_eq_source :
      forall f : SchwartzLineTestFunction,
        formulaData.sideData.residualSide f = sourceResidualSide f)
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficient_one_eq_sourceResidual :
      liData.coefficient 1 = sourceResidualSide coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tail_coefficient_eq_sourceResidual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n = sourceResidualSide (tailCoefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
      formulaData admissible liData :=
  ofResidualSideEq sourceResidualSide residualSide_eq_source
    coefficientOneTest coefficientOneTest_admissible 1
    (by norm_num)
    (by
      simp [coefficient_one_eq_sourceResidual])
    tailCoefficientTest tailCoefficientTest_admissible (fun _ => 1)
    (by
      intro _ _
      norm_num)
    (by
      intro n hn
      simp [tail_coefficient_eq_sourceResidual n hn])

/--
Unit-scale constructor for the cutoff-2 support-restricted coefficient bridge.
-/
noncomputable def ofCoefficientTests
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {admissible : SchwartzLineTestFunction -> Prop}
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (coefficientOneTest : SchwartzLineTestFunction)
    (coefficientOneTest_admissible : admissible coefficientOneTest)
    (coefficient_one_eq_residual :
      liData.coefficient 1 =
        formulaData.sideData.residualSide coefficientOneTest)
    (tailCoefficientTest : Nat -> SchwartzLineTestFunction)
    (tailCoefficientTest_admissible :
      forall n : Nat, 2 <= n -> admissible (tailCoefficientTest n))
    (tail_coefficient_eq_residual :
      forall n : Nat,
        2 <= n ->
          liData.coefficient n =
            formulaData.sideData.residualSide (tailCoefficientTest n)) :
    SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge
      formulaData admissible liData where
  coefficientOneTest := coefficientOneTest
  coefficientOneTest_admissible := coefficientOneTest_admissible
  coefficientOneScale := 1
  coefficientOneScale_nonneg := by norm_num
  coefficient_one_eq_scaled_residual := by
    simp [coefficient_one_eq_residual]
  tailCoefficientTest := tailCoefficientTest
  tailCoefficientTest_admissible := tailCoefficientTest_admissible
  tailCoefficientScale := fun _ => 1
  tailCoefficientScale_nonneg := by
    intro _ _
    norm_num
  tail_coefficient_eq_scaled_residual := by
    intro n hn
    simp [tail_coefficient_eq_residual n hn]

end SupportRestrictedFormulaResidualToLiCutoffTwoCoefficientBridge

end

end RiemannHypothesisProject
