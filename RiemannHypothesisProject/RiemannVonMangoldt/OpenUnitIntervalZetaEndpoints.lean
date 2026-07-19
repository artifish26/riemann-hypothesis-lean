import RiemannHypothesisProject.RiemannVonMangoldt.EtaLFunctionBridges
import RiemannHypothesisProject.RiemannVonMangoldt.ZModTwoHalfTailContinuation

/-!
# Open-unit-interval zeta endpoint constructors

This module contains the eta/zeta formula targets and constructors for zeta negativity, nonvanishing, and real-axis zero-freeness on the open interval.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/--
Analytic-continuation bridge between the eta alternating-series value and zeta
on the open real interval `(0, 1)`.

This is the remaining source theorem after the checked alternating-series
positivity argument: classically
`eta(x) = (1 - 2^(1 - x)) * zeta(x)`.
-/
def OpenUnitIntervalRiemannZetaEtaFormula : Prop :=
  forall x eta : Real,
    0 < x ->
      x < 1 ->
        DirichletEtaAlternatingLimit x eta ->
          eta =
            (1 - (2 : Real) ^ (1 - x)) *
              (riemannZeta (x : Complex)).re

/--
Canonical-value version of the eta/zeta analytic-continuation bridge on
`(0, 1)`.
-/
def OpenUnitIntervalRiemannZetaEtaValueFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        dirichletEtaAlternatingValue x =
          (1 - (2 : Real) ^ (1 - x)) *
            (riemannZeta (x : Complex)).re

/--
The two eta L-function identifications imply the canonical eta/zeta bridge.

This sharpens the old single analytic-continuation obligation into an
alternating-series-to-L-function statement and an L-function-to-zeta statement.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunction
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaZeta : OpenUnitIntervalDirichletEtaLFunctionZetaRealFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula := by
  intro x hx_pos hx_lt_one
  rw [hetaValue x hx_pos hx_lt_one]
  exact hetaZeta x hx_pos hx_lt_one

/--
The canonical eta/zeta bridge follows from the eta alternating-value
identification plus only the right-half-plane eta/zeta multiplier identity.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue_and_rightHalfPlane
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunction
    hetaValue
    (openUnitIntervalDirichletEtaLFunctionZetaRealFormula_of_rightHalfPlane
      hetaRight)

/--
The canonical eta/zeta bridge follows from the remaining alternating-value
identification with the checked eta L-function.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue_and_rightHalfPlane
    hetaValue dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/--
The canonical eta/zeta bridge recovers the eta alternating-value
identification with the checked eta L-function.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_etaValueFormula
    (hetaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula := by
  intro x hx_pos hx_lt_one
  rw [hetaValueFormula x hx_pos hx_lt_one]
  exact (openUnitIntervalDirichletEtaLFunctionZetaRealFormula
    x hx_pos hx_lt_one).symm

/--
The canonical eta/zeta value formula is equivalent to the eta L-function value
formula, since the eta L-function/zeta real-part identity is checked.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_iff_etaValueFormula :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula <->
      OpenUnitIntervalRiemannZetaEtaValueFormula :=
  ⟨openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue,
    openUnitIntervalDirichletEtaLFunctionValueFormula_of_etaValueFormula⟩

/--
The canonical eta/zeta value formula is equivalent to the conditional-sum eta
L-function value formula.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_iff_etaValueFormula :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula <->
      OpenUnitIntervalRiemannZetaEtaValueFormula := by
  constructor
  · intro hetaSum
    exact
      openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue
        ((openUnitIntervalDirichletEtaLFunctionValueFormula_iff_conditionalSum).2
          hetaSum)
  · intro hetaValueFormula
    exact
      (openUnitIntervalDirichletEtaLFunctionValueFormula_iff_conditionalSum).1
        (openUnitIntervalDirichletEtaLFunctionValueFormula_of_etaValueFormula
          hetaValueFormula)

/--
The Abel-boundary eta theorem plus the right-half-plane eta/zeta multiplier
identity gives the canonical eta/zeta bridge.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaAbelBoundary_and_rightHalfPlane
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula)
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue_and_rightHalfPlane
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_abelBoundary habel)
    hetaRight

/--
The Abel-boundary eta theorem gives the canonical eta/zeta bridge, using the
checked eta/zeta multiplier identity.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaAbelBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaAbelBoundary_and_rightHalfPlane
    habel dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/--
The exponential-zeta Abel-boundary eta theorem gives the canonical eta/zeta
bridge, using the checked eta/zeta multiplier identity.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaExpZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaAbelBoundary
    (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary
      hexp)

/--
The reusable nonzero additive-character Abel theorem gives the canonical
eta/zeta bridge through its `ZMod 2` specialization.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaExpZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The checked-boundary-value additive-character theorem gives the canonical
eta/zeta bridge through the direct eta L-function value route.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodBoundaryValue
      hvalue)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem gives the canonical
eta/zeta bridge through the direct eta L-function value route.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodTwoBoundaryValue
      hvalue)

/--
The canonical eta/zeta value formula is equivalent to the source-shaped
`ZMod 2` checked-boundary-value theorem.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalRiemannZetaEtaValueFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  constructor
  · intro hetaValueFormula
    exact
      (openUnitIntervalDirichletEtaLFunctionValueFormula_iff_zmodTwoBoundaryValue).1
        (openUnitIntervalDirichletEtaLFunctionValueFormula_of_etaValueFormula
          hetaValueFormula)
  · exact openUnitIntervalRiemannZetaEtaValueFormula_of_zmodTwoBoundaryValue

/--
The canonical-value eta formula implies the all-limits eta formula used by the
existing zero-free route.
-/
theorem openUnitIntervalRiemannZetaEtaFormula_of_valueFormula
    (hetaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula) :
    OpenUnitIntervalRiemannZetaEtaFormula := by
  intro x eta hx_pos hx_lt_one hetaLimit
  rw [dirichletEtaAlternatingLimit_eq_value hx_pos hetaLimit]
  exact hetaValueFormula x hx_pos hx_lt_one

/--
The all-limits eta formula recovers the canonical eta-value formula by
specializing to the checked canonical alternating-series value.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_etaFormula
    (hetaFormula : OpenUnitIntervalRiemannZetaEtaFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula := by
  intro x hx_pos hx_lt_one
  exact hetaFormula x (dirichletEtaAlternatingValue x)
    hx_pos hx_lt_one (dirichletEtaAlternatingValue_spec hx_pos)

/--
The canonical-value eta formula and the all-limits eta formula are equivalent.

This closes a small normalization gap in the zero-counting/eta route: the
zero-free argument may use the all-limits formulation, while the ZMod boundary
work naturally targets the canonical alternating value.
-/
theorem openUnitIntervalRiemannZetaEtaFormula_iff_valueFormula :
    OpenUnitIntervalRiemannZetaEtaFormula <->
      OpenUnitIntervalRiemannZetaEtaValueFormula :=
  ⟨openUnitIntervalRiemannZetaEtaValueFormula_of_etaFormula,
    openUnitIntervalRiemannZetaEtaFormula_of_valueFormula⟩

/--
The all-limits eta formula is equivalent to the source-shaped `ZMod 2`
checked-boundary-value theorem.
-/
theorem openUnitIntervalRiemannZetaEtaFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalRiemannZetaEtaFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  constructor
  · intro hetaFormula
    exact
      (openUnitIntervalRiemannZetaEtaValueFormula_iff_zmodTwoBoundaryValue).1
        (openUnitIntervalRiemannZetaEtaValueFormula_of_etaFormula
          hetaFormula)
  · intro hvalue
    exact openUnitIntervalRiemannZetaEtaFormula_of_valueFormula
      ((openUnitIntervalRiemannZetaEtaValueFormula_iff_zmodTwoBoundaryValue).2
        hvalue)

/--
The eta analytic-continuation formula on `(0, 1)` implies the negative
real-part zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_etaFormula
    (hetaFormula : OpenUnitIntervalRiemannZetaEtaFormula) :
    OpenUnitIntervalRiemannZetaReNegative := by
  intro x hx_pos hx_lt_one
  let h_exists := exists_dirichletEtaAlternatingLimit_of_pos hx_pos
  let eta := Classical.choose h_exists
  have hetaLimit : DirichletEtaAlternatingLimit x eta :=
    Classical.choose_spec h_exists
  have heta_pos : 0 < eta :=
    dirichletEtaAlternatingLimit_pos_of_pos hx_pos hetaLimit
  have hcoef_neg : 1 - (2 : Real) ^ (1 - x) < 0 := by
    have hpow : 1 < (2 : Real) ^ (1 - x) :=
      Real.one_lt_rpow one_lt_two (by linarith)
    linarith
  have hformula := hetaFormula x eta hx_pos hx_lt_one hetaLimit
  have hprod_pos :
      0 < (1 - (2 : Real) ^ (1 - x)) *
        (riemannZeta (x : Complex)).re := by
    simpa [hformula] using heta_pos
  exact neg_of_mul_pos_right hprod_pos hcoef_neg.le

/--
The canonical-value eta formula on `(0, 1)` implies the negative real-part zeta
target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (hetaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaFormula
    (openUnitIntervalRiemannZetaEtaFormula_of_valueFormula
      hetaValueFormula)

/--
The split eta L-function route supplies the negative real-part zeta target on
`(0, 1)` once the alternating-value identity and right-half-plane multiplier
identity are available.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_etaLFunctionValue_and_rightHalfPlane
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue_and_rightHalfPlane
      hetaValue hetaRight)

/--
The remaining alternating-value-to-L-function identification supplies the
negative real-part zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_etaLFunctionValue
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaLFunctionValue_and_rightHalfPlane
    hetaValue dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/--
The Abel-boundary eta theorem supplies the negative real-part zeta target on
`(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_etaAbelBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_etaAbelBoundary habel)

/--
The exponential-zeta Abel-boundary eta theorem supplies the negative real-part
zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_etaExpZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_etaExpZetaBoundary hexp)

/--
The reusable nonzero additive-character Abel theorem supplies the negative
real-part zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaExpZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The checked-boundary-value additive-character theorem supplies the negative
real-part zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_zmodBoundaryValue hvalue)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem supplies the
negative real-part zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_zmodTwoBoundaryValue hvalue)

/-- A negative real part on `(0, 1)` implies nonvanishing there. -/
theorem openUnitIntervalRiemannZetaNonzero_of_reNegative
    (hneg : OpenUnitIntervalRiemannZetaReNegative) :
    OpenUnitIntervalRiemannZetaNonzero := by
  intro x hx_pos hx_lt_one hz
  have hre_zero : (riemannZeta (x : Complex)).re = 0 := by
    rw [hz]
    simp
  have hre_neg := hneg x hx_pos hx_lt_one
  rw [hre_zero] at hre_neg
  exact (lt_irrefl (0 : Real)) hre_neg

/-- The eta formula on `(0, 1)` implies zeta is nonzero there. -/
theorem openUnitIntervalRiemannZetaNonzero_of_etaFormula
    (hetaFormula : OpenUnitIntervalRiemannZetaEtaFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaFormula hetaFormula)

/-- The canonical eta formula on `(0, 1)` implies zeta is nonzero there. -/
theorem openUnitIntervalRiemannZetaNonzero_of_etaValueFormula
    (hetaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
      hetaValueFormula)

/-- The split eta L-function route implies zeta is nonzero on `(0, 1)`. -/
theorem openUnitIntervalRiemannZetaNonzero_of_etaLFunctionValue_and_rightHalfPlane
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaLFunctionValue_and_rightHalfPlane
      hetaValue hetaRight)

/--
The remaining alternating-value-to-L-function identification implies zeta is
nonzero on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaNonzero_of_etaLFunctionValue
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_etaLFunctionValue_and_rightHalfPlane
    hetaValue dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/-- The Abel-boundary eta theorem implies zeta is nonzero on `(0, 1)`. -/
theorem openUnitIntervalRiemannZetaNonzero_of_etaAbelBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaAbelBoundary habel)

/-- The exponential-zeta Abel-boundary eta theorem implies zeta is nonzero on `(0, 1)`. -/
theorem openUnitIntervalRiemannZetaNonzero_of_etaExpZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaExpZetaBoundary hexp)

/--
The reusable nonzero additive-character Abel theorem implies zeta is nonzero
on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaNonzero_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_etaExpZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The checked-boundary-value additive-character theorem implies zeta is nonzero
on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaNonzero_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_zmodBoundaryValue hvalue)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem implies zeta is
nonzero on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaNonzero_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_zmodTwoBoundaryValue hvalue)

/--
The isolated regularized Hurwitz-tail theorem supplies the eta
exponential-zeta Abel-boundary theorem.
-/
theorem openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodTwoBoundaryValue
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the eta L-function
Abel-boundary theorem.
-/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the eta Hurwitz
Abel-boundary theorem.
-/
theorem openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_lFunctionBoundary
    (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the complex
conditional-sum eta boundary theorem.
-/
theorem openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula :=
  openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_abelBoundary
    (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the canonical
real-valued eta boundary theorem.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_of_complexConditionalSum
    (openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the eta conditional-sum
boundary theorem.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula :=
  openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_valueFormula
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the canonical eta/zeta
value formula on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaEtaValueFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalRiemannZetaEtaValueFormula :=
  openUnitIntervalRiemannZetaEtaValueFormula_of_etaLFunctionValue
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the all-limits eta/zeta
formula on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaEtaFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalRiemannZetaEtaFormula :=
  openUnitIntervalRiemannZetaEtaFormula_of_valueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies the negative-real-part
zeta target on `(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaReNegative_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalRiemannZetaReNegative :=
  openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
    (openUnitIntervalRiemannZetaEtaValueFormula_of_regularizedTailHurwitz
      htail)

/--
The isolated regularized Hurwitz-tail theorem supplies zeta nonvanishing on
`(0, 1)`.
-/
theorem openUnitIntervalRiemannZetaNonzero_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalRiemannZetaNonzero :=
  openUnitIntervalRiemannZetaNonzero_of_reNegative
    (openUnitIntervalRiemannZetaReNegative_of_regularizedTailHurwitz htail)

/--
The real-variable nonzero theorem on `(0, 1)` supplies the complex real-axis
zero-free target.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaNonzero
    (hnonzero : OpenUnitIntervalRiemannZetaNonzero) :
    OpenUnitIntervalRealAxisZetaZeroFree := by
  intro s hz haxis hre_pos hre_lt_one
  let x : Real := s.re
  have hs_eq : s = (x : Complex) :=
    Complex.ext (by change s.re = x; rfl) (by change s.im = 0; exact haxis)
  exact hnonzero x (by simpa [x] using hre_pos)
    (by simpa [x] using hre_lt_one) (by simpa [hs_eq, IsZetaZero] using hz)

/--
The classical negative-real-part theorem on `(0, 1)` supplies the complex
real-axis zero-free target.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (hneg : OpenUnitIntervalRiemannZetaReNegative) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaNonzero
    (openUnitIntervalRiemannZetaNonzero_of_reNegative hneg)

/-- The eta formula on `(0, 1)` supplies the complex real-axis zero-free target. -/
theorem openUnitIntervalRealAxisZetaZeroFree_of_etaFormula
    (hetaFormula : OpenUnitIntervalRiemannZetaEtaFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaFormula hetaFormula)

/-- The canonical eta formula on `(0, 1)` supplies the real-axis zero-free target. -/
theorem openUnitIntervalRealAxisZetaZeroFree_of_etaValueFormula
    (hetaValueFormula : OpenUnitIntervalRiemannZetaEtaValueFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaValueFormula
      hetaValueFormula)

/--
The split eta L-function route supplies the remaining open-unit-interval
real-axis zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_etaLFunctionValue_and_rightHalfPlane
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaLFunctionValue_and_rightHalfPlane
      hetaValue hetaRight)

/--
The remaining alternating-value-to-L-function identification supplies the
open-unit-interval real-axis zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_etaLFunctionValue
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_etaLFunctionValue_and_rightHalfPlane
    hetaValue dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/--
The Abel-boundary eta theorem supplies the open-unit-interval real-axis
zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_etaAbelBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaAbelBoundary habel)

/--
The exponential-zeta Abel-boundary eta theorem supplies the open-unit-interval
real-axis zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_etaExpZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_etaExpZetaBoundary hexp)

/--
The reusable nonzero additive-character Abel theorem supplies the
open-unit-interval real-axis zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_etaExpZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The checked-boundary-value additive-character theorem supplies the
open-unit-interval real-axis zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_zmodBoundaryValue hvalue)

/--
The isolated regularized Hurwitz-tail theorem supplies open-unit-interval
real-axis zero-freeness.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_zmodBoundaryValue
    (zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      htail)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem supplies the
open-unit-interval real-axis zero-free input.
-/
theorem openUnitIntervalRealAxisZetaZeroFree_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_openUnitIntervalRiemannZetaReNegative
    (openUnitIntervalRiemannZetaReNegative_of_zmodTwoBoundaryValue hvalue)

/-- Zeta has no real-axis zero with real part in the open unit interval. -/
theorem openUnitIntervalRealAxisZetaZeroFree :
    OpenUnitIntervalRealAxisZetaZeroFree :=
  openUnitIntervalRealAxisZetaZeroFree_of_zmodTwoBoundaryValue
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedHalfTailHurwitz
      zmodTwoRegularizedHalfTailHurwitzFormula)
end

end ComplexCompactExhaustion

end RiemannHypothesisProject
