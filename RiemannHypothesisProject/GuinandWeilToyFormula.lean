import Mathlib.Topology.Basic
import RiemannHypothesisProject.GuinandWeilSourceFormula
import RiemannHypothesisProject.ToyPositivity

/-!
# Toy Guinand-Weil formula model

This file gives a fully checked zero formula model for the Guinand-Weil
componentwise normalization path.  It proves no zeta theorem; its purpose is to
exercise the exact source-zero/prime/pole/gamma-to-project formula route with
all sides simplified to zero.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

noncomputable section

/-- The zero Riemann-Weil zero side. -/
def guinandWeilToyZeroSide : SchwartzRiemannWeilZeroSide where
  weight := fun _ _ => 0
  summable_weight := fun _ => summable_zero

namespace GuinandWeilToyFormula

/-- The toy zero side has zero global value for every test function. -/
theorem zeroSide_eq_zero (f : SchwartzLineTestFunction) :
    guinandWeilToyZeroSide.zeroSide f = 0 := by
  simp [guinandWeilToyZeroSide, SchwartzRiemannWeilZeroSide.zeroSide,
    SchwartzRiemannWeilZeroSide.toGlobalZetaZeroSide,
    GlobalZetaZeroSide.zeroSide]

/-- Source side data with zero zero, prime, pole, and gamma sides. -/
def sourceSideData : GuinandWeilFormulaSideData where
  sourceZeroSide := fun _ => 0
  sourcePrimeSide := fun _ => 0
  sourcePoleSide := fun _ => 0
  sourceGammaSide := fun _ => 0

/-- Source formula data with zero zero, prime, pole, and gamma sides. -/
def sourceData : GuinandWeilFormulaIdentityData where
  sideData := sourceSideData
  sourceExplicitFormula := by
    intro f
    simp [sourceSideData, GuinandWeilFormulaSideData.sourceResidualSide]

/-- The toy source residual side is identically zero. -/
theorem sourceResidualSide_eq_zero (f : SchwartzLineTestFunction) :
    sourceData.sideData.sourceResidualSide f = 0 := by
  simp [sourceData, sourceSideData, GuinandWeilFormulaSideData.sourceResidualSide]

/-- Zero-side normalization for the toy source formula. -/
def normalizationBridge :
    GuinandWeilNormalizationBridge sourceData guinandWeilToyZeroSide where
  zeroSide_eq_sourceZeroSide := by
    intro f
    simp [sourceData, sourceSideData, zeroSide_eq_zero f]

/--
Componentwise normalization for the toy source formula, with every project side
equal to its zero source counterpart.
-/
def componentwiseNormalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge
      sourceData guinandWeilToyZeroSide where
  sideData :=
    { primeSide := fun _ => 0
      poleSide := fun _ => 0
      gammaSide := fun _ => 0 }
  zeroSide_eq_sourceZeroSide := by
    intro f
    simp [sourceData, sourceSideData, zeroSide_eq_zero f]
  primeSide_eq_sourcePrimeSide := by
    intro f
    simp [sourceData, sourceSideData]
  poleSide_eq_sourcePoleSide := by
    intro f
    simp [sourceData, sourceSideData]
  gammaSide_eq_sourceGammaSide := by
    intro f
    simp [sourceData, sourceSideData]

/-- The checked project formula identity produced by the toy componentwise bridge. -/
def formulaData :
    SchwartzRiemannWeilFormulaIdentityData guinandWeilToyZeroSide :=
  componentwiseNormalizationBridge.toFormulaIdentityData

/-- The toy project residual side is identically zero. -/
theorem formulaData_residualSide_eq_zero (f : SchwartzLineTestFunction) :
    formulaData.sideData.residualSide f = 0 := by
  calc
    formulaData.sideData.residualSide f =
        sourceData.sideData.sourceResidualSide f := by
      simpa [formulaData] using
        componentwiseNormalizationBridge.toFormulaIdentityData_residualSide f
    _ = 0 := sourceResidualSide_eq_zero f

/-- The toy componentwise Guinand-Weil formula is the identity `0 = 0`. -/
theorem explicitFormula (f : SchwartzLineTestFunction) :
    guinandWeilToyZeroSide.zeroSide f =
      formulaData.sideData.residualSide f := by
  exact formulaData.explicitFormula f

/--
Finite zero-window sums for the toy zero side converge to the zero formula
residual side.
-/
theorem tendsto_windowZeroSide_residualSide
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => guinandWeilToyZeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (formulaData.sideData.residualSide f)) :=
  formulaData.tendsto_windowZeroSide_residualSide exhaustion f

/--
Single-prime component toy source data.

For an arbitrary project zero side, the source zero side and source prime side
are both the zero-side value, while pole and gamma vanish.  This is still a toy
formula, but unlike the all-zero model it exercises one nonzero component in
the componentwise normalization path.
-/
def singlePrimeSourceSideData
    (zeroSide : SchwartzRiemannWeilZeroSide) : GuinandWeilFormulaSideData where
  sourceZeroSide := zeroSide.zeroSide
  sourcePrimeSide := zeroSide.zeroSide
  sourcePoleSide := fun _ => 0
  sourceGammaSide := fun _ => 0

/-- Source formula data for the single-prime component toy model. -/
def singlePrimeSourceData
    (zeroSide : SchwartzRiemannWeilZeroSide) :
    GuinandWeilFormulaIdentityData where
  sideData := singlePrimeSourceSideData zeroSide
  sourceExplicitFormula := by
    intro f
    simp [singlePrimeSourceSideData,
      GuinandWeilFormulaSideData.sourceResidualSide]

/--
Componentwise normalization for the single-prime toy formula.

The project prime side is the chosen zero-side value, while project pole and
gamma sides vanish.
-/
def singlePrimeComponentwiseNormalizationBridge
    (zeroSide : SchwartzRiemannWeilZeroSide) :
    GuinandWeilComponentwiseNormalizationBridge
      (singlePrimeSourceData zeroSide) zeroSide where
  sideData :=
    { primeSide := zeroSide.zeroSide
      poleSide := fun _ => 0
      gammaSide := fun _ => 0 }
  zeroSide_eq_sourceZeroSide := by
    intro f
    rfl
  primeSide_eq_sourcePrimeSide := by
    intro f
    rfl
  poleSide_eq_sourcePoleSide := by
    intro f
    rfl
  gammaSide_eq_sourceGammaSide := by
    intro f
    rfl

/-- Project formula identity data for the single-prime component toy model. -/
def singlePrimeFormulaData
    (zeroSide : SchwartzRiemannWeilZeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  (singlePrimeComponentwiseNormalizationBridge zeroSide).toFormulaIdentityData

/-- The single-prime model residual side is the chosen project zero side. -/
theorem singlePrimeFormulaData_residualSide_eq_zeroSide
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (f : SchwartzLineTestFunction) :
    (singlePrimeFormulaData zeroSide).sideData.residualSide f =
      zeroSide.zeroSide f := by
  calc
    (singlePrimeFormulaData zeroSide).sideData.residualSide f =
        (singlePrimeSourceData zeroSide).sideData.sourceResidualSide f := by
      simpa [singlePrimeFormulaData] using
        GuinandWeilComponentwiseNormalizationBridge.toFormulaIdentityData_residualSide
          (singlePrimeComponentwiseNormalizationBridge zeroSide) f
    _ = zeroSide.zeroSide f := by
      simp [singlePrimeSourceData, singlePrimeSourceSideData,
        GuinandWeilFormulaSideData.sourceResidualSide]

/--
The single-prime componentwise Guinand-Weil toy formula is the identity
`zeroSide = zeroSide + 0 + 0`.
-/
theorem singlePrimeExplicitFormula
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      (singlePrimeFormulaData zeroSide).sideData.residualSide f :=
  (singlePrimeFormulaData zeroSide).explicitFormula f

/--
Finite zero-window sums converge to the single-prime toy residual side for any
abstract zero side.
-/
theorem singlePrime_tendsto_windowZeroSide_residualSide
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => zeroSide.windowZeroSide exhaustion n f)
      atTop (nhds ((singlePrimeFormulaData zeroSide).sideData.residualSide f)) :=
  (singlePrimeFormulaData zeroSide).tendsto_windowZeroSide_residualSide
    exhaustion f

/--
For the single-prime toy formula, residual nonnegativity on an admissible class
is exactly nonnegativity of the chosen abstract zero side on that class.
-/
theorem singlePrime_residual_nonneg_on_admissible
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (zeroSide_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= zeroSide.zeroSide f) :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        0 <= (singlePrimeFormulaData zeroSide).sideData.residualSide f := by
  intro f hf
  rw [singlePrimeFormulaData_residualSide_eq_zeroSide]
  exact zeroSide_nonneg_on_admissible f hf

/--
If the abstract zero side of the single-prime toy formula is identified with a
finite Gram quadratic form, then the project formula residual is that same
finite Gram form.

The residual-identification hypothesis is intentionally explicit: in the real
Guinand-Weil problem this is where the formula-side calculation lives.
-/
theorem singlePrimeFormulaData_residualSide_eq_finiteGram
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (feature : Feature -> Index -> Real)
    (zeroSide_eq_finiteGram :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f = finiteGramQuadraticForm feature (coordinate f))
    (f : SchwartzLineTestFunction) :
    (singlePrimeFormulaData zeroSide).sideData.residualSide f =
      finiteGramQuadraticForm feature (coordinate f) := by
  rw [singlePrimeFormulaData_residualSide_eq_zeroSide,
    zeroSide_eq_finiteGram f]

/--
Finite Gram positivity gives support-restricted formula residual nonnegativity
for the single-prime component toy model once the residual-identification
equation is proved on the admissible class.
-/
theorem singlePrime_finiteGram_residual_nonneg_on_admissible
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (zeroSide_eq_finiteGram_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          zeroSide.zeroSide f =
            finiteGramQuadraticForm feature (coordinate f)) :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        0 <= (singlePrimeFormulaData zeroSide).sideData.residualSide f := by
  intro f hf
  rw [singlePrimeFormulaData_residualSide_eq_zeroSide,
    zeroSide_eq_finiteGram_on_admissible f hf]
  exact finiteGramQuadraticForm_nonneg feature (coordinate f)

/--
Single-prime finite-Gram support-restricted positivity package.

This couples the componentwise formula toy with the finite Gram positivity
model: after the admissible residual-identification equation is supplied, Lean
proves the support-restricted residual positivity input needed by the Li bridge.
-/
noncomputable def singlePrimeFiniteGramSupportRestrictedFormulaResidualPositivityData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> FiniteTestFunction Index)
    (feature : Feature -> Index -> Real)
    (admissible : SchwartzLineTestFunction -> Prop)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        (singlePrimeFormulaData zeroSide) admissible liData)
    (zeroSide_eq_finiteGram_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          zeroSide.zeroSide f =
            finiteGramQuadraticForm feature (coordinate f)) :
    SupportRestrictedFormulaResidualPositivityData
      (singlePrimeFormulaData zeroSide) :=
  bridge.toSupportRestrictedFormulaResidualPositivityData
    (singlePrime_finiteGram_residual_nonneg_on_admissible
      zeroSide coordinate feature admissible
      zeroSide_eq_finiteGram_on_admissible)

/--
A finite-Gram component term for the three-component toy formula below.

The component index is `Fin 3`, interpreted as prime, pole, and gamma in that
order.  The use of a uniform finite index/feature type keeps the model small
while still checking the three separate residual components.
-/
noncomputable def threeComponentFiniteGramTerm
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (component : Fin 3)
    (f : SchwartzLineTestFunction) : Real :=
  finiteGramQuadraticForm (feature component) (coordinate f component)

/--
Source sides for a three-component finite-Gram Guinand-Weil toy formula.

The source zero side is the sum of the prime, pole, and gamma finite-Gram
components, so the source explicit formula is definitional.  The real theorem
must replace these toy finite-Gram identities with the actual source-side
prime, pole, and gamma calculations.
-/
noncomputable def threeComponentFiniteGramSourceSideData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real) :
    GuinandWeilFormulaSideData where
  sourceZeroSide := fun f =>
    threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
      threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f
  sourcePrimeSide := fun f =>
    threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f
  sourcePoleSide := fun f =>
    threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f
  sourceGammaSide := fun f =>
    threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f

/-- Source formula data for the three-component finite-Gram toy formula. -/
noncomputable def threeComponentFiniteGramSourceData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real) :
    GuinandWeilFormulaIdentityData where
  sideData := threeComponentFiniteGramSourceSideData coordinate feature
  sourceExplicitFormula := by
    intro f
    rfl

/--
Componentwise normalization for the three-component finite-Gram toy formula.

The only nontrivial input is the zero-side comparison: the project zero side
must equal the source sum of the three finite-Gram components.  Prime, pole,
and gamma sides are then supplied component by component.
-/
noncomputable def threeComponentFiniteGramComponentwiseNormalizationBridge
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f) :
    GuinandWeilComponentwiseNormalizationBridge
      (threeComponentFiniteGramSourceData coordinate feature) zeroSide where
  sideData :=
    { primeSide := fun f =>
        threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f
      poleSide := fun f =>
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f
      gammaSide := fun f =>
        threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f }
  zeroSide_eq_sourceZeroSide := by
    intro f
    exact zeroSide_eq_threeComponentSource f
  primeSide_eq_sourcePrimeSide := by
    intro f
    rfl
  poleSide_eq_sourcePoleSide := by
    intro f
    rfl
  gammaSide_eq_sourceGammaSide := by
    intro f
    rfl

/-- Project formula data for the three-component finite-Gram toy formula. -/
noncomputable def threeComponentFiniteGramFormulaData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  (threeComponentFiniteGramComponentwiseNormalizationBridge
    zeroSide coordinate feature zeroSide_eq_threeComponentSource)
      |>.toFormulaIdentityData

/--
The three-component finite-Gram toy formula viewed as a truncation/limit
formula with constant truncations.

This exercises the same Lean route as a future real Guinand-Weil proof from
finite cutoffs: truncated zero, prime, pole, and gamma identities plus
componentwise convergence to the source sides.
-/
noncomputable def threeComponentFiniteGramTruncatedLimitData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real) :
    GuinandWeilTruncatedFormulaLimitData
      (threeComponentFiniteGramSourceSideData coordinate feature) where
  truncatedZeroSide := fun _ f =>
    (threeComponentFiniteGramSourceSideData coordinate feature).sourceZeroSide f
  truncatedPrimeSide := fun _ f =>
    (threeComponentFiniteGramSourceSideData coordinate feature).sourcePrimeSide f
  truncatedPoleSide := fun _ f =>
    (threeComponentFiniteGramSourceSideData coordinate feature).sourcePoleSide f
  truncatedGammaSide := fun _ f =>
    (threeComponentFiniteGramSourceSideData coordinate feature).sourceGammaSide f
  truncatedExplicitFormula := by
    intro n f
    rfl
  tendsto_sourceZeroSide := by
    intro f
    exact tendsto_const_nhds
  tendsto_sourcePrimeSide := by
    intro f
    exact tendsto_const_nhds
  tendsto_sourcePoleSide := by
    intro f
    exact tendsto_const_nhds
  tendsto_sourceGammaSide := by
    intro f
    exact tendsto_const_nhds

/--
The three-component finite-Gram toy formula routed through the
truncation/limit project package.
-/
noncomputable def threeComponentFiniteGramTruncatedLimitPackage
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f) :
    GuinandWeilComponentwiseTruncatedLimitPackage zeroSide where
  sourceSideData := threeComponentFiniteGramSourceSideData coordinate feature
  limitData := threeComponentFiniteGramTruncatedLimitData coordinate feature
  normalizationBridge :=
    threeComponentFiniteGramComponentwiseNormalizationBridge
      zeroSide coordinate feature zeroSide_eq_threeComponentSource

/--
The truncation/limit package proves the same three-component project formula
identity as the direct toy package.
-/
theorem threeComponentFiniteGramTruncatedLimit_explicitFormula
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      (GuinandWeilComponentwiseTruncatedLimitPackage.formulaData
        (threeComponentFiniteGramTruncatedLimitPackage
          zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f :=
  (threeComponentFiniteGramTruncatedLimitPackage
    zeroSide coordinate feature zeroSide_eq_threeComponentSource).explicitFormula f

/--
The residual side delivered by the truncation/limit package is the sum of the
three finite-Gram source components.
-/
theorem threeComponentFiniteGramTruncatedLimit_residualSide_eq
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    (GuinandWeilComponentwiseTruncatedLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
      threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := by
  calc
    (GuinandWeilComponentwiseTruncatedLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
        (threeComponentFiniteGramSourceSideData coordinate feature).sourceResidualSide f := by
          exact
            GuinandWeilComponentwiseTruncatedLimitPackage.formulaData_residualSide_eq_sourceResidualSide
                (threeComponentFiniteGramTruncatedLimitPackage
                  zeroSide coordinate feature zeroSide_eq_threeComponentSource) f
    _ = threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := rfl

/--
The three-component finite-Gram toy formula as a vanishing-error truncation.

The error term is identically zero here.  The point is to verify the same
package shape that a contour-shift proof will use when the remaining contour
or truncation contribution is merely proved to tend to zero.
-/
noncomputable def threeComponentFiniteGramTruncatedErrorLimitData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real) :
    GuinandWeilTruncatedFormulaErrorLimitData
      (threeComponentFiniteGramSourceSideData coordinate feature) :=
  GuinandWeilTruncatedFormulaErrorLimitData.ofTruncatedFormulaLimitData
    (threeComponentFiniteGramTruncatedLimitData coordinate feature)

/--
The three-component finite-Gram toy formula routed through the vanishing-error
truncation/limit project package.
-/
noncomputable def threeComponentFiniteGramTruncatedErrorLimitPackage
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f) :
    GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide where
  sourceSideData := threeComponentFiniteGramSourceSideData coordinate feature
  errorLimitData :=
    threeComponentFiniteGramTruncatedErrorLimitData coordinate feature
  normalizationBridge :=
    { sideData :=
        { primeSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f
          poleSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f
          gammaSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f }
      zeroSide_eq_sourceZeroSide := by
        intro f
        exact zeroSide_eq_threeComponentSource f
      primeSide_eq_sourcePrimeSide := by
        intro f
        rfl
      poleSide_eq_sourcePoleSide := by
        intro f
        rfl
      gammaSide_eq_sourceGammaSide := by
        intro f
        rfl }

/--
The vanishing-error truncation package proves the three-component project
formula identity.
-/
theorem threeComponentFiniteGramTruncatedErrorLimit_explicitFormula
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      (GuinandWeilComponentwiseTruncatedErrorLimitPackage.formulaData
        (threeComponentFiniteGramTruncatedErrorLimitPackage
          zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f :=
  (threeComponentFiniteGramTruncatedErrorLimitPackage
    zeroSide coordinate feature zeroSide_eq_threeComponentSource).explicitFormula f

/--
The residual side delivered by the vanishing-error package is the same
three-component finite-Gram source sum.
-/
theorem threeComponentFiniteGramTruncatedErrorLimit_residualSide_eq
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    (GuinandWeilComponentwiseTruncatedErrorLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedErrorLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
      threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := by
  calc
    (GuinandWeilComponentwiseTruncatedErrorLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedErrorLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
        (threeComponentFiniteGramSourceSideData coordinate feature).sourceResidualSide f := by
          exact
            GuinandWeilComponentwiseTruncatedErrorLimitPackage.formulaData_residualSide_eq_sourceResidualSide
                (threeComponentFiniteGramTruncatedErrorLimitPackage
                  zeroSide coordinate feature zeroSide_eq_threeComponentSource) f
    _ = threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := rfl

/--
The three-component finite-Gram toy formula as an absolute-error-envelope
truncation.

The envelope is `|0|` in this toy model.  In the real contour proof this is
where one supplies a nontrivial explicit majorant for the remaining error and
then proves that majorant tends to zero.
-/
noncomputable def threeComponentFiniteGramTruncatedErrorBoundLimitData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real) :
    GuinandWeilTruncatedFormulaErrorBoundLimitData
      (threeComponentFiniteGramSourceSideData coordinate feature) :=
  GuinandWeilTruncatedFormulaErrorBoundLimitData.ofErrorLimitData
    (threeComponentFiniteGramTruncatedErrorLimitData coordinate feature)

/--
The three-component finite-Gram toy formula routed through the absolute
error-envelope truncation package.
-/
noncomputable def threeComponentFiniteGramTruncatedErrorBoundLimitPackage
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f) :
    GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide where
  sourceSideData := threeComponentFiniteGramSourceSideData coordinate feature
  boundLimitData :=
    threeComponentFiniteGramTruncatedErrorBoundLimitData coordinate feature
  normalizationBridge :=
    { sideData :=
        { primeSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f
          poleSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f
          gammaSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f }
      zeroSide_eq_sourceZeroSide := by
        intro f
        exact zeroSide_eq_threeComponentSource f
      primeSide_eq_sourcePrimeSide := by
        intro f
        rfl
      poleSide_eq_sourcePoleSide := by
        intro f
        rfl
      gammaSide_eq_sourceGammaSide := by
        intro f
        rfl }

/--
The absolute-error-envelope package proves the three-component project formula
identity.
-/
theorem threeComponentFiniteGramTruncatedErrorBoundLimit_explicitFormula
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      (GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage.formulaData
        (threeComponentFiniteGramTruncatedErrorBoundLimitPackage
          zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f :=
  (threeComponentFiniteGramTruncatedErrorBoundLimitPackage
    zeroSide coordinate feature zeroSide_eq_threeComponentSource).explicitFormula f

/--
The residual side delivered by the absolute-error-envelope package is the same
three-component finite-Gram source sum.
-/
theorem threeComponentFiniteGramTruncatedErrorBoundLimit_residualSide_eq
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    (GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedErrorBoundLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
      threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := by
  calc
    (GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedErrorBoundLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
        (threeComponentFiniteGramSourceSideData coordinate feature).sourceResidualSide f := by
          exact
            GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage.formulaData_residualSide_eq_sourceResidualSide
                (threeComponentFiniteGramTruncatedErrorBoundLimitPackage
                  zeroSide coordinate feature zeroSide_eq_threeComponentSource) f
    _ = threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := rfl

/--
The three-component finite-Gram toy formula as an eventual absolute-error
envelope truncation.

This is obtained from the pointwise envelope package, but it checks the exact
weaker target that real explicit formula estimates often satisfy only after a
cutoff.
-/
noncomputable def threeComponentFiniteGramTruncatedEventualErrorBoundLimitData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real) :
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData
      (threeComponentFiniteGramSourceSideData coordinate feature) :=
  GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.ofErrorBoundLimitData
    (threeComponentFiniteGramTruncatedErrorBoundLimitData coordinate feature)

/--
The three-component finite-Gram toy formula routed through the eventual
absolute-error-envelope truncation package.
-/
noncomputable def threeComponentFiniteGramTruncatedEventualErrorBoundLimitPackage
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f) :
    GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide where
  sourceSideData := threeComponentFiniteGramSourceSideData coordinate feature
  eventualBoundLimitData :=
    threeComponentFiniteGramTruncatedEventualErrorBoundLimitData coordinate feature
  normalizationBridge :=
    { sideData :=
        { primeSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f
          poleSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f
          gammaSide := fun f =>
            threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f }
      zeroSide_eq_sourceZeroSide := by
        intro f
        exact zeroSide_eq_threeComponentSource f
      primeSide_eq_sourcePrimeSide := by
        intro f
        rfl
      poleSide_eq_sourcePoleSide := by
        intro f
        rfl
      gammaSide_eq_sourceGammaSide := by
        intro f
        rfl }

/--
The eventual absolute-error-envelope package proves the three-component
project formula identity.
-/
theorem threeComponentFiniteGramTruncatedEventualErrorBoundLimit_explicitFormula
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      (GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage.formulaData
        (threeComponentFiniteGramTruncatedEventualErrorBoundLimitPackage
          zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f :=
  (threeComponentFiniteGramTruncatedEventualErrorBoundLimitPackage
    zeroSide coordinate feature zeroSide_eq_threeComponentSource).explicitFormula f

/--
The residual side delivered by the eventual-envelope package is the same
three-component finite-Gram source sum.
-/
theorem threeComponentFiniteGramTruncatedEventualErrorBoundLimit_residualSide_eq
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    (GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedEventualErrorBoundLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
      threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := by
  calc
    (GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage.formulaData
      (threeComponentFiniteGramTruncatedEventualErrorBoundLimitPackage
        zeroSide coordinate feature zeroSide_eq_threeComponentSource)).sideData.residualSide f =
        (threeComponentFiniteGramSourceSideData coordinate feature).sourceResidualSide f := by
          exact
            GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage.formulaData_residualSide_eq_sourceResidualSide
                (threeComponentFiniteGramTruncatedEventualErrorBoundLimitPackage
                  zeroSide coordinate feature zeroSide_eq_threeComponentSource) f
    _ = threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := rfl

/--
The three-component toy project residual is the sum of its prime, pole, and
gamma finite-Gram components.
-/
theorem threeComponentFiniteGramFormulaData_residualSide_eq
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    (threeComponentFiniteGramFormulaData
      zeroSide coordinate feature zeroSide_eq_threeComponentSource).sideData.residualSide f =
      threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := by
  calc
    (threeComponentFiniteGramFormulaData
      zeroSide coordinate feature zeroSide_eq_threeComponentSource).sideData.residualSide f =
        (threeComponentFiniteGramSourceData coordinate feature).sideData.sourceResidualSide f := by
          simpa [threeComponentFiniteGramFormulaData] using
            GuinandWeilComponentwiseNormalizationBridge.toFormulaIdentityData_residualSide
              (threeComponentFiniteGramComponentwiseNormalizationBridge
                zeroSide coordinate feature zeroSide_eq_threeComponentSource) f
    _ = threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
        threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
          threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f := rfl

/--
The three-component finite-Gram toy residual is nonnegative on every test
function.  This is the componentwise positivity shape expected from separate
prime, pole, and gamma residual identifications.
-/
theorem threeComponentFiniteGram_residual_nonneg
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (f : SchwartzLineTestFunction) :
    0 <=
      (threeComponentFiniteGramFormulaData
        zeroSide coordinate feature zeroSide_eq_threeComponentSource).sideData.residualSide f := by
  rw [threeComponentFiniteGramFormulaData_residualSide_eq
    zeroSide coordinate feature zeroSide_eq_threeComponentSource f]
  exact add_nonneg
    (add_nonneg
      (finiteGramQuadraticForm_nonneg (feature (0 : Fin 3))
        (coordinate f (0 : Fin 3)))
      (finiteGramQuadraticForm_nonneg (feature (1 : Fin 3))
        (coordinate f (1 : Fin 3))))
    (finiteGramQuadraticForm_nonneg (feature (2 : Fin 3))
      (coordinate f (2 : Fin 3)))

/--
Support-restricted residual positivity for the three-component finite-Gram
toy formula.

The RH-level Li bridge remains an explicit input; this constructor checks only
the formula-side positivity proof from separate finite-Gram prime, pole, and
gamma components.
-/
noncomputable def threeComponentFiniteGramSupportRestrictedFormulaResidualPositivityData
    {Index Feature : Type} [Fintype Index] [Fintype Feature]
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (coordinate : SchwartzLineTestFunction -> Fin 3 -> FiniteTestFunction Index)
    (feature : Fin 3 -> Feature -> Index -> Real)
    (zeroSide_eq_threeComponentSource :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f =
          threeComponentFiniteGramTerm coordinate feature (0 : Fin 3) f +
            threeComponentFiniteGramTerm coordinate feature (1 : Fin 3) f +
              threeComponentFiniteGramTerm coordinate feature (2 : Fin 3) f)
    (admissible : SchwartzLineTestFunction -> Prop)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        (threeComponentFiniteGramFormulaData
          zeroSide coordinate feature zeroSide_eq_threeComponentSource)
        admissible liData) :
    SupportRestrictedFormulaResidualPositivityData
      (threeComponentFiniteGramFormulaData
        zeroSide coordinate feature zeroSide_eq_threeComponentSource) :=
  bridge.toSupportRestrictedFormulaResidualPositivityData
    (fun f _hf =>
      threeComponentFiniteGram_residual_nonneg
        zeroSide coordinate feature zeroSide_eq_threeComponentSource f)

/--
Single-prime support-restricted positivity package.

The real positivity-to-RH content remains explicit in `bridge`; this constructor
only checks that the one-component formula residual can use a zero-side
nonnegativity theorem as its restricted residual nonnegativity input.
-/
noncomputable def singlePrimeSupportRestrictedFormulaResidualPositivityData
    (zeroSide : SchwartzRiemannWeilZeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (liData : AbstractLiCriterionData (fun _ : Complex => True))
    (bridge :
      SupportRestrictedFormulaResidualToLiBridge
        (singlePrimeFormulaData zeroSide) admissible liData)
    (zeroSide_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= zeroSide.zeroSide f) :
    SupportRestrictedFormulaResidualPositivityData
      (singlePrimeFormulaData zeroSide) :=
  bridge.toSupportRestrictedFormulaResidualPositivityData
    (singlePrime_residual_nonneg_on_admissible
      zeroSide admissible zeroSide_nonneg_on_admissible)

end GuinandWeilToyFormula

end

end RiemannHypothesisProject
