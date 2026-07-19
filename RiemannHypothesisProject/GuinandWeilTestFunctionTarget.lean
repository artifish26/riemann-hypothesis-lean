import RiemannHypothesisProject.GuinandWeilFormulaTarget

/-!
# Guinand-Weil source test-function target

Modern Guinand-Weil formula statements are usually proved first for a source
class of test functions with strip analyticity, decay, and a stated Fourier
convention.  The project's formula packages are stated for
`SchwartzLineTestFunction`.

This file names that missing intermediate layer.  It lets future work prove the
source formula on an admissible class, prove that the source sides agree with
project-side functions after mapping into the Schwartz normalization, and only
then promote the result to the global `GuinandWeilFormulaIdentityData` when a
separate coverage theorem is available.
-/

namespace RiemannHypothesisProject

/--
The source test-function class for a Guinand-Weil formula.

The analytic predicates are intentionally fields rather than definitions: a
future formalization can instantiate them with the exact strip, decay, and
Fourier-convention hypotheses from a chosen source paper.
-/
structure GuinandWeilSourceTestFunctionClass where
  SourceTestFunction : Type
  toSchwartz : SourceTestFunction -> SchwartzLineTestFunction
  sourceFourier : SourceTestFunction -> SchwartzLineTestFunction
  stripAnalytic : SourceTestFunction -> Prop
  rapidDecay : SourceTestFunction -> Prop
  admissible : SourceTestFunction -> Prop
  admissible_stripAnalytic :
    forall g : SourceTestFunction, admissible g -> stripAnalytic g
  admissible_rapidDecay :
    forall g : SourceTestFunction, admissible g -> rapidDecay g
  sourceFourier_eq_projectFourier :
    forall g : SourceTestFunction,
      admissible g ->
        sourceFourier g = SchwartzLineTestFunction.fourier (toSchwartz g)

namespace GuinandWeilSourceTestFunctionClass

/-- Admissible source tests satisfy the packaged strip-analytic hypothesis. -/
theorem stripAnalytic_of_admissible
    (testData : GuinandWeilSourceTestFunctionClass)
    {g : testData.SourceTestFunction}
    (hg : testData.admissible g) :
    testData.stripAnalytic g :=
  testData.admissible_stripAnalytic g hg

/-- Admissible source tests satisfy the packaged rapid-decay hypothesis. -/
theorem rapidDecay_of_admissible
    (testData : GuinandWeilSourceTestFunctionClass)
    {g : testData.SourceTestFunction}
    (hg : testData.admissible g) :
    testData.rapidDecay g :=
  testData.admissible_rapidDecay g hg

end GuinandWeilSourceTestFunctionClass

/-- The four source Guinand-Weil sides before mapping into Schwartz notation. -/
structure GuinandWeilRestrictedFormulaSideData
    (testData : GuinandWeilSourceTestFunctionClass) where
  sourceZeroSide : testData.SourceTestFunction -> Real
  sourcePrimeSide : testData.SourceTestFunction -> Real
  sourcePoleSide : testData.SourceTestFunction -> Real
  sourceGammaSide : testData.SourceTestFunction -> Real

namespace GuinandWeilRestrictedFormulaSideData

/-- The restricted source residual side assembled from prime, pole, and gamma. -/
def sourceResidualSide
    {testData : GuinandWeilSourceTestFunctionClass}
    (sideData : GuinandWeilRestrictedFormulaSideData testData)
    (g : testData.SourceTestFunction) : Real :=
  sideData.sourcePrimeSide g + sideData.sourcePoleSide g +
    sideData.sourceGammaSide g

/-- The restricted residual side is definitionally the sum of the three terms. -/
theorem sourceResidualSide_eq
    {testData : GuinandWeilSourceTestFunctionClass}
    (sideData : GuinandWeilRestrictedFormulaSideData testData)
    (g : testData.SourceTestFunction) :
    sideData.sourceResidualSide g =
      sideData.sourcePrimeSide g + sideData.sourcePoleSide g +
        sideData.sourceGammaSide g :=
  rfl

end GuinandWeilRestrictedFormulaSideData

/-- A Guinand-Weil identity proved only on the admissible source class. -/
structure GuinandWeilRestrictedFormulaIdentityData
    (testData : GuinandWeilSourceTestFunctionClass) where
  sideData : GuinandWeilRestrictedFormulaSideData testData
  sourceExplicitFormula :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        sideData.sourceZeroSide g = sideData.sourceResidualSide g

/--
Agreement between restricted source sides and global Schwartz-indexed source
sides on admissible tests.
-/
structure GuinandWeilSourceToSchwartzSideBridge
    (testData : GuinandWeilSourceTestFunctionClass)
    (restrictedSideData : GuinandWeilRestrictedFormulaSideData testData)
    (globalSideData : GuinandWeilFormulaSideData) where
  sourceZeroSide_eq :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        globalSideData.sourceZeroSide (testData.toSchwartz g) =
          restrictedSideData.sourceZeroSide g
  sourcePrimeSide_eq :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        globalSideData.sourcePrimeSide (testData.toSchwartz g) =
          restrictedSideData.sourcePrimeSide g
  sourcePoleSide_eq :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        globalSideData.sourcePoleSide (testData.toSchwartz g) =
          restrictedSideData.sourcePoleSide g
  sourceGammaSide_eq :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        globalSideData.sourceGammaSide (testData.toSchwartz g) =
          restrictedSideData.sourceGammaSide g

namespace GuinandWeilSourceToSchwartzSideBridge

/-- The restricted-to-global side bridge also preserves the residual side. -/
theorem sourceResidualSide_eq
    {testData : GuinandWeilSourceTestFunctionClass}
    {restrictedSideData : GuinandWeilRestrictedFormulaSideData testData}
    {globalSideData : GuinandWeilFormulaSideData}
    (bridge :
      GuinandWeilSourceToSchwartzSideBridge
        testData restrictedSideData globalSideData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    globalSideData.sourceResidualSide (testData.toSchwartz g) =
      restrictedSideData.sourceResidualSide g := by
  simp [GuinandWeilFormulaSideData.sourceResidualSide,
    GuinandWeilRestrictedFormulaSideData.sourceResidualSide,
    bridge.sourcePrimeSide_eq g hg, bridge.sourcePoleSide_eq g hg,
    bridge.sourceGammaSide_eq g hg]

end GuinandWeilSourceToSchwartzSideBridge

namespace GuinandWeilRestrictedFormulaIdentityData

/--
Promote a restricted source formula to a global source formula when admissible
source tests cover every Schwartz test function.

This is the density/extension or exact-coverage theorem future analytic work
must provide before a restricted Guinand-Weil formula can be used as the
project's full source formula.
-/
def toGlobalFormulaIdentityData
    {testData : GuinandWeilSourceTestFunctionClass}
    (restrictedData : GuinandWeilRestrictedFormulaIdentityData testData)
    (globalSideData : GuinandWeilFormulaSideData)
    (bridge :
      GuinandWeilSourceToSchwartzSideBridge
        testData restrictedData.sideData globalSideData)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g ∧ testData.toSchwartz g = f) :
    GuinandWeilFormulaIdentityData where
  sideData := globalSideData
  sourceExplicitFormula := fun f => by
    rcases coversSchwartz f with ⟨g, hg, hgf⟩
    rw [← hgf]
    calc
      globalSideData.sourceZeroSide (testData.toSchwartz g) =
          restrictedData.sideData.sourceZeroSide g :=
        bridge.sourceZeroSide_eq g hg
      _ = restrictedData.sideData.sourceResidualSide g :=
        restrictedData.sourceExplicitFormula g hg
      _ = globalSideData.sourceResidualSide (testData.toSchwartz g) :=
        (bridge.sourceResidualSide_eq g hg).symm

end GuinandWeilRestrictedFormulaIdentityData

end RiemannHypothesisProject
