import RiemannHypothesisProject.GuinandWeilTestFunctionTarget
import RiemannHypothesisProject.SchwartzExplicitFormula
import RiemannHypothesisProject.GuinandWeilContinuityBridge

/-!
# Density bridge for Guinand-Weil source formulae

`GuinandWeilTestFunctionTarget` promotes a restricted source formula to a
global source formula when admissible source tests exactly cover all Schwartz
tests.  In practice, analytic formulae are more often proved on a dense
admissible source class and then extended by continuity.

This file checks that route.  It does not prove density or continuity; those
remain explicit analytic fields.
-/

namespace RiemannHypothesisProject

/-- The set where the source-normalized Guinand-Weil formula holds. -/
def guinandWeilSourceFormulaEqualitySet
    (sideData : GuinandWeilFormulaSideData) :
    Set SchwartzLineTestFunction :=
  {f : SchwartzLineTestFunction |
    sideData.sourceZeroSide f = sideData.sourceResidualSide f}

/--
Continuity of all four source-normalized Guinand-Weil side functions.

The zero side is included here because density promotion of the formula
identity needs the equality locus to be closed.
-/
structure GuinandWeilFormulaFullSideContinuityData
    (sideData : GuinandWeilFormulaSideData) where
  continuous_sourceZeroSide :
    Continuous sideData.sourceZeroSide
  continuous_sourcePrimeSide :
    Continuous sideData.sourcePrimeSide
  continuous_sourcePoleSide :
    Continuous sideData.sourcePoleSide
  continuous_sourceGammaSide :
    Continuous sideData.sourceGammaSide

namespace GuinandWeilFormulaFullSideContinuityData

/-- Separate continuity of the source prime, pole, and gamma sides gives residual continuity. -/
theorem continuous_sourceResidualSide
    {sideData : GuinandWeilFormulaSideData}
    (continuity : GuinandWeilFormulaFullSideContinuityData sideData) :
    Continuous sideData.sourceResidualSide := by
  change Continuous
    (fun f : SchwartzLineTestFunction =>
      sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
        sideData.sourceGammaSide f)
  exact
    (continuity.continuous_sourcePrimeSide.add
      continuity.continuous_sourcePoleSide).add
        continuity.continuous_sourceGammaSide

/-- Continuity of the source sides closes the source formula equality locus. -/
theorem sourceFormulaEqualitySet_closed
    {sideData : GuinandWeilFormulaSideData}
    (continuity : GuinandWeilFormulaFullSideContinuityData sideData) :
    IsClosed (guinandWeilSourceFormulaEqualitySet sideData) := by
  simpa [guinandWeilSourceFormulaEqualitySet] using
    isClosed_eq continuity.continuous_sourceZeroSide
      continuity.continuous_sourceResidualSide

/-- Forget the zero-side continuity when only prime/pole/gamma continuity is needed. -/
noncomputable def toSideContinuityData
    {sourceData : GuinandWeilFormulaIdentityData}
    (continuity :
      GuinandWeilFormulaFullSideContinuityData sourceData.sideData) :
    GuinandWeilFormulaSideContinuityData sourceData where
  continuous_sourcePrimeSide := continuity.continuous_sourcePrimeSide
  continuous_sourcePoleSide := continuity.continuous_sourcePoleSide
  continuous_sourceGammaSide := continuity.continuous_sourceGammaSide

end GuinandWeilFormulaFullSideContinuityData

/-- The image of admissible source tests inside the project Schwartz test space. -/
def guinandWeilAdmissibleSchwartzImage
    (testData : GuinandWeilSourceTestFunctionClass) :
    Set SchwartzLineTestFunction :=
  {f : SchwartzLineTestFunction |
    exists g : testData.SourceTestFunction,
      testData.admissible g ∧ testData.toSchwartz g = f}

/--
Hilbert-energy positivity on an admissible Guinand-Weil source class.

Once the source residual side is identified with the concrete Schwartz
`L2`-energy of the embedded test function, residual nonnegativity follows from
the checked energy positivity theorem.
-/
theorem guinandWeilSourceResidual_nonneg_of_schwartzL2Energy
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceResidualSide : testData.SourceTestFunction -> Real)
    (sourceResidual_eq_energy :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceResidualSide g = schwartzL2Energy (testData.toSchwartz g)) :
    forall g : testData.SourceTestFunction,
      testData.admissible g -> 0 <= sourceResidualSide g := by
  intro g hg
  rw [sourceResidual_eq_energy g hg]
  exact schwartzL2Energy_nonneg (testData.toSchwartz g)

/--
Support-restricted formula-side residual positivity on the admissible source
image, in the Hilbert-energy normalization.

This is the infinite-dimensional positivity slice needed by the source-image
route: the admissible class lives in the Guinand-Weil source space, the theorem
is stated on its Schwartz image, and the only analytic identity still required
is the equality between the formula residual and the nonnegative Hilbert
energy.
-/
theorem guinandWeilAdmissibleSchwartzImage_formulaResidual_nonneg_of_schwartzL2Energy
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceResidualSide : testData.SourceTestFunction -> Real)
    (formulaResidual_eq_source :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          formulaData.sideData.residualSide (testData.toSchwartz g) =
            sourceResidualSide g)
    (sourceResidual_eq_energy :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceResidualSide g = schwartzL2Energy (testData.toSchwartz g)) :
    forall f : SchwartzLineTestFunction,
      f ∈ guinandWeilAdmissibleSchwartzImage testData ->
        0 <= formulaData.sideData.residualSide f := by
  intro f hf
  rcases hf with ⟨g, hg, hgf⟩
  rw [← hgf, formulaResidual_eq_source g hg, sourceResidual_eq_energy g hg]
  exact schwartzL2Energy_nonneg (testData.toSchwartz g)

/--
Dense-core promotion of the Hilbert-energy source-image positivity theorem.

If a dense core of Schwartz tests lies inside the admissible source image, the
formula residual is continuous, and the residual agrees with the concrete
Hilbert energy on admissible source tests, then formula residual nonnegativity
holds for every Schwartz test function.  This is the density/closedness step of
the support-restricted route stated directly as a theorem, without packaging it
through another bridge object.
-/
theorem guinandWeilDenseCore_formulaResidual_nonneg_of_schwartzL2Energy
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceResidualSide : testData.SourceTestFunction -> Real)
    (core : Set SchwartzLineTestFunction)
    (core_subset_image :
      core ⊆ guinandWeilAdmissibleSchwartzImage testData)
    (dense_core : closure core = Set.univ)
    (residual_continuous :
      Continuous formulaData.sideData.residualSide)
    (formulaResidual_eq_source :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          formulaData.sideData.residualSide (testData.toSchwartz g) =
            sourceResidualSide g)
    (sourceResidual_eq_energy :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceResidualSide g = schwartzL2Energy (testData.toSchwartz g)) :
    forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f := by
  have hclosed : IsClosed (formulaResidualNonnegativeSet formulaData) := by
    simpa [formulaResidualNonnegativeSet] using
      isClosed_le continuous_const residual_continuous
  have hcore_subset_nonnegative :
      core ⊆ formulaResidualNonnegativeSet formulaData := by
    intro f hf
    exact
      guinandWeilAdmissibleSchwartzImage_formulaResidual_nonneg_of_schwartzL2Energy
        testData sourceResidualSide formulaResidual_eq_source
        sourceResidual_eq_energy f (core_subset_image hf)
  have hclosure_subset_nonnegative :
      closure core ⊆ formulaResidualNonnegativeSet formulaData :=
    closure_minimal hcore_subset_nonnegative hclosed
  intro f
  have hf_closure : f ∈ closure core := by
    rw [dense_core]
    exact Set.mem_univ f
  exact hclosure_subset_nonnegative hf_closure

/--
Dense source-image promotion of Hilbert-energy residual positivity.

This is the common special case of
`guinandWeilDenseCore_formulaResidual_nonneg_of_schwartzL2Energy` where the
admissible source image itself is dense in the project Schwartz space.
-/
theorem guinandWeilDenseImage_formulaResidual_nonneg_of_schwartzL2Energy
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceResidualSide : testData.SourceTestFunction -> Real)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ)
    (residual_continuous :
      Continuous formulaData.sideData.residualSide)
    (formulaResidual_eq_source :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          formulaData.sideData.residualSide (testData.toSchwartz g) =
            sourceResidualSide g)
    (sourceResidual_eq_energy :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceResidualSide g = schwartzL2Energy (testData.toSchwartz g)) :
    forall f : SchwartzLineTestFunction,
      0 <= formulaData.sideData.residualSide f :=
  guinandWeilDenseCore_formulaResidual_nonneg_of_schwartzL2Energy
    testData sourceResidualSide
    (guinandWeilAdmissibleSchwartzImage testData)
    (fun _ hf => hf) dense_admissible_image residual_continuous
    formulaResidual_eq_source sourceResidual_eq_energy

namespace GuinandWeilSourceTestFunctionClass

/--
Model source class generated by a concrete core of project Schwartz tests.

This is not a final analytic source class: the strip and rapid-decay fields are
set to `True`.  Its purpose is to let dense-core p-series and Guinand-Weil
formula arguments be tested with the exact same source-image machinery that a
future Paley-Wiener or paper-specific source class will use.
-/
noncomputable def ofDenseCore
    (core : Set SchwartzLineTestFunction) :
    GuinandWeilSourceTestFunctionClass where
  SourceTestFunction := {f : SchwartzLineTestFunction // f ∈ core}
  toSchwartz := fun g => g.1
  sourceFourier := fun g => SchwartzLineTestFunction.fourier g.1
  stripAnalytic := fun _ => True
  rapidDecay := fun _ => True
  admissible := fun _ => True
  admissible_stripAnalytic := by
    intro _ _
    trivial
  admissible_rapidDecay := by
    intro _ _
    trivial
  sourceFourier_eq_projectFourier := by
    intro _ _
    rfl

/-- The admissible image of the dense-core model source class is exactly the core. -/
theorem guinandWeilAdmissibleSchwartzImage_ofDenseCore
    (core : Set SchwartzLineTestFunction) :
    guinandWeilAdmissibleSchwartzImage
        (GuinandWeilSourceTestFunctionClass.ofDenseCore core) =
      core := by
  ext f
  constructor
  · intro hf
    rcases hf with ⟨g, _hg, hgf⟩
    rw [← hgf]
    exact g.2
  · intro hf
    exact Exists.intro (Subtype.mk f hf) (And.intro trivial rfl)

/-- A dense core gives a dense admissible image for the model source class. -/
theorem dense_admissibleSchwartzImage_ofDenseCore
    {core : Set SchwartzLineTestFunction}
    (dense_core : closure core = Set.univ) :
    closure
        (guinandWeilAdmissibleSchwartzImage
          (GuinandWeilSourceTestFunctionClass.ofDenseCore core)) =
      Set.univ := by
  rw [guinandWeilAdmissibleSchwartzImage_ofDenseCore, dense_core]

end GuinandWeilSourceTestFunctionClass

/--
A density/continuity bridge from a restricted Guinand-Weil source formula to a
global source-normalized formula.

Future analytic work should supply `dense_admissible_image` from a density
theorem and `continuity` from continuity of the source zero, prime, pole, and
gamma terms.
-/
structure GuinandWeilRestrictedFormulaDensityBridge
    {testData : GuinandWeilSourceTestFunctionClass}
    (restrictedData : GuinandWeilRestrictedFormulaIdentityData testData)
    (globalSideData : GuinandWeilFormulaSideData) where
  sideBridge :
    GuinandWeilSourceToSchwartzSideBridge
      testData restrictedData.sideData globalSideData
  dense_admissible_image :
    closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ
  continuity :
    GuinandWeilFormulaFullSideContinuityData globalSideData

namespace GuinandWeilRestrictedFormulaDensityBridge

/-- The restricted formula proves the global source formula on the admissible image. -/
theorem sourceFormula_on_admissible_image
    {testData : GuinandWeilSourceTestFunctionClass}
    {restrictedData : GuinandWeilRestrictedFormulaIdentityData testData}
    {globalSideData : GuinandWeilFormulaSideData}
    (bridge :
      GuinandWeilRestrictedFormulaDensityBridge
        restrictedData globalSideData) :
    guinandWeilAdmissibleSchwartzImage testData ⊆
      guinandWeilSourceFormulaEqualitySet globalSideData := by
  intro f hf
  rcases hf with ⟨g, hg, hgf⟩
  rw [← hgf]
  calc
    globalSideData.sourceZeroSide (testData.toSchwartz g) =
        restrictedData.sideData.sourceZeroSide g :=
      bridge.sideBridge.sourceZeroSide_eq g hg
    _ = restrictedData.sideData.sourceResidualSide g :=
      restrictedData.sourceExplicitFormula g hg
    _ = globalSideData.sourceResidualSide (testData.toSchwartz g) :=
      (bridge.sideBridge.sourceResidualSide_eq g hg).symm

/-- Density plus side continuity promotes the restricted source formula globally. -/
theorem sourceExplicitFormula
    {testData : GuinandWeilSourceTestFunctionClass}
    {restrictedData : GuinandWeilRestrictedFormulaIdentityData testData}
    {globalSideData : GuinandWeilFormulaSideData}
    (bridge :
      GuinandWeilRestrictedFormulaDensityBridge
        restrictedData globalSideData) :
    forall f : SchwartzLineTestFunction,
      globalSideData.sourceZeroSide f = globalSideData.sourceResidualSide f := by
  intro f
  have hclosure_subset :
      closure (guinandWeilAdmissibleSchwartzImage testData) ⊆
        guinandWeilSourceFormulaEqualitySet globalSideData :=
    closure_minimal bridge.sourceFormula_on_admissible_image
      bridge.continuity.sourceFormulaEqualitySet_closed
  have hf_closure :
      f ∈ closure (guinandWeilAdmissibleSchwartzImage testData) := by
    rw [bridge.dense_admissible_image]
    exact Set.mem_univ f
  exact hclosure_subset hf_closure

/-- Convert the density-promoted restricted formula into global source identity data. -/
noncomputable def toGlobalFormulaIdentityData
    {testData : GuinandWeilSourceTestFunctionClass}
    {restrictedData : GuinandWeilRestrictedFormulaIdentityData testData}
    {globalSideData : GuinandWeilFormulaSideData}
    (bridge :
      GuinandWeilRestrictedFormulaDensityBridge
        restrictedData globalSideData) :
    GuinandWeilFormulaIdentityData where
  sideData := globalSideData
  sourceExplicitFormula := bridge.sourceExplicitFormula

end GuinandWeilRestrictedFormulaDensityBridge

end RiemannHypothesisProject
