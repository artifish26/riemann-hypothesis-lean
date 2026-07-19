import RiemannHypothesisProject.GuinandWeilFormulaTarget
import RiemannHypothesisProject.SchwartzRiemannWeilResidualContinuity

/-!
# Guinand-Weil side-continuity bridge

The residual-closedness route needs continuity of the project prime, pole, and
gamma sides.  When those sides come from a source-normalized Guinand-Weil
formula, this file lets continuity be proved once for the source sides and
then transported through the normalization bridge.
-/

namespace RiemannHypothesisProject

/--
Continuity of the source-normalized Guinand-Weil side functions.

Future analytic work should prove these fields from the concrete prime,
pole, and gamma terms in the chosen Guinand-Weil normalization.
-/
structure GuinandWeilFormulaSideContinuityData
    (sourceData : GuinandWeilFormulaIdentityData) where
  continuous_sourcePrimeSide :
    Continuous sourceData.sideData.sourcePrimeSide
  continuous_sourcePoleSide :
    Continuous sourceData.sideData.sourcePoleSide
  continuous_sourceGammaSide :
    Continuous sourceData.sideData.sourceGammaSide

namespace GuinandWeilFormulaSideContinuityData

/--
Transport source-side continuity through the Guinand-Weil normalization bridge
to the project's formula-side continuity package.
-/
noncomputable def toSchwartzFormulaSideContinuityData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (continuity : GuinandWeilFormulaSideContinuityData sourceData)
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    SchwartzRiemannWeilFormulaSideContinuityData
      bridge.toFormulaIdentityData where
  continuous_primeSide := by
    change Continuous sourceData.sideData.sourcePrimeSide
    exact continuity.continuous_sourcePrimeSide
  continuous_poleSide := by
    change Continuous sourceData.sideData.sourcePoleSide
    exact continuity.continuous_sourcePoleSide
  continuous_gammaSide := by
    change Continuous sourceData.sideData.sourceGammaSide
    exact continuity.continuous_sourceGammaSide

/-- Source-side continuity gives residual continuity after normalization. -/
noncomputable def toSchwartzResidualContinuityData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (continuity : GuinandWeilFormulaSideContinuityData sourceData)
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    SchwartzRiemannWeilFormulaResidualContinuityData
      bridge.toFormulaIdentityData :=
  (continuity.toSchwartzFormulaSideContinuityData bridge)
    |>.toResidualContinuityData

/-- Source-side continuity closes the residual-nonnegative locus after normalization. -/
theorem residual_nonnegativeSet_closed
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (continuity : GuinandWeilFormulaSideContinuityData sourceData)
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    IsClosed (formulaResidualNonnegativeSet bridge.toFormulaIdentityData) :=
  (continuity.toSchwartzFormulaSideContinuityData bridge)
    |>.residual_nonnegativeSet_closed

end GuinandWeilFormulaSideContinuityData

namespace GuinandWeilComponentwiseNormalizationBridge

/--
Transport source-side continuity through a componentwise Guinand-Weil
normalization bridge to the project's formula-side continuity package.
-/
noncomputable def toSchwartzFormulaSideContinuityData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (continuity : GuinandWeilFormulaSideContinuityData sourceData) :
    SchwartzRiemannWeilFormulaSideContinuityData
      bridge.toFormulaIdentityData where
  continuous_primeSide := by
    change Continuous bridge.sideData.primeSide
    have hprime :
        bridge.sideData.primeSide =
          sourceData.sideData.sourcePrimeSide := by
      funext f
      exact bridge.primeSide_eq_sourcePrimeSide f
    rw [hprime]
    exact continuity.continuous_sourcePrimeSide
  continuous_poleSide := by
    change Continuous bridge.sideData.poleSide
    have hpole :
        bridge.sideData.poleSide =
          sourceData.sideData.sourcePoleSide := by
      funext f
      exact bridge.poleSide_eq_sourcePoleSide f
    rw [hpole]
    exact continuity.continuous_sourcePoleSide
  continuous_gammaSide := by
    change Continuous bridge.sideData.gammaSide
    have hgamma :
        bridge.sideData.gammaSide =
          sourceData.sideData.sourceGammaSide := by
      funext f
      exact bridge.gammaSide_eq_sourceGammaSide f
    rw [hgamma]
    exact continuity.continuous_sourceGammaSide

/-- Componentwise source-side continuity gives residual continuity after normalization. -/
noncomputable def toSchwartzResidualContinuityData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (continuity : GuinandWeilFormulaSideContinuityData sourceData) :
    SchwartzRiemannWeilFormulaResidualContinuityData
      bridge.toFormulaIdentityData :=
  (bridge.toSchwartzFormulaSideContinuityData continuity)
    |>.toResidualContinuityData

/--
Componentwise source-side continuity closes the residual-nonnegative locus
after normalization.
-/
theorem residual_nonnegativeSet_closed
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (continuity : GuinandWeilFormulaSideContinuityData sourceData) :
    IsClosed (formulaResidualNonnegativeSet bridge.toFormulaIdentityData) :=
  (bridge.toSchwartzFormulaSideContinuityData continuity)
    |>.residual_nonnegativeSet_closed

end GuinandWeilComponentwiseNormalizationBridge

end RiemannHypothesisProject
