import RiemannHypothesisProject.SupportRestrictedWeilDensity

/-!
# Residual-side continuity bridge

The support-restricted density route needs the residual-nonnegative locus to be
closed.  Analytically, this should follow from continuity of the explicit
formula residual side in the Schwartz test-function topology.

This file checks that topological step.  It keeps the hard analytic continuity
proofs as fields, but proves that once the residual side is continuous the
closedness hypothesis required by `SupportRestrictedFormulaResidualDensityBridge`
is automatic.  It also derives residual-side continuity from separate
continuity of the prime, pole, and gamma sides.
-/

namespace RiemannHypothesisProject

/--
Continuity of the residual side of a packaged Riemann-Weil explicit formula.

Future analytic work should prove this from continuity of the prime, pole, and
gamma terms in the chosen Schwartz topology, or provide it directly if the
residual side is treated as one functional.
-/
structure SchwartzRiemannWeilFormulaResidualContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) where
  continuous_residualSide :
    Continuous formulaData.sideData.residualSide

namespace SchwartzRiemannWeilFormulaResidualContinuityData

/-- Continuity of the residual side makes the residual-nonnegative locus closed. -/
theorem residual_nonnegativeSet_closed
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (continuity :
      SchwartzRiemannWeilFormulaResidualContinuityData formulaData) :
    IsClosed (formulaResidualNonnegativeSet formulaData) := by
  simpa [formulaResidualNonnegativeSet] using
    isClosed_le continuous_const continuity.continuous_residualSide

/--
Build the support-restricted density bridge from dense admissibility plus
residual continuity.
-/
noncomputable def toSupportRestrictedDensityBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (continuity :
      SchwartzRiemannWeilFormulaResidualContinuityData formulaData)
    (dense_admissible :
      closure {f : SchwartzLineTestFunction | restrictedData.admissible f} =
        Set.univ) :
    SupportRestrictedFormulaResidualDensityBridge restrictedData where
  dense_admissible := dense_admissible
  residual_nonnegativeSet_closed :=
    continuity.residual_nonnegativeSet_closed

end SchwartzRiemannWeilFormulaResidualContinuityData

/--
Continuity of the separate prime, pole, and gamma sides of a packaged formula.

This is the most reusable analytic target: each side can be proved continuous
from its own integral, series, or local term estimates, then recombined by Lean.
-/
structure SchwartzRiemannWeilFormulaSideContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) where
  continuous_primeSide :
    Continuous formulaData.sideData.primeSide
  continuous_poleSide :
    Continuous formulaData.sideData.poleSide
  continuous_gammaSide :
    Continuous formulaData.sideData.gammaSide

namespace SchwartzRiemannWeilFormulaSideContinuityData

/-- Separate continuity of the prime, pole, and gamma sides gives residual continuity. -/
theorem continuous_residualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (continuity :
      SchwartzRiemannWeilFormulaSideContinuityData formulaData) :
    Continuous formulaData.sideData.residualSide := by
  change Continuous
    (fun f : SchwartzLineTestFunction =>
      formulaData.sideData.primeSide f + formulaData.sideData.poleSide f +
        formulaData.sideData.gammaSide f)
  exact
    (continuity.continuous_primeSide.add continuity.continuous_poleSide).add
      continuity.continuous_gammaSide

/-- Package separate side continuity as residual-side continuity. -/
noncomputable def toResidualContinuityData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (continuity :
      SchwartzRiemannWeilFormulaSideContinuityData formulaData) :
    SchwartzRiemannWeilFormulaResidualContinuityData formulaData where
  continuous_residualSide := continuity.continuous_residualSide

/-- Separate side continuity makes the residual-nonnegative locus closed. -/
theorem residual_nonnegativeSet_closed
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    (continuity :
      SchwartzRiemannWeilFormulaSideContinuityData formulaData) :
    IsClosed (formulaResidualNonnegativeSet formulaData) :=
  continuity.toResidualContinuityData.residual_nonnegativeSet_closed

/--
Build the support-restricted density bridge from separate side continuity and
dense admissibility.
-/
noncomputable def toSupportRestrictedDensityBridge
    {zeroSide : SchwartzRiemannWeilZeroSide}
    {formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide}
    {restrictedData :
      SupportRestrictedFormulaResidualPositivityData formulaData}
    (continuity :
      SchwartzRiemannWeilFormulaSideContinuityData formulaData)
    (dense_admissible :
      closure {f : SchwartzLineTestFunction | restrictedData.admissible f} =
        Set.univ) :
    SupportRestrictedFormulaResidualDensityBridge restrictedData :=
  continuity.toResidualContinuityData.toSupportRestrictedDensityBridge
    dense_admissible

end SchwartzRiemannWeilFormulaSideContinuityData

end RiemannHypothesisProject
