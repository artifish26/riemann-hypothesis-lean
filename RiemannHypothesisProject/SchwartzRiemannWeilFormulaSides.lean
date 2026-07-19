import RiemannHypothesisProject.SchwartzRiemannWeilCertificateData

/-!
# Formula-side packages for the Schwartz Riemann-Weil route

The decomposed Riemann-Weil certificate already separates explicit-formula data
from positivity data. This module makes the explicit-formula side itself a
smaller reusable target: package the prime, pole, and gamma sides first, then
package the identity relating their residual side to a chosen zero side.

These packages convert back to the existing `SchwartzRiemannWeilExplicitFormulaData`
endpoint, so downstream global criterion and RH consequences remain unchanged.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/-- Prime, pole, and gamma sides for a Schwartz Riemann-Weil explicit formula. -/
structure SchwartzRiemannWeilFormulaSideData where
  primeSide : SchwartzLineTestFunction -> Real
  poleSide : SchwartzLineTestFunction -> Real
  gammaSide : SchwartzLineTestFunction -> Real

namespace SchwartzRiemannWeilFormulaSideData

/-- The residual side assembled from prime, pole, and gamma contributions. -/
noncomputable def residualSide
    (sideData : SchwartzRiemannWeilFormulaSideData)
    (f : SchwartzLineTestFunction) : Real :=
  sideData.primeSide f + sideData.poleSide f + sideData.gammaSide f

/-- The residual side is definitionally the sum of the three packaged sides. -/
theorem residualSide_eq
    (sideData : SchwartzRiemannWeilFormulaSideData)
    (f : SchwartzLineTestFunction) :
    sideData.residualSide f =
      sideData.primeSide f + sideData.poleSide f + sideData.gammaSide f :=
  rfl

end SchwartzRiemannWeilFormulaSideData

/--
An explicit-formula identity for a fixed zero side and packaged formula sides.

This is the work unit for the analytic explicit formula: after the zero side
and prime/pole/gamma side functions have been chosen, prove the identity
`zeroSide = prime + pole + gamma`.
-/
structure SchwartzRiemannWeilFormulaIdentityData
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sideData : SchwartzRiemannWeilFormulaSideData
  explicitFormula :
    forall f : SchwartzLineTestFunction,
      zeroSide.zeroSide f = sideData.residualSide f

namespace SchwartzRiemannWeilFormulaIdentityData

/--
Build formula identity data directly from prime, pole, and gamma side
functions, plus the explicit-formula equality.
-/
noncomputable def ofRawSides
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (primeSide poleSide gammaSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        zeroSide.zeroSide f = primeSide f + poleSide f + gammaSide f) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide where
  sideData :=
    { primeSide := primeSide
      poleSide := poleSide
      gammaSide := gammaSide }
  explicitFormula := fun f => by
    simpa [SchwartzRiemannWeilFormulaSideData.residualSide]
      using explicitFormula f

/-- Convert packaged formula-side identity data to the existing explicit-formula package. -/
noncomputable def toExplicitFormulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) :
    SchwartzRiemannWeilExplicitFormulaData where
  zeroSide := zeroSide
  primeSide := formulaData.sideData.primeSide
  poleSide := formulaData.sideData.poleSide
  gammaSide := formulaData.sideData.gammaSide
  explicitFormula := fun f => by
    simpa [SchwartzRiemannWeilFormulaSideData.residualSide]
      using formulaData.explicitFormula f

/-- The converted explicit-formula data keeps the packaged prime side. -/
theorem toExplicitFormulaData_primeSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) :
    formulaData.toExplicitFormulaData.primeSide =
      formulaData.sideData.primeSide :=
  rfl

/-- The converted explicit-formula data keeps the packaged pole side. -/
theorem toExplicitFormulaData_poleSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) :
    formulaData.toExplicitFormulaData.poleSide =
      formulaData.sideData.poleSide :=
  rfl

/-- The converted explicit-formula data keeps the packaged gamma side. -/
theorem toExplicitFormulaData_gammaSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide) :
    formulaData.toExplicitFormulaData.gammaSide =
      formulaData.sideData.gammaSide :=
  rfl

/-- Compact-exhaustion zero-window sums converge to the packaged zero side. -/
theorem tendsto_windowZeroSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => zeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (zeroSide.zeroSide f)) :=
  formulaData.toExplicitFormulaData.tendsto_windowZeroSide exhaustion f

/-- Compact-exhaustion zero-window sums converge to the packaged residual side. -/
theorem tendsto_windowZeroSide_residualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (formulaData : SchwartzRiemannWeilFormulaIdentityData zeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => zeroSide.windowZeroSide exhaustion n f)
      atTop (nhds (formulaData.sideData.residualSide f)) := by
  rw [← formulaData.explicitFormula f]
  exact formulaData.tendsto_windowZeroSide exhaustion f

/-- Build formula identity data from an existing explicit-formula package. -/
noncomputable def ofExplicitFormulaData
    (formulaData : SchwartzRiemannWeilExplicitFormulaData) :
    SchwartzRiemannWeilFormulaIdentityData formulaData.zeroSide where
  sideData :=
    { primeSide := formulaData.primeSide
      poleSide := formulaData.poleSide
      gammaSide := formulaData.gammaSide }
  explicitFormula := fun f => by
    simpa [SchwartzRiemannWeilFormulaSideData.residualSide]
      using formulaData.explicitFormula f

end SchwartzRiemannWeilFormulaIdentityData

end RiemannHypothesisProject
