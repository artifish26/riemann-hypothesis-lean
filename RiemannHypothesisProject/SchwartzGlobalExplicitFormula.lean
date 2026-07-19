import RiemannHypothesisProject.GlobalZeroSide
import RiemannHypothesisProject.SchwartzExplicitFormula

/-!
# Schwartz global explicit-formula bridge

This file connects the global zeta-zero `tsum` interface to the Schwartz
explicit-formula skeleton.

It still does not assert the Riemann-Weil explicit formula. Instead it records
the checked shape of a future normalization whose zero side is genuinely a
summable sum over actual zeta zeroes. Once such a zero weight and the remaining
prime/pole/gamma sides are supplied, compact-exhaustion window sums are proved
to converge to the zero side, residual side, and any matching quadratic form.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

namespace SchwartzExplicitFormulaNormalization

/-- The nonzero-side contribution in a Schwartz explicit-formula normalization. -/
def residualSide
    (normalization : SchwartzExplicitFormulaNormalization)
    (f : SchwartzLineTestFunction) : ℝ :=
  normalization.primeSide f + normalization.poleSide f + normalization.gammaSide f

/-- The zero side equals the residual side by the Schwartz explicit formula. -/
theorem zeroSide_eq_residualSide
    (normalization : SchwartzExplicitFormulaNormalization)
    (f : SchwartzLineTestFunction) :
    normalization.zeroSide f = normalization.residualSide f :=
  normalization.explicitFormula f

end SchwartzExplicitFormulaNormalization

/--
A Schwartz explicit-formula normalization whose zero side is supplied by a
summable global zeta-zero weight.
-/
structure SchwartzGlobalExplicitFormulaNormalization extends
    SchwartzExplicitFormulaNormalization where
  globalZeroSide : SchwartzGlobalZetaZeroSide
  zeroSide_eq_globalZeroSide :
    ∀ f : SchwartzLineTestFunction,
      zeroSide f = globalZeroSide.zeroSide f

namespace SchwartzGlobalExplicitFormulaNormalization

/-- Window zero sides converge to the zero side of the normalization. -/
theorem tendsto_windowZeroSide_zeroSide
    (normalization : SchwartzGlobalExplicitFormulaNormalization)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : ℕ => normalization.globalZeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (normalization.zeroSide f)) := by
  have h :=
    normalization.globalZeroSide.tendsto_windowZeroSide exhaustion f
  simpa [normalization.zeroSide_eq_globalZeroSide f] using h

/-- Window zero sides converge to the residual side of the explicit formula. -/
theorem tendsto_windowZeroSide_residualSide
    (normalization : SchwartzGlobalExplicitFormulaNormalization)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : ℕ => normalization.globalZeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (normalization.toSchwartzExplicitFormulaNormalization.residualSide f)) := by
  have h := normalization.tendsto_windowZeroSide_zeroSide exhaustion f
  simpa [SchwartzExplicitFormulaNormalization.residualSide,
    normalization.explicitFormula f] using h

end SchwartzGlobalExplicitFormulaNormalization

/--
A local Schwartz explicit-formula criterion whose zero side is a summable global
zeta-zero side.
-/
structure SchwartzGlobalExplicitFormulaLocalCriterion
    (family : ℂ → Prop) extends
    SchwartzGlobalExplicitFormulaNormalization where
  quadraticForm : SchwartzLineTestFunction → ℝ
  quadraticForm_eq_zeroSide :
    ∀ f : SchwartzLineTestFunction, quadraticForm f = zeroSide f
  positivity_implies_RHOn :
    (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) → RHOn family

namespace SchwartzGlobalExplicitFormulaLocalCriterion

/-- Forget a global-zero-side local criterion to the ordinary Schwartz local criterion. -/
def toSchwartzExplicitFormulaLocalCriterion
    {family : ℂ → Prop}
    (criterion : SchwartzGlobalExplicitFormulaLocalCriterion family) :
    SchwartzExplicitFormulaLocalCriterion family where
  zeroSide := criterion.zeroSide
  primeSide := criterion.primeSide
  poleSide := criterion.poleSide
  gammaSide := criterion.gammaSide
  explicitFormula := criterion.explicitFormula
  quadraticForm := criterion.quadraticForm
  quadraticForm_eq_zeroSide := criterion.quadraticForm_eq_zeroSide
  positivity_implies_RHOn := criterion.positivity_implies_RHOn

/-- Positivity for a global Schwartz explicit-formula criterion proves local RH. -/
theorem RHOn
    {family : ℂ → Prop}
    (criterion : SchwartzGlobalExplicitFormulaLocalCriterion family)
    (hpos : ∀ f : SchwartzLineTestFunction, 0 ≤ criterion.quadraticForm f) :
    RHOn family :=
  RHOn.of_schwartzExplicitFormulaLocalCriterion
    criterion.toSchwartzExplicitFormulaLocalCriterion hpos

/-- Window zero sides converge to the criterion's quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    {family : ℂ → Prop}
    (criterion : SchwartzGlobalExplicitFormulaLocalCriterion family)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : ℕ => criterion.globalZeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (criterion.quadraticForm f)) := by
  have h :=
    criterion.toSchwartzGlobalExplicitFormulaNormalization
      |>.tendsto_windowZeroSide_zeroSide exhaustion f
  simpa [criterion.quadraticForm_eq_zeroSide f] using h

end SchwartzGlobalExplicitFormulaLocalCriterion

end RiemannHypothesisProject
