import RiemannHypothesisProject.SchwartzHeightZeroSide

/-!
# Height-sampling explicit-formula criterion

This file packages the height-sampling zero side into the global Schwartz
explicit-formula interfaces.

The construction is conditional. It assumes the explicit-formula identity and
the implication from positivity of the chosen quadratic form to local RH. Lean
then handles the bookkeeping: the zero side is a global zeta-zero `tsum`, the
quadratic form is the height-sampling zero side, positivity is automatic, and
the local RH conclusion follows.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

namespace SchwartzHeightZeroSide

/--
Build a global Schwartz explicit-formula normalization from the height-sampling
zero side and supplied prime/pole/gamma sides.
-/
noncomputable def toGlobalExplicitFormulaNormalization
    (side : SchwartzHeightZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f) :
    SchwartzGlobalExplicitFormulaNormalization where
  zeroSide := side.zeroSide
  primeSide := primeSide
  poleSide := poleSide
  gammaSide := gammaSide
  explicitFormula := explicitFormula
  globalZeroSide := side.toGlobalZetaZeroSide
  zeroSide_eq_globalZeroSide := by
    intro f
    rfl

/--
Build a local global-Schwartz explicit-formula criterion from the height-sampling
zero side.

The quadratic form is exactly the global height-sampling zero side. Its
nonnegativity is proved in `SchwartzHeightZeroSide.zeroSide_nonneg`.
-/
noncomputable def toGlobalExplicitFormulaLocalCriterion
    {family : ℂ → Prop}
    (side : SchwartzHeightZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f)
    (positivity_implies_RHOn :
      (∀ f : SchwartzLineTestFunction, 0 ≤ side.zeroSide f) → RHOn family) :
    SchwartzGlobalExplicitFormulaLocalCriterion family where
  zeroSide := side.zeroSide
  primeSide := primeSide
  poleSide := poleSide
  gammaSide := gammaSide
  explicitFormula := explicitFormula
  globalZeroSide := side.toGlobalZetaZeroSide
  zeroSide_eq_globalZeroSide := by
    intro f
    rfl
  quadraticForm := side.zeroSide
  quadraticForm_eq_zeroSide := by
    intro f
    rfl
  positivity_implies_RHOn := positivity_implies_RHOn

/--
The conditional height-sampling explicit-formula criterion proves local RH.

This theorem is intentionally honest about its hypotheses: the actual analytic
explicit formula and the RH implication must still be supplied.
-/
theorem RHOn_of_heightExplicitFormula
    {family : ℂ → Prop}
    (side : SchwartzHeightZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f)
    (positivity_implies_RHOn :
      (∀ f : SchwartzLineTestFunction, 0 ≤ side.zeroSide f) → RHOn family) :
    RHOn family := by
  let criterion :=
    side.toGlobalExplicitFormulaLocalCriterion
      primeSide poleSide gammaSide explicitFormula positivity_implies_RHOn
  exact criterion.RHOn side.zeroSide_nonneg

/--
Under the packaged criterion, compact-exhaustion energies converge to the
criterion's quadratic form.
-/
theorem tendsto_windowEnergy_quadraticForm
    {family : ℂ → Prop}
    (side : SchwartzHeightZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f)
    (positivity_implies_RHOn :
      (∀ f : SchwartzLineTestFunction, 0 ≤ side.zeroSide f) → RHOn family)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => exhaustion.schwartzZetaZeroWindowEnergy n f)
      atTop
      (𝓝 ((side.toGlobalExplicitFormulaLocalCriterion
        primeSide poleSide gammaSide explicitFormula
        positivity_implies_RHOn).quadraticForm f)) := by
  change Tendsto (fun n : ℕ => exhaustion.schwartzZetaZeroWindowEnergy n f)
    atTop (𝓝 (side.zeroSide f))
  exact side.tendsto_schwartzZetaZeroWindowEnergy exhaustion f

end SchwartzHeightZeroSide

end RiemannHypothesisProject
