import RiemannHypothesisProject.SchwartzGlobalExplicitFormula

/-!
# Schwartz Riemann-Weil zero-side specification

This file gives a named interface for the future Riemann-Weil zero contribution
for Schwartz test functions.

Unlike `SchwartzHeightZeroSide`, this file does not choose a toy positive
weight. Instead it records the exact data a genuine zero side must supply:
a weight on actual zeta zeroes, summability of that weight for each test
function, and the explicit-formula / positivity inputs needed to obtain local
RH through the already-checked global criterion pipeline.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/--
A candidate Riemann-Weil zero side for Schwartz test functions.

The field `weight` is intentionally left abstract. A future faithful
formalization should replace this field with the actual expression appearing in
the chosen explicit-formula normalization, then prove `summable_weight`.
-/
structure SchwartzRiemannWeilZeroSide where
  weight : SchwartzLineTestFunction → ZetaZeroSubtype → ℝ
  summable_weight :
    ∀ f : SchwartzLineTestFunction, Summable (weight f)

namespace SchwartzRiemannWeilZeroSide

/-- Forget the named Riemann-Weil zero-side spec to the generic global zero-side interface. -/
noncomputable def toGlobalZetaZeroSide
    (side : SchwartzRiemannWeilZeroSide) : SchwartzGlobalZetaZeroSide where
  weight := side.weight
  summable_weight := side.summable_weight

/-- The global zero-side value associated to the candidate Riemann-Weil zero weight. -/
noncomputable def zeroSide
    (side : SchwartzRiemannWeilZeroSide) (f : SchwartzLineTestFunction) : ℝ :=
  side.toGlobalZetaZeroSide.zeroSide f

/-- The finite-window zero side along a compact exhaustion. -/
noncomputable def windowZeroSide
    (side : SchwartzRiemannWeilZeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (f : SchwartzLineTestFunction) : ℝ :=
  side.toGlobalZetaZeroSide.windowZeroSide exhaustion n f

/-- Compact-exhaustion window sums converge to the global zero side. -/
theorem tendsto_windowZeroSide
    (side : SchwartzRiemannWeilZeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => side.windowZeroSide exhaustion n f)
      atTop (𝓝 (side.zeroSide f)) := by
  unfold windowZeroSide zeroSide
  exact side.toGlobalZetaZeroSide.tendsto_windowZeroSide exhaustion f

/--
Build a global Schwartz explicit-formula normalization from a candidate
Riemann-Weil zero side and supplied prime/pole/gamma sides.
-/
noncomputable def toGlobalExplicitFormulaNormalization
    (side : SchwartzRiemannWeilZeroSide)
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
Build a local global-Schwartz explicit-formula criterion from a candidate
Riemann-Weil zero side.

The quadratic form and positivity-to-RH theorem are supplied separately. This
keeps the future analytic positivity theorem as a visible hypothesis.
-/
noncomputable def toGlobalExplicitFormulaLocalCriterion
    {family : ℂ → Prop}
    (side : SchwartzRiemannWeilZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f)
    (quadraticForm : SchwartzLineTestFunction → ℝ)
    (quadraticForm_eq_zeroSide :
      ∀ f : SchwartzLineTestFunction, quadraticForm f = side.zeroSide f)
    (positivity_implies_RHOn :
      (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) → RHOn family) :
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
  quadraticForm := quadraticForm
  quadraticForm_eq_zeroSide := quadraticForm_eq_zeroSide
  positivity_implies_RHOn := positivity_implies_RHOn

/--
The candidate Riemann-Weil explicit-formula criterion proves local RH once the
explicit formula, quadratic-form identification, positivity, and positivity-to-RH
inputs are supplied.
-/
theorem RHOn_of_riemannWeilExplicitFormula
    {family : ℂ → Prop}
    (side : SchwartzRiemannWeilZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f)
    (quadraticForm : SchwartzLineTestFunction → ℝ)
    (quadraticForm_eq_zeroSide :
      ∀ f : SchwartzLineTestFunction, quadraticForm f = side.zeroSide f)
    (positivity_implies_RHOn :
      (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) → RHOn family)
    (hpos : ∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) :
    RHOn family := by
  let criterion :=
    side.toGlobalExplicitFormulaLocalCriterion
      primeSide poleSide gammaSide explicitFormula
      quadraticForm quadraticForm_eq_zeroSide positivity_implies_RHOn
  exact criterion.RHOn hpos

/-- Window zero sides converge to any quadratic form identified with the zero side. -/
theorem tendsto_windowZeroSide_quadraticForm
    {family : ℂ → Prop}
    (side : SchwartzRiemannWeilZeroSide)
    (primeSide poleSide gammaSide : SchwartzLineTestFunction → ℝ)
    (explicitFormula :
      ∀ f : SchwartzLineTestFunction,
        side.zeroSide f = primeSide f + poleSide f + gammaSide f)
    (quadraticForm : SchwartzLineTestFunction → ℝ)
    (quadraticForm_eq_zeroSide :
      ∀ f : SchwartzLineTestFunction, quadraticForm f = side.zeroSide f)
    (positivity_implies_RHOn :
      (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) → RHOn family)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => side.windowZeroSide exhaustion n f)
      atTop
      (𝓝 ((side.toGlobalExplicitFormulaLocalCriterion
        primeSide poleSide gammaSide explicitFormula
        quadraticForm quadraticForm_eq_zeroSide
        positivity_implies_RHOn).quadraticForm f)) := by
  change Tendsto (fun n : ℕ => side.windowZeroSide exhaustion n f)
    atTop (𝓝 (quadraticForm f))
  rw [quadraticForm_eq_zeroSide f]
  exact side.tendsto_windowZeroSide exhaustion f

end SchwartzRiemannWeilZeroSide

end RiemannHypothesisProject
