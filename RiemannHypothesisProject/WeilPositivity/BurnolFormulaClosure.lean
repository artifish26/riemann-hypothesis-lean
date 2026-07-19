import RiemannHypothesisProject.WeilPositivity.BurnolFormulaIdentification
import RiemannHypothesisProject.WeilPositivity.BurnolLocalSupportUnconditional

/-!
# Unconditional Burnol residual closure

This module composes the unconditional Binet/Burnol fixed-support theorem with
the exact Guinand-Weil residual identification. The prime-moment/PNT source
closure is deliberately not imported: it is a separate source dependency.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open ComplexCompactExhaustion

namespace SchwartzLineTestFunction

noncomputable section

/-- There is one fixed positive support radius on which the actual
prime/pole/Gamma residual is unconditionally identified with, and inherits
nonnegativity from, Burnol's local spectral form. -/
theorem exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg :
    ∃ r > 0, ∀ g : SchwartzLineTestFunction,
      Function.support g ⊆ Set.Icc (-r) r →
      Integrable (fun t : Real =>
          burnolLocalCoefficient t * fourierEnergyDensity g t) ∧
        burnolLocalSpectralQuadraticForm g =
          2 * Real.pi * guinandWeilBurnolLiteratureResidualSide g ∧
        0 ≤ guinandWeilBurnolLiteratureResidualSide g := by
  obtain ⟨epsilon, hepsilon, A, hA, hnonneg⟩ :=
    exists_burnolFixedSupport_spectral_nonneg
  let r : Real := min (epsilon / (8 * Real.pi))
    (burnolPoleDisplacement / 4)
  have hepsilonRadius : 0 < epsilon / (8 * Real.pi) := by positivity
  have hpoleRadius : 0 < burnolPoleDisplacement / 4 := by
    exact div_pos burnolPoleDisplacement_pos (by norm_num)
  have hr : 0 < r := by
    exact lt_min hepsilonRadius hpoleRadius
  refine ⟨r, hr, ?_⟩
  intro g hsupport
  have hrEpsilon : r ≤ epsilon / (8 * Real.pi) := by
    exact min_le_left _ _
  have hrPole : r ≤ burnolPoleDisplacement / 4 := by
    exact min_le_right _ _
  have hsupportEpsilon :
      Function.support g ⊆
        Set.Icc (-(epsilon / (8 * Real.pi)))
          (epsilon / (8 * Real.pi)) := by
    intro x hx
    have hxInterval := hsupport hx
    constructor
    · exact (neg_le_neg hrEpsilon).trans hxInterval.1
    · exact hxInterval.2.trans hrEpsilon
  have hcutoff : 2 * r < burnolPoleDisplacement := by
    nlinarith [burnolPoleDisplacement_pos]
  have hintegrable :=
    integrable_burnolLocalCoefficient_mul_fourierEnergyDensity g
  have hformNonneg := hnonneg g hsupportEpsilon
  have hbridge :=
    burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureResidualSide
      hsupport hcutoff hintegrable
  have hresidualNonneg :=
    guinandWeilBurnolLiteratureResidualSide_nonneg_of_burnolLocal
      hsupport hcutoff hintegrable hformNonneg
  exact ⟨hintegrable, hbridge, hresidualNonneg⟩

/-- On the same fixed support class, supplying the borrowed Guinand-Weil
source theorem identifies the nonnegative residual with the
multiplicity-aware completed-zeta zero pairing. Entirety, absolute zero-side
summability, and the formula identity remain visible in `hsource`. -/
theorem exists_burnolFixedSupport_guinandWeilBurnolLiteratureZeroSide_nonneg :
    ∃ r > 0, ∀ g : SchwartzLineTestFunction,
      Function.support g ⊆ Set.Icc (-r) r →
      BurnolGuinandWeilSourceAssumptions g →
      burnolLocalSpectralQuadraticForm g =
          2 * Real.pi * guinandWeilBurnolLiteratureZeroSide g ∧
        0 ≤ guinandWeilBurnolLiteratureZeroSide g := by
  obtain ⟨r, hr, hresidual⟩ :=
    exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg
  refine ⟨r, hr, ?_⟩
  intro g hsupport hsource
  obtain ⟨_, hbridge, hnonneg⟩ := hresidual g hsupport
  constructor
  · calc
      burnolLocalSpectralQuadraticForm g =
          2 * Real.pi * guinandWeilBurnolLiteratureResidualSide g := hbridge
      _ = 2 * Real.pi * guinandWeilBurnolLiteratureZeroSide g := by
        rw [hsource.formula]
  · rw [hsource.formula]
    exact hnonneg

end

end SchwartzLineTestFunction

end RiemannHypothesisProject
