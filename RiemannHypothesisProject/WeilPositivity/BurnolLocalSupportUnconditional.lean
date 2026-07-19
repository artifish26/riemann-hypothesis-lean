import RiemannHypothesisProject.RiemannVonMangoldt.Binet.DigammaFormula
import RiemannHypothesisProject.WeilPositivity.BurnolLocalSupport

/-!
# Unconditional Burnol fixed-support consumers

This module discharges the explicit Binet premise from the production Burnol
coefficient and fixed-support theorems using the unconditional right-half-plane
formula.  The conditional source-facing theorems remain available in their
original modules.
-/

namespace RiemannHypothesisProject

noncomputable section

open ComplexCompactExhaustion

/-- Unconditional logarithmic lower bound for the Gamma-line digamma term. -/
theorem burnolDigamma_re_lower (t B : Real)
    (ht : 2 * Real.exp (B + 4) <= |t|) :
    B <= (Complex.digamma (bellottiWongGammaLine t)).re :=
  burnolDigamma_re_lower_of_binet bennettGammaBinetDigammaFormula t B ht

/-- Unconditional coarse linear bound for Burnol's local coefficient. -/
theorem abs_burnolLocalCoefficient_le (t : Real) :
    |burnolLocalCoefficient t| <=
      (20 + |Real.log Real.pi| + |Real.log (1 / 4)| + Real.pi) + |t| :=
  abs_burnolLocalCoefficient_le_of_binet
    bennettGammaBinetDigammaFormula t

/-- Burnol's exact local coefficient is unconditionally coercive in both
directions. -/
theorem twoSidedCoercive_burnolLocalCoefficient :
    TwoSidedCoercive burnolLocalCoefficient :=
  twoSidedCoercive_burnolLocalCoefficient_of_binet
    bennettGammaBinetDigammaFormula

/-- Unconditional positive cosine correction for Burnol's local
coefficient. -/
theorem exists_burnolLocalCoefficient_cosineCorrection_unconditional :
    ∃ epsilon > 0, ∃ A ≥ 0, ∀ t : Real,
      0 <= A * Real.cos (epsilon * t) + burnolLocalCoefficient t :=
  exists_burnolLocalCoefficient_cosineCorrection_of_binet
    bennettGammaBinetDigammaFormula

namespace SchwartzLineTestFunction

/-- The local spectral integrand is unconditionally integrable for every
Schwartz test. -/
theorem integrable_burnolLocalCoefficient_mul_fourierEnergyDensity
    (g : SchwartzLineTestFunction) :
    MeasureTheory.Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t) :=
  integrable_burnolLocalCoefficient_mul_fourierEnergyDensity_of_binet
    bennettGammaBinetDigammaFormula g

/-- Unconditional additive-coordinate fixed-support positivity. -/
theorem exists_burnolFixedSupport_spectral_nonneg :
    ∃ epsilon > 0, ∃ A : Real, 0 <= A ∧
      ∀ g : SchwartzLineTestFunction,
        Function.support g ⊆
            Set.Icc (-(epsilon / (8 * Real.pi)))
              (epsilon / (8 * Real.pi)) →
        0 <= burnolLocalSpectralQuadraticForm g :=
  exists_burnolFixedSupport_spectral_nonneg_of_binet
    bennettGammaBinetDigammaFormula

/-- Unconditional multiplicative-coordinate fixed-support positivity. -/
theorem exists_burnolFixedSupport_multiplicative_nonneg :
    ∃ epsilon > 0, ∃ A : Real, 0 <= A ∧
      ∀ g : SchwartzLineTestFunction,
        Function.support (multiplicativeLogPushforward g) ⊆
            Set.Icc
              (Real.exp (-(epsilon / (8 * Real.pi))))
              (Real.exp (epsilon / (8 * Real.pi))) →
        0 <= burnolLocalSpectralQuadraticForm g :=
  exists_burnolFixedSupport_multiplicative_nonneg_of_binet
    bennettGammaBinetDigammaFormula

end SchwartzLineTestFunction

end

end RiemannHypothesisProject
