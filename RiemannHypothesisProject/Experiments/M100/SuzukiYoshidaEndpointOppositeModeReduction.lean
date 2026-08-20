import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointSourceMasterIntegrability

/-!
# Opposite-mode reduction of the endpoint master value

This module converts the remaining paired-pole master integral into the real
part of one ordinary endpoint Fourier pairing.  It uses only the checked
almost-everywhere profile identity and the exact source-variable Jacobian.
The remaining analytic theorem can therefore be attacked through the
physical translation correlation of the opposite endpoint modes.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory

/-- Integration of the almost-everywhere opposite-mode identity. -/
theorem integral_suzukiYoshidaEndpointSourceModeMasterIntegrand_eq_oppositeMode
    {r : Real} (hr : 0 < r) (n : Nat) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceModeMasterIntegrand r n z) =
      -((n : Real) * Real.pi) *
        (∫ z : Real,
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (n : Int) (-(n : Int)) z).re := by
  rw [integral_congr_ae
    (suzukiYoshidaEndpointSourceModeMasterIntegrand_ae_eq_oppositeMode
      hr n)]
  rw [integral_const_mul]
  congr 1
  simpa [Function.comp_def] using
    (integral_re
      (integrable_suzukiYoshidaEndpointSourceVariableIntegrand
        hr (n : Int) (-(n : Int))))

/-- After the exact `z = -2*pi*xi` substitution, the master integral is
`-2*n*pi^2` times the real ordinary endpoint source pairing. -/
theorem integral_suzukiYoshidaEndpointSourceModeMasterIntegrand_eq_pairing
    {r : Real} (hr : 0 < r) (n : Nat) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceModeMasterIntegrand r n z) =
      -2 * (n : Real) * Real.pi ^ 2 *
        (suzukiYoshidaEndpointSourceFourierPairing
          r (n : Int) (-(n : Int))).re := by
  rw [integral_suzukiYoshidaEndpointSourceModeMasterIntegrand_eq_oppositeMode
    hr n]
  have hjacobian :=
    congrArg Complex.re
      (two_pi_mul_suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
        hr (n : Int) (-(n : Int)))
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hjacobian
  rw [← hjacobian]
  ring

/-- Endpoint-pairing normal form of the remaining analytic value theorem. -/
def SuzukiYoshidaEndpointOppositeModeSourcePairingEvaluation : Prop :=
  ∀ n : Nat, 0 < n →
    (suzukiYoshidaEndpointSourceFourierPairing
      suzukiProjectAStar (n : Int) (-(n : Int))).re =
      -suzukiYoshidaComparisonSourceSineTransform n /
        (2 * (n : Real) * Real.pi)

/-- The endpoint-pairing evaluation supplies the value-only paired-pole
master theorem. -/
theorem suzukiYoshidaEndpointSourceModeMasterIntegralEvaluation_of_pairing
    (hevaluation :
      SuzukiYoshidaEndpointOppositeModeSourcePairingEvaluation) :
    SuzukiYoshidaEndpointSourceModeMasterIntegralEvaluation := by
  intro n hn
  rw [integral_suzukiYoshidaEndpointSourceModeMasterIntegrand_eq_pairing
    suzukiProjectAStar_pos n]
  rw [hevaluation n hn]
  have hnReal : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnReal, Real.pi_ne_zero]

end

end RiemannHypothesisProject.Experiments.M100
