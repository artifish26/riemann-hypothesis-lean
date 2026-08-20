import RiemannHypothesisProject.Experiments.M100.SuzukiSingularFourierCutoff
import RiemannHypothesisProject.Experiments.M100.Polarization

/-!
# Polarized finite reciprocal-kernel identity

This module upgrades the checked diagonal finite-cutoff Plancherel identity to
the ordered Schwartz cross-correlation.  Its Fourier side is the literal
polarized product `F(u) * conj (F(v))`, so no four-diagonal polarization remains
in the later endpoint passage.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory
open scoped ComplexConjugate FourierTransform

/-- Physical pairing of the reciprocal cutoff kernel with an ordered Schwartz
cross-correlation. -/
def suzukiReciprocalCutoffCrossCorrelationPairing
    (ε R : Real) (u v : SchwartzLineTestFunction) : Complex :=
  ∫ t : Real,
    suzukiReciprocalCutoffKernel ε R t *
      schwartzCrossCorrelation u v t

/-- Fourier pairing of the finite cosine multiplier with an ordered Schwartz
Fourier product. -/
def suzukiReciprocalCutoffPolarizedFourierPairing
    (ε R : Real) (u v : SchwartzLineTestFunction) : Complex :=
  ∫ ξ : Real,
    (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
      ((𝓕 u) ξ * conj ((𝓕 v) ξ))

/-- Ordered finite-cutoff Plancherel identity.  It uses only the honest `L¹`
reciprocal kernel and Schwartz Fourier inversion. -/
theorem suzukiReciprocalCutoffCrossCorrelationPairing_eq_fourier
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (u v : SchwartzLineTestFunction) :
    suzukiReciprocalCutoffCrossCorrelationPairing ε R u v =
      suzukiReciprocalCutoffPolarizedFourierPairing ε R u v := by
  let A : SchwartzLineTestFunction := schwartzCrossCorrelation u v
  let B : SchwartzLineTestFunction := fourierSchwartzCrossCorrelation u v
  have hinverse : (𝓕⁻ B : SchwartzLineTestFunction) = A := by
    simp [A, B, fourierSchwartzCrossCorrelation]
  have hinversePoint (t : Real) :
      A t = ∫ ξ : Real,
        Complex.exp (((2 * Real.pi * ξ * t : Real) : Complex) * Complex.I) *
          B ξ := by
    rw [← hinverse]
    rw [SchwartzMap.fourierInv_coe]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    apply congrArg (fun z : Complex => z * B ξ)
    apply congrArg Complex.exp
    push_cast
    ring
  have hk := integrable_suzukiReciprocalCutoffKernel (R := R) hε
  have hbase : Integrable (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R p.1 * B p.2)
      (volume.prod volume) :=
    hk.mul_prod B.integrable
  have hbounded : Integrable (fun p : Real × Real =>
      Complex.exp
          (((2 * Real.pi * p.2 * p.1 : Real) : Complex) * Complex.I) *
        (suzukiReciprocalCutoffKernel ε R p.1 * B p.2))
      (volume.prod volume) := by
    apply hbase.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with p
      rw [Complex.norm_exp]
      simp
  have hprod : Integrable (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R p.1 *
        (Complex.exp
            (((2 * Real.pi * p.2 * p.1 : Real) : Complex) * Complex.I) *
          B p.2)) (volume.prod volume) := by
    apply hbounded.congr
    filter_upwards with p
    ring
  unfold suzukiReciprocalCutoffCrossCorrelationPairing
    suzukiReciprocalCutoffPolarizedFourierPairing
  change (∫ t : Real,
      suzukiReciprocalCutoffKernel ε R t * A t) = _
  calc
    (∫ t : Real,
        suzukiReciprocalCutoffKernel ε R t * A t) =
        ∫ t : Real, ∫ ξ : Real,
          suzukiReciprocalCutoffKernel ε R t *
            (Complex.exp
                (((2 * Real.pi * ξ * t : Real) : Complex) * Complex.I) *
              B ξ) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hinversePoint]
      rw [integral_const_mul]
    _ = ∫ ξ : Real, ∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            (Complex.exp
                (((2 * Real.pi * ξ * t : Real) : Complex) * Complex.I) *
              B ξ) :=
      integral_integral_swap hprod
    _ = ∫ ξ : Real,
        (∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            Complex.exp
              (((2 * Real.pi * t * ξ : Real) : Complex) * Complex.I)) *
          B ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with t
      rw [show 2 * Real.pi * ξ * t =
          2 * Real.pi * t * ξ by ring]
      ring
    _ = ∫ ξ : Real,
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
          B ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [integral_suzukiReciprocalCutoffKernel_mul_exp hε hεR]
    _ = ∫ ξ : Real,
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
          ((𝓕 u) ξ * conj ((𝓕 v) ξ)) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [show B ξ = (𝓕 u) ξ * conj ((𝓕 v) ξ) by
        exact fourierSchwartzCrossCorrelation_apply u v ξ]
  rfl

end

end RiemannHypothesisProject.Experiments.M100
