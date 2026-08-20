import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualEnergyAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCompleteEnergyCoercivity

/-!
# Actual-form cross estimates for M100-DF6D5B3R

This module performs the final B3R conversion.  The B3R-E comparison-energy
cross estimates are combined with B3F-F's comparison-to-complete energy order
on the same exact parity-far receivers.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- The canonical even B3R estimate for the corrected complete form. -/
theorem suzukiDF6D5B3R_evenCrossEstimate
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiDF6D5B3TEvenCrossEstimate
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)
      suzukiYoshidaCorrectedCompleteHermitianForm := by
  intro z v
  change
    ‖suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖ ^ 2 ≤
      (5 / 2 : Real) * suzukiDF6D5EvenCouplingHermitianQuadratic z *
        (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re
  by_cases hv : v.1 = 0
  · have hcrossZero :
        suzukiYoshidaCorrectedCompleteForm
            (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
              (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1 =
          0 := by
      have hzero := suzukiYoshidaCorrectedCompleteForm_smul_right
        (0 : Complex)
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hzero
      simpa [hv] using hzero
    have hselfZero : suzukiYoshidaCorrectedCompleteForm v.1 v.1 = 0 := by
      have hzero := suzukiYoshidaCorrectedCompleteForm_smul_right
        (0 : Complex) v.1 (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hzero
      simpa [hv] using hzero
    simp [hcrossZero, hselfZero]
  · have hcross :=
      suzukiDF6D5B3REEvenComparisonEnergyCrossEstimate
        hsource hequation25 z v
    have henergy :=
      (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).1
    have hcomparison :=
      suzukiDF6D5B3FF_even_comparison_le_five_halves_complete
        henergy suzukiDF6D5B3FFPrimeBound_of_support
        (suzukiDF6D5B3FF_evenGammaRemainderBound_of_ambient hsource
          suzukiDF6D5B3FFAmbientGammaRemainderBound_proved) v
    have hvL2 : suzukiLogRadiusLinearCompletionToL2 v.1 ≠ 0 := by
      intro hzero
      apply hv
      apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
      simpa only [map_zero] using hzero
    have hvNorm : 0 < ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ :=
      norm_pos_iff.mpr hvL2
    have hcomparisonPos :
        0 < (suzukiYoshidaComparisonForm v.1 v.1).re := by
      have hfive := suzukiDF6D5B3FE_even_five_mul_norm_sq_le henergy v
      nlinarith [sq_pos_of_pos hvNorm]
    have hcoupling :
        0 ≤ suzukiDF6D5EvenCouplingHermitianQuadratic z := by
      nlinarith [sq_nonneg
        ‖suzukiYoshidaCorrectedCompleteForm
          (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
            (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖]
    calc
      ‖suzukiYoshidaCorrectedCompleteForm
          (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
            (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖ ^ 2 ≤
          suzukiDF6D5EvenCouplingHermitianQuadratic z *
            (suzukiYoshidaComparisonForm v.1 v.1).re := hcross
      _ ≤ suzukiDF6D5EvenCouplingHermitianQuadratic z *
          ((5 / 2 : Real) *
            (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re) :=
        mul_le_mul_of_nonneg_left hcomparison hcoupling
      _ = (5 / 2 : Real) * suzukiDF6D5EvenCouplingHermitianQuadratic z *
          (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re := by ring

/-- The canonical odd B3R estimate for the corrected complete form. -/
theorem suzukiDF6D5B3R_oddCrossEstimate
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiDF6D5B3TOddCrossEstimate
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)
      suzukiYoshidaCorrectedCompleteHermitianForm := by
  intro z v
  change
    ‖suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖ ^ 2 ≤
      (5 / 2 : Real) * suzukiDF6D5OddCouplingHermitianQuadratic z *
        (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re
  by_cases hv : v.1 = 0
  · have hcrossZero :
        suzukiYoshidaCorrectedCompleteForm
            (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
              (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1 =
          0 := by
      have hzero := suzukiYoshidaCorrectedCompleteForm_smul_right
        (0 : Complex)
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hzero
      simpa [hv] using hzero
    have hselfZero : suzukiYoshidaCorrectedCompleteForm v.1 v.1 = 0 := by
      have hzero := suzukiYoshidaCorrectedCompleteForm_smul_right
        (0 : Complex) v.1 (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hzero
      simpa [hv] using hzero
    simp [hcrossZero, hselfZero]
  · have hcross :=
      suzukiDF6D5B3REOddComparisonEnergyCrossEstimate
        hsource hequation25 z v
    have henergy :=
      (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).2
    have hcomparison :=
      suzukiDF6D5B3FF_odd_comparison_le_five_halves_complete
        henergy suzukiDF6D5B3FFPrimeBound_of_support
        (suzukiDF6D5B3FF_oddGammaRemainderBound_of_ambient hsource
          suzukiDF6D5B3FFAmbientGammaRemainderBound_proved) v
    have hvL2 : suzukiLogRadiusLinearCompletionToL2 v.1 ≠ 0 := by
      intro hzero
      apply hv
      apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
      simpa only [map_zero] using hzero
    have hvNorm : 0 < ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ :=
      norm_pos_iff.mpr hvL2
    have hcomparisonPos :
        0 < (suzukiYoshidaComparisonForm v.1 v.1).re := by
      have hfive := suzukiDF6D5B3FE_odd_five_mul_norm_sq_le henergy v
      nlinarith [sq_pos_of_pos hvNorm]
    have hcoupling :
        0 ≤ suzukiDF6D5OddCouplingHermitianQuadratic z := by
      nlinarith [sq_nonneg
        ‖suzukiYoshidaCorrectedCompleteForm
          (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
            (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖]
    calc
      ‖suzukiYoshidaCorrectedCompleteForm
          (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
            (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖ ^ 2 ≤
          suzukiDF6D5OddCouplingHermitianQuadratic z *
            (suzukiYoshidaComparisonForm v.1 v.1).re := hcross
      _ ≤ suzukiDF6D5OddCouplingHermitianQuadratic z *
          ((5 / 2 : Real) *
            (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re) :=
        mul_le_mul_of_nonneg_left hcomparison hcoupling
      _ = (5 / 2 : Real) * suzukiDF6D5OddCouplingHermitianQuadratic z *
          (suzukiYoshidaCorrectedCompleteForm v.1 v.1).re := by ring

/-- Paired canonical B3R endpoint, with both source premises still visible. -/
theorem suzukiDF6D5B3R_canonicalCrossEstimate
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiDF6D5B3TEvenCrossEstimate
        (suzukiProjectB2EndpointModeCertificateOfSource hsource)
        suzukiYoshidaCorrectedCompleteHermitianForm ∧
      SuzukiDF6D5B3TOddCrossEstimate
        (suzukiProjectB2EndpointModeCertificateOfSource hsource)
        suzukiYoshidaCorrectedCompleteHermitianForm :=
  ⟨suzukiDF6D5B3R_evenCrossEstimate hsource hequation25,
    suzukiDF6D5B3R_oddCrossEstimate hsource hequation25⟩

end

end RiemannHypothesisProject.Experiments.M100
