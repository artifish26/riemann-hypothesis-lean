import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaActualFormCrossEstimate
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEquation25SourceClosure

/-!
# Fixed-endpoint assembly for M100-DF6D5B4

This module consumes the checked finite complex block inequalities together
with the corrected-form low, far, and cross inputs.  The final theorem keeps
the B2S form-core source and equation-(2.5) premises visible.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped ComplexConjugate

private theorem correctedCompleteForm_fintype_sum_left
    {ι : Type*} [Fintype ι]
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm (∑ i, f i) v =
      ∑ i, suzukiYoshidaCorrectedCompleteForm (f i) v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaCorrectedCompleteForm_smul_left
          (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain) v)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaCorrectedCompleteForm_add_left, ih]

private theorem correctedCompleteForm_fintype_sum_right
    {ι : Type*} [Fintype ι]
    (u : SuzukiYoshidaCorrectedCommonFormDomain)
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u (∑ i, f i) =
      ∑ i, suzukiYoshidaCorrectedCompleteForm u (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaCorrectedCompleteForm_smul_right
          (0 : Complex) u (0 : SuzukiYoshidaCorrectedCommonFormDomain))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaCorrectedCompleteForm_add_right, ih]

/-- Corrected-form normalization on the retained even source modes. -/
theorem suzukiDF6D5B4_evenLowModePairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i j : Fin 45) :
    suzukiYoshidaCorrectedCompleteForm
        ((suzukiProjectB2EndpointModeCertificateOfSource hsource).evenMode i)
        ((suzukiProjectB2EndpointModeCertificateOfSource hsource).evenMode j) =
      (suzukiDF6D4EvenEndpointMatrix i j : Complex) := by
  rw [suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq,
    suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq]
  rw [suzukiYoshidaCorrectedCompleteForm_evenSource hsource hequation25]
  have hkernel :
      suzukiYoshidaEquation25LimitKernel hsource =
        suzukiYoshidaCorrectedExplicitKernel := by
    funext m n
    exact suzukiYoshidaEquation25EndpointKernelEvaluation
      hsource hequation25 m n
  rw [hkernel]
  exact suzukiYoshidaCorrectedExplicitKernel_lowMatrixNormalization.1 i j

/-- Corrected-form normalization on the retained odd source modes. -/
theorem suzukiDF6D5B4_oddLowModePairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i j : Fin 44) :
    suzukiYoshidaCorrectedCompleteForm
        ((suzukiProjectB2EndpointModeCertificateOfSource hsource).oddMode i)
        ((suzukiProjectB2EndpointModeCertificateOfSource hsource).oddMode j) =
      (suzukiDF6D4OddEndpointMatrix i j : Complex) := by
  rw [suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq,
    suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq]
  rw [suzukiYoshidaCorrectedCompleteForm_oddSource hsource hequation25]
  have hkernel :
      suzukiYoshidaEquation25LimitKernel hsource =
        suzukiYoshidaCorrectedExplicitKernel := by
    funext m n
    exact suzukiYoshidaEquation25EndpointKernelEvaluation
      hsource hequation25 m n
  rw [hkernel]
  exact suzukiYoshidaCorrectedExplicitKernel_lowMatrixNormalization.2 i j

/-- The corrected form on the retained even reconstruction is exactly the
certified DF6D4 Hermitian quadratic. -/
theorem suzukiDF6D5B4_evenLowQuadratic
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45)) :
    (suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)).re =
      suzukiDF6D5EvenEndpointHermitianQuadratic z := by
  classical
  unfold SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
  rw [suzukiFiniteCompletionReconstruction_apply,
    correctedCompleteForm_fintype_sum_left]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_left,
    correctedCompleteForm_fintype_sum_right,
    suzukiYoshidaCorrectedCompleteForm_smul_right,
    suzukiDF6D5B4_evenLowModePairing hsource hequation25]
  simp [suzukiDF6D5EvenEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic, dotProduct, Matrix.mulVec,
    suzukiDF6D5ComplexifyMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The corrected form on the retained odd reconstruction is exactly the
certified DF6D4 Hermitian quadratic. -/
theorem suzukiDF6D5B4_oddLowQuadratic
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44)) :
    (suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)).re =
      suzukiDF6D5OddEndpointHermitianQuadratic z := by
  classical
  unfold SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
  rw [suzukiFiniteCompletionReconstruction_apply,
    correctedCompleteForm_fintype_sum_left]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_left,
    correctedCompleteForm_fintype_sum_right,
    suzukiYoshidaCorrectedCompleteForm_smul_right,
    suzukiDF6D5B4_oddLowModePairing hsource hequation25]
  simp [suzukiDF6D5OddEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic, dotProduct, Matrix.mulVec,
    suzukiDF6D5ComplexifyMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- B4 coercivity on the complete even parity block. -/
theorem suzukiDF6D5B4_evenParity_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    (1 / 400000 : Real) *
        ‖suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v)‖ ^ 2 ≤
      (suzukiYoshidaCorrectedCompleteForm
        (suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v)
        (suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v)).re := by
  let certificate := suzukiProjectB2EndpointModeCertificateOfSource hsource
  let e := suzukiLogRadiusLinearEvenProjector suzukiProjectAStar v
  let z := certificate.evenCoordinateMap e
  let far := certificate.evenParityFarRemainder v
  have hfar := (suzukiDF6D5B3FF_canonicalFarCoercivity hsource).1 far
  change 2 * ‖suzukiLogRadiusLinearCompletionToL2 far.1‖ ^ 2 ≤
    (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re at hfar
  have hcross :=
    suzukiDF6D5B3R_evenCrossEstimate hsource hequation25 z far
  change
    ‖suzukiYoshidaCorrectedCompleteForm
        (certificate.evenReconstructionCompletion z) far.1‖ ^ 2 ≤
      (5 / 2 : Real) * suzukiDF6D5EvenCouplingHermitianQuadratic z *
        (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re at hcross
  have hblock := suzukiDF6D5EvenComplexCoordinateBlock_coercive z
    (sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 far.1‖) hfar hcross
  have hlowNorm :
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.evenLowProjectionCompletion e)‖ ^ 2 =
        suzukiDF6D5ComplexCoordinateNormSq z := by
    rw [certificate.toL2_evenLowProjectionCompletion,
      suzukiFiniteL2LowProjection_norm_sq certificate.evenOrthonormal]
    unfold suzukiDF6D5ComplexCoordinateNormSq z
    apply Finset.sum_congr rfl
    intro i hi
    rw [certificate.evenCoordinateMap_apply]
  have hnorm :
      ‖suzukiLogRadiusLinearCompletionToL2 e‖ ^ 2 =
        suzukiDF6D5ComplexCoordinateNormSq z +
          ‖suzukiLogRadiusLinearCompletionToL2 far.1‖ ^ 2 := by
    rw [show e = suzukiLogRadiusLinearEvenProjector
      suzukiProjectAStar v by rfl,
      certificate.evenParity_l2_norm_sq_split v, hlowNorm]
  have hformBlock :
      suzukiDF6D5ComplexBlockFormValue
          (suzukiDF6D5EvenEndpointHermitianQuadratic z)
          (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re
          (suzukiYoshidaCorrectedCompleteForm
            (certificate.evenReconstructionCompletion z) far.1) =
        (suzukiYoshidaCorrectedCompleteForm e e).re := by
    rw [suzukiDF6D5ComplexBlockFormValue, blockSchurFormValue,
      ← suzukiDF6D5B4_evenLowQuadratic hsource hequation25 z]
    rw [← suzukiYoshidaCorrectedCompleteForm_block]
    rw [show certificate.evenReconstructionCompletion z =
        certificate.evenLowProjectionCompletion e by rfl,
      certificate.evenParityLow_add_far v]
  change (1 / 400000 : Real) *
      ‖suzukiLogRadiusLinearCompletionToL2 e‖ ^ 2 ≤
    (suzukiYoshidaCorrectedCompleteForm e e).re
  calc
    (1 / 400000 : Real) * ‖suzukiLogRadiusLinearCompletionToL2 e‖ ^ 2 =
        (1 / 400000 : Real) *
          (suzukiDF6D5ComplexCoordinateNormSq z +
            ‖suzukiLogRadiusLinearCompletionToL2 far.1‖ ^ 2) := by rw [hnorm]
    _ ≤ suzukiDF6D5ComplexBlockFormValue
          (suzukiDF6D5EvenEndpointHermitianQuadratic z)
          (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re
          (suzukiYoshidaCorrectedCompleteForm
            (certificate.evenReconstructionCompletion z) far.1) := hblock
    _ = (suzukiYoshidaCorrectedCompleteForm e e).re := hformBlock

/-- B4 coercivity on the complete odd parity block. -/
theorem suzukiDF6D5B4_oddParity_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    (1 / 400000 : Real) *
        ‖suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearOddProjector suzukiProjectAStar v)‖ ^ 2 ≤
      (suzukiYoshidaCorrectedCompleteForm
        (suzukiLogRadiusLinearOddProjector suzukiProjectAStar v)
        (suzukiLogRadiusLinearOddProjector suzukiProjectAStar v)).re := by
  let certificate := suzukiProjectB2EndpointModeCertificateOfSource hsource
  let o := suzukiLogRadiusLinearOddProjector suzukiProjectAStar v
  let z := certificate.oddCoordinateMap o
  let far := certificate.oddParityFarRemainder v
  have hfar := (suzukiDF6D5B3FF_canonicalFarCoercivity hsource).2 far
  change 2 * ‖suzukiLogRadiusLinearCompletionToL2 far.1‖ ^ 2 ≤
    (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re at hfar
  have hcross :=
    suzukiDF6D5B3R_oddCrossEstimate hsource hequation25 z far
  change
    ‖suzukiYoshidaCorrectedCompleteForm
        (certificate.oddReconstructionCompletion z) far.1‖ ^ 2 ≤
      (5 / 2 : Real) * suzukiDF6D5OddCouplingHermitianQuadratic z *
        (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re at hcross
  have hblock := suzukiDF6D5OddComplexCoordinateBlock_coercive z
    (sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 far.1‖) hfar hcross
  have hlowNorm :
      ‖suzukiLogRadiusLinearCompletionToL2
        (certificate.oddLowProjectionCompletion o)‖ ^ 2 =
        suzukiDF6D5ComplexCoordinateNormSq z := by
    rw [certificate.toL2_oddLowProjectionCompletion,
      suzukiFiniteL2LowProjection_norm_sq certificate.oddOrthonormal]
    unfold suzukiDF6D5ComplexCoordinateNormSq z
    apply Finset.sum_congr rfl
    intro i hi
    rw [certificate.oddCoordinateMap_apply]
  have hnorm :
      ‖suzukiLogRadiusLinearCompletionToL2 o‖ ^ 2 =
        suzukiDF6D5ComplexCoordinateNormSq z +
          ‖suzukiLogRadiusLinearCompletionToL2 far.1‖ ^ 2 := by
    rw [show o = suzukiLogRadiusLinearOddProjector
      suzukiProjectAStar v by rfl,
      certificate.oddParity_l2_norm_sq_split v, hlowNorm]
  have hformBlock :
      suzukiDF6D5ComplexBlockFormValue
          (suzukiDF6D5OddEndpointHermitianQuadratic z)
          (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re
          (suzukiYoshidaCorrectedCompleteForm
            (certificate.oddReconstructionCompletion z) far.1) =
        (suzukiYoshidaCorrectedCompleteForm o o).re := by
    rw [suzukiDF6D5ComplexBlockFormValue, blockSchurFormValue,
      ← suzukiDF6D5B4_oddLowQuadratic hsource hequation25 z]
    rw [← suzukiYoshidaCorrectedCompleteForm_block]
    rw [show certificate.oddReconstructionCompletion z =
        certificate.oddLowProjectionCompletion o by rfl,
      certificate.oddParityLow_add_far v]
  change (1 / 400000 : Real) *
      ‖suzukiLogRadiusLinearCompletionToL2 o‖ ^ 2 ≤
    (suzukiYoshidaCorrectedCompleteForm o o).re
  calc
    (1 / 400000 : Real) * ‖suzukiLogRadiusLinearCompletionToL2 o‖ ^ 2 =
        (1 / 400000 : Real) *
          (suzukiDF6D5ComplexCoordinateNormSq z +
            ‖suzukiLogRadiusLinearCompletionToL2 far.1‖ ^ 2) := by rw [hnorm]
    _ ≤ suzukiDF6D5ComplexBlockFormValue
          (suzukiDF6D5OddEndpointHermitianQuadratic z)
          (suzukiYoshidaCorrectedCompleteForm far.1 far.1).re
          (suzukiYoshidaCorrectedCompleteForm
            (certificate.oddReconstructionCompletion z) far.1) := hblock
    _ = (suzukiYoshidaCorrectedCompleteForm o o).re := hformBlock

/-- B4 endpoint theorem: the corrected source form satisfies the original
`1/400000` lower bound on its whole closed endpoint domain. -/
theorem suzukiDF6D5B4_fixedEndpoint_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    (1 / 400000 : Real) *
        ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 ≤
      (suzukiYoshidaCorrectedCompleteForm v v).re := by
  have heven := suzukiDF6D5B4_evenParity_coercive
    hsource hequation25 v
  have hodd := suzukiDF6D5B4_oddParity_coercive
    hsource hequation25 v
  rw [suzukiLogRadiusLinear_l2_norm_sq_even_odd_split,
    suzukiYoshidaCorrectedCompleteForm_even_odd_split,
    Complex.add_re]
  nlinarith

/-- The B4 endpoint bound no longer needs an independent equation-(2.5)
premise: the proved Gamma-tail source closure supplies it. -/
theorem suzukiDF6D5B4_fixedEndpoint_coercive_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    (1 / 400000 : Real) *
        ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 ≤
      (suzukiYoshidaCorrectedCompleteForm v v).re :=
  suzukiDF6D5B4_fixedEndpoint_coercive hsource
    (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar) v

end

end RiemannHypothesisProject.Experiments.M100
