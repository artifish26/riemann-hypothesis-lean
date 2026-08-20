import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCompleteFormBlocks

/-!
# Actual form-coordinate normalization for M100-DF6D5B3N

This module isolates the first B3N normalization step.  It proves that
entrywise identification of the actual complete-form Yoshida-mode pairings
with a real endpoint matrix is sufficient for the corresponding finite
complex Hermitian quadratic identity.

The entrywise identities remain visible analytic theorem targets.  No broad
endpoint certificate packages or assumes them.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators ComplexConjugate

/-- The frozen finite translation remainder is conjugate-linear in its first
argument. -/
theorem suzukiProjectFiniteTranslationEnergy_smul_left
    (c : Complex) (u v : SuzukiL2) :
    suzukiL2FiniteTranslationEnergy
        (suzukiProjectPrimeIndexSet suzukiProjectAStar)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
        (c • u) v =
      conj c *
        suzukiL2FiniteTranslationEnergy
          (suzukiProjectPrimeIndexSet suzukiProjectAStar)
          suzukiProjectPrimeCoefficient suzukiProjectPrimeShift u v := by
  unfold suzukiL2FiniteTranslationEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [suzukiL2SymmetricTranslationEnergy, map_smul, inner_smul_left]
  ring

/-- The frozen finite translation remainder is linear in its second
argument. -/
theorem suzukiProjectFiniteTranslationEnergy_smul_right
    (c : Complex) (u v : SuzukiL2) :
    suzukiL2FiniteTranslationEnergy
        (suzukiProjectPrimeIndexSet suzukiProjectAStar)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
        u (c • v) =
      c *
        suzukiL2FiniteTranslationEnergy
          (suzukiProjectPrimeIndexSet suzukiProjectAStar)
          suzukiProjectPrimeCoefficient suzukiProjectPrimeShift u v := by
  unfold suzukiL2FiniteTranslationEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [suzukiL2SymmetricTranslationEnergy, map_smul, inner_smul_right]
  ring

/-- The frozen project complete form is conjugate-linear in its first
argument. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_smul_left
    (c : Complex)
    (u v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiProjectLogRadiusLinearCompleteEnergy (c • u) v =
      conj c * suzukiProjectLogRadiusLinearCompleteEnergy u v := by
  unfold suzukiProjectLogRadiusLinearCompleteEnergy
    suzukiLogRadiusLinearCompleteEnergy
    suzukiL2FiniteRadiusRemainderEnergy
    suzukiL2BoundedOperatorEnergy
  simp only [map_smul]
  rw [suzukiProjectFiniteTranslationEnergy_smul_left]
  simp [inner_smul_left]
  ring

/-- The frozen project complete form is linear in its second argument. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_smul_right
    (c : Complex)
    (u v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiProjectLogRadiusLinearCompleteEnergy u (c • v) =
      c * suzukiProjectLogRadiusLinearCompleteEnergy u v := by
  unfold suzukiProjectLogRadiusLinearCompleteEnergy
    suzukiLogRadiusLinearCompleteEnergy
    suzukiL2FiniteRadiusRemainderEnergy
    suzukiL2BoundedOperatorEnergy
  simp only [map_smul]
  rw [suzukiProjectFiniteTranslationEnergy_smul_right]
  simp [inner_smul_right]
  ring

/-- The frozen project complete form is additive in its first argument. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_add_left
    (u w v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiProjectLogRadiusLinearCompleteEnergy (u + w) v =
      suzukiProjectLogRadiusLinearCompleteEnergy u v +
        suzukiProjectLogRadiusLinearCompleteEnergy w v := by
  unfold suzukiProjectLogRadiusLinearCompleteEnergy
  exact suzukiLogRadiusLinearCompleteEnergy_add_left
    suzukiProjectAStar
    (suzukiProjectPrimeIndexSet suzukiProjectAStar)
    suzukiProjectCompleteScalar suzukiProjectPrimeCoefficient
    suzukiProjectPrimeShift
    (suzukiRSecondSourceRemainderOperator suzukiProjectAStar)
    u w v

/-- The frozen project complete form is additive in its second argument. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_add_right
    (u v w : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiProjectLogRadiusLinearCompleteEnergy u (v + w) =
      suzukiProjectLogRadiusLinearCompleteEnergy u v +
        suzukiProjectLogRadiusLinearCompleteEnergy u w := by
  unfold suzukiProjectLogRadiusLinearCompleteEnergy
  exact suzukiLogRadiusLinearCompleteEnergy_add_right
    suzukiProjectAStar
    (suzukiProjectPrimeIndexSet suzukiProjectAStar)
    suzukiProjectCompleteScalar suzukiProjectPrimeCoefficient
    suzukiProjectPrimeShift
    (suzukiRSecondSourceRemainderOperator suzukiProjectAStar)
    u v w

/-- Finite reconstruction turns the actual complete form into the full
entrywise sesquilinear sum. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_reconstruction
    {n : Nat}
    (mode : Fin n →
      SuzukiLogRadiusLinearCompletion suzukiProjectAStar)
    (x y : EuclideanSpace Complex (Fin n)) :
    suzukiProjectLogRadiusLinearCompleteEnergy
        (suzukiFiniteCompletionReconstruction mode x)
        (suzukiFiniteCompletionReconstruction mode y) =
      ∑ i, ∑ j, conj (x i) * y j *
        suzukiProjectLogRadiusLinearCompleteEnergy (mode i) (mode j) := by
  simp only [suzukiFiniteCompletionReconstruction_apply]
  let leftForm :
      SuzukiLogRadiusLinearCompletion suzukiProjectAStar →+
        Complex :=
    { toFun := fun u => suzukiProjectLogRadiusLinearCompleteEnergy
        u (∑ j, y j • mode j)
      map_zero' := by
        have h := suzukiProjectLogRadiusLinearCompleteEnergy_smul_left
          0 (0 : SuzukiLogRadiusLinearCompletion suzukiProjectAStar)
            (∑ j, y j • mode j)
        simpa using h
      map_add' := fun u w =>
        suzukiProjectLogRadiusLinearCompleteEnergy_add_left
          u w (∑ j, y j • mode j) }
  change leftForm (∑ i, x i • mode i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change suzukiProjectLogRadiusLinearCompleteEnergy
      (x i • mode i) (∑ j, y j • mode j) = _
  rw [suzukiProjectLogRadiusLinearCompleteEnergy_smul_left]
  let rightForm :
      SuzukiLogRadiusLinearCompletion suzukiProjectAStar →+
        Complex :=
    { toFun := fun v =>
        suzukiProjectLogRadiusLinearCompleteEnergy (mode i) v
      map_zero' := by
        have h := suzukiProjectLogRadiusLinearCompleteEnergy_smul_right
          0 (mode i)
            (0 : SuzukiLogRadiusLinearCompletion suzukiProjectAStar)
        simpa using h
      map_add' :=
        suzukiProjectLogRadiusLinearCompleteEnergy_add_right (mode i) }
  have hright :
      suzukiProjectLogRadiusLinearCompleteEnergy
          (mode i) (∑ j, y j • mode j) =
        ∑ j, suzukiProjectLogRadiusLinearCompleteEnergy
          (mode i) (y j • mode j) := by
    change rightForm (∑ j, y j • mode j) = _
    rw [map_sum]
    rfl
  rw [hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [suzukiProjectLogRadiusLinearCompleteEnergy_smul_right]
  ring

/-- Exact analytic target for the even endpoint entries. -/
def SuzukiDF6D5B3NEvenModePairingIdentity
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ i j : Fin 45,
    suzukiProjectLogRadiusLinearCompleteEnergy
        (certificate.evenMode i) (certificate.evenMode j) =
      (suzukiDF6D4EvenEndpointMatrix i j : Complex)

/-- Exact analytic target for the odd endpoint entries. -/
def SuzukiDF6D5B3NOddModePairingIdentity
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar) : Prop :=
  ∀ i j : Fin 44,
    suzukiProjectLogRadiusLinearCompleteEnergy
        (certificate.oddMode i) (certificate.oddMode j) =
      (suzukiDF6D4OddEndpointMatrix i j : Complex)

/-- Entrywise even mode-pairing normalization implies the full 45-dimensional
actual low-block identity. -/
theorem suzukiDF6D5B3_evenLowMatrixIdentity_of_modePairing
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar)
    (hpair : SuzukiDF6D5B3NEvenModePairingIdentity certificate) :
    SuzukiDF6D5B3EvenLowMatrixIdentity certificate := by
  intro x
  unfold SuzukiB2EndpointModeCertificate.evenActualLowValue
    SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
  rw [suzukiProjectLogRadiusLinearCompleteEnergy_reconstruction]
  unfold SuzukiDF6D5B3NEvenModePairingIdentity at hpair
  simp_rw [hpair]
  simp [suzukiDF6D5EvenEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic, dotProduct, Matrix.mulVec,
    suzukiDF6D5ComplexifyMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Entrywise odd mode-pairing normalization implies the full 44-dimensional
actual low-block identity. -/
theorem suzukiDF6D5B3_oddLowMatrixIdentity_of_modePairing
    (certificate :
      SuzukiB2EndpointModeCertificate suzukiProjectAStar)
    (hpair : SuzukiDF6D5B3NOddModePairingIdentity certificate) :
    SuzukiDF6D5B3OddLowMatrixIdentity certificate := by
  intro x
  unfold SuzukiB2EndpointModeCertificate.oddActualLowValue
    SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
  rw [suzukiProjectLogRadiusLinearCompleteEnergy_reconstruction]
  unfold SuzukiDF6D5B3NOddModePairingIdentity at hpair
  simp_rw [hpair]
  simp [suzukiDF6D5OddEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic, dotProduct, Matrix.mulVec,
    suzukiDF6D5ComplexifyMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end RiemannHypothesisProject.Experiments.M100
