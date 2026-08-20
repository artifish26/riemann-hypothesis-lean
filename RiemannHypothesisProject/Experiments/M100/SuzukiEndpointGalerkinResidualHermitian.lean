import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly

/-!
# Hermitianity of the M100-DF6D4 residual target matrices

This module isolates the algebraic symmetry required by the rational
certificate consumer.  The Galerkin-base double sum is the only nontrivial
reindexing step; the remaining matrix components are assembled separately.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private theorem symmetric_bilinear_sum
    {n m : Nat}
    (G : Fin n -> Fin n -> Real)
    (A : Fin n -> Fin m -> Real)
    (hG : forall (k l : Fin n), G k l = G l k)
    (i j : Fin m) :
    (∑ k : Fin n, A k i * ∑ l : Fin n, G k l * A l j) =
      ∑ k : Fin n, A k j * ∑ l : Fin n, G k l * A l i := by
  calc
    (∑ k : Fin n, A k i * ∑ l : Fin n, G k l * A l j) =
        ∑ k : Fin n, ∑ l : Fin n, A k i * (G k l * A l j) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ l : Fin n, ∑ k : Fin n, A k i * (G k l * A l j) :=
      Finset.sum_comm
    _ = ∑ l : Fin n, ∑ k : Fin n, A l j * (G l k * A k i) := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      rw [← hG k l]
      ring
    _ = ∑ l : Fin n, A l j * ∑ k : Fin n, G l k * A k i := by
      simp_rw [Finset.mul_sum]

private theorem galerkin_base_sum_symmetric
    {n m : Nat}
    (C : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real)
    (A : Fin n -> Fin m -> Real)
    (hG : forall (k l : Fin n), G k l = G l k)
    (i j : Fin m) :
    (Finset.univ.sum fun k : Fin n =>
        C i k * A k j +
          A k i * (C j k -
            Finset.univ.sum fun l : Fin n => G (k : Fin n) l * A l j)) =
      Finset.univ.sum fun k : Fin n =>
        C j k * A k i +
          A k j * (C i k -
            Finset.univ.sum fun l : Fin n => G (k : Fin n) l * A l i) := by
  have hcross (a b : Fin m) :
      (∑ k : Fin n, C a k * A k b) =
        ∑ k : Fin n, A k b * C a k := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hdouble :=
    symmetric_bilinear_sum (n := n) (m := m) G A hG i j
  simp_rw [mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hcross i j, hcross j i, hdouble]
  ring

theorem suzukiDF6D4EvenComparisonGalerkinEntry_symmetric
    (i j : Fin 256) :
    suzukiDF6D4EvenComparisonGalerkinEntry i j =
      suzukiDF6D4EvenComparisonGalerkinEntry j i := by
  by_cases heq : i = j
  · subst j
    rfl
  · by_cases hlt : i.val < j.val
    · have hnot : ¬j.val < i.val := by omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4EvenComparisonGalerkinEntry, heq, hneji, hlt, hnot]
    · have hgt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4EvenComparisonGalerkinEntry, heq, hneji, hlt, hgt]

theorem suzukiDF6D4OddComparisonGalerkinEntry_symmetric
    (i j : Fin 256) :
    suzukiDF6D4OddComparisonGalerkinEntry i j =
      suzukiDF6D4OddComparisonGalerkinEntry j i := by
  by_cases heq : i = j
  · subst j
    rfl
  · by_cases hlt : i.val < j.val
    · have hnot : ¬j.val < i.val := by omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4OddComparisonGalerkinEntry, heq, hneji, hlt, hnot]
    · have hgt : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      have hneji : j ≠ i := Ne.symm heq
      simp [suzukiDF6D4OddComparisonGalerkinEntry, heq, hneji, hlt, hgt]

theorem suzukiDF6D4EvenGalerkinBaseEntry_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenGalerkinBaseEntry i j =
      suzukiDF6D4EvenGalerkinBaseEntry j i := by
  simpa [suzukiDF6D4EvenGalerkinBaseEntry,
    suzukiDF6D4EvenGalerkinSolveResidual] using
    (galerkin_base_sum_symmetric
      suzukiDF6D4EvenCompleteCrossEntry
      suzukiDF6D4EvenComparisonGalerkinEntry
      (fun k i => (suzukiDF6D4EvenGalerkinApproximant k i : Real))
      suzukiDF6D4EvenComparisonGalerkinEntry_symmetric i j)

theorem suzukiDF6D4OddGalerkinBaseEntry_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddGalerkinBaseEntry i j =
      suzukiDF6D4OddGalerkinBaseEntry j i := by
  simpa [suzukiDF6D4OddGalerkinBaseEntry,
    suzukiDF6D4OddGalerkinSolveResidual] using
    (galerkin_base_sum_symmetric
      suzukiDF6D4OddCompleteCrossEntry
      suzukiDF6D4OddComparisonGalerkinEntry
      (fun k i => (suzukiDF6D4OddGalerkinApproximant k i : Real))
      suzukiDF6D4OddComparisonGalerkinEntry_symmetric i j)

theorem suzukiDF6D4EvenEndpointMatrix_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenEndpointMatrix i j =
      suzukiDF6D4EvenEndpointMatrix j i := by
  by_cases h : i.val = j.val
  · have : i = j := Fin.ext h
    subst j
    rfl
  · simp [suzukiDF6D4EvenEndpointMatrix, h, Ne.symm h, min_comm, max_comm]

theorem suzukiDF6D4OddEndpointMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddEndpointMatrix i j =
      suzukiDF6D4OddEndpointMatrix j i := by
  by_cases h : i.val = j.val
  · have : i = j := Fin.ext h
    subst j
    rfl
  · simp [suzukiDF6D4OddEndpointMatrix, h, Ne.symm h, min_comm, max_comm]

theorem suzukiDF6D4EvenFiniteResidualGramEntry_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenFiniteResidualGramEntry i j =
      suzukiDF6D4EvenFiniteResidualGramEntry j i := by
  unfold suzukiDF6D4EvenFiniteResidualGramEntry
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro k _ <;>
    ring

theorem suzukiDF6D4OddFiniteResidualGramEntry_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddFiniteResidualGramEntry i j =
      suzukiDF6D4OddFiniteResidualGramEntry j i := by
  unfold suzukiDF6D4OddFiniteResidualGramEntry
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro k _ <;>
    ring

private theorem outer_self_symmetric
    {d : Nat} (c : Real) (v : Fin d → Real) (i j : Fin d) :
    suzukiDF6D4OuterMatrix c v v i j =
      suzukiDF6D4OuterMatrix c v v j i := by
  unfold suzukiDF6D4OuterMatrix
  ring

private theorem outer_cross_pair_symmetric
    {d : Nat} (c : Real) (u v : Fin d → Real) (i j : Fin d) :
    (suzukiDF6D4OuterMatrix c u v +
        suzukiDF6D4OuterMatrix c v u) i j =
      (suzukiDF6D4OuterMatrix c u v +
        suzukiDF6D4OuterMatrix c v u) j i := by
  simp only [Matrix.add_apply, suzukiDF6D4OuterMatrix]
  ring

private theorem diagonal_envelope_symmetric
    {d : Nat} (c : Real) (v : Fin d → Real) (i j : Fin d) :
    suzukiDF6D4DiagonalEnvelopeMatrix c v i j =
      suzukiDF6D4DiagonalEnvelopeMatrix c v j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp [suzukiDF6D4DiagonalEnvelopeMatrix, h, Ne.symm h]

theorem suzukiDF6D4EvenResidualTailMainMatrix_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenResidualTailMainMatrix i j =
      suzukiDF6D4EvenResidualTailMainMatrix j i := by
  unfold suzukiDF6D4EvenResidualTailMainMatrix
  simp only [Matrix.add_apply, suzukiDF6D4OuterMatrix]
  ring

theorem suzukiDF6D4OddResidualTailMainMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddResidualTailMainMatrix i j =
      suzukiDF6D4OddResidualTailMainMatrix j i := by
  exact outer_self_symmetric
    suzukiDF6D4OddTailMainCoefficient
    (suzukiDF6D4OddResidualTailFixedMoment 0) i j

theorem suzukiDF6D4EvenStructuredTailContributionMatrix_symmetric
    (index : Fin 15) (i j : Fin 45) :
    suzukiDF6D4EvenStructuredTailContributionMatrix index i j =
      suzukiDF6D4EvenStructuredTailContributionMatrix index j i := by
  unfold suzukiDF6D4EvenStructuredTailContributionMatrix
  split_ifs <;> simp only [suzukiDF6D4OuterMatrix] <;> ring

theorem suzukiDF6D4OddStructuredTailContributionMatrix_symmetric
    (index : Fin 14) (i j : Fin 44) :
    suzukiDF6D4OddStructuredTailContributionMatrix index i j =
      suzukiDF6D4OddStructuredTailContributionMatrix index j i := by
  unfold suzukiDF6D4OddStructuredTailContributionMatrix
  simp only
  split_ifs <;> simp only [suzukiDF6D4OuterMatrix] <;> ring

theorem suzukiDF6D4EvenAnalyticTailMatrix_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenAnalyticTailMatrix i j =
      suzukiDF6D4EvenAnalyticTailMatrix j i := by
  have hmain := suzukiDF6D4EvenResidualTailMainMatrix_symmetric i j
  have hstructured :
      suzukiDF6D4EvenStructuredTailMatrix i j =
        suzukiDF6D4EvenStructuredTailMatrix j i := by
    unfold suzukiDF6D4EvenStructuredTailMatrix
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    exact suzukiDF6D4EvenStructuredTailContributionMatrix_symmetric index i j
  have hgeometric :
      suzukiDF6D4EvenGeometricTailMatrix i j =
        suzukiDF6D4EvenGeometricTailMatrix j i := by
    exact diagonal_envelope_symmetric
      (suzukiDF6D4GeometricTailCoefficient
        suzukiDF6D4EvenResidualGeometricEnvelope)
      suzukiDF6D4EvenResidualGeometricEnvelope i j
  unfold suzukiDF6D4EvenAnalyticTailMatrix
    suzukiDF6D4EvenResidualRemainderTailMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hmain, hstructured, hgeometric]

theorem suzukiDF6D4OddAnalyticTailMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddAnalyticTailMatrix i j =
      suzukiDF6D4OddAnalyticTailMatrix j i := by
  have hmain := suzukiDF6D4OddResidualTailMainMatrix_symmetric i j
  have hstructured :
      suzukiDF6D4OddStructuredTailMatrix i j =
        suzukiDF6D4OddStructuredTailMatrix j i := by
    unfold suzukiDF6D4OddStructuredTailMatrix
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro index _
    exact suzukiDF6D4OddStructuredTailContributionMatrix_symmetric index i j
  have hgeometric :
      suzukiDF6D4OddGeometricTailMatrix i j =
        suzukiDF6D4OddGeometricTailMatrix j i := by
    exact diagonal_envelope_symmetric
      (suzukiDF6D4GeometricTailCoefficient
        suzukiDF6D4OddResidualGeometricEnvelope)
      suzukiDF6D4OddResidualGeometricEnvelope i j
  unfold suzukiDF6D4OddAnalyticTailMatrix
    suzukiDF6D4OddResidualRemainderTailMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hmain, hstructured, hgeometric]

theorem suzukiDF6D4EvenCouplingUpperMatrix_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenCouplingUpperMatrix i j =
      suzukiDF6D4EvenCouplingUpperMatrix j i := by
  unfold suzukiDF6D4EvenCouplingUpperMatrix
    suzukiDF6D4EvenGalerkinBaseMatrix
    suzukiDF6D4EvenFiniteResidualGramMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [suzukiDF6D4EvenGalerkinBaseEntry_symmetric,
    suzukiDF6D4EvenFiniteResidualGramEntry_symmetric,
    suzukiDF6D4EvenAnalyticTailMatrix_symmetric]

theorem suzukiDF6D4OddCouplingUpperMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddCouplingUpperMatrix i j =
      suzukiDF6D4OddCouplingUpperMatrix j i := by
  unfold suzukiDF6D4OddCouplingUpperMatrix
    suzukiDF6D4OddGalerkinBaseMatrix
    suzukiDF6D4OddFiniteResidualGramMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [suzukiDF6D4OddGalerkinBaseEntry_symmetric,
    suzukiDF6D4OddFiniteResidualGramEntry_symmetric,
    suzukiDF6D4OddAnalyticTailMatrix_symmetric]

theorem suzukiDF6D4EvenResidualCertificateTargetMatrix_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenResidualCertificateTargetMatrix i j =
      suzukiDF6D4EvenResidualCertificateTargetMatrix j i := by
  unfold suzukiDF6D4EvenResidualCertificateTargetMatrix
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [suzukiDF6D4EvenEndpointMatrix_symmetric,
    suzukiDF6D4EvenCouplingUpperMatrix_symmetric]

theorem suzukiDF6D4OddResidualCertificateTargetMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddResidualCertificateTargetMatrix i j =
      suzukiDF6D4OddResidualCertificateTargetMatrix j i := by
  unfold suzukiDF6D4OddResidualCertificateTargetMatrix
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [suzukiDF6D4OddEndpointMatrix_symmetric,
    suzukiDF6D4OddCouplingUpperMatrix_symmetric]

theorem suzukiDF6D4EvenResidualCertificateTargetMatrix_isHermitian :
    suzukiDF6D4EvenResidualCertificateTargetMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  exact suzukiDF6D4EvenResidualCertificateTargetMatrix_symmetric j i

theorem suzukiDF6D4OddResidualCertificateTargetMatrix_isHermitian :
    suzukiDF6D4OddResidualCertificateTargetMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  exact suzukiDF6D4OddResidualCertificateTargetMatrix_symmetric j i

end

end RiemannHypothesisProject.Experiments.M100
