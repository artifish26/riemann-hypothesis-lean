import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateSymmetry
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualHermitian

/-!
# Symmetric upper-triangle consumer for the DF6D4 residual certificates

This module isolates the final exact certificate-consumption step.  Numerical
work need only provide upper-triangle target intervals; symmetry transports those
enclosures to the lower triangle before the rational PSD checker is applied.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

private theorem certificate_contains_of_admitted_interval
    {n : Nat}
    (c : RationalMatrixCertificate n)
    (M : Matrix (Fin n) (Fin n) Real)
    (I : Fin n → Fin n → RationalInterval)
    (hadmit : ∀ i j,
      (c.entry i j).lower ≤ (I i j).lower ∧
        (I i j).upper ≤ (c.entry i j).upper)
    (hcontains : ∀ i j, (I i j).Contains (M i j))
    (i j : Fin n) :
    (c.entry i j).Contains (M i j) := by
  exact RationalInterval.contains_of_widen
    (hadmit i j).1 (hadmit i j).2 (hcontains i j)

private theorem certificate_contains_all_of_upper
    {n : Nat}
    (c : RationalMatrixCertificate n)
    (M : Matrix (Fin n) (Fin n) Real)
    (hcertificate : ∀ i j, c.entry i j = c.entry j i)
    (hmatrix : ∀ i j, M i j = M j i)
    (hupper : ∀ i j, i.val ≤ j.val → (c.entry i j).Contains (M i j)) :
    ∀ i j, (c.entry i j).Contains (M i j) := by
  intro i j
  by_cases hij : i.val ≤ j.val
  · exact hupper i j hij
  · have hji : j.val ≤ i.val := by omega
    rw [hcertificate i j, hmatrix i j]
    exact hupper j i hji

theorem suzukiDF6D4EvenResidualTargetCertificate_contains_all_of_upper
    (hupper : ∀ i j : Fin 45, i.val ≤ j.val →
      (suzukiDF6D4EvenResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4EvenResidualCertificateTargetMatrix i j)) :
    ∀ i j : Fin 45,
      (suzukiDF6D4EvenResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4EvenResidualCertificateTargetMatrix i j) := by
  exact certificate_contains_all_of_upper
    suzukiDF6D4EvenResidualTargetCertificate
    suzukiDF6D4EvenResidualCertificateTargetMatrix
    suzukiDF6D4EvenResidualTargetCertificate_entry_symmetric
    suzukiDF6D4EvenResidualCertificateTargetMatrix_symmetric
    hupper

theorem suzukiDF6D4OddResidualTargetCertificate_contains_all_of_upper
    (hupper : ∀ i j : Fin 44, i.val ≤ j.val →
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4OddResidualCertificateTargetMatrix i j)) :
    ∀ i j : Fin 44,
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4OddResidualCertificateTargetMatrix i j) := by
  exact certificate_contains_all_of_upper
    suzukiDF6D4OddResidualTargetCertificate
    suzukiDF6D4OddResidualCertificateTargetMatrix
    suzukiDF6D4OddResidualTargetCertificate_entry_symmetric
    suzukiDF6D4OddResidualCertificateTargetMatrix_symmetric
    hupper

theorem suzukiDF6D4EvenResidualCertificateTargetMatrix_posSemidef_of_upper
    (hupper : ∀ i j : Fin 45, i.val ≤ j.val →
      (suzukiDF6D4EvenResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4EvenResidualCertificateTargetMatrix i j)) :
    suzukiDF6D4EvenResidualCertificateTargetMatrix.PosSemidef := by
  exact RationalMatrixCertificate.posSemidef_of_valid_of_entry_enclosures
    suzukiDF6D4EvenResidualTargetCertificate
    suzukiDF6D4EvenResidualCertificateTargetMatrix
    suzukiDF6D4EvenResidualTargetCertificate_valid
    suzukiDF6D4EvenResidualCertificateTargetMatrix_isHermitian
    (suzukiDF6D4EvenResidualTargetCertificate_contains_all_of_upper hupper)

theorem suzukiDF6D4OddResidualCertificateTargetMatrix_posSemidef_of_upper
    (hupper : ∀ i j : Fin 44, i.val ≤ j.val →
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4OddResidualCertificateTargetMatrix i j)) :
    suzukiDF6D4OddResidualCertificateTargetMatrix.PosSemidef := by
  exact RationalMatrixCertificate.posSemidef_of_valid_of_entry_enclosures
    suzukiDF6D4OddResidualTargetCertificate
    suzukiDF6D4OddResidualCertificateTargetMatrix
    suzukiDF6D4OddResidualTargetCertificate_valid
    suzukiDF6D4OddResidualCertificateTargetMatrix_isHermitian
    (suzukiDF6D4OddResidualTargetCertificate_contains_all_of_upper hupper)

theorem suzukiDF6D4EvenResidualCertificateTargetMatrix_posSemidef_of_admission
    (I : Fin 45 → Fin 45 → RationalInterval)
    (hadmit : ∀ i j, i.val ≤ j.val →
      (suzukiDF6D4EvenResidualTargetCertificate.entry i j).lower ≤
          (I i j).lower ∧
        (I i j).upper ≤
          (suzukiDF6D4EvenResidualTargetCertificate.entry i j).upper)
    (hcontains : ∀ i j, (I i j).Contains
      (suzukiDF6D4EvenResidualCertificateTargetMatrix i j)) :
    suzukiDF6D4EvenResidualCertificateTargetMatrix.PosSemidef := by
  apply suzukiDF6D4EvenResidualCertificateTargetMatrix_posSemidef_of_upper
  intro i j hij
  exact RationalInterval.contains_of_widen
    (hadmit i j hij).1 (hadmit i j hij).2 (hcontains i j)

theorem suzukiDF6D4OddResidualCertificateTargetMatrix_posSemidef_of_admission
    (I : Fin 44 → Fin 44 → RationalInterval)
    (hadmit : ∀ i j, i.val ≤ j.val →
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).lower ≤
          (I i j).lower ∧
        (I i j).upper ≤
          (suzukiDF6D4OddResidualTargetCertificate.entry i j).upper)
    (hcontains : ∀ i j, (I i j).Contains
      (suzukiDF6D4OddResidualCertificateTargetMatrix i j)) :
    suzukiDF6D4OddResidualCertificateTargetMatrix.PosSemidef := by
  apply suzukiDF6D4OddResidualCertificateTargetMatrix_posSemidef_of_upper
  intro i j hij
  exact RationalInterval.contains_of_widen
    (hadmit i j hij).1 (hadmit i j hij).2 (hcontains i j)

end RiemannHypothesisProject.Experiments.M100
