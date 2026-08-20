import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage2Certificate
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointOddAdditiveCertificateData

/-!
# Checked odd additive-reserve certificate for M100-DF6D5

This module transports DF6D4's live fixed-grid entry enclosures through the
exact diagonal shift and consumes the generated DF6D5 rational certificate.
The result is a checked `1 / 500` additive reserve for the concrete odd
residual target matrix.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

set_option maxRecDepth 100000

theorem suzukiDF6D5OddAdditiveTargetMatrix_apply
    (i j : Fin 44) :
    suzukiDF6D5OddAdditiveTargetMatrix i j =
      suzukiDF6D4OddResidualCertificateTargetMatrix i j -
        (((if i = j then suzukiDF6D5OddAdditiveReserve else 0) : Rat) :
          Real) := by
  by_cases hij : i = j
  · subst j
    simp [suzukiDF6D5OddAdditiveTargetMatrix]
  · simp [suzukiDF6D5OddAdditiveTargetMatrix, hij]

theorem suzukiDF6D5OddAdditiveTargetMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D5OddAdditiveTargetMatrix i j =
      suzukiDF6D5OddAdditiveTargetMatrix j i := by
  rw [suzukiDF6D5OddAdditiveTargetMatrix_apply,
    suzukiDF6D5OddAdditiveTargetMatrix_apply,
    suzukiDF6D4OddResidualCertificateTargetMatrix_symmetric]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

theorem suzukiDF6D5OddAdditiveTargetMatrix_isHermitian :
    suzukiDF6D5OddAdditiveTargetMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [star_trivial]
  exact suzukiDF6D5OddAdditiveTargetMatrix_symmetric j i

private theorem suzukiDF6D4OddResidualTargetCertificate_contains_live :
    ∀ i j : Fin 44,
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).Contains
        (suzukiDF6D4OddResidualCertificateTargetMatrix i j) := by
  apply suzukiDF6D4OddResidualTargetCertificate_contains_all_of_upper
  intro i j hij
  exact RationalInterval.contains_of_widen
    (suzukiDF6D4FixedGridOddStage2_admitted i j hij).1
    (suzukiDF6D4FixedGridOddStage2_admitted i j hij).2
    (suzukiDF6D4FixedGridOddStage2TargetEntry_contains i j)

theorem suzukiDF6D5OddAdditiveTargetEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D5OddAdditiveTargetEntryInterval i j).Contains
      (suzukiDF6D5OddAdditiveTargetMatrix i j) := by
  have hshift :=
    RationalInterval.contains_sub
      (suzukiDF6D4OddResidualTargetCertificate_contains_live i j)
      (RationalInterval.contains_point
        (if i = j then suzukiDF6D5OddAdditiveReserve else 0))
  rw [suzukiDF6D5OddAdditiveTargetMatrix_apply]
  exact hshift

theorem suzukiDF6D5OddAdditiveTargetMatrix_posSemidef :
    suzukiDF6D5OddAdditiveTargetMatrix.PosSemidef := by
  exact RationalMatrixCertificate.posSemidef_of_valid_of_entry_enclosures
    suzukiDF6D5OddAdditiveTargetCertificate
    suzukiDF6D5OddAdditiveTargetMatrix
    suzukiDF6D5OddAdditiveTargetCertificate_valid
    suzukiDF6D5OddAdditiveTargetMatrix_isHermitian
    suzukiDF6D5OddAdditiveTargetEntryInterval_contains

end

end RiemannHypothesisProject.Experiments.M100
