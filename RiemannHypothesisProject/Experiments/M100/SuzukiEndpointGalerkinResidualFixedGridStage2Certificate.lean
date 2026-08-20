import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateConsumer
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage2AdmissionAggregate

/-!
# DF6D4 fixed-grid Stage-2 residual certificates

This module assembles the independently checked upper-triangle admissions with
the live fixed-grid containment proofs and the exact rational PSD certificates.
-/

namespace RiemannHypothesisProject.Experiments.M100

theorem suzukiDF6D4EvenResidualCertificateTargetMatrix_posSemidef :
    suzukiDF6D4EvenResidualCertificateTargetMatrix.PosSemidef := by
  apply suzukiDF6D4EvenResidualCertificateTargetMatrix_posSemidef_of_admission
    (fun i j =>
      FixedGridInterval.toRationalInterval
        suzukiDF6D4FixedGridEvenStage2Denominator
        (suzukiDF6D4FixedGridEvenStage2TargetEntry i j))
  · exact suzukiDF6D4FixedGridEvenStage2_admitted
  · exact suzukiDF6D4FixedGridEvenStage2TargetEntry_contains

theorem suzukiDF6D4OddResidualCertificateTargetMatrix_posSemidef :
    suzukiDF6D4OddResidualCertificateTargetMatrix.PosSemidef := by
  apply suzukiDF6D4OddResidualCertificateTargetMatrix_posSemidef_of_admission
    (fun i j =>
      FixedGridInterval.toRationalInterval
        suzukiDF6D4FixedGridOddStage2Denominator
        (suzukiDF6D4FixedGridOddStage2TargetEntry i j))
  · exact suzukiDF6D4FixedGridOddStage2_admitted
  · exact suzukiDF6D4FixedGridOddStage2TargetEntry_contains

end RiemannHypothesisProject.Experiments.M100
