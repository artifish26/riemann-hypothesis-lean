import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage2CommonOdd
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Whole-grid odd Stage-2 diagonal admission

This module checks every live fixed-grid odd diagonal against the installed
residual-target certificate.  It is the global calibration gate used before
resuming upper-triangle row admissions.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridOddStage2Diagonals_admitted :
    forall i : Fin 44,
      (suzukiDF6D4OddResidualTargetCertificate.entry i i).lower <=
          (FixedGridInterval.toRationalInterval
            suzukiDF6D4FixedGridOddStage2Denominator
            (suzukiDF6D4FixedGridOddStage2TargetEntry i i)).lower /\
        (FixedGridInterval.toRationalInterval
          suzukiDF6D4FixedGridOddStage2Denominator
          (suzukiDF6D4FixedGridOddStage2TargetEntry i i)).upper <=
          (suzukiDF6D4OddResidualTargetCertificate.entry i i).upper := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
