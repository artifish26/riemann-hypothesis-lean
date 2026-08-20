import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualRoundedCertificateEnclosures

/-!
# Bounded soundness prototype for the rounded DF6D4 certificate path

This module tests the symbolic containment route without evaluating any
certificate-admission row.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

theorem suzukiDF6D4EvenRoundedGalerkinSolveResidualInterval_contains
    (j : Fin 256) (i : Fin 45) :
    (suzukiDF6D4EvenRoundedGalerkinSolveResidualInterval j i).Contains
      (suzukiDF6D4EvenGalerkinSolveResidual j i) := by
  unfold suzukiDF6D4EvenRoundedGalerkinSolveResidualInterval
    suzukiDF6D4ResidualAdmissionRound
    suzukiDF6D4EvenGalerkinSolveResidual
  apply contains_fastRoundOut (by
    norm_num [suzukiDF6D4ResidualAdmissionDenominator])
  apply contains_sub
  · exact contains_fastRoundOut (by
      norm_num [suzukiDF6D4ResidualAdmissionDenominator])
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i j)
  · simpa only [suzukiDF6D4ResidualAdmissionRound, mul_comm] using
      contains_fastScaleFinSum
        (D := suzukiDF6D4ResidualAdmissionDenominator)
        (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
        (I := fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
          (suzukiDF6D4EvenComparisonGalerkinEntryInterval j k))
        (x := fun k : Fin 256 =>
          suzukiDF6D4EvenComparisonGalerkinEntry j k)
        (by norm_num [suzukiDF6D4ResidualAdmissionDenominator])
        (fun k => contains_fastRoundOut
          (D := suzukiDF6D4ResidualAdmissionDenominator)
          (by norm_num [suzukiDF6D4ResidualAdmissionDenominator])
          (suzukiDF6D4EvenComparisonGalerkinEntryInterval_contains j k))

end RiemannHypothesisProject.Experiments.M100
