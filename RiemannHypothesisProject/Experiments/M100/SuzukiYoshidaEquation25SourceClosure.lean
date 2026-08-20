import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25GammaTailLimit
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDiagonalArchimedeanEvaluation

/-!
# Source closure for the equation-(2.5) Yoshida endpoint kernel

This module combines the proved renormalized Gamma-tail limit with the
independently checked endpoint component evaluations.  The equation-(2.5)
source identity and the all-integer DF6D4 endpoint-kernel evaluation therefore
no longer require separate analytic hypotheses.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- The proved equation-(2.5) identity supplies the all-integer endpoint
kernel evaluation for any checked endpoint form-core source. -/
theorem suzukiYoshidaEquation25EndpointKernelEvaluation_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiYoshidaEquation25EndpointKernelEvaluation hsource :=
  suzukiYoshidaEquation25EndpointKernelEvaluation hsource
    (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)

/-- The corrected complete form on every pair of endpoint exponential modes
equals the independently normalized DF6D4 kernel. -/
theorem suzukiYoshidaCorrectedCompleteForm_exponential_eq_explicitKernel_proved
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaCorrectedExplicitKernel m n :=
  suzukiYoshidaCorrectedCompleteForm_exponential_eq_explicitKernel_of_source
    hsource (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar) m n

end

end RiemannHypothesisProject.Experiments.M100
