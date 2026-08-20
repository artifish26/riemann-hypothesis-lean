import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Symmetry of the generated M100-DF6D4 residual certificate grids

The exact certificate validity predicate checks interval order and the
Gershgorin residual inequalities, but does not itself assert symmetry.  These
small exact checks record the additional property needed to transport
upper-triangle analytic enclosures to the lower triangle.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

private theorem rationalInterval_eq_of_endpoints
    {I J : RationalInterval}
    (hlower : I.lower = J.lower) (hupper : I.upper = J.upper) :
    I = J := by
  cases I
  cases J
  simp_all

theorem suzukiDF6D4EvenResidualTargetCertificate_entry_symmetric
    (i j : Fin 45) :
    suzukiDF6D4EvenResidualTargetCertificate.entry i j =
      suzukiDF6D4EvenResidualTargetCertificate.entry j i := by
  apply rationalInterval_eq_of_endpoints <;> native_decide +revert

theorem suzukiDF6D4OddResidualTargetCertificate_entry_symmetric
    (i j : Fin 44) :
    suzukiDF6D4OddResidualTargetCertificate.entry i j =
      suzukiDF6D4OddResidualTargetCertificate.entry j i := by
  apply rationalInterval_eq_of_endpoints <;> native_decide +revert

end RiemannHypothesisProject.Experiments.M100
