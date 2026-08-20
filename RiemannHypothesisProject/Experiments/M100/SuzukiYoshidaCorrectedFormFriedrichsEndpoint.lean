import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaIdentification

/-!
# M100-DF6F concrete Friedrichs endpoint

This module composes the completed-domain coercivity theorem with the generic
surjectivity and maximality bridges.  The Hilbert-space instances are supplied
explicitly at the generic theorem boundary so Lean does not repeatedly
normalize the completed graph-space type during elaboration.

The two analytic source premises and the source `A_a` graph characterization
remain visible.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace LinearPMap ComplexConjugate NNReal

local instance suzukiCorrectedFormFriedrichsEndpointCompleteSpace :
    CompleteSpace (SuzukiFiniteIntervalL2 suzukiProjectAStar) := by
  infer_instance

set_option maxHeartbeats 800000 in
/-- The visible endpoint source premises make the explicit shifted-form
representative surjective. -/
theorem suzukiCorrectedShiftedFormOperatorSurjective_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiCorrectedShiftedFormOperatorSurjective := by
  rcases suzukiCorrectedShiftedFormOperatorCoercive_of_source
    hsource hequation25 with ⟨c, hc, hdiag⟩
  exact
    @continuousLinearMap_surjective_of_forall_le_norm_inner_map
      SuzukiYoshidaCorrectedCommonFormDomain
      (inferInstance : NormedAddCommGroup
        SuzukiYoshidaCorrectedCommonFormDomain)
      (inferInstance : InnerProductSpace Complex
        SuzukiYoshidaCorrectedCommonFormDomain)
      (inferInstance : CompleteSpace SuzukiYoshidaCorrectedCommonFormDomain)
      suzukiYoshidaCorrectedShiftedFormOperator c hc hdiag

/-- Under the two visible endpoint source premises, the corrected associated
operator is self-adjoint. -/
theorem suzukiYoshidaCorrectedFormAssociatedOperator_isSelfAdjoint_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    IsSelfAdjoint suzukiYoshidaCorrectedFormAssociatedOperator :=
  suzukiYoshidaCorrectedFormAssociatedOperator_isSelfAdjoint_of_shiftedFormOperatorSurjective
    (suzukiCorrectedShiftedFormOperatorSurjective_of_source
      hsource hequation25)

/-- Any independently supplied source operator with Suzuki's associated-form
graph characterization is self-adjoint under the two visible endpoint source
premises. -/
theorem sourceAa_isSelfAdjoint_of_source
    (A : SuzukiSourceAaOperator)
    (hA : SuzukiSourceAaAssociatedFormRepresentation A)
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    IsSelfAdjoint A :=
  sourceAa_isSelfAdjoint_of_shiftedFormOperatorSurjective A hA
    (suzukiCorrectedShiftedFormOperatorSurjective_of_source
      hsource hequation25)

end

end RiemannHypothesisProject.Experiments.M100
