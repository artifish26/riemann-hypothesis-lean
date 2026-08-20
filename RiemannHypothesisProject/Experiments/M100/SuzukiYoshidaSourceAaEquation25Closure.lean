import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaBoundaryCutoffSource
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaFormNormalization
import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25GammaTailLimit

/-!
# Equation-(2.5)-free source-`A_a` receiving surface

The B2S endpoint source and project-normalized equation-(2.5) identity now
have checked inhabitants.  This module specializes the source-`A_a` receivers
so that only the three genuinely independent source-form inputs remain
visible: the associated-form graph theorem, boundedness after domain
transport, and the smooth-core `G_a` restriction.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- The source graph theorem, transported form-norm continuity, and the
smooth-core `G_a` representation identify the supplied source operator.  This
is the direct receiver for Suzuki's closed-form construction: it does not ask
for an all-domain absolute zero-sampling theorem. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_closedFormContinuity_proved
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_closedFormSource
    A sourceForm hsourceGraph hcontinuous hcore
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)

/-- The three independent source-form inputs identify the supplied source
`A_a` with the corrected-form associated operator. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_proved
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_boundedClosedFormSource
    A sourceForm hsourceGraph hbounded hcore
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)

/-- The same closed-form source surface gives self-adjointness, with the
already checked B2S and equation-(2.5) inputs supplied internally. -/
theorem sourceAa_isSelfAdjoint_of_closedFormContinuity_proved
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm) :
    IsSelfAdjoint A :=
  sourceAa_isSelfAdjoint_of_closedFormSource
    A sourceForm hsourceGraph hcontinuous hcore
      (suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff
        suzukiProjectAStar)
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)

/-- The identified source `A_a` is self-adjoint, with B2S and equation (2.5)
supplied by their checked closure theorems. -/
theorem sourceAa_isSelfAdjoint_proved
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm) :
    IsSelfAdjoint A :=
  sourceAa_isSelfAdjoint_of_boundedClosedFormSource
    A sourceForm hsourceGraph hbounded hcore
      (suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff
        suzukiProjectAStar)
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar)

/-- On the smooth core, closed-form continuity plus the source graph and
`G_a` representation also identify the formal operator `D† G_a D` with the
independently supplied `A_a`. -/
theorem suzukiSourceBOperator_eq_sourceAa_on_core_of_closedFormContinuity_proved
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceBOperator suzukiProjectAStar_pos
        (suzukiSourceGDifferentialInAdjointDomainAt_of_source
          (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar))
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar) u⟩ =
      A
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          suzukiSmoothCore_mem_sourceAa_domain A
            ((suzukiSourceAaAssociatedSourceFormRepresentation_iff
              A sourceForm
              (suzukiSourceAaClosedFormNormalization_of_source
                sourceForm hcontinuous hcore
                  (suzukiEquation25SourceIdentityAt_proved
                    suzukiProjectAStar))).mp hsourceGraph) u⟩ :=
  suzukiSourceBOperator_eq_sourceAa_on_core_of_sourceForm
    A sourceForm hsourceGraph
      (suzukiSourceAaClosedFormNormalization_of_source
        sourceForm hcontinuous hcore
          (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar))
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar) u

/-- On every smooth primitive, the formal source operator `D† G_a D` equals
the independently supplied source `A_a`. -/
theorem suzukiSourceBOperator_eq_sourceAa_on_core_proved
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceBOperator suzukiProjectAStar_pos
        (suzukiSourceGDifferentialInAdjointDomainAt_of_source
          (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar))
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar) u⟩ =
      A
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          suzukiSmoothCore_mem_sourceAa_domain A
            ((suzukiSourceAaAssociatedSourceFormRepresentation_iff
              A sourceForm
              (suzukiSourceAaClosedFormNormalization_of_boundedSource
                sourceForm hbounded hcore
                  (suzukiEquation25SourceIdentityAt_proved
                    suzukiProjectAStar))).mp hsourceGraph) u⟩ :=
  suzukiSourceBOperator_eq_sourceAa_on_core_of_boundedClosedFormSource
    A sourceForm hsourceGraph hbounded hcore
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar) u

end

end RiemannHypothesisProject.Experiments.M100
