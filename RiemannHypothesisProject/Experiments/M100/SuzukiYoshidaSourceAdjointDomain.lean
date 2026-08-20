import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaUnboundedDifferential
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaAmbientResidualFunctional

/-!
# M100-DF6F source adjoint-domain reduction

This module reduces the maximal-adjoint-domain gate for `D* G_a D` to the
two explicit Fourier-domain facts which make the already checked corrected
form an ambient `L2` functional against each fixed smooth source.  It uses the
literal interval-to-global zero-extension isometry; no closed-form or
Friedrichs representation theorem is assumed.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace LinearPMap

/-- The two fixed-source Fourier domains needed by the existing ambient
corrected-form functional, stated only on the smooth endpoint core. -/
def SuzukiSmoothCoreCorrectedAmbientDomainsAt
    (a : Real) : Prop :=
  ∀ u : SuzukiSmoothCoreLinearSubmodule a,
    SuzukiExtraLogFourierDomain
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap a u)) ∧
      SuzukiLowLossExtraFourierDomain
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap a u))

/-- The corrected complete form against one fixed admissible smooth source,
restricted from global `L2` to interval `L2` through literal zero extension.
-/
def suzukiCorrectedCompleteCoreIntervalFunctional
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u))) :
    SuzukiFiniteIntervalL2 suzukiProjectAStar →L[Complex] Complex :=
  (suzukiYoshidaCorrectedCompleteAmbientFunctional
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar u) huExtra huLow).comp
    (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).toContinuousLinearMap

/-- On embedded smooth primitives, the interval functional is exactly the
checked corrected complete form. -/
@[simp]
theorem suzukiCorrectedCompleteCoreIntervalFunctional_core_apply
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u))) :
    suzukiCorrectedCompleteCoreIntervalFunctional u huExtra huLow
        (suzukiSmoothCoreFiniteIntervalL2LinearMap
          suzukiProjectAStar v) =
      suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) := by
  rw [suzukiCorrectedCompleteCoreIntervalFunctional,
    ContinuousLinearMap.comp_apply]
  change (suzukiYoshidaCorrectedCompleteAmbientFunctional
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar u) huExtra huLow)
      (suzukiFiniteIntervalL2ZeroExtension suzukiProjectAStar
        (suzukiSmoothCoreFiniteIntervalL2LinearMap
          suzukiProjectAStar v)) = _
  rw [suzukiFiniteIntervalL2ZeroExtension_smoothCore,
    ← suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2 v,
    suzukiYoshidaCorrectedCompleteAmbientFunctional_pairing]

/-- Riesz representer in interval `L2` for the fixed-source corrected form.
-/
def suzukiCorrectedCompleteCoreIntervalRepresenter
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u))) :
    SuzukiFiniteIntervalL2 suzukiProjectAStar :=
  (InnerProductSpace.toDual Complex
    (SuzukiFiniteIntervalL2 suzukiProjectAStar)).symm
      (suzukiCorrectedCompleteCoreIntervalFunctional u huExtra huLow)

/-- The Riesz vector represents the corrected form on every smooth primitive.
-/
theorem inner_suzukiCorrectedCompleteCoreIntervalRepresenter_core
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (huExtra : SuzukiExtraLogFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)))
    (huLow : SuzukiLowLossExtraFourierDomain
      (suzukiLogRadiusLinearCompletionToL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u))) :
    inner Complex
        (suzukiCorrectedCompleteCoreIntervalRepresenter u huExtra huLow)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap
          suzukiProjectAStar v) =
      suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) := by
  rw [suzukiCorrectedCompleteCoreIntervalRepresenter,
    InnerProductSpace.toDual_symm_apply,
    suzukiCorrectedCompleteCoreIntervalFunctional_core_apply]

/-- Equation (2.5) plus the two elementary smooth-source Fourier domains
places every `G_a D u` in the genuine maximal adjoint domain of `D`. -/
theorem suzukiSourceGDifferentialInAdjointDomainAt_of_ambientDomains
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (hdomains : SuzukiSmoothCoreCorrectedAmbientDomainsAt
      suzukiProjectAStar) :
    SuzukiSourceGDifferentialInAdjointDomainAt
      suzukiProjectAStar suzukiProjectAStar_pos := by
  rw [suzukiSourceGDifferentialInAdjointDomainAt_iff_core]
  intro u
  rcases hdomains u with ⟨huExtra, huLow⟩
  apply LinearPMap.mem_adjoint_domain_of_exists
  refine ⟨suzukiCorrectedCompleteCoreIntervalRepresenter
    u huExtra huLow, ?_⟩
  intro x
  rcases x.2 with ⟨v, hv⟩
  have hx : x =
      ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap
          suzukiProjectAStar v,
        LinearMap.mem_range_self
          (suzukiSmoothCoreFiniteIntervalL2LinearMap
            suzukiProjectAStar) v⟩ :=
    Subtype.ext hv.symm
  rw [hx, suzukiSourceDifferentialPMap_core_apply]
  exact (inner_suzukiCorrectedCompleteCoreIntervalRepresenter_core
    u v huExtra huLow).trans
      (inner_suzukiSourceGOperator_differentials_eq_correctedCompleteForm
        hsource u v).symm

end

end RiemannHypothesisProject.Experiments.M100
