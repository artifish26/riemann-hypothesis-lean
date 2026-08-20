import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSmoothCoreFourierDomains

/-!
# M100-DF6F operator associated to the corrected completed form

This module constructs the literal interval-`L2` operator graph represented by
the corrected completed form.  It does not assert the abstract Friedrichs
representation theorem.  Instead it supplies the concrete graph and proves
that, under equation (2.5), the checked `D† G_a D` core is contained in it.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap ComplexConjugate

local instance suzukiCorrectedFormAssociatedCompleteSpace :
    CompleteSpace (SuzukiFiniteIntervalL2 suzukiProjectAStar) := by
  infer_instance

/-- Restrict the first coordinate of the completed logarithmic graph to the
physical interval.  It is expressed canonically as the adjoint of literal
zero extension. -/
def suzukiLogRadiusLinearCompletionToFiniteIntervalL2 :
    SuzukiYoshidaCorrectedCommonFormDomain →L[Complex]
      SuzukiFiniteIntervalL2 suzukiProjectAStar :=
  (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).toContinuousLinearMap.adjoint.comp
    suzukiLogRadiusLinearCompletionToL2

/-- On smooth primitives, completed-form restriction is the existing literal
interval-`L2` embedding. -/
@[simp]
theorem suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u) =
      suzukiSmoothCoreFiniteIntervalL2LinearMap
        suzukiProjectAStar u := by
  rw [suzukiLogRadiusLinearCompletionToFiniteIntervalL2,
    ContinuousLinearMap.comp_apply,
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2,
    ← suzukiFiniteIntervalL2ZeroExtension_smoothCore]
  change ((suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).toContinuousLinearMap.adjoint.comp
        (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar).toContinuousLinearMap)
      (suzukiSmoothCoreFiniteIntervalL2LinearMap
        suzukiProjectAStar u) = _
  rw [(suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
    suzukiProjectAStar).adjoint_comp_self]
  rfl

/-- Zero extension after completed-form restriction recovers the global first
coordinate.  Equality is first checked on the dense smooth core and then
extended by continuity. -/
theorem suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction :
    (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
        suzukiProjectAStar).toContinuousLinearMap.comp
      suzukiLogRadiusLinearCompletionToFiniteIntervalL2 =
        suzukiLogRadiusLinearCompletionToL2 := by
  let f : SuzukiYoshidaCorrectedCommonFormDomain → SuzukiL2 :=
    fun v => ((suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).toContinuousLinearMap.comp
        suzukiLogRadiusLinearCompletionToFiniteIntervalL2) v
  let g : SuzukiYoshidaCorrectedCommonFormDomain → SuzukiL2 :=
    fun v => suzukiLogRadiusLinearCompletionToL2 v
  have hfg : f = g :=
    (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
      suzukiProjectAStar).equalizer
      (by exact ContinuousLinearMap.continuous _)
      (by exact ContinuousLinearMap.continuous _) (by
        funext u
        dsimp only [f, g]
        change ((suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar).toContinuousLinearMap.comp
              suzukiLogRadiusLinearCompletionToFiniteIntervalL2)
            (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
              suzukiProjectAStar u) =
          suzukiLogRadiusLinearCompletionToL2
            (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
              suzukiProjectAStar u)
        rw [ContinuousLinearMap.comp_apply,
          suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply]
        change suzukiFiniteIntervalL2ZeroExtension suzukiProjectAStar
            (suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar u) = _
        rw [suzukiFiniteIntervalL2ZeroExtension_smoothCore,
          suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2])
  apply ContinuousLinearMap.ext
  intro v
  exact congrFun hfg v

/-- The completed-form restriction into interval `L2` is injective. -/
theorem suzukiLogRadiusLinearCompletionToFiniteIntervalL2_injective :
    Function.Injective
      suzukiLogRadiusLinearCompletionToFiniteIntervalL2 := by
  intro u v huv
  apply suzukiLogRadiusLinearCompletionToL2_injective
    suzukiProjectAStar
  have hu := congrArg
    (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 => T u)
    suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
  have hv := congrArg
    (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 => T v)
    suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
  calc
    suzukiLogRadiusLinearCompletionToL2 u =
        (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar)
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) := by
      simpa using hu.symm
    _ = (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar)
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) := by
      rw [huv]
    _ = suzukiLogRadiusLinearCompletionToL2 v := by
      simpa using hv

/-- The completed form domain remains dense after restriction to interval
`L2`; the already checked smooth primitive range is contained in its range.
-/
theorem denseRange_suzukiLogRadiusLinearCompletionToFiniteIntervalL2 :
    DenseRange suzukiLogRadiusLinearCompletionToFiniteIntervalL2 := by
  apply (denseRange_suzukiSmoothCoreFiniteIntervalL2LinearMap
    suzukiProjectAStar_pos).mono
  rintro x ⟨u, rfl⟩
  exact ⟨suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
      suzukiProjectAStar u,
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply u⟩

/-- The graph relation associated with the corrected completed form: `y`
represents the functional `F(u, ·)` in physical interval `L2`. -/
def suzukiYoshidaCorrectedFormAssociatedGraph :
    Submodule Complex
      (SuzukiFiniteIntervalL2 suzukiProjectAStar ×
        SuzukiFiniteIntervalL2 suzukiProjectAStar) where
  carrier := {p | ∃ u : SuzukiYoshidaCorrectedCommonFormDomain,
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u = p.1 ∧
      ∀ v : SuzukiYoshidaCorrectedCommonFormDomain,
        inner Complex p.2
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
          suzukiYoshidaCorrectedCompleteForm u v}
  zero_mem' := by
    refine ⟨0, map_zero _, ?_⟩
    intro v
    have h := suzukiYoshidaCorrectedCompleteForm_smul_left
      (c := (0 : Complex)) (u := (0 : SuzukiYoshidaCorrectedCommonFormDomain)) v
    simpa using h.symm
  add_mem' := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
      ⟨u₁, hu₁, hpair₁⟩ ⟨u₂, hu₂, hpair₂⟩
    refine ⟨u₁ + u₂, ?_, ?_⟩
    · simpa only [Prod.fst_add, map_add] using congrArg₂ (· + ·) hu₁ hu₂
    · intro v
      simp only [Prod.snd_add, inner_add_left,
        hpair₁ v, hpair₂ v,
        suzukiYoshidaCorrectedCompleteForm_add_left]
  smul_mem' := by
    rintro c ⟨x, y⟩ ⟨u, hu, hpair⟩
    refine ⟨c • u, ?_, ?_⟩
    · change suzukiLogRadiusLinearCompletionToFiniteIntervalL2 (c • u) =
        c • x
      rw [map_smul, hu]
    · intro v
      change inner Complex (c • y)
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
        suzukiYoshidaCorrectedCompleteForm (c • u) v
      rw [inner_smul_left, hpair v,
        suzukiYoshidaCorrectedCompleteForm_smul_left]

/-- The associated relation is single-valued in its physical output. -/
theorem suzukiYoshidaCorrectedFormAssociatedGraph_singleValued
    (p : SuzukiFiniteIntervalL2 suzukiProjectAStar ×
      SuzukiFiniteIntervalL2 suzukiProjectAStar)
    (hp : p ∈ suzukiYoshidaCorrectedFormAssociatedGraph)
    (hp0 : p.1 = 0) : p.2 = 0 := by
  rcases hp with ⟨u, hu, hpair⟩
  have hu0 : u = 0 := by
    apply suzukiLogRadiusLinearCompletionToFiniteIntervalL2_injective
    rw [hu, hp0, map_zero]
  apply denseRange_suzukiLogRadiusLinearCompletionToFiniteIntervalL2
    |>.eq_zero_of_inner_left Complex
  intro v
  rw [hpair v, hu0]
  have h := suzukiYoshidaCorrectedCompleteForm_smul_left
    (c := (0 : Complex)) (u := (0 : SuzukiYoshidaCorrectedCommonFormDomain)) v
  simpa using h

/-- The concrete partially defined interval operator associated with the
corrected completed form. -/
def suzukiYoshidaCorrectedFormAssociatedOperator :
    SuzukiFiniteIntervalL2 suzukiProjectAStar →ₗ.[Complex]
      SuzukiFiniteIntervalL2 suzukiProjectAStar :=
  suzukiYoshidaCorrectedFormAssociatedGraph.toLinearPMap

@[simp]
theorem suzukiYoshidaCorrectedFormAssociatedOperator_graph :
    suzukiYoshidaCorrectedFormAssociatedOperator.graph =
      suzukiYoshidaCorrectedFormAssociatedGraph := by
  exact Submodule.toLinearPMap_graph_eq _
    suzukiYoshidaCorrectedFormAssociatedGraph_singleValued

/-- The Riesz representer already constructed for a smooth source belongs to
the full associated-form graph, not merely to its smooth-core restriction. -/
theorem suzukiCorrectedCompleteCoreIntervalRepresenter_mem_associatedGraph
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
      suzukiCorrectedCompleteCoreIntervalRepresenter u
        (suzukiSmoothCoreToL2_mem_extraLogFourierDomain
          (suzukiSmoothCoreLinearSubmoduleAsCore u))
        (suzukiSmoothCoreToL2_mem_lowLossExtraFourierDomain
          (suzukiSmoothCoreLinearSubmoduleAsCore u))) ∈
      suzukiYoshidaCorrectedFormAssociatedGraph := by
  let huExtra := suzukiSmoothCoreToL2_mem_extraLogFourierDomain
    (suzukiSmoothCoreLinearSubmoduleAsCore u)
  let huLow := suzukiSmoothCoreToL2_mem_lowLossExtraFourierDomain
    (suzukiSmoothCoreLinearSubmoduleAsCore u)
  refine ⟨suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
      suzukiProjectAStar u,
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply u, ?_⟩
  intro v
  rw [suzukiCorrectedCompleteCoreIntervalRepresenter,
    InnerProductSpace.toDual_symm_apply]
  change suzukiCorrectedCompleteCoreIntervalFunctional u huExtra huLow
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) = _
  rw [suzukiCorrectedCompleteCoreIntervalFunctional,
    ContinuousLinearMap.comp_apply]
  change (suzukiYoshidaCorrectedCompleteAmbientFunctional
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar u) huExtra huLow)
      (suzukiFiniteIntervalL2ZeroExtension suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v)) = _
  have hrecover := congrArg
    (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 =>
      T v)
    suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
  rw [show suzukiFiniteIntervalL2ZeroExtension suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
      suzukiLogRadiusLinearCompletionToL2 v by
        change (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar)
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) = _
        simpa using hrecover]
  exact suzukiYoshidaCorrectedCompleteAmbientFunctional_pairing _ _ _ _

/-- Every smooth primitive lies in the domain of the associated operator. -/
theorem suzukiSmoothCore_mem_correctedFormAssociatedOperator_domain
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u ∈
      suzukiYoshidaCorrectedFormAssociatedOperator.domain := by
  change suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u ∈
    suzukiYoshidaCorrectedFormAssociatedGraph.map
      (LinearMap.fst Complex _ _)
  refine ⟨(suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
      suzukiCorrectedCompleteCoreIntervalRepresenter u
      (suzukiSmoothCoreToL2_mem_extraLogFourierDomain
        (suzukiSmoothCoreLinearSubmoduleAsCore u))
      (suzukiSmoothCoreToL2_mem_lowLossExtraFourierDomain
        (suzukiSmoothCoreLinearSubmoduleAsCore u))),
    suzukiCorrectedCompleteCoreIntervalRepresenter_mem_associatedGraph u,
    rfl⟩

/-- On a smooth primitive, the associated operator returns the previously
constructed corrected-form Riesz representer. -/
theorem suzukiYoshidaCorrectedFormAssociatedOperator_core_apply
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiYoshidaCorrectedFormAssociatedOperator
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          suzukiSmoothCore_mem_correctedFormAssociatedOperator_domain u⟩ =
      suzukiCorrectedCompleteCoreIntervalRepresenter u
        (suzukiSmoothCoreToL2_mem_extraLogFourierDomain
          (suzukiSmoothCoreLinearSubmoduleAsCore u))
        (suzukiSmoothCoreToL2_mem_lowLossExtraFourierDomain
          (suzukiSmoothCoreLinearSubmoduleAsCore u)) := by
  have hgraph := suzukiCorrectedCompleteCoreIntervalRepresenter_mem_associatedGraph u
  rw [← suzukiYoshidaCorrectedFormAssociatedOperator_graph,
    LinearPMap.mem_graph_iff] at hgraph
  rcases hgraph with ⟨x, hx, hvalue⟩
  have hx' : x =
      ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
        suzukiSmoothCore_mem_correctedFormAssociatedOperator_domain u⟩ :=
    Subtype.ext hx
  simpa [hx'] using hvalue

/-- The associated operator is densely defined because its domain contains
the already checked dense smooth primitive range. -/
theorem dense_suzukiYoshidaCorrectedFormAssociatedOperator_domain :
    Dense (suzukiYoshidaCorrectedFormAssociatedOperator.domain :
      Set (SuzukiFiniteIntervalL2 suzukiProjectAStar)) := by
  apply (denseRange_suzukiSmoothCoreFiniteIntervalL2LinearMap
    suzukiProjectAStar_pos).mono
  rintro x ⟨u, rfl⟩
  exact suzukiSmoothCore_mem_correctedFormAssociatedOperator_domain u

/-- Hermitian symmetry of the corrected completed form makes its associated
operator symmetric on its full represented domain. -/
theorem suzukiYoshidaCorrectedFormAssociatedOperator_isFormalAdjoint :
    suzukiYoshidaCorrectedFormAssociatedOperator.IsFormalAdjoint
      suzukiYoshidaCorrectedFormAssociatedOperator := by
  intro x y
  have hx := suzukiYoshidaCorrectedFormAssociatedOperator.mem_graph x
  have hy := suzukiYoshidaCorrectedFormAssociatedOperator.mem_graph y
  rw [suzukiYoshidaCorrectedFormAssociatedOperator_graph] at hx hy
  rcases hx with ⟨u, hu, hpairu⟩
  rcases hy with ⟨v, hv, hpairv⟩
  calc
    inner Complex
        (suzukiYoshidaCorrectedFormAssociatedOperator x) (y :
          SuzukiFiniteIntervalL2 suzukiProjectAStar) =
      inner Complex
        (suzukiYoshidaCorrectedFormAssociatedOperator x)
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) := by
          rw [hv]
    _ = suzukiYoshidaCorrectedCompleteForm u v := hpairu v
    _ = conj (suzukiYoshidaCorrectedCompleteForm v u) :=
      suzukiYoshidaCorrectedCompleteForm_conj_symm u v
    _ = conj (inner Complex
        (suzukiYoshidaCorrectedFormAssociatedOperator y)
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)) := by
          rw [hpairv u]
    _ = inner Complex
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
        (suzukiYoshidaCorrectedFormAssociatedOperator y) := by
          rw [inner_conj_symm]
    _ = inner Complex (x : SuzukiFiniteIntervalL2 suzukiProjectAStar)
        (suzukiYoshidaCorrectedFormAssociatedOperator y) := by
          rw [hu]

/-- The associated operator is closable.  This is the checked symmetric-core
consequence; self-adjointness/maximality is deliberately not inferred. -/
theorem suzukiYoshidaCorrectedFormAssociatedOperator_isClosable :
    suzukiYoshidaCorrectedFormAssociatedOperator.IsClosable := by
  have hle : suzukiYoshidaCorrectedFormAssociatedOperator ≤
      suzukiYoshidaCorrectedFormAssociatedOperator† :=
    suzukiYoshidaCorrectedFormAssociatedOperator_isFormalAdjoint.le_adjoint
      dense_suzukiYoshidaCorrectedFormAssociatedOperator_domain
  exact (LinearPMap.adjoint_isClosed
    dense_suzukiYoshidaCorrectedFormAssociatedOperator_domain).isClosable
      |>.leIsClosable hle

/-- Under equation (2.5), the formal differential operator and the operator
associated with the corrected completed form agree on the whole smooth
primitive core. -/
theorem suzukiSourceBOperator_eq_correctedFormAssociatedOperator_on_core
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceBOperator suzukiProjectAStar_pos
        (suzukiSourceGDifferentialInAdjointDomainAt_of_source hsource)
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar) u⟩ =
      suzukiYoshidaCorrectedFormAssociatedOperator
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          suzukiSmoothCore_mem_correctedFormAssociatedOperator_domain u⟩ := by
  rw [suzukiYoshidaCorrectedFormAssociatedOperator_core_apply]
  apply (denseRange_suzukiSmoothCoreFiniteIntervalL2LinearMap
    suzukiProjectAStar_pos).eq_of_inner_left Complex
  intro v
  rw [inner_suzukiSourceBOperator_core_eq_correctedCompleteForm
      hsource (suzukiSourceGDifferentialInAdjointDomainAt_of_source hsource),
    inner_suzukiCorrectedCompleteCoreIntervalRepresenter_core]

end

end RiemannHypothesisProject.Experiments.M100
