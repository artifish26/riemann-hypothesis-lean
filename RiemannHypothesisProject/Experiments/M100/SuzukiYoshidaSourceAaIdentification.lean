import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedFormFriedrichs

/-!
# M100-DF6F source `A_a` identification

Suzuki characterizes `A_a` as the unique operator associated with the closed
localized Weil form: its graph consists exactly of the pairs `(x, y)` for
which a form-domain representative of `x` has pairing `inner y ·` against
every form-domain test vector.  This module records that source-shaped
characterization as a visible premise and identifies any operator satisfying
it with the corrected-form associated operator already constructed in Lean.

It does not assert an inhabitant of the source characterization or of the two
endpoint analytic source premises.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap ComplexConjugate

local instance suzukiSourceAaIdentificationCompleteSpace :
    CompleteSpace (SuzukiFiniteIntervalL2 suzukiProjectAStar) := by
  infer_instance

/-- The interval-`L2` operator type occupied by Suzuki's `A_a` at the frozen
project endpoint. -/
abbrev SuzukiSourceAaOperator :=
  SuzukiFiniteIntervalL2 suzukiProjectAStar →ₗ.[Complex]
    SuzukiFiniteIntervalL2 suzukiProjectAStar

/-- Source-shaped characterization of `A_a` by the graph represented by the
closed localized Weil form.  This is the exact normalization bridge that must
be checked before a source operator may be called the project's `A_a`. -/
def SuzukiSourceAaAssociatedFormRepresentation
    (A : SuzukiSourceAaOperator) : Prop :=
  A.graph = suzukiYoshidaCorrectedFormAssociatedGraph

/-- Unfold the source `A_a` characterization into the literal form-domain
pairing used by Suzuki's definition of the associated operator. -/
theorem suzukiSourceAaAssociatedFormRepresentation_iff
    (A : SuzukiSourceAaOperator) :
    SuzukiSourceAaAssociatedFormRepresentation A ↔
      ∀ p : SuzukiFiniteIntervalL2 suzukiProjectAStar ×
          SuzukiFiniteIntervalL2 suzukiProjectAStar,
        p ∈ A.graph ↔
          ∃ u : SuzukiYoshidaCorrectedCommonFormDomain,
            suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u = p.1 ∧
              ∀ v : SuzukiYoshidaCorrectedCommonFormDomain,
                inner Complex p.2
                    (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
                  suzukiYoshidaCorrectedCompleteForm u v := by
  constructor
  · intro hA p
    rw [hA]
    rfl
  · intro hA
    ext p
    exact hA p

/-- The constructed corrected-form operator satisfies the source-shaped
associated-form characterization definitionally. -/
theorem suzukiYoshidaCorrectedFormAssociatedOperator_is_sourceAa :
    SuzukiSourceAaAssociatedFormRepresentation
      suzukiYoshidaCorrectedFormAssociatedOperator :=
  suzukiYoshidaCorrectedFormAssociatedOperator_graph

/-- Any interval operator satisfying Suzuki's associated-form
characterization is the corrected-form associated operator. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator
    (A : SuzukiSourceAaOperator)
    (hA : SuzukiSourceAaAssociatedFormRepresentation A) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  LinearPMap.eq_of_eq_graph
    (hA.trans suzukiYoshidaCorrectedFormAssociatedOperator_graph.symm)

/-- The corrected-form associated operator is the unique interval operator
with Suzuki's source-shaped associated-form graph. -/
theorem existsUnique_sourceAaAssociatedFormRepresentation :
    ∃! A : SuzukiSourceAaOperator,
      SuzukiSourceAaAssociatedFormRepresentation A := by
  refine ⟨suzukiYoshidaCorrectedFormAssociatedOperator,
    suzukiYoshidaCorrectedFormAssociatedOperator_is_sourceAa, ?_⟩
  intro A hA
  exact sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator A hA

/-- Every smooth primitive lies in the domain of any source operator carrying
Suzuki's associated-form characterization. -/
theorem suzukiSmoothCore_mem_sourceAa_domain
    (A : SuzukiSourceAaOperator)
    (hA : SuzukiSourceAaAssociatedFormRepresentation A)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u ∈
      A.domain := by
  rw [sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator A hA]
  exact suzukiSmoothCore_mem_correctedFormAssociatedOperator_domain u

/-- Under equation (2.5), Suzuki's formal `B_a = D† G_a D` and every operator
carrying the source `A_a` graph characterization agree on the whole smooth
primitive core. -/
theorem suzukiSourceBOperator_eq_sourceAa_on_core
    (A : SuzukiSourceAaOperator)
    (hA : SuzukiSourceAaAssociatedFormRepresentation A)
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceBOperator suzukiProjectAStar_pos
        (suzukiSourceGDifferentialInAdjointDomainAt_of_source hsource)
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar) u⟩ =
      A
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          suzukiSmoothCore_mem_sourceAa_domain A hA u⟩ := by
  have hEq := sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator A hA
  subst A
  exact suzukiSourceBOperator_eq_correctedFormAssociatedOperator_on_core
    hsource u

/-- Once the explicit shifted-form representative is onto, every operator
with Suzuki's associated-form characterization is self-adjoint. -/
theorem sourceAa_isSelfAdjoint_of_shiftedFormOperatorSurjective
    (A : SuzukiSourceAaOperator)
    (hA : SuzukiSourceAaAssociatedFormRepresentation A)
    (hSurjective : SuzukiCorrectedShiftedFormOperatorSurjective) :
    IsSelfAdjoint A := by
  rw [sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator A hA]
  exact
    suzukiYoshidaCorrectedFormAssociatedOperator_isSelfAdjoint_of_shiftedFormOperatorSurjective
      hSurjective

end

end RiemannHypothesisProject.Experiments.M100
