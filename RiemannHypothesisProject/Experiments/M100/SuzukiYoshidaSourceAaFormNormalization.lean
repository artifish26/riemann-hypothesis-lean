import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedFormFriedrichsEndpoint

/-!
# M100-DF6F source `A_a` form normalization

Suzuki defines `A_a` independently as the operator associated with the closed
localized Weil form.  The project has separately constructed the operator
associated with its corrected completed form.  These are two logically
different inputs: the source theorem characterizing `A_a` by a source form,
and the normalization theorem identifying that source form with the project's
completed form.

This module keeps those inputs separate and proves the exact bridge to
`SuzukiSourceAaAssociatedFormRepresentation`.  It does not define the source
operator by the project graph and does not assume the two forms equal inside
an omnibus endpoint record.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

/-- Type of a source-side sesquilinear form after transporting its closed form
domain to the project's completed logarithmic domain. -/
abbrev SuzukiSourceAaClosedForm :=
  SuzukiYoshidaCorrectedCommonFormDomain →
    SuzukiYoshidaCorrectedCommonFormDomain → Complex

/-- Source-theorem layer: `A_a` is the operator represented by a specified
closed localized Weil form.  This is Suzuki's characterization from the
paragraph preceding Lemma 3.1, with the domain transport still explicit in
the choice of `sourceForm`. -/
def SuzukiSourceAaAssociatedSourceFormRepresentation
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm) : Prop :=
  ∀ p : SuzukiFiniteIntervalL2 suzukiProjectAStar ×
      SuzukiFiniteIntervalL2 suzukiProjectAStar,
    p ∈ A.graph ↔
      ∃ u : SuzukiYoshidaCorrectedCommonFormDomain,
        suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u = p.1 ∧
          ∀ v : SuzukiYoshidaCorrectedCommonFormDomain,
            inner Complex p.2
                (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
              sourceForm u v

/-- Normalization/window bridge: the transported source closed form is the
project's corrected completed form on the whole completed domain. -/
def SuzukiSourceAaClosedFormNormalization
    (sourceForm : SuzukiSourceAaClosedForm) : Prop :=
  ∀ u v : SuzukiYoshidaCorrectedCommonFormDomain,
    sourceForm u v = suzukiYoshidaCorrectedCompleteForm u v

/-- Source-form continuity after transporting its form domain to the project
completion.  Closed lower-bounded forms acquire this continuity in their form
norm; it remains explicit here because the source-domain transport is the
analytic input. -/
def SuzukiSourceAaClosedFormJointContinuous
    (sourceForm : SuzukiSourceAaClosedForm) : Prop :=
  Continuous (Function.uncurry sourceForm)

/-- Concrete bounded-form interface for the transported source form.  A
complex sesquilinear form is real bilinear; after transport to the source form
norm, the usual bounded-form estimate is exactly Mathlib's bounded real
bilinear-map predicate. -/
def SuzukiSourceAaClosedFormBoundedRealBilinear
    (sourceForm : SuzukiSourceAaClosedForm) : Prop :=
  IsBoundedBilinearMap ℝ (Function.uncurry sourceForm)

/-- A bounded transported source form is jointly continuous. -/
theorem suzukiSourceAaClosedFormJointContinuous_of_boundedRealBilinear
    (sourceForm : SuzukiSourceAaClosedForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm) :
    SuzukiSourceAaClosedFormJointContinuous sourceForm :=
  hbounded.continuous

/-- Source restriction on the dense smooth core: the transported localized
Weil form is the ordinary source `G_a` pairing of the two differentials. -/
def SuzukiSourceAaClosedFormCoreGRepresentation
    (sourceForm : SuzukiSourceAaClosedForm) : Prop :=
  ∀ u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
    sourceForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) =
      inner Complex
        (suzukiSourceGOperator suzukiProjectAStar
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap
            suzukiProjectAStar_pos u))
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap
          suzukiProjectAStar_pos v)

/-- Equation (2.5) turns the source `G_a` core restriction into the exact
project corrected-form identity on the dense smooth core. -/
theorem suzukiSourceAaClosedForm_coreNormalization_of_equation25
    (sourceForm : SuzukiSourceAaClosedForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    sourceForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) =
      suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) := by
  exact (hcore u v).trans
    (inner_suzukiSourceGOperator_differentials_eq_correctedCompleteForm
      hequation25 u v)

/-- Joint continuity and equality on the dense smooth core promote the source
form normalization to the whole completed domain. -/
theorem suzukiSourceAaClosedFormNormalization_of_core
    (sourceForm : SuzukiSourceAaClosedForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : ∀ u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
      sourceForm
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar u)
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar v) =
        suzukiYoshidaCorrectedCompleteForm
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar u)
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar v)) :
    SuzukiSourceAaClosedFormNormalization sourceForm := by
  intro x y
  let coreMap :=
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
      suzukiProjectAStar
  have hdense : DenseRange coreMap :=
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
      suzukiProjectAStar
  have hdenseProd : DenseRange
      (fun p : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar ×
          SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar =>
        (coreMap p.1, coreMap p.2)) :=
    hdense.prodMap hdense
  have hforms : Function.uncurry sourceForm =
      Function.uncurry suzukiYoshidaCorrectedCompleteForm :=
    hdenseProd.equalizer hcontinuous
      suzukiYoshidaCorrectedCompleteForm_jointContinuous (by
        funext p
        exact hcore p.1 p.2)
  exact congrFun hforms (x, y)

/-- Literature-shaped endpoint: source core representation, source form-norm
continuity, and equation (2.5) suffice for the full source-to-project form
normalization. -/
theorem suzukiSourceAaClosedFormNormalization_of_source
    (sourceForm : SuzukiSourceAaClosedForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiSourceAaClosedFormNormalization sourceForm := by
  apply suzukiSourceAaClosedFormNormalization_of_core
    sourceForm hcontinuous
  exact suzukiSourceAaClosedForm_coreNormalization_of_equation25
    sourceForm hcore hequation25

/-- Bounded-form version of the source normalization endpoint. -/
theorem suzukiSourceAaClosedFormNormalization_of_boundedSource
    (sourceForm : SuzukiSourceAaClosedForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiSourceAaClosedFormNormalization sourceForm := by
  exact suzukiSourceAaClosedFormNormalization_of_source sourceForm
    (suzukiSourceAaClosedFormJointContinuous_of_boundedRealBilinear
      sourceForm hbounded)
    hcore hequation25

/-- Once the source form is normalized, Suzuki's source graph
characterization is exactly the project graph characterization. -/
theorem suzukiSourceAaAssociatedSourceFormRepresentation_iff
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hnormalization : SuzukiSourceAaClosedFormNormalization sourceForm) :
    SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm ↔
      SuzukiSourceAaAssociatedFormRepresentation A := by
  rw [suzukiSourceAaAssociatedFormRepresentation_iff]
  unfold SuzukiSourceAaAssociatedSourceFormRepresentation
  constructor
  · intro hsourceGraph p
    rw [hsourceGraph p]
    constructor
    · rintro ⟨u, hu, hpair⟩
      exact ⟨u, hu, fun v => (hpair v).trans (hnormalization u v)⟩
    · rintro ⟨u, hu, hpair⟩
      exact ⟨u, hu, fun v => (hpair v).trans (hnormalization u v).symm⟩
  · intro hprojectGraph p
    rw [hprojectGraph p]
    constructor
    · rintro ⟨u, hu, hpair⟩
      exact ⟨u, hu, fun v => (hpair v).trans (hnormalization u v).symm⟩
    · rintro ⟨u, hu, hpair⟩
      exact ⟨u, hu, fun v => (hpair v).trans (hnormalization u v)⟩

/-- The separated source theorem and form normalization identify the source
operator with the checked corrected-form realization. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_sourceForm
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hnormalization : SuzukiSourceAaClosedFormNormalization sourceForm) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator := by
  apply sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator
  exact (suzukiSourceAaAssociatedSourceFormRepresentation_iff
    A sourceForm hnormalization).mp hsourceGraph

/-- Full self-adjointness endpoint with the source graph theorem and the
source-to-project form normalization still separate from the two analytic
endpoint premises. -/
theorem sourceAa_isSelfAdjoint_of_sourceForm
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hnormalization : SuzukiSourceAaClosedFormNormalization sourceForm)
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    IsSelfAdjoint A := by
  exact sourceAa_isSelfAdjoint_of_source A
    ((suzukiSourceAaAssociatedSourceFormRepresentation_iff
      A sourceForm hnormalization).mp hsourceGraph)
    hsource hequation25

/-- Under the same two identification inputs, the formal source operator
`D† G_a D` agrees with the independently supplied `A_a` on every smooth
primitive. -/
theorem suzukiSourceBOperator_eq_sourceAa_on_core_of_sourceForm
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hnormalization : SuzukiSourceAaClosedFormNormalization sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceBOperator suzukiProjectAStar_pos
        (suzukiSourceGDifferentialInAdjointDomainAt_of_source hequation25)
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          LinearMap.mem_range_self
            (suzukiSmoothCoreFiniteIntervalL2LinearMap
              suzukiProjectAStar) u⟩ =
      A
        ⟨suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u,
          suzukiSmoothCore_mem_sourceAa_domain A
            ((suzukiSourceAaAssociatedSourceFormRepresentation_iff
              A sourceForm hnormalization).mp hsourceGraph) u⟩ := by
  exact suzukiSourceBOperator_eq_sourceAa_on_core A
    ((suzukiSourceAaAssociatedSourceFormRepresentation_iff
      A sourceForm hnormalization).mp hsourceGraph)
    hequation25 u

/-- Direct source-shaped identification endpoint: the source graph theorem,
form-norm continuity, the smooth `G_a` restriction, and equation (2.5)
identify the independently supplied `A_a` with the project realization. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_closedFormSource
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator := by
  exact
    sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_sourceForm
      A sourceForm hsourceGraph
      (suzukiSourceAaClosedFormNormalization_of_source
        sourceForm hcontinuous hcore hequation25)

/-- Direct self-adjointness endpoint with all source inputs visible. -/
theorem sourceAa_isSelfAdjoint_of_closedFormSource
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hcontinuous : SuzukiSourceAaClosedFormJointContinuous sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    IsSelfAdjoint A := by
  exact sourceAa_isSelfAdjoint_of_sourceForm A sourceForm hsourceGraph
    (suzukiSourceAaClosedFormNormalization_of_source
      sourceForm hcontinuous hcore hequation25)
    hsource hequation25

/-- Direct source-shaped identification endpoint using the usual bounded-form
interface instead of a bare joint-continuity hypothesis. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_boundedClosedFormSource
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator := by
  exact
    sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_closedFormSource
      A sourceForm hsourceGraph
      (suzukiSourceAaClosedFormJointContinuous_of_boundedRealBilinear
        sourceForm hbounded)
      hcore hequation25

/-- Direct self-adjointness endpoint using the bounded transported source
form. -/
theorem sourceAa_isSelfAdjoint_of_boundedClosedFormSource
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    IsSelfAdjoint A := by
  exact sourceAa_isSelfAdjoint_of_closedFormSource A sourceForm hsourceGraph
    (suzukiSourceAaClosedFormJointContinuous_of_boundedRealBilinear
      sourceForm hbounded)
    hcore hsource hequation25

/-- Direct smooth-core source-operator endpoint using the bounded transported
source form.  This is the source-facing `D† G_a D = A_a` statement with no
all-domain normalization premise. -/
theorem suzukiSourceBOperator_eq_sourceAa_on_core_of_boundedClosedFormSource
    (A : SuzukiSourceAaOperator)
    (sourceForm : SuzukiSourceAaClosedForm)
    (hsourceGraph :
      SuzukiSourceAaAssociatedSourceFormRepresentation A sourceForm)
    (hbounded : SuzukiSourceAaClosedFormBoundedRealBilinear sourceForm)
    (hcore : SuzukiSourceAaClosedFormCoreGRepresentation sourceForm)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceBOperator suzukiProjectAStar_pos
        (suzukiSourceGDifferentialInAdjointDomainAt_of_source hequation25)
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
                sourceForm hbounded hcore hequation25)).mp hsourceGraph) u⟩ := by
  exact suzukiSourceBOperator_eq_sourceAa_on_core_of_sourceForm
    A sourceForm hsourceGraph
    (suzukiSourceAaClosedFormNormalization_of_boundedSource
      sourceForm hbounded hcore hequation25)
    hequation25 u

end

end RiemannHypothesisProject.Experiments.M100
