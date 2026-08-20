import RiemannHypothesisProject.Experiments.M100.SuzukiLogRadiusCompletion
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# M100-DF6D5B0 linear logarithmic radius completion

The DF6D2 completion is a set closure inside the graph of the logarithmic
Fourier multiplier.  Its ordinary product norm is complete, but that
presentation does not expose a complex module or an inner-product structure.

This module gives an equivalent closed-submodule presentation in the
`WithLp 2` product of the two global `L²` factors.  The resulting radius
completion is a complex Hilbert space.  The identity on the two graph
coordinates is a homeomorphism to the DF6D2 completion, the smooth core is
dense, the first coordinate is a continuous injective `L²` embedding, and
zero extension is an isometric complex-linear map.

No parity decomposition, Yoshida mode, finite projection, or endpoint
coercivity statement is introduced here; those belong to DF6D5B1 and later.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- The exact smooth core as a complex submodule of the Schwartz space. -/
def SuzukiSmoothCoreLinearSubmodule (r : Real) :
    Submodule Complex SchwartzLineTestFunction where
  carrier := {v | Function.support v ⊆ Set.Ioo (-r) r}
  zero_mem' := by
    simp [Function.support]
  add_mem' := by
    intro u v hu hv x hx
    by_cases hux : u x = 0
    · exact hv (by
        intro hvx
        apply hx
        simp [hux, hvx])
    · exact hu hux
  smul_mem' := by
    intro c v hv x hx
    exact hv (by
      intro hvx
      apply hx
      simp [hvx])

/-- Forget the bundled submodule structure and recover the existing smooth
core facade without changing the underlying Schwartz function. -/
def suzukiSmoothCoreLinearSubmoduleAsCore {r : Real}
    (v : SuzukiSmoothCoreLinearSubmodule r) : SuzukiSmoothCore r :=
  ⟨v.1, v.2⟩

/-- The logarithmic multiplier graph transported to the Hilbert `L²` product
norm. -/
def SuzukiLogHilbertGraphSubmodule :
    Submodule Complex (WithLp 2 (SuzukiL2 × SuzukiL2)) :=
  suzukiLogFourierPMap.graph.comap
    (WithLp.linearEquiv 2 Complex (SuzukiL2 × SuzukiL2)).toLinearMap

/-- The Hilbert realization of the closed logarithmic multiplier graph. -/
abbrev SuzukiLogHilbertGraphSpace := SuzukiLogHilbertGraphSubmodule

theorem isClosed_suzukiLogHilbertGraphSubmodule :
    IsClosed (SuzukiLogHilbertGraphSubmodule :
      Set (WithLp 2 (SuzukiL2 × SuzukiL2))) := by
  change IsClosed
    ((WithLp.homeomorphProd (p := (2 : ENNReal))
      (α := SuzukiL2) (β := SuzukiL2)) ⁻¹'
        (suzukiLogFourierPMap.graph : Set (SuzukiL2 × SuzukiL2)))
  exact suzukiLogFourierPMap_isClosed.preimage
    (WithLp.homeomorphProd (p := (2 : ENNReal))
      (α := SuzukiL2) (β := SuzukiL2)).continuous

noncomputable instance : CompleteSpace SuzukiLogHilbertGraphSpace :=
  isClosed_suzukiLogHilbertGraphSubmodule.completeSpace_coe

/-- The identity on graph coordinates, viewed as a linear equivalence between
the ordinary-product and Hilbert-product graph models. -/
def suzukiLogGraphHilbertLinearEquiv :
    SuzukiLogGraphSpace ≃ₗ[Complex] SuzukiLogHilbertGraphSpace where
  toFun x := ⟨WithLp.toLp 2 x.1, x.2⟩
  invFun x := ⟨WithLp.ofLp x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ordinary and Hilbert graph norms induce the same topology. -/
def suzukiLogGraphHilbertHomeomorph :
    SuzukiLogGraphSpace ≃ₜ SuzukiLogHilbertGraphSpace where
  toEquiv := suzukiLogGraphHilbertLinearEquiv.toEquiv
  continuous_toFun := by
    exact Continuous.subtype_mk
      ((WithLp.homeomorphProd (p := (2 : ENNReal))
        (α := SuzukiL2) (β := SuzukiL2)).symm.continuous.comp
          continuous_subtype_val) _
  continuous_invFun := by
    exact Continuous.subtype_mk
      ((WithLp.homeomorphProd (p := (2 : ENNReal))
        (α := SuzukiL2) (β := SuzukiL2)).continuous.comp
          continuous_subtype_val) _

/-- The smooth-core graph map as an exact complex-linear map. -/
def suzukiSmoothCoreToLogGraphLinearMap (r : Real) :
    SuzukiSmoothCoreLinearSubmodule r →ₗ[Complex] SuzukiLogGraphSpace where
  toFun v :=
    suzukiSmoothCoreToLogGraph
      (suzukiSmoothCoreLinearSubmoduleAsCore v)
  map_add' u v := by
    apply Subtype.ext
    apply Prod.ext
    · change
        SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
            (u.1 + v.1) =
          SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume u.1 +
            SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume v.1
      exact map_add _ _ _
    · apply suzukiLogFourierPMap.mem_graph_snd_inj
        (suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreLinearSubmoduleAsCore (u + v))).2
        (suzukiSmoothCoreToLogGraph
            (suzukiSmoothCoreLinearSubmoduleAsCore u) +
          suzukiSmoothCoreToLogGraph
            (suzukiSmoothCoreLinearSubmoduleAsCore v)).2
      change
        SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
            (u.1 + v.1) =
          SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume u.1 +
            SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume v.1
      exact map_add _ _ _
  map_smul' c v := by
    apply Subtype.ext
    apply Prod.ext
    · change
        SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
            (c • v.1) =
          c • SchwartzMap.toLpCLM Complex Complex
            (2 : ENNReal) volume v.1
      exact map_smul _ _ _
    · apply suzukiLogFourierPMap.mem_graph_snd_inj
        (suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreLinearSubmoduleAsCore (c • v))).2
        (c • suzukiSmoothCoreToLogGraph
          (suzukiSmoothCoreLinearSubmoduleAsCore v)).2
      change
        SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
            (c • v.1) =
          c • SchwartzMap.toLpCLM Complex Complex
            (2 : ENNReal) volume v.1
      exact map_smul _ _ _

/-- The smooth core embedded linearly in the Hilbert graph. -/
def suzukiSmoothCoreToHilbertGraphLinearMap (r : Real) :
    SuzukiSmoothCoreLinearSubmodule r →ₗ[Complex]
      SuzukiLogHilbertGraphSpace :=
  suzukiLogGraphHilbertLinearEquiv.toLinearMap.comp
    (suzukiSmoothCoreToLogGraphLinearMap r)

/-- The closed complex submodule generated by the exact radius-`r` smooth
core inside the Hilbert logarithmic graph. -/
def SuzukiLogRadiusLinearSubmodule (r : Real) :
    Submodule Complex SuzukiLogHilbertGraphSpace :=
  (LinearMap.range
    (suzukiSmoothCoreToHilbertGraphLinearMap r)).topologicalClosure

/-- The DF6D5B0 complex Hilbert completion at radius `r`. -/
abbrev SuzukiLogRadiusLinearCompletion (r : Real) :=
  SuzukiLogRadiusLinearSubmodule r

noncomputable instance (r : Real) :
    CompleteSpace (SuzukiLogRadiusLinearCompletion r) :=
  (Submodule.isClosed_topologicalClosure
    (LinearMap.range
      (suzukiSmoothCoreToHilbertGraphLinearMap r))).completeSpace_coe

theorem suzukiSmoothCoreHilbertGraph_range_eq (r : Real) :
    (LinearMap.range
        (suzukiSmoothCoreToHilbertGraphLinearMap r) :
      Set SuzukiLogHilbertGraphSpace) =
      suzukiLogGraphHilbertHomeomorph ''
        Set.range (suzukiSmoothCoreToLogGraph (r := r)) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨suzukiSmoothCoreToLogGraph
        (suzukiSmoothCoreLinearSubmoduleAsCore v),
      ⟨suzukiSmoothCoreLinearSubmoduleAsCore v, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    let w : SuzukiSmoothCoreLinearSubmodule r := ⟨v.1, v.2⟩
    exact ⟨w, rfl⟩

theorem suzukiLogRadiusLinearSubmodule_carrier_eq (r : Real) :
    (SuzukiLogRadiusLinearSubmodule r :
        Set SuzukiLogHilbertGraphSpace) =
      suzukiLogGraphHilbertHomeomorph ''
        closure (Set.range
          (suzukiSmoothCoreToLogGraph (r := r))) := by
  rw [SuzukiLogRadiusLinearSubmodule,
    Submodule.topologicalClosure_coe,
    suzukiSmoothCoreHilbertGraph_range_eq,
    suzukiLogGraphHilbertHomeomorph.image_closure]

/-- Transport an element of the existing DF6D2 completion to the Hilbert
completion without changing either graph coordinate. -/
def suzukiLogRadiusCompletionToLinear {r : Real}
    (v : SuzukiLogRadiusCompletion r) :
    SuzukiLogRadiusLinearCompletion r :=
  ⟨suzukiLogGraphHilbertHomeomorph v.1, by
    change suzukiLogGraphHilbertHomeomorph v.1 ∈
      (SuzukiLogRadiusLinearSubmodule r :
        Set SuzukiLogHilbertGraphSpace)
    rw [suzukiLogRadiusLinearSubmodule_carrier_eq]
    exact ⟨v.1, v.2, rfl⟩⟩

theorem suzukiLogRadiusLinearCompletionToLegacy_mem {r : Real}
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogGraphHilbertHomeomorph.symm v.1 ∈
      closure (Set.range
        (suzukiSmoothCoreToLogGraph (r := r))) := by
  have hv : v.1 ∈ suzukiLogGraphHilbertHomeomorph ''
      closure (Set.range
        (suzukiSmoothCoreToLogGraph (r := r))) := by
    rw [← suzukiLogRadiusLinearSubmodule_carrier_eq]
    exact v.2
  rw [suzukiLogGraphHilbertHomeomorph.image_closure] at hv
  change v.1 ∈ suzukiLogGraphHilbertHomeomorph.symm ⁻¹'
    closure (Set.range
      (suzukiSmoothCoreToLogGraph (r := r)))
  rw [suzukiLogGraphHilbertHomeomorph.symm.preimage_closure]
  have himage :
      suzukiLogGraphHilbertHomeomorph.symm ⁻¹'
          Set.range (suzukiSmoothCoreToLogGraph (r := r)) =
        suzukiLogGraphHilbertHomeomorph ''
          Set.range (suzukiSmoothCoreToLogGraph (r := r)) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨suzukiSmoothCoreToLogGraph y, ⟨y, rfl⟩, by
        rw [hy]
        exact suzukiLogGraphHilbertHomeomorph.apply_symm_apply x⟩
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      exact ⟨y, by
        rw [← hy]
        exact
          (suzukiLogGraphHilbertHomeomorph.symm_apply_apply _).symm⟩
  rw [himage]
  exact hv

/-- Transport a Hilbert-completion element back to the existing DF6D2
completion facade. -/
def suzukiLogRadiusLinearCompletionToLegacy {r : Real}
    (v : SuzukiLogRadiusLinearCompletion r) :
    SuzukiLogRadiusCompletion r :=
  ⟨suzukiLogGraphHilbertHomeomorph.symm v.1,
    suzukiLogRadiusLinearCompletionToLegacy_mem v⟩

/-- The existing and Hilbert radius completions have exactly the same
elements. -/
def suzukiLogRadiusCompletionHilbertEquiv {r : Real} :
    SuzukiLogRadiusCompletion r ≃
      SuzukiLogRadiusLinearCompletion r where
  toFun := suzukiLogRadiusCompletionToLinear
  invFun := suzukiLogRadiusLinearCompletionToLegacy
  left_inv v := by
    apply Subtype.ext
    rfl
  right_inv v := by
    apply Subtype.ext
    rfl

/-- The existing graph norm and the Hilbert graph norm induce equivalent
radius-completion topologies. -/
def suzukiLogRadiusCompletionHilbertHomeomorph {r : Real} :
    SuzukiLogRadiusCompletion r ≃ₜ
      SuzukiLogRadiusLinearCompletion r where
  toEquiv := suzukiLogRadiusCompletionHilbertEquiv
  continuous_toFun := by
    exact Continuous.subtype_mk
      (suzukiLogGraphHilbertHomeomorph.continuous.comp
        continuous_subtype_val) _
  continuous_invFun := by
    exact Continuous.subtype_mk
      (suzukiLogGraphHilbertHomeomorph.symm.continuous.comp
        continuous_subtype_val) _

/-- The canonical smooth-core map into the Hilbert completion. -/
def suzukiSmoothCoreToLogRadiusLinearCompletion {r : Real}
    (v : SuzukiSmoothCore r) :
    SuzukiLogRadiusLinearCompletion r :=
  suzukiLogRadiusCompletionToLinear
    (suzukiSmoothCoreToLogRadiusCompletion v)

theorem suzukiSmoothCoreToLogRadiusLinearCompletion_denseRange
    (r : Real) :
    DenseRange
      (suzukiSmoothCoreToLogRadiusLinearCompletion (r := r)) := by
  change DenseRange
    (suzukiLogRadiusCompletionHilbertHomeomorph ∘
      suzukiSmoothCoreToLogRadiusCompletion)
  exact
    suzukiLogRadiusCompletionHilbertHomeomorph.surjective.denseRange.comp
      (suzukiSmoothCoreToLogRadiusCompletion_denseRange r)
      suzukiLogRadiusCompletionHilbertHomeomorph.continuous

/-- The first graph coordinate as a continuous complex-linear `L²`
embedding. -/
def suzukiLogRadiusLinearCompletionToL2 {r : Real} :
    SuzukiLogRadiusLinearCompletion r →L[Complex] SuzukiL2 :=
  (WithLp.fstL (2 : ENNReal) Complex SuzukiL2 SuzukiL2).comp
    ((Submodule.subtypeL SuzukiLogHilbertGraphSubmodule).comp
      (Submodule.subtypeL (SuzukiLogRadiusLinearSubmodule r)))

@[simp]
theorem suzukiLogRadiusLinearCompletionToL2_apply {r : Real}
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2 v =
      suzukiLogRadiusCompletionToL2
        (suzukiLogRadiusLinearCompletionToLegacy v) :=
  rfl

theorem suzukiLogRadiusLinearCompletionToL2_norm_le
    {r : Real} (v : SuzukiLogRadiusLinearCompletion r) :
    ‖suzukiLogRadiusLinearCompletionToL2 v‖ ≤ ‖v‖ :=
  WithLp.norm_fst_le SuzukiL2 v.1.1

theorem suzukiLogRadiusLinearCompletionToL2_injective
    (r : Real) :
    Function.Injective
      (suzukiLogRadiusLinearCompletionToL2 (r := r)) := by
  intro u v huv
  have hlegacy :
      suzukiLogRadiusLinearCompletionToLegacy u =
        suzukiLogRadiusLinearCompletionToLegacy v := by
    apply suzukiLogRadiusCompletionToL2_injective r
    exact huv
  apply Subtype.ext
  have hgraph := congrArg
    (fun w : SuzukiLogRadiusCompletion r => w.1) hlegacy
  exact suzukiLogGraphHilbertHomeomorph.symm.injective hgraph

theorem suzukiLogRadiusLinearCompletionToL2_supportedAt
    {r : Real} (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiL2SupportedAt r
      (suzukiLogRadiusLinearCompletionToL2 v) := by
  rw [suzukiLogRadiusLinearCompletionToL2_apply]
  exact suzukiLogRadiusCompletionToL2_supportedAt
    (suzukiLogRadiusLinearCompletionToLegacy v)

/-- The Hilbert inner product is exactly the existing logarithmic graph
energy. -/
theorem suzukiLogRadiusLinear_inner_eq_legacyEnergy
    {r : Real} (u v : SuzukiLogRadiusLinearCompletion r) :
    inner Complex u v =
      suzukiLogRadiusEnergy
        (suzukiLogRadiusLinearCompletionToLegacy u)
        (suzukiLogRadiusLinearCompletionToLegacy v) := by
  change inner Complex u.1.1 v.1.1 =
    inner Complex u.1.1.fst v.1.1.fst +
      inner Complex u.1.1.snd v.1.1.snd
  exact WithLp.prod_inner_apply u.1.1 v.1.1

/-- Quantitative norm compatibility: the squared Hilbert norm is the real
diagonal of the existing logarithmic graph energy. -/
theorem suzukiLogRadiusLinear_norm_sq_eq_legacyEnergy_re
    {r : Real} (v : SuzukiLogRadiusLinearCompletion r) :
    ‖v‖ ^ 2 =
      (suzukiLogRadiusEnergy
        (suzukiLogRadiusLinearCompletionToLegacy v)
        (suzukiLogRadiusLinearCompletionToLegacy v)).re := by
  rw [← suzukiLogRadiusLinear_inner_eq_legacyEnergy]
  exact (inner_self_eq_norm_sq (𝕜 := Complex) v).symm

/-- Widen a bundled smooth-core support radius without changing the
underlying Schwartz function. -/
def suzukiSmoothCoreLinearSubmoduleWiden
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    SuzukiSmoothCoreLinearSubmodule b :=
  ⟨(suzukiSmoothCoreZeroExtension hab
      (suzukiSmoothCoreLinearSubmoduleAsCore v)).1,
    (suzukiSmoothCoreZeroExtension hab
      (suzukiSmoothCoreLinearSubmoduleAsCore v)).2⟩

theorem suzukiSmoothCoreLinearSubmoduleAsCore_widen
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiSmoothCoreLinearSubmoduleWiden hab v) =
      suzukiSmoothCoreZeroExtension hab
        (suzukiSmoothCoreLinearSubmoduleAsCore v) := by
  apply Subtype.ext
  rfl

theorem suzukiSmoothCoreHilbertGraph_range_mono
    {a b : Real} (hab : a ≤ b) :
    LinearMap.range (suzukiSmoothCoreToHilbertGraphLinearMap a) ≤
      LinearMap.range
        (suzukiSmoothCoreToHilbertGraphLinearMap b) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨suzukiSmoothCoreLinearSubmoduleWiden hab v, ?_⟩
  change suzukiLogGraphHilbertLinearEquiv
      (suzukiSmoothCoreToLogGraph
        (suzukiSmoothCoreLinearSubmoduleAsCore
          (suzukiSmoothCoreLinearSubmoduleWiden hab v))) =
    suzukiLogGraphHilbertLinearEquiv
      (suzukiSmoothCoreToLogGraph
        (suzukiSmoothCoreLinearSubmoduleAsCore v))
  rw [suzukiSmoothCoreLinearSubmoduleAsCore_widen,
    suzukiSmoothCoreToLogGraph_zeroExtension hab]

theorem suzukiLogRadiusLinearSubmodule_mono
    {a b : Real} (hab : a ≤ b) :
    SuzukiLogRadiusLinearSubmodule a ≤
      SuzukiLogRadiusLinearSubmodule b :=
  Submodule.topologicalClosure_mono
    (suzukiSmoothCoreHilbertGraph_range_mono hab)

/-- Zero extension on the Hilbert completions is literal closed-submodule
inclusion. -/
def suzukiLogRadiusLinearCompletionZeroExtension
    {a b : Real} (hab : a ≤ b) :
    SuzukiLogRadiusLinearCompletion a →L[Complex]
      SuzukiLogRadiusLinearCompletion b :=
  LinearMap.mkContinuous
    (Submodule.inclusion
      (suzukiLogRadiusLinearSubmodule_mono hab))
    1 (by
      intro v
      change ‖v.1‖ ≤ 1 * ‖v.1‖
      simp)

@[simp]
theorem suzukiLogRadiusLinearCompletionZeroExtension_apply
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiLogRadiusLinearCompletion a) :
    (suzukiLogRadiusLinearCompletionZeroExtension hab v).1 = v.1 :=
  rfl

@[simp]
theorem suzukiLogRadiusLinearCompletionZeroExtension_norm
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiLogRadiusLinearCompletion a) :
    ‖suzukiLogRadiusLinearCompletionZeroExtension hab v‖ = ‖v‖ :=
  rfl

theorem suzukiLogRadiusLinearCompletionZeroExtension_injective
    {a b : Real} (hab : a ≤ b) :
    Function.Injective
      (suzukiLogRadiusLinearCompletionZeroExtension hab) := by
  intro u v huv
  apply Subtype.ext
  exact congrArg
    (fun w : SuzukiLogRadiusLinearCompletion b => w.1) huv

@[simp]
theorem suzukiLogRadiusLinearCompletionToL2_zeroExtension
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiLogRadiusLinearCompletion a) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearCompletionZeroExtension hab v) =
      suzukiLogRadiusLinearCompletionToL2 v :=
  rfl

theorem suzukiLogRadiusLinearCompletionToLegacy_zeroExtension
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiLogRadiusLinearCompletion a) :
    suzukiLogRadiusLinearCompletionToLegacy
        (suzukiLogRadiusLinearCompletionZeroExtension hab v) =
      suzukiLogRadiusCompletionZeroExtension hab
        (suzukiLogRadiusLinearCompletionToLegacy v) := by
  apply Subtype.ext
  rfl

theorem suzukiLogRadiusLinear_inner_zeroExtension
    {a b : Real} (hab : a ≤ b)
    (u v : SuzukiLogRadiusLinearCompletion a) :
    inner Complex
        (suzukiLogRadiusLinearCompletionZeroExtension hab u)
        (suzukiLogRadiusLinearCompletionZeroExtension hab v) =
      inner Complex u v :=
  rfl

theorem suzukiSmoothCoreToLogRadiusLinearCompletion_zeroExtension
    {a b : Real} (hab : a ≤ b) (v : SuzukiSmoothCore a) :
    suzukiLogRadiusLinearCompletionZeroExtension hab
        (suzukiSmoothCoreToLogRadiusLinearCompletion v) =
      suzukiSmoothCoreToLogRadiusLinearCompletion
        (suzukiSmoothCoreZeroExtension hab v) := by
  apply Subtype.ext
  change suzukiLogGraphHilbertHomeomorph
      (suzukiSmoothCoreToLogGraph v) =
    suzukiLogGraphHilbertHomeomorph
      (suzukiSmoothCoreToLogGraph
        (suzukiSmoothCoreZeroExtension hab v))
  rw [suzukiSmoothCoreToLogGraph_zeroExtension hab]

/-- The existing complete shifted energy written directly on the Hilbert
completion. -/
def suzukiLogRadiusLinearCompleteEnergy
    {I : Type*} [DecidableEq I] {r : Real} (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiLogRadiusLinearCompletion r) : Complex :=
  inner Complex u v +
    suzukiL2FiniteRadiusRemainderEnergy s scalar coefficient shift K
      (suzukiLogRadiusLinearCompletionToL2 u)
      (suzukiLogRadiusLinearCompletionToL2 v)

theorem suzukiLogRadiusLinearCompleteEnergy_eq_legacy
    {I : Type*} [DecidableEq I] {r : Real} (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K u v =
      suzukiLogRadiusCompleteEnergy s scalar coefficient shift K
        (suzukiLogRadiusLinearCompletionToLegacy u)
        (suzukiLogRadiusLinearCompletionToLegacy v) := by
  unfold suzukiLogRadiusLinearCompleteEnergy
    suzukiLogRadiusCompleteEnergy
  rw [suzukiLogRadiusLinear_inner_eq_legacyEnergy]
  rfl

theorem suzukiLogRadiusLinearCompleteEnergy_jointContinuous
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2) :
    Continuous (Function.uncurry
      (suzukiLogRadiusLinearCompleteEnergy (r := r)
        s scalar coefficient shift K)) := by
  have hpair : Continuous
      (fun p : SuzukiLogRadiusLinearCompletion r ×
          SuzukiLogRadiusLinearCompletion r =>
        (suzukiLogRadiusLinearCompletionToLegacy p.1,
          suzukiLogRadiusLinearCompletionToLegacy p.2)) :=
    (suzukiLogRadiusCompletionHilbertHomeomorph.symm.continuous.comp
      continuous_fst).prodMk
        (suzukiLogRadiusCompletionHilbertHomeomorph.symm.continuous.comp
          continuous_snd)
  have hlegacy :=
    (suzukiLogRadiusCompleteEnergy_jointContinuous
      r s scalar coefficient shift K).comp hpair
  convert hlegacy using 1
  funext p
  exact (suzukiLogRadiusLinearCompleteEnergy_eq_legacy
    s scalar coefficient shift K p.1 p.2).symm

end

end M100
end Experiments
end RiemannHypothesisProject
