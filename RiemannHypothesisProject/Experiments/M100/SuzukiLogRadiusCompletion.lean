import RiemannHypothesisProject.Experiments.M100.SuzukiLogMultiplierClosed
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# M100-DF6D2 logarithmic radius completions

This module realizes the radius-wise completion of Suzuki's smooth core as
its closure inside the closed graph of the logarithmic Fourier multiplier.
Consequently the core has dense range by construction, every completed
element has a canonical global `L²` representative, and zero extension is the
unchanged graph element.

The energy defined here is the canonical graph energy. Identification with
Suzuki's singular local integral and with the complete Weil form is kept out
of this module; those are source/normalization theorems rather than completion
machinery.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- A smooth Suzuki core function as an element of the closed logarithmic
graph. -/
def suzukiSmoothCoreToLogGraph {r : Real}
    (v : SuzukiSmoothCore r) : SuzukiLogGraphSpace :=
  ⟨(suzukiSmoothCoreToL2 v,
      suzukiLogWeightedFourierToL2
        ⟨suzukiSmoothCoreToL2 v,
          (show suzukiSmoothCoreToL2 v ∈ SuzukiLogFourierSubmodule by
            exact suzukiSmoothCoreToL2_mem_logFourierDomain v)⟩), by
    change (suzukiSmoothCoreToL2 v,
      suzukiLogWeightedFourierToL2
        ⟨suzukiSmoothCoreToL2 v,
          (show suzukiSmoothCoreToL2 v ∈ SuzukiLogFourierSubmodule by
            exact suzukiSmoothCoreToL2_mem_logFourierDomain v)⟩) ∈
        suzukiLogFourierPMap.graph
    rw [LinearPMap.mem_graph_iff]
    exact ⟨⟨suzukiSmoothCoreToL2 v,
      (show suzukiSmoothCoreToL2 v ∈ SuzukiLogFourierSubmodule by
        exact suzukiSmoothCoreToL2_mem_logFourierDomain v)⟩, rfl, rfl⟩⟩

theorem suzukiSmoothCoreToLogGraph_zeroExtension
    {a b : Real} (hab : a ≤ b) (v : SuzukiSmoothCore a) :
    suzukiSmoothCoreToLogGraph (suzukiSmoothCoreZeroExtension hab v) =
      suzukiSmoothCoreToLogGraph v := by
  apply Subtype.ext
  apply Prod.ext
  · exact suzukiSmoothCoreToL2_zeroExtension hab v
  · exact suzukiLogFourierPMap.mem_graph_snd_inj
      (suzukiSmoothCoreToLogGraph
        (suzukiSmoothCoreZeroExtension hab v)).2
      (suzukiSmoothCoreToLogGraph v).2
      (suzukiSmoothCoreToL2_zeroExtension hab v)

/-- The radius-`r` logarithmic form completion: the closure of the concrete
smooth core inside the closed multiplier graph. -/
abbrev SuzukiLogRadiusCompletion (r : Real) :=
  {v : SuzukiLogGraphSpace //
    v ∈ closure (Set.range
      (suzukiSmoothCoreToLogGraph (r := r)))}

/-- The graph norm inherited from the closed multiplier graph. -/
instance (r : Real) : Norm (SuzukiLogRadiusCompletion r) :=
  ⟨fun v ↦ norm v.1⟩

@[simp]
theorem suzukiLogRadiusCompletion_norm {r : Real}
    (v : SuzukiLogRadiusCompletion r) :
    norm v = norm v.1 :=
  rfl

noncomputable instance (r : Real) :
    CompleteSpace (SuzukiLogRadiusCompletion r) :=
  isClosed_closure.completeSpace_coe

/-- The canonical dense core map into its logarithmic completion. -/
def suzukiSmoothCoreToLogRadiusCompletion {r : Real}
    (v : SuzukiSmoothCore r) : SuzukiLogRadiusCompletion r :=
  ⟨suzukiSmoothCoreToLogGraph v,
    subset_closure (Set.mem_range_self v)⟩

theorem suzukiSmoothCoreToLogRadiusCompletion_denseRange (r : Real) :
    DenseRange
      (suzukiSmoothCoreToLogRadiusCompletion (r := r)) := by
  let f : SuzukiSmoothCore r → SuzukiLogGraphSpace :=
    suzukiSmoothCoreToLogGraph
  have hdense : DenseRange
      (Set.inclusion (subset_closure : Set.range f ⊆ closure (Set.range f)) ∘
        Set.rangeFactorization f) :=
    ((denseRange_inclusion_iff subset_closure).2 subset_rfl).comp
      Set.rangeFactorization_surjective.denseRange
      (continuous_inclusion subset_closure)
  change DenseRange (fun v : SuzukiSmoothCore r ↦
    (⟨f v, subset_closure (Set.mem_range_self v)⟩ :
      closure (Set.range f)))
  have hfun :
      (fun v : SuzukiSmoothCore r ↦
        (⟨f v, subset_closure (Set.mem_range_self v)⟩ :
          closure (Set.range f))) =
        (Set.inclusion
          (subset_closure : Set.range f ⊆ closure (Set.range f)) ∘
            Set.rangeFactorization f) := by
    funext v
    rfl
  rw [hfun]
  exact hdense

private theorem suzukiLogRadiusCompletion_range_mono
    {a b : Real} (hab : a ≤ b) :
    Set.range (suzukiSmoothCoreToLogGraph (r := a)) ⊆
      Set.range (suzukiSmoothCoreToLogGraph (r := b)) := by
  rintro _ ⟨v, rfl⟩
  exact ⟨suzukiSmoothCoreZeroExtension hab v,
    suzukiSmoothCoreToLogGraph_zeroExtension hab v⟩

/-- Zero extension between logarithmic completions is literal inclusion of
the unchanged closed-graph element. -/
def suzukiLogRadiusCompletionZeroExtension
    {a b : Real} (hab : a ≤ b) :
    SuzukiLogRadiusCompletion a → SuzukiLogRadiusCompletion b :=
  fun v ↦ ⟨v.1, closure_mono
    (suzukiLogRadiusCompletion_range_mono hab) v.2⟩

@[simp]
theorem suzukiLogRadiusCompletionZeroExtension_apply
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiLogRadiusCompletion a) :
    (suzukiLogRadiusCompletionZeroExtension hab v).1 = v.1 :=
  rfl

theorem suzukiLogRadiusCompletionZeroExtension_continuous
    {a b : Real} (hab : a ≤ b) :
    Continuous (suzukiLogRadiusCompletionZeroExtension hab) := by
  exact continuous_subtype_val.subtype_mk _

theorem suzukiLogRadiusCompletionZeroExtension_injective
    {a b : Real} (hab : a ≤ b) :
    Function.Injective (suzukiLogRadiusCompletionZeroExtension hab) := by
  intro u v huv
  have hval :
      (suzukiLogRadiusCompletionZeroExtension hab u).1 =
        (suzukiLogRadiusCompletionZeroExtension hab v).1 :=
    congrArg (fun w : SuzukiLogRadiusCompletion b ↦ w.1) huv
  apply Subtype.ext
  exact hval

theorem suzukiSmoothCoreToLogRadiusCompletion_zeroExtension
    {a b : Real} (hab : a ≤ b) (v : SuzukiSmoothCore a) :
    suzukiLogRadiusCompletionZeroExtension hab
        (suzukiSmoothCoreToLogRadiusCompletion v) =
      suzukiSmoothCoreToLogRadiusCompletion
        (suzukiSmoothCoreZeroExtension hab v) := by
  apply Subtype.ext
  exact (suzukiSmoothCoreToLogGraph_zeroExtension hab v).symm

/-- The canonical global `L²` representative of a logarithmic completion
element. -/
def suzukiLogRadiusCompletionToL2 {r : Real}
    (v : SuzukiLogRadiusCompletion r) : SuzukiL2 :=
  v.1.1.1

theorem suzukiLogRadiusCompletionToL2_injective (r : Real) :
    Function.Injective (suzukiLogRadiusCompletionToL2 (r := r)) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext huv
  exact suzukiLogFourierPMap.mem_graph_snd_inj u.1.2 v.1.2 huv

theorem isClosed_suzukiL2SupportedAt (r : Real) :
    IsClosed {v : SuzukiL2 | suzukiL2SupportedAt r v} := by
  refine IsSeqClosed.isClosed fun f v hf hfv ↦ ?_
  obtain ⟨φ, -, hφ⟩ :=
    tendstoInMeasure_of_tendsto_Lp hfv |>.exists_seq_tendsto_ae
  filter_upwards [countable_iInter_mem.mpr hf, hφ] with x hx hφx
  intro hxOutside
  have hzero : ∀ n, f (φ n) x = 0 := by
    intro n
    exact Set.mem_iInter.mp hx (φ n) hxOutside
  have hseq : (fun n ↦ f (φ n) x) = (fun _ ↦ (0 : Complex)) := by
    funext n
    exact hzero n
  rw [hseq] at hφx
  exact tendsto_nhds_unique hφx tendsto_const_nhds

theorem suzukiLogRadiusCompletionToL2_supportedAt
    {r : Real} (v : SuzukiLogRadiusCompletion r) :
    suzukiL2SupportedAt r (suzukiLogRadiusCompletionToL2 v) := by
  have hclosed : IsClosed
      {g : SuzukiLogGraphSpace | suzukiL2SupportedAt r g.1.1} :=
    (isClosed_suzukiL2SupportedAt r).preimage
      (continuous_fst.comp continuous_subtype_val)
  have hrange : Set.range (suzukiSmoothCoreToLogGraph (r := r)) ⊆
      {g : SuzukiLogGraphSpace | suzukiL2SupportedAt r g.1.1} := by
    rintro _ ⟨w, rfl⟩
    exact suzukiSmoothCoreToL2_supportedAt w
  exact closure_minimal hrange hclosed v.2

/-- The concrete range of the radius completion inside global `L²`. -/
def SuzukiLogRadiusL2Range (r : Real) : Set SuzukiL2 :=
  Set.range (suzukiLogRadiusCompletionToL2 (r := r))

theorem SuzukiLogRadiusL2Range_supportedAt
    {r : Real} {v : SuzukiL2} (hv : v ∈ SuzukiLogRadiusL2Range r) :
    suzukiL2SupportedAt r v := by
  obtain ⟨w, rfl⟩ := hv
  exact suzukiLogRadiusCompletionToL2_supportedAt w

@[simp]
theorem suzukiLogRadiusCompletionToL2_zeroExtension
    {a b : Real} (hab : a ≤ b)
    (v : SuzukiLogRadiusCompletion a) :
    suzukiLogRadiusCompletionToL2
        (suzukiLogRadiusCompletionZeroExtension hab v) =
      suzukiLogRadiusCompletionToL2 v :=
  rfl

/-- The canonical shifted logarithmic graph energy. -/
def suzukiLogRadiusEnergy {r : Real}
    (u v : SuzukiLogRadiusCompletion r) : Complex :=
  inner Complex u.1.1.1 v.1.1.1 +
    inner Complex u.1.1.2 v.1.1.2

theorem suzukiLogRadiusEnergy_jointContinuous (r : Real) :
    Continuous (Function.uncurry
      (suzukiLogRadiusEnergy (r := r))) := by
  unfold suzukiLogRadiusEnergy Function.uncurry
  fun_prop

/-- The complete shifted energy on the same logarithmic completion, obtained
by adding the polarized finite-radius `L²` remainder. -/
def suzukiLogRadiusCompleteEnergy
    {I : Type*} [DecidableEq I] {r : Real} (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiLogRadiusCompletion r) : Complex :=
  suzukiLogRadiusEnergy u v +
    suzukiL2FiniteRadiusRemainderEnergy s scalar coefficient shift K
      (suzukiLogRadiusCompletionToL2 u)
      (suzukiLogRadiusCompletionToL2 v)

theorem suzukiLogRadiusCompleteEnergy_jointContinuous
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2) :
    Continuous (Function.uncurry
      (suzukiLogRadiusCompleteEnergy (r := r)
        s scalar coefficient shift K)) := by
  have htoL2 : Continuous
      (suzukiLogRadiusCompletionToL2 (r := r)) := by
    unfold suzukiLogRadiusCompletionToL2
    fun_prop
  have hpair : Continuous
      (fun p : SuzukiLogRadiusCompletion r ×
          SuzukiLogRadiusCompletion r ↦
        (suzukiLogRadiusCompletionToL2 p.1,
          suzukiLogRadiusCompletionToL2 p.2)) :=
    (htoL2.comp continuous_fst).prodMk
      (htoL2.comp continuous_snd)
  have hremainder : Continuous (Function.uncurry
      (suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift K)) :=
    suzukiL2FiniteRadiusRemainderEnergy_jointContinuous
      s scalar coefficient shift K
  change Continuous (fun p : SuzukiLogRadiusCompletion r ×
      SuzukiLogRadiusCompletion r ↦
    suzukiLogRadiusEnergy p.1 p.2 +
      Function.uncurry
        (suzukiL2FiniteRadiusRemainderEnergy
          s scalar coefficient shift K)
        (suzukiLogRadiusCompletionToL2 p.1,
          suzukiLogRadiusCompletionToL2 p.2))
  exact (suzukiLogRadiusEnergy_jointContinuous r).add
    (hremainder.comp hpair)

theorem suzukiLogRadiusEnergy_self_re_nonneg
    {r : Real} (v : SuzukiLogRadiusCompletion r) :
    0 ≤ (suzukiLogRadiusEnergy v v).re := by
  unfold suzukiLogRadiusEnergy
  rw [Complex.add_re]
  have hbase :
      (inner Complex v.1.1.1 v.1.1.1).re = norm v.1.1.1 ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) v.1.1.1
  have hweighted :
      (inner Complex v.1.1.2 v.1.1.2).re = norm v.1.1.2 ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) v.1.1.2
  rw [hbase, hweighted]
  positivity

theorem suzukiLogRadiusRemainderEnergy_self_re_abs_le
    {I : Type*} [DecidableEq I] {r : Real} (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (v : SuzukiLogRadiusCompletion r) :
    abs ((suzukiL2FiniteRadiusRemainderEnergy
      s scalar coefficient shift K
      (suzukiLogRadiusCompletionToL2 v)
      (suzukiLogRadiusCompletionToL2 v)).re) ≤
        (abs scalar +
          Finset.sum s (fun i ↦ 2 * abs (coefficient i)) + norm K) *
          norm v ^ 2 := by
  rw [suzukiL2FiniteRadiusRemainderEnergy_self_re]
  have hraw := suzukiL2FiniteRadiusRemainder_abs_le
    s scalar coefficient shift K
      (suzukiLogRadiusCompletionToL2 v)
  have hbase : norm (suzukiLogRadiusCompletionToL2 v) ≤ norm v := by
    change norm v.1.1.1 ≤ norm v.1.1
    exact norm_fst_le v.1.1
  have hsquare :
      norm (suzukiLogRadiusCompletionToL2 v) ^ 2 ≤ norm v ^ 2 := by
    nlinarith [norm_nonneg (suzukiLogRadiusCompletionToL2 v),
      norm_nonneg v.1]
  have hconstant : 0 ≤
      abs scalar +
        Finset.sum s (fun i ↦ 2 * abs (coefficient i)) + norm K := by
    positivity
  exact hraw.trans (mul_le_mul_of_nonneg_left hsquare hconstant)

/-- Explicit equivalence estimate for the canonical logarithmic shifted form
and its complete finite-radius bounded perturbation. This is the concrete
reason both forms extend on the same radius completion. -/
theorem suzukiLogRadius_shiftedForm_comparison
    {I : Type*} [DecidableEq I] {r : Real} (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (v : SuzukiLogRadiusCompletion r) :
    let bound := abs scalar +
      Finset.sum s (fun i ↦ 2 * abs (coefficient i)) + norm K
    let localForm := fun w : SuzukiLogRadiusCompletion r ↦
      (suzukiLogRadiusEnergy w w).re
    let boundedPart := fun w : SuzukiLogRadiusCompletion r ↦
      (suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift K
        (suzukiLogRadiusCompletionToL2 w)
        (suzukiLogRadiusCompletionToL2 w)).re
    let localNormSq := suzukiShiftedFormNormSq localForm 1 v
    let completeNormSq := suzukiShiftedFormNormSq
      (fun w ↦ localForm w + boundedPart w) (bound + 1) v
    0 ≤ localNormSq ∧
      localNormSq ≤ completeNormSq ∧
      completeNormSq ≤ (1 + 2 * bound) * localNormSq := by
  dsimp only
  let bound := abs scalar +
    Finset.sum s (fun i ↦ 2 * abs (coefficient i)) + norm K
  let localForm := fun w : SuzukiLogRadiusCompletion r ↦
    (suzukiLogRadiusEnergy w w).re
  let boundedPart := fun w : SuzukiLogRadiusCompletion r ↦
    (suzukiL2FiniteRadiusRemainderEnergy
      s scalar coefficient shift K
      (suzukiLogRadiusCompletionToL2 w)
      (suzukiLogRadiusCompletionToL2 w)).re
  have hbound : 0 ≤ bound := by
    dsimp only [bound]
    positivity
  have hlower : ∀ w : SuzukiLogRadiusCompletion r,
      -(0 * norm w ^ 2) ≤ localForm w := by
    intro w
    dsimp only [localForm]
    simpa using suzukiLogRadiusEnergy_self_re_nonneg w
  have hbounded : ∀ w : SuzukiLogRadiusCompletion r,
      abs (boundedPart w) ≤ bound * norm w ^ 2 := by
    intro w
    exact suzukiLogRadiusRemainderEnergy_self_re_abs_le
      s scalar coefficient shift K w
  simpa only [bound, localForm, boundedPart, zero_add] using
    (suzukiShiftedFormNormSq_boundedPerturbation_comparison
      localForm boundedPart 0 bound hbound hlower hbounded v)

theorem suzukiLogRadiusEnergy_zeroExtension
    {a b : Real} (hab : a ≤ b)
    (u v : SuzukiLogRadiusCompletion a) :
    suzukiLogRadiusEnergy
        (suzukiLogRadiusCompletionZeroExtension hab u)
        (suzukiLogRadiusCompletionZeroExtension hab v) =
      suzukiLogRadiusEnergy u v :=
  rfl

/-- The DF6C dense-core argument instantiated on the concrete logarithmic
radius completions and their canonical graph energy. -/
theorem suzukiLogRadiusEnergy_closedNesting
    {a b : Real} (hab : a ≤ b) :
    ∀ u v : SuzukiLogRadiusCompletion a,
      suzukiLogRadiusEnergy
          (suzukiLogRadiusCompletionZeroExtension hab u)
          (suzukiLogRadiusCompletionZeroExtension hab v) =
        suzukiLogRadiusEnergy u v := by
  apply suzukiClosedLocalEnergyNesting_of_core hab
    (suzukiSmoothCoreToLogRadiusCompletion (r := a))
    (suzukiLogRadiusCompletionZeroExtension hab)
    suzukiLogRadiusEnergy suzukiLogRadiusEnergy
    suzukiSmoothCorePolarizedWeight
  · exact suzukiSmoothCoreToLogRadiusCompletion_denseRange a
  · exact suzukiLogRadiusCompletionZeroExtension_continuous hab
  · exact suzukiLogRadiusEnergy_jointContinuous a
  · exact suzukiLogRadiusEnergy_jointContinuous b
  · intro u v
    rw [suzukiLogRadiusEnergy_zeroExtension hab]
    simp only [sub_self]
    exact (suzukiSmoothCore_polarizedLocalEnergyRadiusIncrement_eq_zero
      hab u v).symm

end

end M100
end Experiments
end RiemannHypothesisProject
