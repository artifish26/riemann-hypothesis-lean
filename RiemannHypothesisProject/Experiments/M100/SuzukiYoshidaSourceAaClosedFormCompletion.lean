import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaBurnolFormula
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaFourierLinearZeroDecay
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedFormFriedrichs

/-!
# M100-DF6F closed source-form completion

Suzuki's localized Weil form is closed in its shifted form norm.  This module
identifies that topology at the frozen endpoint without imposing the stronger
absolute Paley--Wiener sampling estimate.

The smooth-core Burnol formula and the proved linear zero-coordinate decay
first identify the literal multiplicity-aware zero pairing with the corrected
project form.  The concrete bounded representative of the unit-shifted form
then gives the upper norm estimate, while the checked endpoint coercivity gives
the reverse estimate.  Consequently the unit-shifted source-form Cauchy
sequences are exactly the Cauchy sequences of the existing logarithmic graph
completion.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter
open scoped InnerProductSpace

/-- The compact-support Guinand--Weil identity is now unconditional on the
whole smooth core: the contour theorem supplies the diagonal Burnol formula,
and one integration by parts supplies the all-pairs zero summability needed
for polarization. -/
theorem suzukiSourceAaSmoothCoreGuinandWeilFormula_proved :
    SuzukiSourceAaSmoothCoreGuinandWeilFormula :=
  suzukiSourceAaSmoothCoreGuinandWeilFormula_iff_fourier.mpr
    (suzukiSourceAaSmoothCoreFourierGuinandWeilFormula_of_decay_burnol
      suzukiSourceAaSmoothCoreFourierLinearZeroDecay_proved
      suzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions_proved)

/-- On two compactly supported smooth vectors, the literal localized zero
pairing is exactly the corrected completed form.  This is the source-form
identity whose closure topology is analyzed below. -/
theorem suzukiSourceLocalizedWeilPairing_smoothCore_eq_correctedCompleteForm
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceLocalizedWeilPairing suzukiProjectAStar
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar v)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u) =
      suzukiYoshidaCorrectedCompleteForm
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u)
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar v) := by
  have hcore :=
    suzukiSourceAaLocalizedWeilFormCoreGRepresentation_of_smoothCoreGuinandWeil
      suzukiSourceAaSmoothCoreGuinandWeilFormula_proved
  rw [← suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply v,
    ← suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply u]
  change suzukiSourceAaLocalizedWeilForm
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar u)
      (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
        suzukiProjectAStar v) = _
  exact (hcore u v).trans
    (inner_suzukiSourceGOperator_differentials_eq_correctedCompleteForm
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar) u v)

/-- Squared unit-shifted localized source-form norm on the completed domain.
The physical term is the literal interval `L²` norm appearing in Suzuki's
form norm. -/
def suzukiSourceAaUnitShiftedFormNormSq
    (u : SuzukiYoshidaCorrectedCommonFormDomain) : Real :=
  (suzukiYoshidaCorrectedCompleteForm u u).re +
    ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ ^ 2

/-- The unit-shifted source-form norm square is the real diagonal of the
explicit bounded shifted-form representative. -/
theorem suzukiSourceAaUnitShiftedFormNormSq_eq_re_inner
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaUnitShiftedFormNormSq u =
      (inner Complex (suzukiYoshidaCorrectedShiftedFormOperator u) u).re := by
  rw [suzukiSourceAaUnitShiftedFormNormSq,
    inner_suzukiYoshidaCorrectedShiftedFormOperator, Complex.add_re]
  rw [show (inner Complex
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)).re =
        ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ ^ 2 by
      exact inner_self_eq_norm_sq (𝕜 := Complex) _]

/-- The literal smooth-core zero pairing gives the diagonal term in the
unit-shifted source form norm. -/
theorem suzukiSourceAaUnitShiftedFormNormSq_core_eq_zeroPairing
    (u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceAaUnitShiftedFormNormSq
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u) =
      (suzukiSourceLocalizedWeilPairing suzukiProjectAStar
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u)
        (suzukiSmoothCoreFiniteIntervalL2LinearMap suzukiProjectAStar u)).re +
      ‖suzukiSmoothCoreFiniteIntervalL2LinearMap
        suzukiProjectAStar u‖ ^ 2 := by
  rw [suzukiSourceAaUnitShiftedFormNormSq,
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply,
    suzukiSourceLocalizedWeilPairing_smoothCore_eq_correctedCompleteForm]

/-- A positive explicit comparison constant for the reverse form-norm
estimate. -/
def suzukiSourceAaFormNormLowerComparison : Real :=
  1 + suzukiCorrectedShiftedFormL2LossBound

theorem suzukiSourceAaFormNormLowerComparison_pos :
    0 < suzukiSourceAaFormNormLowerComparison := by
  unfold suzukiSourceAaFormNormLowerComparison
    suzukiCorrectedShiftedFormL2LossBound
  have hprime : 0 ≤ suzukiDF6D4DF0PrimeNorm := by
    unfold suzukiDF6D4DF0PrimeNorm
    positivity
  nlinarith [suzukiProjectAStar_pos.le, hprime,
    norm_nonneg (suzukiRSecondGlobalL2Operator suzukiProjectAStar)]

/-- Endpoint coercivity gives the reverse comparison: the logarithmic graph
norm is controlled by the shifted localized source form norm. -/
theorem norm_sq_le_suzukiSourceAaFormNormLowerComparison_mul
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    ‖u‖ ^ 2 ≤ suzukiSourceAaFormNormLowerComparison *
      suzukiSourceAaUnitShiftedFormNormSq u := by
  have hgraph :=
    norm_sq_le_re_inner_suzukiYoshidaCorrectedShiftedFormOperator_add_l2 u
  have hphysical :=
    norm_sq_suzukiCorrectedFormGlobalRestriction_le_re_inner_shiftedForm
      (suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff
        suzukiProjectAStar)
      (suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar) u
  rw [suzukiSourceAaUnitShiftedFormNormSq_eq_re_inner]
  unfold suzukiSourceAaFormNormLowerComparison
  have hB : 0 ≤ suzukiCorrectedShiftedFormL2LossBound := by
    unfold suzukiCorrectedShiftedFormL2LossBound
    have hprime : 0 ≤ suzukiDF6D4DF0PrimeNorm := by
      unfold suzukiDF6D4DF0PrimeNorm
      positivity
    nlinarith [suzukiProjectAStar_pos.le, hprime,
      norm_nonneg (suzukiRSecondGlobalL2Operator suzukiProjectAStar)]
  nlinarith [hgraph, hphysical,
    mul_le_mul_of_nonneg_left hphysical hB]

/-- The shifted localized source-form norm square is continuous in the
logarithmic graph topology.  Together with the reverse coercive estimate this
is the topological equivalence needed for the completion theorem. -/
theorem continuous_suzukiSourceAaUnitShiftedFormNormSq :
    Continuous suzukiSourceAaUnitShiftedFormNormSq := by
  rw [show suzukiSourceAaUnitShiftedFormNormSq =
      fun u : SuzukiYoshidaCorrectedCommonFormDomain =>
        (inner Complex
          (suzukiYoshidaCorrectedShiftedFormOperator u) u).re by
    funext u
    exact suzukiSourceAaUnitShiftedFormNormSq_eq_re_inner u]
  fun_prop

/-- The shifted localized source form is nonnegative on the completed domain.
-/
theorem suzukiSourceAaUnitShiftedFormNormSq_nonneg
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    0 ≤ suzukiSourceAaUnitShiftedFormNormSq u := by
  have hnorm : 0 ≤ ‖u‖ ^ 2 := sq_nonneg _
  have hbound := norm_sq_le_suzukiSourceAaFormNormLowerComparison_mul u
  have hC := suzukiSourceAaFormNormLowerComparison_pos
  nlinarith

/-- Cauchy criterion for the unit-shifted localized source form on the
completed logarithmic domain. -/
def SuzukiSourceAaUnitShiftedFormCauchy
    (u : Nat → SuzukiYoshidaCorrectedCommonFormDomain) : Prop :=
  ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
    suzukiSourceAaUnitShiftedFormNormSq (u m - u n) < ε

/-- The unit-shifted localized source-form Cauchy sequences are exactly the
Cauchy sequences of the existing complete logarithmic graph domain.  This is
the completion-level domain identification required by the closed-form route.
-/
theorem suzukiSourceAaUnitShiftedFormCauchy_iff
    (u : Nat → SuzukiYoshidaCorrectedCommonFormDomain) :
    SuzukiSourceAaUnitShiftedFormCauchy u ↔ CauchySeq u := by
  constructor
  · intro hsource
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let C := suzukiSourceAaFormNormLowerComparison
    have hC : 0 < C := suzukiSourceAaFormNormLowerComparison_pos
    obtain ⟨N, hN⟩ := hsource (ε ^ 2 / C) (div_pos (sq_pos_of_pos hε) hC)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hform := hN m hm n hn
    have hlower := norm_sq_le_suzukiSourceAaFormNormLowerComparison_mul
      (u m - u n)
    have hsquare : ‖u m - u n‖ ^ 2 < ε ^ 2 := by
      calc
        ‖u m - u n‖ ^ 2 ≤
            C * suzukiSourceAaUnitShiftedFormNormSq (u m - u n) := by
          simpa only [C] using hlower
        _ < C * (ε ^ 2 / C) := mul_lt_mul_of_pos_left hform hC
        _ = ε ^ 2 := by field_simp
    rw [dist_eq_norm]
    exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hsquare
  · intro hgraph
    rw [Metric.cauchySeq_iff] at hgraph
    intro ε hε
    have hcontinuous : ContinuousAt
        suzukiSourceAaUnitShiftedFormNormSq 0 :=
      continuous_suzukiSourceAaUnitShiftedFormNormSq.continuousAt
    rw [Metric.continuousAt_iff] at hcontinuous
    obtain ⟨δ, hδ, hmap⟩ := hcontinuous ε hε
    obtain ⟨N, hN⟩ := hgraph δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hdist := hN m hm n hn
    have hnear : dist (u m - u n) 0 < δ := by
      rw [dist_zero_right]
      simpa only [dist_eq_norm] using hdist
    have himage := hmap hnear
    have hzero : suzukiSourceAaUnitShiftedFormNormSq 0 = 0 := by
      rw [suzukiSourceAaUnitShiftedFormNormSq_eq_re_inner]
      simp
    rw [Real.dist_eq, hzero, sub_zero,
      abs_of_nonneg (suzukiSourceAaUnitShiftedFormNormSq_nonneg _)] at himage
    exact himage

/-- Every Cauchy sequence for the unit-shifted localized source form converges
in the completed logarithmic domain.  Thus the form closure constructed from
the literal smooth-core zero pairing is complete at the frozen endpoint. -/
theorem suzukiSourceAaUnitShiftedFormCauchy_exists_tendsto
    (u : Nat → SuzukiYoshidaCorrectedCommonFormDomain)
    (hu : SuzukiSourceAaUnitShiftedFormCauchy u) :
    ∃ v : SuzukiYoshidaCorrectedCommonFormDomain,
      Tendsto u atTop (nhds v) :=
  cauchySeq_tendsto_of_complete
    ((suzukiSourceAaUnitShiftedFormCauchy_iff u).mp hu)

/-- Every completed-domain vector is the graph limit of literal smooth-core
vectors, and the unit-shifted localized source-form energy of the error tends
to zero.  This is the form-core statement needed to identify the closed form
as the closure of its compact-support restriction. -/
theorem exists_suzukiSourceAaSmoothCoreFormApproximation
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    ∃ approximation :
        Nat → SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
      Tendsto
          (fun k =>
            suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
              suzukiProjectAStar (approximation k))
          atTop (nhds u) ∧
        Tendsto
          (fun k =>
            suzukiSourceAaUnitShiftedFormNormSq
              (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
                suzukiProjectAStar (approximation k) - u))
          atTop (nhds 0) := by
  let coreMap :=
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap suzukiProjectAStar
  have hu : u ∈ closure (Set.range coreMap) :=
    (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
      suzukiProjectAStar) u
  rw [mem_closure_iff_seq_limit] at hu
  obtain ⟨sequence, hsequenceRange, hsequence⟩ := hu
  choose approximation happ using hsequenceRange
  have htendsto : Tendsto (fun k => coreMap (approximation k))
      atTop (nhds u) := by
    simpa only [happ] using hsequence
  refine ⟨approximation, htendsto, ?_⟩
  have hdiff : Tendsto (fun k => coreMap (approximation k) - u)
      atTop (nhds (u - u)) :=
    htendsto.sub tendsto_const_nhds
  have hform :=
    continuous_suzukiSourceAaUnitShiftedFormNormSq.continuousAt.tendsto.comp
      hdiff
  change Tendsto
    (suzukiSourceAaUnitShiftedFormNormSq ∘
      fun k => coreMap (approximation k) - u) atTop (nhds 0)
  have hzero : suzukiSourceAaUnitShiftedFormNormSq (u - u) = 0 := by
    rw [sub_self, suzukiSourceAaUnitShiftedFormNormSq_eq_re_inner]
    simp
  rw [hzero] at hform
  exact hform

end

end RiemannHypothesisProject.Experiments.M100
