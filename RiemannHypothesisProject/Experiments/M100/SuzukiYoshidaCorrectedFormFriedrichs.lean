import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedFormAssociatedOperator
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointAssembly
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# M100-DF6F Friedrichs maximality bridge

This module isolates the exact maximality step for the operator represented by
the corrected completed form.  A densely defined symmetric operator is
self-adjoint once one real shifted resolvent is onto.  For the concrete Suzuki
operator, that range condition follows from the corresponding shifted
variational equation on the completed form domain.

No inhabitant of the visible source premises or identification with Suzuki's
named `A_a` is asserted here.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap ComplexConjugate NNReal

local instance suzukiCorrectedFormFriedrichsCompleteSpace :
    CompleteSpace (SuzukiFiniteIntervalL2 suzukiProjectAStar) := by
  infer_instance

/-! ## Bounded representative of the unit-shifted form -/

private abbrev suzukiCorrectedFormGlobalRestriction :
    SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 :=
  suzukiLogRadiusLinearCompletionToL2 (r := suzukiProjectAStar)

private def suzukiCorrectedFormGlobalRestrictionAdjoint :
    SuzukiL2 →L[Complex] SuzukiYoshidaCorrectedCommonFormDomain :=
  ContinuousLinearMap.adjoint (𝕜 := Complex)
    (E := SuzukiYoshidaCorrectedCommonFormDomain) (F := SuzukiL2)
    suzukiCorrectedFormGlobalRestriction

private abbrev suzukiCorrectedFormLowFrequencyMap :
    SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 :=
  suzukiLowFrequencyWeightedFourierCompletionMap suzukiProjectAStar_pos

private def suzukiCorrectedFormLowFrequencyMapAdjoint :
    SuzukiL2 →L[Complex] SuzukiYoshidaCorrectedCommonFormDomain :=
  ContinuousLinearMap.adjoint (𝕜 := Complex)
    (E := SuzukiYoshidaCorrectedCommonFormDomain) (F := SuzukiL2)
    suzukiCorrectedFormLowFrequencyMap

/-- The smooth-core `4r` low-frequency estimate extends to every element of
the completed form domain. -/
theorem norm_sq_suzukiCorrectedFormLowFrequencyMap_le
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    ‖suzukiCorrectedFormLowFrequencyMap u‖ ^ 2 ≤
      4 * suzukiProjectAStar *
        ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 := by
  let e := suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
    suzukiProjectAStar
  have hmem : ∀ x : SuzukiYoshidaCorrectedCommonFormDomain,
      x ∈ LinearMap.range e →
        ‖suzukiCorrectedFormLowFrequencyMap x‖ ^ 2 ≤
          4 * suzukiProjectAStar *
            ‖suzukiCorrectedFormGlobalRestriction x‖ ^ 2 := by
    rintro _ ⟨v, rfl⟩
    rw [suzukiLowFrequencyWeightedFourierCompletionMap_core,
      norm_sq_suzukiLowFrequencyWeightedFourierLinearMap]
    exact suzukiLowFrequencyLogLossForm_le suzukiProjectAStar_pos
      (suzukiSmoothCoreLinearSubmoduleAsCore v)
  exact
    (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
      suzukiProjectAStar).induction hmem
        (isClosed_le (by fun_prop) (by fun_prop)) u

/-- The bounded physical `L²` operator whose pairing is the frozen prime-2
translation form. -/
def suzukiYoshidaPrimeTwoL2Operator : SuzukiL2 →L[Complex] SuzukiL2 :=
  ∑ i ∈ suzukiProjectPrimeIndexSet suzukiProjectAStar,
    (suzukiProjectPrimeCoefficient i : Complex) •
      (suzukiL2TranslateCLM (suzukiProjectPrimeShift i) +
        suzukiL2TranslateCLM (-suzukiProjectPrimeShift i))

/-- The physical prime-2 operator represents exactly the completed prime-2
form. -/
theorem inner_suzukiYoshidaPrimeTwoL2Operator
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    inner Complex
        (suzukiYoshidaPrimeTwoL2Operator
          (suzukiLogRadiusLinearCompletionToL2 u))
        (suzukiLogRadiusLinearCompletionToL2 v) =
      suzukiYoshidaPrimeTwoForm u v := by
  unfold suzukiYoshidaPrimeTwoForm
  classical
  unfold suzukiYoshidaPrimeTwoL2Operator
    suzukiL2FiniteTranslationEnergy suzukiL2SymmetricTranslationEnergy
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, sum_inner, inner_smul_left,
    Complex.conj_ofReal, inner_add_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show inner Complex
      (suzukiL2TranslateCLM (-suzukiProjectPrimeShift i)
        (suzukiLogRadiusLinearCompletionToL2 u))
      (suzukiLogRadiusLinearCompletionToL2 v) =
        inner Complex (suzukiLogRadiusLinearCompletionToL2 u)
          (suzukiL2TranslateCLM (suzukiProjectPrimeShift i)
            (suzukiLogRadiusLinearCompletionToL2 v)) by
      rw [← suzukiL2Translate_adjoint,
        ContinuousLinearMap.adjoint_inner_left]]

/-- The bounded operator on the completed form domain representing the
corrected form plus the unit physical `L²` shift. -/
def suzukiYoshidaCorrectedShiftedFormOperator :
    SuzukiYoshidaCorrectedCommonFormDomain →L[Complex]
      SuzukiYoshidaCorrectedCommonFormDomain :=
  ContinuousLinearMap.id Complex SuzukiYoshidaCorrectedCommonFormDomain -
    suzukiCorrectedFormGlobalRestrictionAdjoint.comp
      suzukiCorrectedFormGlobalRestriction -
    suzukiCorrectedFormLowFrequencyMapAdjoint.comp
      suzukiCorrectedFormLowFrequencyMap +
    suzukiCorrectedFormGlobalRestrictionAdjoint.comp
      (suzukiYoshidaPrimeTwoL2Operator.comp
        suzukiCorrectedFormGlobalRestriction) -
    suzukiCorrectedFormGlobalRestrictionAdjoint.comp
      ((suzukiRSecondGlobalL2Operator suzukiProjectAStar).comp
        suzukiCorrectedFormGlobalRestriction)

set_option maxHeartbeats 800000 in
/-- The explicit bounded operator represents the corrected completed form plus
the unit physical `L²` shift. -/
theorem inner_suzukiYoshidaCorrectedShiftedFormOperator
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    inner Complex (suzukiYoshidaCorrectedShiftedFormOperator u) v =
      suzukiYoshidaCorrectedCompleteForm u v +
        inner Complex
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) := by
  have hu :
      (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar)
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) =
        suzukiLogRadiusLinearCompletionToL2 u := by
    have h := congrArg
      (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 =>
        T u)
      suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
    change (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).toContinuousLinearMap
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) = _
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hv :
      (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar)
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
        suzukiLogRadiusLinearCompletionToL2 v := by
    have h := congrArg
      (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 =>
        T v)
      suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
    change (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).toContinuousLinearMap
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) = _
    simpa only [ContinuousLinearMap.comp_apply] using h
  have hinterval :
      inner Complex
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
          (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
        inner Complex
          (suzukiLogRadiusLinearCompletionToL2 u)
          (suzukiLogRadiusLinearCompletionToL2 v) := by
    rw [← (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
      suzukiProjectAStar).inner_map_map, hu, hv]
  unfold suzukiYoshidaCorrectedShiftedFormOperator
    suzukiCorrectedFormGlobalRestrictionAdjoint
    suzukiCorrectedFormLowFrequencyMapAdjoint
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply]
  let a : SuzukiYoshidaCorrectedCommonFormDomain :=
    (ContinuousLinearMap.adjoint (𝕜 := Complex)
      (E := SuzukiYoshidaCorrectedCommonFormDomain) (F := SuzukiL2)
      suzukiCorrectedFormGlobalRestriction)
      (suzukiCorrectedFormGlobalRestriction u)
  let b : SuzukiYoshidaCorrectedCommonFormDomain :=
    (ContinuousLinearMap.adjoint (𝕜 := Complex)
      (E := SuzukiYoshidaCorrectedCommonFormDomain) (F := SuzukiL2)
      suzukiCorrectedFormLowFrequencyMap)
      (suzukiCorrectedFormLowFrequencyMap u)
  let c : SuzukiYoshidaCorrectedCommonFormDomain :=
    (ContinuousLinearMap.adjoint (𝕜 := Complex)
      (E := SuzukiYoshidaCorrectedCommonFormDomain) (F := SuzukiL2)
      suzukiCorrectedFormGlobalRestriction)
      (suzukiYoshidaPrimeTwoL2Operator
        (suzukiCorrectedFormGlobalRestriction u))
  let d : SuzukiYoshidaCorrectedCommonFormDomain :=
    (ContinuousLinearMap.adjoint (𝕜 := Complex)
      (E := SuzukiYoshidaCorrectedCommonFormDomain) (F := SuzukiL2)
      suzukiCorrectedFormGlobalRestriction)
      ((suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (suzukiCorrectedFormGlobalRestriction u))
  change ((innerₛₗ Complex
    (E := SuzukiYoshidaCorrectedCommonFormDomain)).flip v)
      ((((u - a) - b) + c) - d) = _
  simp only [map_sub, map_add]
  change inner Complex u v - inner Complex a v - inner Complex b v +
      inner Complex c v - inner Complex d v = _
  dsimp only [a, b, c, d]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [inner_suzukiYoshidaPrimeTwoL2Operator, hinterval]
  unfold suzukiYoshidaCorrectedCompleteForm suzukiYoshidaComparisonForm
    suzukiYoshidaGammaRemainderForm suzukiL2BoundedOperatorEnergy
    suzukiLowFrequencyLogLossEnergy
  push_cast
  ring

/-- Real diagonal expansion of the explicit shifted-form representative. -/
theorem re_inner_suzukiYoshidaCorrectedShiftedFormOperator
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    (inner Complex (suzukiYoshidaCorrectedShiftedFormOperator u) u).re =
      ‖u‖ ^ 2 - ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 -
        ‖suzukiCorrectedFormLowFrequencyMap u‖ ^ 2 +
        (suzukiYoshidaPrimeTwoForm u u).re -
        (suzukiYoshidaGammaRemainderForm u u).re := by
  have hrecover := congrArg
    (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 =>
      T u)
    suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
  have hintervalNorm :
      ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ =
        ‖suzukiCorrectedFormGlobalRestriction u‖ := by
    calc
      ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ =
          ‖(suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar)
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)‖ :=
        ((suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar).norm_map _).symm
      _ = ‖suzukiCorrectedFormGlobalRestriction u‖ := by
        rw [show (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar)
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) =
            suzukiCorrectedFormGlobalRestriction u by
          change (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar).toContinuousLinearMap
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) = _
          simpa only [ContinuousLinearMap.comp_apply] using hrecover]
  rw [inner_suzukiYoshidaCorrectedShiftedFormOperator, Complex.add_re]
  rw [show (inner Complex
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)).re =
        ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ ^ 2 by
      exact inner_self_eq_norm_sq (𝕜 := Complex)
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)]
  rw [hintervalNorm]
  unfold suzukiYoshidaCorrectedCompleteForm suzukiYoshidaComparisonForm
    suzukiLowFrequencyLogLossEnergy
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [show (inner Complex u u).re = ‖u‖ ^ 2 by
      exact inner_self_eq_norm_sq (𝕜 := Complex) u]
  rw [show (inner Complex
      (suzukiCorrectedFormGlobalRestriction u)
      (suzukiCorrectedFormGlobalRestriction u)).re =
        ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 by
      exact inner_self_eq_norm_sq (𝕜 := Complex)
        (suzukiCorrectedFormGlobalRestriction u)]
  rw [show (inner Complex
      (suzukiCorrectedFormLowFrequencyMap u)
      (suzukiCorrectedFormLowFrequencyMap u)).re =
        ‖suzukiCorrectedFormLowFrequencyMap u‖ ^ 2 by
      exact inner_self_eq_norm_sq (𝕜 := Complex)
        (suzukiCorrectedFormLowFrequencyMap u)]
  ring

/-- A finite `L²`-loss constant for the elementary completed-domain lower
bound.  Its size is irrelevant: endpoint positivity will absorb this loss. -/
def suzukiCorrectedShiftedFormL2LossBound : Real :=
  1 + 4 * suzukiProjectAStar + suzukiDF6D4DF0PrimeNorm +
    ‖suzukiRSecondGlobalL2Operator suzukiProjectAStar‖

/-- The shifted-form diagonal controls the completed graph norm up to one
finite multiple of the physical `L²` norm. -/
theorem norm_sq_le_re_inner_suzukiYoshidaCorrectedShiftedFormOperator_add_l2
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    ‖u‖ ^ 2 ≤
      (inner Complex
        (suzukiYoshidaCorrectedShiftedFormOperator u) u).re +
      suzukiCorrectedShiftedFormL2LossBound *
        ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 := by
  have hlow := norm_sq_suzukiCorrectedFormLowFrequencyMap_le u
  have hprimeAbs := suzukiDF6D5B3FFPrimeBound_of_support u
  have hprime :
      -(suzukiDF6D4DF0PrimeNorm *
          ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2) ≤
        (suzukiYoshidaPrimeTwoForm u u).re :=
    (neg_le_neg hprimeAbs).trans (neg_abs_le _)
  have hgammaAbs := suzukiL2BoundedOperatorDiagonal_abs_le
    (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
    (suzukiCorrectedFormGlobalRestriction u)
  have hgamma :
      (suzukiYoshidaGammaRemainderForm u u).re ≤
        ‖suzukiRSecondGlobalL2Operator suzukiProjectAStar‖ *
          ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 := by
    exact (le_abs_self _).trans (by
      simpa only [suzukiYoshidaGammaRemainderForm,
        suzukiL2BoundedOperatorEnergy,
        suzukiL2BoundedOperatorDiagonal] using hgammaAbs)
  rw [re_inner_suzukiYoshidaCorrectedShiftedFormOperator]
  unfold suzukiCorrectedShiftedFormL2LossBound
  nlinarith

/-- Endpoint positivity makes the shifted-form diagonal dominate the physical
`L²` coordinate. -/
theorem norm_sq_suzukiCorrectedFormGlobalRestriction_le_re_inner_shiftedForm
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 ≤
      (inner Complex
        (suzukiYoshidaCorrectedShiftedFormOperator u) u).re := by
  have hendpoint := suzukiDF6D5B4_fixedEndpoint_coercive
    hsource hequation25 u
  have hrecover := congrArg
    (fun T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] SuzukiL2 =>
      T u)
    suzukiFiniteIntervalL2ZeroExtension_comp_completionRestriction
  have hintervalNorm :
      ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ =
        ‖suzukiCorrectedFormGlobalRestriction u‖ := by
    calc
      ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ =
          ‖(suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar)
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)‖ :=
        ((suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
          suzukiProjectAStar).norm_map _).symm
      _ = ‖suzukiCorrectedFormGlobalRestriction u‖ := by
        rw [show (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar)
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) =
            suzukiCorrectedFormGlobalRestriction u by
          change (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry
            suzukiProjectAStar).toContinuousLinearMap
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u) = _
          simpa only [ContinuousLinearMap.comp_apply] using hrecover]
  have hpair := congrArg Complex.re
    (inner_suzukiYoshidaCorrectedShiftedFormOperator u u)
  rw [Complex.add_re] at hpair
  rw [show (inner Complex
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
      (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)).re =
        ‖suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u‖ ^ 2 by
      exact inner_self_eq_norm_sq (𝕜 := Complex)
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u),
    hintervalNorm] at hpair
  rw [hpair]
  nlinarith

/-- The exact completed-form-domain estimate: the explicit bounded
representative of the unit-shifted corrected form has a positive uniform
diagonal lower bound. -/
def SuzukiCorrectedShiftedFormOperatorCoercive : Prop :=
  ∃ c : ℝ≥0, 0 < c ∧
    ∀ u : SuzukiYoshidaCorrectedCommonFormDomain,
      ‖u‖ ^ 2 * c ≤
        ‖inner Complex (suzukiYoshidaCorrectedShiftedFormOperator u) u‖

/-- The checked endpoint source and equation-(2.5) premises prove the exact
completed-form-domain coercivity estimate required by the Friedrichs bridge.
-/
theorem suzukiCorrectedShiftedFormOperatorCoercive_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiCorrectedShiftedFormOperatorCoercive := by
  have hprimeNonneg : 0 ≤ suzukiDF6D4DF0PrimeNorm := by
    unfold suzukiDF6D4DF0PrimeNorm
    positivity
  have hB : 0 ≤ suzukiCorrectedShiftedFormL2LossBound := by
    unfold suzukiCorrectedShiftedFormL2LossBound
    nlinarith [suzukiProjectAStar_pos.le, hprimeNonneg,
      norm_nonneg (suzukiRSecondGlobalL2Operator suzukiProjectAStar)]
  have hden : 0 < 1 + suzukiCorrectedShiftedFormL2LossBound := by
    linarith
  let c : ℝ≥0 :=
    ⟨(1 + suzukiCorrectedShiftedFormL2LossBound)⁻¹,
      inv_nonneg.mpr hden.le⟩
  refine ⟨c, ?_, ?_⟩
  · change 0 < (1 + suzukiCorrectedShiftedFormL2LossBound)⁻¹
    exact inv_pos.mpr hden
  · intro u
    let q : Complex :=
      inner Complex (suzukiYoshidaCorrectedShiftedFormOperator u) u
    have hgraph :=
      norm_sq_le_re_inner_suzukiYoshidaCorrectedShiftedFormOperator_add_l2 u
    have hphysical :=
      norm_sq_suzukiCorrectedFormGlobalRestriction_le_re_inner_shiftedForm
        hsource hequation25 u
    have hqNonneg : 0 ≤ q.re :=
      (sq_nonneg ‖suzukiCorrectedFormGlobalRestriction u‖).trans hphysical
    have hscaled :
        ‖u‖ ^ 2 ≤
          (1 + suzukiCorrectedShiftedFormL2LossBound) * q.re := by
      calc
        ‖u‖ ^ 2 ≤ q.re + suzukiCorrectedShiftedFormL2LossBound *
            ‖suzukiCorrectedFormGlobalRestriction u‖ ^ 2 := by
          simpa only [q] using hgraph
        _ ≤ q.re + suzukiCorrectedShiftedFormL2LossBound * q.re := by
          gcongr
        _ = (1 + suzukiCorrectedShiftedFormL2LossBound) * q.re := by ring
    change ‖u‖ ^ 2 *
        (1 + suzukiCorrectedShiftedFormL2LossBound)⁻¹ ≤ ‖q‖
    calc
      ‖u‖ ^ 2 * (1 + suzukiCorrectedShiftedFormL2LossBound)⁻¹ ≤ q.re := by
        rw [← div_eq_mul_inv]
        apply (div_le_iff₀ hden).2
        simpa only [mul_comm] using hscaled
      _ = |q.re| := (abs_of_nonneg hqNonneg).symm
      _ ≤ ‖q‖ := Complex.abs_re_le_norm q

/-- Surjectivity of one real shifted resolvent makes a densely defined
symmetric partial operator maximal symmetric, hence self-adjoint. -/
theorem linearPMap_isSelfAdjoint_of_isFormalAdjoint_of_add_identity_surjective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H]
    (A : H →ₗ.[Complex] H)
    (hDense : Dense (A.domain : Set H))
    (hSymm : A.IsFormalAdjoint A)
    (hSurj : ∀ f : H, ∃ x : A.domain, A x + (x : H) = f) :
    IsSelfAdjoint A := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hA_le : A ≤ A† := hSymm.le_adjoint hDense
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let y' : A†.domain := ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hSurj (A† y' + y)
      have hyx : y = (x : H) := by
        rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := Complex)]
        obtain ⟨v, hv⟩ := hSurj (y - (x : H))
        calc
          inner Complex (y - (x : H)) (y - (x : H)) =
              inner Complex (y - (x : H)) (A v + (v : H)) := by rw [hv]
          _ = inner Complex (A† y') (v : H) -
                inner Complex (A x) (v : H) +
              (inner Complex y (v : H) - inner Complex (x : H) (v : H)) := by
                rw [inner_add_right, inner_sub_left, inner_sub_left]
                rw [(LinearPMap.adjoint_isFormalAdjoint hDense) y' v,
                  hSymm x v]
          _ = inner Complex ((A† y' + y) - (A x + (x : H))) (v : H) := by
                simp only [inner_sub_left, inner_add_left]
                ring
          _ = 0 := by rw [← hx, sub_self, inner_zero_left]
      rw [hyx]
      exact x.2
    · intro y x hyx
      exact (hA_le.2 hyx.symm).symm
  · exact hA_le

/-- A bounded complex Hilbert-space operator with a uniform diagonal lower
bound is onto.  This is the complex coercivity consequence used below. -/
theorem continuousLinearMap_surjective_of_forall_le_norm_inner_map
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [CompleteSpace H]
    (T : H →L[Complex] H) {c : ℝ≥0} (hc : 0 < c)
    (hcoercive : ∀ u : H, ‖u‖ ^ 2 * c ≤ ‖inner Complex (T u) u‖) :
    Function.Surjective T := by
  have hunit : IsUnit T :=
    ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
      (𝕜 := Complex) T hc hcoercive
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2

/-- The exact real-shift variational solvability statement for the corrected
completed form.  This is the remaining closed-form/Friedrichs theorem shape,
not an admitted consequence of the current source premises. -/
def SuzukiCorrectedFormShiftedVariationalSolvable : Prop :=
  ∀ f : SuzukiFiniteIntervalL2 suzukiProjectAStar,
    ∃ u : SuzukiYoshidaCorrectedCommonFormDomain,
      ∀ v : SuzukiYoshidaCorrectedCommonFormDomain,
        inner Complex f
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
          suzukiYoshidaCorrectedCompleteForm u v +
            inner Complex
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
              (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v)

set_option maxHeartbeats 800000 in
/-- A surjective bounded form-domain representative supplies the shifted
variational solutions.  The generic coercivity theorem above supplies this
surjectivity from a genuine completed-form-domain diagonal lower bound. -/
theorem suzukiCorrectedForm_shiftedVariationalSolvable_of_surjectiveRepresentation
    (T : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex]
      SuzukiYoshidaCorrectedCommonFormDomain)
    (hsurj : Function.Surjective T)
    (hpair : ∀ u v : SuzukiYoshidaCorrectedCommonFormDomain,
      inner Complex (T u) v =
        suzukiYoshidaCorrectedCompleteForm u v +
          inner Complex
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v)) :
    SuzukiCorrectedFormShiftedVariationalSolvable := by
  let J : SuzukiYoshidaCorrectedCommonFormDomain →L[Complex]
      SuzukiFiniteIntervalL2 suzukiProjectAStar :=
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2
  let Jadj : SuzukiFiniteIntervalL2 suzukiProjectAStar →L[Complex]
      SuzukiYoshidaCorrectedCommonFormDomain :=
    ContinuousLinearMap.adjoint (𝕜 := Complex)
      (E := SuzukiYoshidaCorrectedCommonFormDomain)
      (F := SuzukiFiniteIntervalL2 suzukiProjectAStar) J
  intro f
  obtain ⟨u, hu⟩ := hsurj (Jadj f)
  refine ⟨u, ?_⟩
  intro v
  calc
    inner Complex f
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) =
      inner Complex
        (Jadj f) v := by
          exact (ContinuousLinearMap.adjoint_inner_left
            (𝕜 := Complex)
            (E := SuzukiYoshidaCorrectedCommonFormDomain)
            (F := SuzukiFiniteIntervalL2 suzukiProjectAStar) J v f).symm
    _ = inner Complex (T u) v := by rw [hu]
    _ = suzukiYoshidaCorrectedCompleteForm u v +
          inner Complex
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)
            (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v) := hpair u v

/-- A shifted variational solution gives a graph point whose operator value
is `f - u`; equivalently, the real shifted resolvent has value `f`. -/
theorem suzukiCorrectedForm_add_identity_surjective_of_variational
    (hVariational : SuzukiCorrectedFormShiftedVariationalSolvable) :
    ∀ f : SuzukiFiniteIntervalL2 suzukiProjectAStar,
      ∃ x : suzukiYoshidaCorrectedFormAssociatedOperator.domain,
        suzukiYoshidaCorrectedFormAssociatedOperator x +
            (x : SuzukiFiniteIntervalL2 suzukiProjectAStar) = f := by
  intro f
  obtain ⟨u, hu⟩ := hVariational f
  let x0 := suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u
  let y0 := f - x0
  have hgraph : (x0, y0) ∈ suzukiYoshidaCorrectedFormAssociatedGraph := by
    refine ⟨u, rfl, ?_⟩
    intro v
    dsimp only [y0, x0]
    rw [inner_sub_left, hu v]
    ring
  rw [← suzukiYoshidaCorrectedFormAssociatedOperator_graph,
    LinearPMap.mem_graph_iff] at hgraph
  rcases hgraph with ⟨x, hx, hvalue⟩
  refine ⟨x, ?_⟩
  rw [hvalue, hx]
  dsimp only [y0, x0]
  abel

/-- The shifted variational theorem is sufficient for self-adjointness of the
concrete operator represented by the corrected completed form. -/
theorem suzukiYoshidaCorrectedFormAssociatedOperator_isSelfAdjoint_of_variational
    (hVariational : SuzukiCorrectedFormShiftedVariationalSolvable) :
    IsSelfAdjoint suzukiYoshidaCorrectedFormAssociatedOperator :=
  linearPMap_isSelfAdjoint_of_isFormalAdjoint_of_add_identity_surjective
    suzukiYoshidaCorrectedFormAssociatedOperator
    dense_suzukiYoshidaCorrectedFormAssociatedOperator_domain
    suzukiYoshidaCorrectedFormAssociatedOperator_isFormalAdjoint
    (suzukiCorrectedForm_add_identity_surjective_of_variational hVariational)

/-- Surjectivity of the explicit shifted-form representative is the exact
bounded-operator input consumed by the variational/Friedrichs chain. -/
def SuzukiCorrectedShiftedFormOperatorSurjective : Prop :=
  Function.Surjective suzukiYoshidaCorrectedShiftedFormOperator

/-- Surjectivity of the explicit shifted-form representative closes the
Friedrichs maximality step for the corrected associated operator.  The generic
coercivity theorem above supplies this input from a positive diagonal lower
bound without adding that analytic estimate as a premise here. -/
theorem
    suzukiYoshidaCorrectedFormAssociatedOperator_isSelfAdjoint_of_shiftedFormOperatorSurjective
    (hSurjective : SuzukiCorrectedShiftedFormOperatorSurjective) :
    IsSelfAdjoint suzukiYoshidaCorrectedFormAssociatedOperator := by
  apply
    suzukiYoshidaCorrectedFormAssociatedOperator_isSelfAdjoint_of_variational
  exact suzukiCorrectedForm_shiftedVariationalSolvable_of_surjectiveRepresentation
    suzukiYoshidaCorrectedShiftedFormOperator hSurjective
    inner_suzukiYoshidaCorrectedShiftedFormOperator

end

end RiemannHypothesisProject.Experiments.M100
