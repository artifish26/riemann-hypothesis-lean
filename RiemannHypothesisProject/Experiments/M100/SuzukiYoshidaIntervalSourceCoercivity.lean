import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaIntervalConsumer
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourcePrimitiveBridge

/-!
# M100-DF6F interval source coercivity

This module feeds DF6E's closed interval estimate into the exact Suzuki source
operators.  The endpoint source premises remain explicit.  Cutoff invariance
is proved from literal support, so no equation-(2.5) premise is silently
introduced at smaller radii.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- On a smooth core vector, the radius-`a` interval form is the endpoint
project-normalized form of its literal zero extension. -/
theorem suzukiYoshidaIntervalCompleteForm_smoothCore
    {a : Real} (ha : a ≤ suzukiProjectAStar) (v : SuzukiSmoothCore a) :
    suzukiYoshidaIntervalCompleteForm ha
        (suzukiSmoothCoreToLogRadiusLinearCompletion v)
        (suzukiSmoothCoreToLogRadiusLinearCompletion v) =
      (suzukiProjectNormalizedCompleteCoreForm
        (suzukiSmoothCoreZeroExtension ha v) : Complex) := by
  let w : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar :=
    ⟨(suzukiSmoothCoreZeroExtension ha v).1,
      (suzukiSmoothCoreZeroExtension ha v).2⟩
  have hcore := suzukiYoshidaCorrectedCompleteForm_core_self w
  have hw :
      suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar w =
        suzukiSmoothCoreToLogRadiusLinearCompletion
          (suzukiSmoothCoreZeroExtension ha v) := by
    apply Subtype.ext
    rfl
  have hwcore :
      suzukiSmoothCoreLinearSubmoduleAsCore w =
        suzukiSmoothCoreZeroExtension ha v := by
    apply Subtype.ext
    rfl
  rw [hw, hwcore] at hcore
  unfold suzukiYoshidaIntervalCompleteForm
    suzukiYoshidaIntervalZeroExtension
  rw [suzukiSmoothCoreToLogRadiusLinearCompletion_zeroExtension ha]
  exact hcore

/-- Enlarging the square cutoff does not change a kernel pairing when both
source slots are supported in the smaller interval. -/
theorem suzukiFiniteKernelPairingComplex_eq_of_support_subset
    {a b : Real} (hab : a ≤ b) (kernel : Real → Real)
    {u : Real → Complex}
    (hsupport : Function.support u ⊆ Icc (-a) a) :
    suzukiFiniteKernelPairingComplex kernel b u =
      suzukiFiniteKernelPairingComplex kernel a u := by
  unfold suzukiFiniteKernelPairingComplex
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isCompact_suzukiFiniteSquare b).measurableSet
  · intro p hp
    exact ⟨⟨(neg_le_neg hab).trans hp.1.1, hp.1.2.trans hab⟩,
      ⟨(neg_le_neg hab).trans hp.2.1, hp.2.2.trans hab⟩⟩
  · intro p hp
    by_cases hx : p.1 ∈ Icc (-a) a
    · have hy : p.2 ∉ Icc (-a) a := by
        intro hy
        exact hp.2 ⟨hx, hy⟩
      have huy : u p.2 = 0 := by
        by_contra hne
        exact hy (hsupport hne)
      simp [suzukiKernelPairingIntegrand, huy]
    · have hux : u p.1 = 0 := by
        by_contra hne
        exact hx (hsupport hne)
      simp [suzukiKernelPairingIntegrand, hux]

/-- Real-valued facade of cutoff invariance. -/
theorem suzukiFiniteKernelPairing_eq_of_support_subset
    {a b : Real} (hab : a ≤ b) (kernel : Real → Real)
    {u : Real → Complex}
    (hsupport : Function.support u ⊆ Icc (-a) a) :
    suzukiFiniteKernelPairing kernel b u =
      suzukiFiniteKernelPairing kernel a u := by
  exact congrArg Complex.re
    (suzukiFiniteKernelPairingComplex_eq_of_support_subset
      hab kernel hsupport)

/-- Every radius in the named DF6E interval is positive. -/
theorem suzukiDF6E_radius_pos {a : Real} (ha : a ∈ SuzukiDF6EInterval) :
    0 < a := by
  have hlower : 0 < Real.log 2 / 2 :=
    div_pos (Real.log_pos (by norm_num)) (by norm_num)
  exact hlower.trans_le ha.1

/-- DF6F smooth-core source conclusion on the full named DF6E interval.
Only the frozen endpoint source premises are used. -/
theorem suzukiDF6F_interval_source_core_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) (v : SuzukiSmoothCore a) :
    (1 / 400000 : Real) *
        (inner Complex
          (suzukiSourceKOperator a
            (suzukiSmoothCoreDifferentialZeroMeanL2
              (suzukiDF6E_radius_pos ha) v))
          (suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos ha) v)).re ≤
      (inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos ha) v))
        (suzukiSmoothCoreDifferentialZeroMeanL2
          (suzukiDF6E_radius_pos ha) v)).re := by
  have haPos : 0 < a := suzukiDF6E_radius_pos ha
  have hDF6E := suzukiDF6E_interval_coercive hsource hequation25 ha
    (suzukiSmoothCoreToLogRadiusLinearCompletion v)
  rw [suzukiYoshidaIntervalCompleteForm_smoothCore ha.2 v] at hDF6E
  change (1 / 400000 : Real) * ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
    suzukiProjectNormalizedCompleteCoreForm
      (suzukiSmoothCoreZeroExtension ha.2 v) at hDF6E
  have hendpoint := hequation25 suzukiProjectAStar_pos
    (suzukiSmoothCoreZeroExtension ha.2 v)
  change suzukiFiniteKernelPairing suzukiScrewFunction suzukiProjectAStar
      (suzukiDifferential v.1) =
    suzukiProjectNormalizedCompleteCoreForm
      (suzukiSmoothCoreZeroExtension ha.2 v) at hendpoint
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hdiffSupport :
      Function.support (suzukiDifferential v.1) ⊆ Icc (-a) a :=
    support_suzukiDifferential_subset_Icc hsupport
  have hcutoff := suzukiFiniteKernelPairing_eq_of_support_subset
    ha.2 suzukiScrewFunction hdiffSupport
  have hsourceBound :
      (1 / 400000 : Real) * ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
        suzukiFiniteKernelPairing suzukiScrewFunction a
          (suzukiDifferential v.1) := by
    rw [← hcutoff, hendpoint]
    exact hDF6E
  unfold suzukiSmoothCoreDifferentialZeroMeanL2
  rw [inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq haPos v,
    re_inner_suzukiSourceGOperator_smoothCoreDifferential_eq_pairing haPos v]
  change (1 / 400000 : Real) * ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
    suzukiFiniteKernelPairing suzukiScrewFunction a
      (suzukiDifferential v.1)
  exact hsourceBound

/-- The exact remaining density statement for passing from compactly
supported primitives to the full closed zero-mean source space.  It is kept as
a separate named analytic target, not folded into an endpoint package. -/
def SuzukiSmoothDifferentialCoreDenseAt (a : Real) (ha : 0 < a) : Prop :=
  DenseRange (fun v : SuzukiSmoothCore a =>
    suzukiSmoothCoreDifferentialZeroMeanL2 ha v)

/-- Bounded-operator continuity extends the checked source comparison from
the smooth differential core to the full zero-mean space once the precise
density target is supplied. -/
theorem suzukiDF6F_interval_source_coercive_of_dense
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hdense : SuzukiSmoothDifferentialCoreDenseAt a
      (suzukiDF6E_radius_pos ha))
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    (1 / 400000 : Real) *
        (inner Complex (suzukiSourceKOperator a u) u).re ≤
      (inner Complex (suzukiSourceGOperator a u) u).re := by
  let p : SuzukiFiniteIntervalZeroMeanL2 a → Prop := fun w =>
    (1 / 400000 : Real) *
        (inner Complex (suzukiSourceKOperator a w) w).re ≤
      (inner Complex (suzukiSourceGOperator a w) w).re
  apply DenseRange.induction_on (p := p) hdense u
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro v
    dsimp only [p]
    exact suzukiDF6F_interval_source_core_coercive
      hsource hequation25 ha v

/-- The corresponding shifted source estimate.  In particular `lambda = 0`
recovers the exact X19B-entry comparison on the named interval; no global
choice of `lambda = 0` is asserted. -/
theorem suzukiDF6F_interval_shifted_source_coercive_of_dense
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hdense : SuzukiSmoothDifferentialCoreDenseAt a
      (suzukiDF6E_radius_pos ha))
    (lambda : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    ((1 / 400000 : Real) - lambda) *
        (inner Complex (suzukiSourceKOperator a u) u).re ≤
      (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re := by
  have hsourceCoercive :=
    suzukiDF6F_interval_source_coercive_of_dense
      hsource hequation25 ha hdense u
  rw [re_inner_suzukiSourceShiftedOperator]
  linarith

end

end RiemannHypothesisProject.Experiments.M100
