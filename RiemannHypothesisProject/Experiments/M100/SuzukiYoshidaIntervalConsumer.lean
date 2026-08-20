import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointAssembly

/-!
# Concrete interval consumer for M100-DF6E

This module restricts the closed corrected endpoint form along the literal
zero-extension inclusions of the logarithmic radius completions.  It transfers
the B4 `1 / 400000` lower bound to every radius in the named first-prime
window.  The two source premises remain visible, and no source-operator
identification is asserted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set

/-- The exact compact radius window used by DF5C and DF6E. -/
def SuzukiDF6EInterval : Set Real :=
  Set.Icc (Real.log 2 / 2) suzukiProjectAStar

/-- The frozen endpoint lies strictly above the lower end of the DF6E
window. -/
theorem suzukiDF6E_log_two_div_two_lt_aStar :
    Real.log 2 / 2 < suzukiProjectAStar := by
  unfold suzukiProjectAStar
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp :
      0 < Real.exp (-2 * Real.sqrt 2 * Real.log 2) :=
    Real.exp_pos _
  have hradicand :
      0 ≤ Real.log 2 ^ 2 +
        4 * Real.exp (-2 * Real.sqrt 2 * Real.log 2) := by
    positivity
  have hsqrt_nonneg :
      0 ≤ Real.sqrt (Real.log 2 ^ 2 +
        4 * Real.exp (-2 * Real.sqrt 2 * Real.log 2)) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      Real.sqrt (Real.log 2 ^ 2 +
          4 * Real.exp (-2 * Real.sqrt 2 * Real.log 2)) ^ 2 =
        Real.log 2 ^ 2 +
          4 * Real.exp (-2 * Real.sqrt 2 * Real.log 2) :=
    Real.sq_sqrt hradicand
  nlinarith

theorem suzukiDF6E_interval_nonempty :
    SuzukiDF6EInterval.Nonempty := by
  exact ⟨Real.log 2 / 2,
    le_rfl, suzukiDF6E_log_two_div_two_lt_aStar.le⟩

/-- The full closed logarithmic form domain at a radius in the named window. -/
abbrev SuzukiYoshidaIntervalFormDomain (a : Real) : Type :=
  SuzukiLogRadiusLinearCompletion a

/-- Literal zero extension from a smaller radius to the frozen endpoint. -/
def suzukiYoshidaIntervalZeroExtension
    {a : Real} (ha : a ≤ suzukiProjectAStar) :
    SuzukiYoshidaIntervalFormDomain a →L[Complex]
      SuzukiYoshidaCorrectedCommonFormDomain :=
  suzukiLogRadiusLinearCompletionZeroExtension ha

@[simp]
theorem suzukiYoshidaIntervalZeroExtension_toL2
    {a : Real} (ha : a ≤ suzukiProjectAStar)
    (v : SuzukiYoshidaIntervalFormDomain a) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiYoshidaIntervalZeroExtension ha v) =
      suzukiLogRadiusLinearCompletionToL2 v :=
  suzukiLogRadiusLinearCompletionToL2_zeroExtension ha v

@[simp]
theorem suzukiYoshidaIntervalZeroExtension_norm
    {a : Real} (ha : a ≤ suzukiProjectAStar)
    (v : SuzukiYoshidaIntervalFormDomain a) :
    ‖suzukiYoshidaIntervalZeroExtension ha v‖ = ‖v‖ :=
  suzukiLogRadiusLinearCompletionZeroExtension_norm ha v

/-- The concrete radius-`a` project form is the restriction of the closed
endpoint form along literal zero extension. -/
def suzukiYoshidaIntervalCompleteForm
    {a : Real} (ha : a ≤ suzukiProjectAStar)
    (u v : SuzukiYoshidaIntervalFormDomain a) : Complex :=
  suzukiYoshidaCorrectedCompleteForm
    (suzukiYoshidaIntervalZeroExtension ha u)
    (suzukiYoshidaIntervalZeroExtension ha v)

/-- Concrete DF6C nesting: widening the radius before restricting the endpoint
form gives exactly the same form value. -/
theorem suzukiYoshidaIntervalCompleteForm_zeroExtension
    {a b : Real} (hab : a ≤ b) (hb : b ≤ suzukiProjectAStar)
    (u v : SuzukiYoshidaIntervalFormDomain a) :
    suzukiYoshidaIntervalCompleteForm hb
        (suzukiLogRadiusLinearCompletionZeroExtension hab u)
        (suzukiLogRadiusLinearCompletionZeroExtension hab v) =
      suzukiYoshidaIntervalCompleteForm (hab.trans hb) u v := by
  have hu :
      suzukiYoshidaIntervalZeroExtension hb
          (suzukiLogRadiusLinearCompletionZeroExtension hab u) =
        suzukiYoshidaIntervalZeroExtension (hab.trans hb) u := by
    apply Subtype.ext
    rfl
  have hv :
      suzukiYoshidaIntervalZeroExtension hb
          (suzukiLogRadiusLinearCompletionZeroExtension hab v) =
        suzukiYoshidaIntervalZeroExtension (hab.trans hb) v := by
    apply Subtype.ext
    rfl
  rw [suzukiYoshidaIntervalCompleteForm,
    suzukiYoshidaIntervalCompleteForm, hu, hv]

/-- DF6E form-level conclusion: the B4 constant holds at every radius in the
exact named interval, on the whole closed radius domain. -/
theorem suzukiDF6E_interval_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (v : SuzukiYoshidaIntervalFormDomain a) :
    (1 / 400000 : Real) *
        ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 ≤
      (suzukiYoshidaIntervalCompleteForm ha.2 v v).re := by
  have hendpoint :=
    suzukiDF6D5B4_fixedEndpoint_coercive hsource hequation25
      (suzukiYoshidaIntervalZeroExtension ha.2 v)
  rw [suzukiYoshidaIntervalZeroExtension_toL2] at hendpoint
  exact hendpoint

end

end RiemannHypothesisProject.Experiments.M100
