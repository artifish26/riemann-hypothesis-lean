import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaModePairingNormalization

/-!
# Exponential-source pairing bridge for M100-DF6D5B3P

This module separates the two analytic inputs needed to identify the actual
completed Yoshida-mode pairings with the frozen DF6D4 endpoint matrices:

1. a source-to-project theorem evaluating the completed form on the periodic
   exponential basis; and
2. a normalization theorem identifying the corresponding even and odd
   combinations of that source kernel with the endpoint entries.

The bridge from those inputs to the existing B3N pairing targets is proved
here.  Neither analytic input is assumed by an endpoint certificate.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped ComplexConjugate

/-- A canonical completed lift of a periodic endpoint exponential, chosen
from the exact B2S form-core source theorem. -/
noncomputable def suzukiYoshidaExponentialLinearCompletionOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    SuzukiLogRadiusLinearCompletion r :=
  Classical.choose
    (exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
      hsource hr n)

@[simp]
theorem suzukiYoshidaExponentialLinearCompletionOfSource_toL2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiYoshidaExponentialLinearCompletionOfSource hsource hr n) =
      suzukiYoshidaExponentialL2 r hr n :=
  Classical.choose_spec
    (exists_suzukiYoshidaExponentialLogRadiusLinearCompletion
      hsource hr n)

/-- The canonical completed even mode assembled from exponential lifts. -/
noncomputable def suzukiYoshidaEvenLinearCompletionOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    SuzukiLogRadiusLinearCompletion r :=
  if _hn : n = 0 then
    suzukiYoshidaExponentialLinearCompletionOfSource hsource hr 0
  else
    ((Real.sqrt 2)⁻¹ : Complex) •
      (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource hr (n : Int) +
        suzukiYoshidaExponentialLinearCompletionOfSource
          hsource hr (-(n : Int)))

/-- The canonical completed odd mode assembled from exponential lifts. -/
noncomputable def suzukiYoshidaOddLinearCompletionOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    SuzukiLogRadiusLinearCompletion r :=
  ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) •
    (suzukiYoshidaExponentialLinearCompletionOfSource
        hsource hr (n : Int) -
      suzukiYoshidaExponentialLinearCompletionOfSource
        hsource hr (-(n : Int)))

@[simp]
theorem suzukiYoshidaEvenLinearCompletionOfSource_toL2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiYoshidaEvenLinearCompletionOfSource hsource hr n) =
      suzukiYoshidaEvenL2 r hr n := by
  unfold suzukiYoshidaEvenLinearCompletionOfSource suzukiYoshidaEvenL2
  split_ifs
  · exact
      suzukiYoshidaExponentialLinearCompletionOfSource_toL2
        hsource hr 0
  · rw [map_smul, map_add]
    rw [suzukiYoshidaExponentialLinearCompletionOfSource_toL2,
      suzukiYoshidaExponentialLinearCompletionOfSource_toL2]

@[simp]
theorem suzukiYoshidaOddLinearCompletionOfSource_toL2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiYoshidaOddLinearCompletionOfSource hsource hr n) =
      suzukiYoshidaOddL2 r hr n := by
  unfold suzukiYoshidaOddLinearCompletionOfSource suzukiYoshidaOddL2
  rw [map_smul, map_sub]
  rw [suzukiYoshidaExponentialLinearCompletionOfSource_toL2,
    suzukiYoshidaExponentialLinearCompletionOfSource_toL2]

/-- The B2S certificate's chosen even lift is the canonical exponential
combination.  This uses injectivity of the completion-to-`L²` map, so the
statement is independent of the implementation of `Classical.choose`. -/
theorem suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    (suzukiProjectB2EndpointModeCertificateOfSource hsource).evenMode i =
      suzukiYoshidaEvenLinearCompletionOfSource
        hsource suzukiProjectAStar_pos i.1 := by
  apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
  rw [suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  unfold suzukiProjectB2EndpointModeCertificateOfSource
    suzukiB2EndpointModeCertificateOfSource
    suzukiB2EndpointModeCertificateOfMembership
  exact Classical.choose_spec
    (exists_suzukiYoshidaEvenLogRadiusLinearCompletion_fin45
      hsource suzukiProjectAStar_pos i)

/-- The B2S certificate's chosen odd lift is the canonical exponential
combination. -/
theorem suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    (suzukiProjectB2EndpointModeCertificateOfSource hsource).oddMode i =
      suzukiYoshidaOddLinearCompletionOfSource
        hsource suzukiProjectAStar_pos (i.1 + 1) := by
  apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
  rw [suzukiYoshidaOddLinearCompletionOfSource_toL2]
  unfold suzukiProjectB2EndpointModeCertificateOfSource
    suzukiB2EndpointModeCertificateOfSource
    suzukiB2EndpointModeCertificateOfMembership
  exact Classical.choose_spec
    (exists_suzukiYoshidaOddLogRadiusLinearCompletion_fin44
      hsource suzukiProjectAStar_pos i)

/-- Conjugate-linearity gives subtraction in the first argument. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_sub_left
    (u w v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiProjectLogRadiusLinearCompleteEnergy (u - w) v =
      suzukiProjectLogRadiusLinearCompleteEnergy u v -
        suzukiProjectLogRadiusLinearCompleteEnergy w v := by
  rw [sub_eq_add_neg,
    suzukiProjectLogRadiusLinearCompleteEnergy_add_left]
  rw [show -w = (-1 : Complex) • w by
      exact (neg_one_smul Complex w).symm,
    suzukiProjectLogRadiusLinearCompleteEnergy_smul_left]
  rw [sub_eq_add_neg]
  norm_num

/-- Linearity gives subtraction in the second argument. -/
theorem suzukiProjectLogRadiusLinearCompleteEnergy_sub_right
    (u v w : SuzukiLogRadiusLinearCompletion suzukiProjectAStar) :
    suzukiProjectLogRadiusLinearCompleteEnergy u (v - w) =
      suzukiProjectLogRadiusLinearCompleteEnergy u v -
        suzukiProjectLogRadiusLinearCompleteEnergy u w := by
  rw [sub_eq_add_neg,
    suzukiProjectLogRadiusLinearCompleteEnergy_add_right]
  rw [show -w = (-1 : Complex) • w by
      exact (neg_one_smul Complex w).symm,
    suzukiProjectLogRadiusLinearCompleteEnergy_smul_right]
  rw [sub_eq_add_neg]
  norm_num

/-- The source kernel combined into two normalized even Yoshida modes.  The
zero-mode branches keep the exceptional constant-mode normalization
explicit. -/
def suzukiYoshidaEvenSourceKernelPairing
    (kernel : Int → Int → Complex) (m n : Nat) : Complex :=
  let s : Complex := (Real.sqrt 2)⁻¹
  if _hm : m = 0 then
    if _hn : n = 0 then kernel 0 0
    else
      s * (kernel 0 (n : Int) + kernel 0 (-(n : Int)))
  else
    if _hn : n = 0 then
      conj s * (kernel (m : Int) 0 + kernel (-(m : Int)) 0)
    else
      conj s * s *
        (kernel (m : Int) (n : Int) +
          kernel (m : Int) (-(n : Int)) +
          kernel (-(m : Int)) (n : Int) +
          kernel (-(m : Int)) (-(n : Int)))

/-- The source kernel combined into two normalized odd Yoshida modes. -/
def suzukiYoshidaOddSourceKernelPairing
    (kernel : Int → Int → Complex) (m n : Nat) : Complex :=
  let t : Complex := (Complex.I * (Real.sqrt 2 : Complex))⁻¹
  conj t * t *
    (kernel (m : Int) (n : Int) -
      kernel (m : Int) (-(n : Int)) -
      kernel (-(m : Int)) (n : Int) +
      kernel (-(m : Int)) (-(n : Int)))

/-- Literature-shaped source-to-project bridge: an explicit source kernel
evaluates the actual completed form on every pair of periodic exponentials.
No endpoint matrix or positivity conclusion occurs in this statement. -/
def SuzukiYoshidaExponentialSourceToProjectPairingBridge
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (kernel : Int → Int → Complex) : Prop :=
  ∀ m n : Int,
    suzukiProjectLogRadiusLinearCompleteEnergy
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      kernel m n

/-- Checked normalization target from a source exponential kernel to the
frozen DF6D4 even and odd endpoint entries.  This statement contains no
completed vectors and is therefore separate from the source-to-project
form bridge. -/
def SuzukiDF6D5B3PExponentialKernelNormalization
    (kernel : Int → Int → Complex) : Prop :=
  (∀ i j : Fin 45,
      suzukiYoshidaEvenSourceKernelPairing kernel i.1 j.1 =
        (suzukiDF6D4EvenEndpointMatrix i j : Complex)) ∧
    (∀ i j : Fin 44,
      suzukiYoshidaOddSourceKernelPairing kernel
          (i.1 + 1) (j.1 + 1) =
        (suzukiDF6D4OddEndpointMatrix i j : Complex))

theorem suzukiProjectLogRadiusLinearCompleteEnergy_evenSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (kernel : Int → Int → Complex)
    (hbridge :
      SuzukiYoshidaExponentialSourceToProjectPairingBridge hsource kernel)
    (m n : Nat) :
    suzukiProjectLogRadiusLinearCompleteEnergy
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaEvenSourceKernelPairing kernel m n := by
  unfold SuzukiYoshidaExponentialSourceToProjectPairingBridge at hbridge
  unfold suzukiYoshidaEvenLinearCompletionOfSource
    suzukiYoshidaEvenSourceKernelPairing
  split_ifs with hm hn hn
  · simpa using hbridge 0 0
  · rw [suzukiProjectLogRadiusLinearCompleteEnergy_smul_right,
      suzukiProjectLogRadiusLinearCompleteEnergy_add_right]
    simp_rw [hbridge]
  · rw [suzukiProjectLogRadiusLinearCompleteEnergy_smul_left,
      suzukiProjectLogRadiusLinearCompleteEnergy_add_left]
    simp_rw [hbridge]
  · rw [suzukiProjectLogRadiusLinearCompleteEnergy_smul_left,
      suzukiProjectLogRadiusLinearCompleteEnergy_smul_right,
      suzukiProjectLogRadiusLinearCompleteEnergy_add_left,
      suzukiProjectLogRadiusLinearCompleteEnergy_add_right,
      suzukiProjectLogRadiusLinearCompleteEnergy_add_right]
    simp_rw [hbridge]
    ring

theorem suzukiProjectLogRadiusLinearCompleteEnergy_oddSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (kernel : Int → Int → Complex)
    (hbridge :
      SuzukiYoshidaExponentialSourceToProjectPairingBridge hsource kernel)
    (m n : Nat) :
    suzukiProjectLogRadiusLinearCompleteEnergy
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaOddSourceKernelPairing kernel m n := by
  unfold SuzukiYoshidaExponentialSourceToProjectPairingBridge at hbridge
  unfold suzukiYoshidaOddLinearCompletionOfSource
    suzukiYoshidaOddSourceKernelPairing
  rw [suzukiProjectLogRadiusLinearCompleteEnergy_smul_left,
    suzukiProjectLogRadiusLinearCompleteEnergy_smul_right,
    suzukiProjectLogRadiusLinearCompleteEnergy_sub_left,
    suzukiProjectLogRadiusLinearCompleteEnergy_sub_right,
    suzukiProjectLogRadiusLinearCompleteEnergy_sub_right]
  simp_rw [hbridge]
  ring

/-- The separated exponential source theorem and kernel normalization prove
the exact even B3N entrywise target for the existing B2S certificate. -/
theorem suzukiDF6D5B3P_evenModePairing_of_exponentialSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (kernel : Int → Int → Complex)
    (hbridge :
      SuzukiYoshidaExponentialSourceToProjectPairingBridge hsource kernel)
    (hnormalization :
      SuzukiDF6D5B3PExponentialKernelNormalization kernel) :
    SuzukiDF6D5B3NEvenModePairingIdentity
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  intro i j
  rw [suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq,
    suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq,
    suzukiProjectLogRadiusLinearCompleteEnergy_evenSource
      hsource kernel hbridge]
  exact hnormalization.1 i j

/-- The separated exponential source theorem and kernel normalization prove
the exact odd B3N entrywise target for the existing B2S certificate. -/
theorem suzukiDF6D5B3P_oddModePairing_of_exponentialSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (kernel : Int → Int → Complex)
    (hbridge :
      SuzukiYoshidaExponentialSourceToProjectPairingBridge hsource kernel)
    (hnormalization :
      SuzukiDF6D5B3PExponentialKernelNormalization kernel) :
    SuzukiDF6D5B3NOddModePairingIdentity
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  intro i j
  rw [suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq,
    suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq,
    suzukiProjectLogRadiusLinearCompleteEnergy_oddSource
      hsource kernel hbridge]
  exact hnormalization.2 i j

/-- B3P endpoint: the two explicit analytic inputs discharge both actual
low-matrix identities through the B3N finite assembly. -/
theorem suzukiDF6D5B3P_lowMatrixIdentities_of_exponentialSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (kernel : Int → Int → Complex)
    (hbridge :
      SuzukiYoshidaExponentialSourceToProjectPairingBridge hsource kernel)
    (hnormalization :
      SuzukiDF6D5B3PExponentialKernelNormalization kernel) :
    SuzukiDF6D5B3EvenLowMatrixIdentity
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) ∧
      SuzukiDF6D5B3OddLowMatrixIdentity
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  constructor
  · exact suzukiDF6D5B3_evenLowMatrixIdentity_of_modePairing _
      (suzukiDF6D5B3P_evenModePairing_of_exponentialSource
        hsource kernel hbridge hnormalization)
  · exact suzukiDF6D5B3_oddLowMatrixIdentity_of_modePairing _
      (suzukiDF6D5B3P_oddModePairing_of_exponentialSource
        hsource kernel hbridge hnormalization)

end

end RiemannHypothesisProject.Experiments.M100
