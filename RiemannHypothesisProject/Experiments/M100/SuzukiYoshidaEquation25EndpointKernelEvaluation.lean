import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCorrectedExponentialKernel

/-!
# Equation-(2.5) endpoint-kernel evaluation for M100-DF6D5B3Q-E

This module isolates the exact all-mode source evaluation still needed after
DF6D5B3Q.  Suzuki's equation (2.5), together with the B3V continuity bridge,
makes the source-limit kernel reflection invariant.  The remaining analytic
content is therefore exactly the evaluation of the complete even and odd
periodic Yoshida families.  Once those two all-mode families are supplied,
the theorem below reconstructs every integer-mode pair, including all zero
and sign branches.

The two parity propositions are theorem targets, not assumed endpoint
certificate fields.  They remain visibly separate from the B2S form-core
premise and from Suzuki's equation-(2.5) identity.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped ComplexConjugate

/-! ## Reflection of the canonical exponential lifts -/

theorem suzukiYoshidaExponentialLinearCompletionOfSource_reflection
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    suzukiLogRadiusLinearReflection r
        (suzukiYoshidaExponentialLinearCompletionOfSource hsource hr n) =
      suzukiYoshidaExponentialLinearCompletionOfSource hsource hr (-n) := by
  apply suzukiLogRadiusLinearCompletionToL2_injective r
  rw [suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiYoshidaExponentialLinearCompletionOfSource_toL2,
    suzukiYoshidaExponentialLinearCompletionOfSource_toL2,
    suzukiL2Reflection_exponential]

/-- Equation (2.5) and B3V continuity make the source-limit kernel invariant
under simultaneous reversal of both periodic frequencies. -/
theorem suzukiYoshidaEquation25LimitKernel_neg_neg
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaEquation25LimitKernel hsource (-m) (-n) =
      suzukiYoshidaEquation25LimitKernel hsource m n := by
  rw [← suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
      hsource hequation25,
    ← suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
      hsource hequation25,
    ← suzukiYoshidaExponentialLinearCompletionOfSource_reflection
      hsource suzukiProjectAStar_pos,
    ← suzukiYoshidaExponentialLinearCompletionOfSource_reflection
      hsource suzukiProjectAStar_pos,
    suzukiYoshidaCorrectedCompleteForm_reflection]

/-! ## Exact source-evaluation targets -/

/-- Citation-facing even periodic-mode evaluation.  It ranges over every
natural mode, including the exceptional constant mode. -/
def SuzukiEquation25EvenYoshidaEntryEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ m n : Nat,
    suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaEquation25LimitKernel hsource) m n =
      (suzukiYoshidaCorrectedEvenEntry m n : Complex)

/-- Citation-facing odd periodic-mode evaluation.  Only positive physical
frequencies occur in the odd family. -/
def SuzukiEquation25OddYoshidaEntryEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ m n : Nat, 0 < m → 0 < n →
    suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaEquation25LimitKernel hsource) m n =
      (suzukiYoshidaCorrectedOddEntry m n : Complex)

private theorem suzukiYoshidaEquation25_sqrtTwo_ne_zero :
    Real.sqrt 2 ≠ 0 := by
  positivity

private theorem suzukiYoshidaEquation25_even_coefficient :
    conj (((Real.sqrt 2)⁻¹ : Complex)) *
        ((Real.sqrt 2)⁻¹ : Complex) = (2 : Complex)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsquareC :
      (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [suzukiYoshidaEquation25_sqrtTwo_ne_zero]

private theorem suzukiYoshidaEquation25_even_normalization :
    (((Real.sqrt 2)⁻¹ : Complex) *
        ((Real.sqrt 2)⁻¹ : Complex)) * 2 = 1 := by
  rw [show
      (((Real.sqrt 2)⁻¹ : Complex) *
          ((Real.sqrt 2)⁻¹ : Complex)) = (2 : Complex)⁻¹ by
    simpa only [Complex.conj_ofReal, map_inv₀] using
      suzukiYoshidaEquation25_even_coefficient]
  norm_num

private theorem suzukiYoshidaEquation25_even_coefficient_plain :
    (((Real.sqrt 2)⁻¹ : Complex) *
        ((Real.sqrt 2)⁻¹ : Complex)) = (2 : Complex)⁻¹ := by
  simpa only [Complex.conj_ofReal, map_inv₀] using
    suzukiYoshidaEquation25_even_coefficient

private theorem suzukiYoshidaEquation25_odd_coefficient :
    conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) =
      (2 : Complex)⁻¹ := by
  rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsquareC :
      (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [suzukiYoshidaEquation25_sqrtTwo_ne_zero,
    Complex.I_ne_zero]
  rw [Complex.I_sq]

/-! ## Algebraic all-integer reconstruction -/

/-- The complete even and odd source evaluations determine the source kernel
on every integer-mode pair.  The proof explicitly covers the constant-mode,
same-sign, and opposite-sign branches. -/
theorem suzukiYoshidaEquation25EndpointKernelEvaluation_of_parityEntries
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (heven : SuzukiEquation25EvenYoshidaEntryEvaluation hsource)
    (hodd : SuzukiEquation25OddYoshidaEntryEvaluation hsource) :
    SuzukiYoshidaEquation25EndpointKernelEvaluation hsource := by
  let kernel : Int → Int → Complex :=
    suzukiYoshidaEquation25LimitKernel hsource
  have hreflection (m n : Int) :
      kernel (-m) (-n) = kernel m n := by
    exact suzukiYoshidaEquation25LimitKernel_neg_neg
      hsource hequation25 m n
  have hzeroZero :
      kernel 0 0 =
        (suzukiYoshidaCorrectedEvenEntry 0 0 : Complex) := by
    simpa [SuzukiEquation25EvenYoshidaEntryEvaluation,
      suzukiYoshidaEvenSourceKernelPairing, kernel] using heven 0 0
  have hzeroRight (n : Nat) (hn : 0 < n) :
      kernel 0 (n : Int) =
        ((Real.sqrt 2)⁻¹ : Complex) *
          (suzukiYoshidaCorrectedEvenEntry 0 n : Complex) := by
    have h :=
      heven 0 n
    have hreflect :
        kernel 0 (-(n : Int)) = kernel 0 (n : Int) := by
      simpa using hreflection 0 (n : Int)
    change
      suzukiYoshidaEvenSourceKernelPairing kernel 0 n =
        (suzukiYoshidaCorrectedEvenEntry 0 n : Complex) at h
    unfold suzukiYoshidaEvenSourceKernelPairing at h
    simp [Nat.ne_of_gt hn] at h
    rw [hreflect] at h
    calc
      kernel 0 (n : Int) =
          ((((Real.sqrt 2)⁻¹ : Complex) *
              ((Real.sqrt 2)⁻¹ : Complex)) * 2) *
            kernel 0 (n : Int) := by
              rw [suzukiYoshidaEquation25_even_normalization]
              simp
      _ = ((Real.sqrt 2)⁻¹ : Complex) *
          (((Real.sqrt 2)⁻¹ : Complex) *
            (kernel 0 (n : Int) + kernel 0 (n : Int))) := by ring
      _ = ((Real.sqrt 2)⁻¹ : Complex) *
          (suzukiYoshidaCorrectedEvenEntry 0 n : Complex) := by
            exact congrArg (((Real.sqrt 2)⁻¹ : Complex) * ·) h
  have hzeroLeft (m : Nat) (hm : 0 < m) :
      kernel (m : Int) 0 =
        ((Real.sqrt 2)⁻¹ : Complex) *
          (suzukiYoshidaCorrectedEvenEntry m 0 : Complex) := by
    have h := heven m 0
    have hreflect :
        kernel (-(m : Int)) 0 = kernel (m : Int) 0 := by
      simpa using hreflection (m : Int) 0
    change
      suzukiYoshidaEvenSourceKernelPairing kernel m 0 =
        (suzukiYoshidaCorrectedEvenEntry m 0 : Complex) at h
    unfold suzukiYoshidaEvenSourceKernelPairing at h
    simp [Nat.ne_of_gt hm] at h
    rw [hreflect] at h
    calc
      kernel (m : Int) 0 =
          ((((Real.sqrt 2)⁻¹ : Complex) *
              ((Real.sqrt 2)⁻¹ : Complex)) * 2) *
            kernel (m : Int) 0 := by
              rw [suzukiYoshidaEquation25_even_normalization]
              simp
      _ = ((Real.sqrt 2)⁻¹ : Complex) *
          (((Real.sqrt 2)⁻¹ : Complex) *
            (kernel (m : Int) 0 + kernel (m : Int) 0)) := by ring
      _ = ((Real.sqrt 2)⁻¹ : Complex) *
          (suzukiYoshidaCorrectedEvenEntry m 0 : Complex) := by
            exact congrArg (((Real.sqrt 2)⁻¹ : Complex) * ·) h
  have hsame (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
      kernel (m : Int) (n : Int) =
        (2 : Complex)⁻¹ *
          ((suzukiYoshidaCorrectedEvenEntry m n : Complex) +
            (suzukiYoshidaCorrectedOddEntry m n : Complex)) := by
    have hE := heven m n
    have hO := hodd m n hm hn
    have hnn :
        kernel (-(m : Int)) (-(n : Int)) =
          kernel (m : Int) (n : Int) :=
      hreflection (m : Int) (n : Int)
    have hnp :
        kernel (-(m : Int)) (n : Int) =
          kernel (m : Int) (-(n : Int)) := by
      simpa using hreflection (m : Int) (-(n : Int))
    change
      suzukiYoshidaEvenSourceKernelPairing kernel m n =
        (suzukiYoshidaCorrectedEvenEntry m n : Complex) at hE
    change
      suzukiYoshidaOddSourceKernelPairing kernel m n =
        (suzukiYoshidaCorrectedOddEntry m n : Complex) at hO
    unfold suzukiYoshidaEvenSourceKernelPairing at hE
    simp [Nat.ne_of_gt hm, Nat.ne_of_gt hn] at hE
    rw [hnn, hnp, suzukiYoshidaEquation25_even_coefficient_plain] at hE
    simp only [suzukiYoshidaOddSourceKernelPairing] at hO
    rw [hnn, hnp, suzukiYoshidaEquation25_odd_coefficient] at hO
    linear_combination (1 / 2 : Complex) * hE +
      (1 / 2 : Complex) * hO
  have hcross (m n : Nat) (hm : 0 < m) (hn : 0 < n) :
      kernel (m : Int) (-(n : Int)) =
        (2 : Complex)⁻¹ *
          ((suzukiYoshidaCorrectedEvenEntry m n : Complex) -
            (suzukiYoshidaCorrectedOddEntry m n : Complex)) := by
    have hE := heven m n
    have hO := hodd m n hm hn
    have hnn :
        kernel (-(m : Int)) (-(n : Int)) =
          kernel (m : Int) (n : Int) :=
      hreflection (m : Int) (n : Int)
    have hnp :
        kernel (-(m : Int)) (n : Int) =
          kernel (m : Int) (-(n : Int)) := by
      simpa using hreflection (m : Int) (-(n : Int))
    change
      suzukiYoshidaEvenSourceKernelPairing kernel m n =
        (suzukiYoshidaCorrectedEvenEntry m n : Complex) at hE
    change
      suzukiYoshidaOddSourceKernelPairing kernel m n =
        (suzukiYoshidaCorrectedOddEntry m n : Complex) at hO
    unfold suzukiYoshidaEvenSourceKernelPairing at hE
    simp [Nat.ne_of_gt hm, Nat.ne_of_gt hn] at hE
    rw [hnn, hnp, suzukiYoshidaEquation25_even_coefficient_plain] at hE
    simp only [suzukiYoshidaOddSourceKernelPairing] at hO
    rw [hnn, hnp, suzukiYoshidaEquation25_odd_coefficient] at hO
    linear_combination (1 / 2 : Complex) * hE -
      (1 / 2 : Complex) * hO
  intro m n
  change kernel m n = suzukiYoshidaCorrectedExplicitKernel m n
  cases m with
  | ofNat m =>
      cases n with
      | ofNat n =>
          by_cases hm : m = 0
          · subst m
            by_cases hn : n = 0
            · subst n
              simpa [kernel, suzukiYoshidaCorrectedExplicitKernel] using
                hzeroZero
            · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
              simpa [kernel, suzukiYoshidaCorrectedExplicitKernel, hn,
                hnPos] using hzeroRight n hnPos
          · have hmPos : 0 < m := Nat.pos_of_ne_zero hm
            by_cases hn : n = 0
            · subst n
              simpa [kernel, suzukiYoshidaCorrectedExplicitKernel, hm,
                hmPos] using hzeroLeft m hmPos
            · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
              simpa [kernel, suzukiYoshidaCorrectedExplicitKernel, hm, hn,
                hmPos, hnPos] using hsame m n hmPos hnPos
      | negSucc n =>
          by_cases hm : m = 0
          · subst m
            have hnPos : 0 < n + 1 := by omega
            have hreflect :
                kernel 0 (-((n + 1 : Nat) : Int)) =
                  kernel 0 ((n + 1 : Nat) : Int) := by
              simpa using hreflection 0 ((n + 1 : Nat) : Int)
            change
              kernel 0 (-((n + 1 : Nat) : Int)) =
                suzukiYoshidaCorrectedExplicitKernel
                  0 (-((n + 1 : Nat) : Int))
            rw [hreflect, hzeroRight (n + 1) hnPos]
            have hn0 : (-1 + -(n : Int)) ≠ 0 := by omega
            have hnAbs : (-1 + -(n : Int)).natAbs = n + 1 := by
              rw [show -1 + -(n : Int) = -((n + 1 : Nat) : Int) by omega,
                Int.natAbs_neg]
              exact Int.natAbs_natCast (n + 1)
            simp [suzukiYoshidaCorrectedExplicitKernel, hn0, hnAbs]
          · have hmPos : 0 < m := Nat.pos_of_ne_zero hm
            have hnPos : 0 < n + 1 := by omega
            change
              kernel (m : Int) (-((n + 1 : Nat) : Int)) =
                suzukiYoshidaCorrectedExplicitKernel
                  (m : Int) (-((n + 1 : Nat) : Int))
            rw [hcross m (n + 1) hmPos hnPos]
            have hn0 : (-1 + -(n : Int)) ≠ 0 := by omega
            have hnNotPos : ¬(0 : Int) < -1 + -(n : Int) := by omega
            have hnAbs : (-1 + -(n : Int)).natAbs = n + 1 := by
              rw [show -1 + -(n : Int) = -((n + 1 : Nat) : Int) by omega,
                Int.natAbs_neg]
              exact Int.natAbs_natCast (n + 1)
            simp [suzukiYoshidaCorrectedExplicitKernel, hm, hn0,
              hnNotPos, hnAbs]
  | negSucc m =>
      cases n with
      | ofNat n =>
          have hmPos : 0 < m + 1 := by omega
          by_cases hn : n = 0
          · subst n
            have hreflect :
                kernel (-((m + 1 : Nat) : Int)) 0 =
                  kernel ((m + 1 : Nat) : Int) 0 := by
              simpa using hreflection ((m + 1 : Nat) : Int) 0
            change
              kernel (-((m + 1 : Nat) : Int)) 0 =
                suzukiYoshidaCorrectedExplicitKernel
                  (-((m + 1 : Nat) : Int)) 0
            rw [hreflect, hzeroLeft (m + 1) hmPos]
            have hm0 : (-1 + -(m : Int)) ≠ 0 := by omega
            have hmAbs : (-1 + -(m : Int)).natAbs = m + 1 := by
              rw [show -1 + -(m : Int) = -((m + 1 : Nat) : Int) by omega,
                Int.natAbs_neg]
              exact Int.natAbs_natCast (m + 1)
            simp [suzukiYoshidaCorrectedExplicitKernel, hm0, hmAbs]
          · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
            have hreflect :
                kernel (-((m + 1 : Nat) : Int)) (n : Int) =
                  kernel ((m + 1 : Nat) : Int) (-(n : Int)) := by
              simpa using
                hreflection ((m + 1 : Nat) : Int) (-(n : Int))
            change
              kernel (-((m + 1 : Nat) : Int)) (n : Int) =
                suzukiYoshidaCorrectedExplicitKernel
                  (-((m + 1 : Nat) : Int)) (n : Int)
            rw [hreflect, hcross (m + 1) n hmPos hnPos]
            have hm0 : (-1 + -(m : Int)) ≠ 0 := by omega
            have hmNotPos : ¬(0 : Int) < -1 + -(m : Int) := by omega
            have hmAbs : (-1 + -(m : Int)).natAbs = m + 1 := by
              rw [show -1 + -(m : Int) = -((m + 1 : Nat) : Int) by omega,
                Int.natAbs_neg]
              exact Int.natAbs_natCast (m + 1)
            simp [suzukiYoshidaCorrectedExplicitKernel, hn, hm0,
              hmNotPos, hmAbs]
      | negSucc n =>
          have hmPos : 0 < m + 1 := by omega
          have hnPos : 0 < n + 1 := by omega
          have hreflect :
              kernel (-((m + 1 : Nat) : Int))
                  (-((n + 1 : Nat) : Int)) =
                kernel ((m + 1 : Nat) : Int) ((n + 1 : Nat) : Int) :=
            hreflection ((m + 1 : Nat) : Int) ((n + 1 : Nat) : Int)
          change
            kernel (-((m + 1 : Nat) : Int))
                (-((n + 1 : Nat) : Int)) =
              suzukiYoshidaCorrectedExplicitKernel
                (-((m + 1 : Nat) : Int)) (-((n + 1 : Nat) : Int))
          rw [hreflect, hsame (m + 1) (n + 1) hmPos hnPos]
          have hm0 : (-1 + -(m : Int)) ≠ 0 := by omega
          have hn0 : (-1 + -(n : Int)) ≠ 0 := by omega
          have hmNotPos : ¬(0 : Int) < -1 + -(m : Int) := by omega
          have hnNotPos : ¬(0 : Int) < -1 + -(n : Int) := by omega
          have hmAbs : (-1 + -(m : Int)).natAbs = m + 1 := by
            rw [show -1 + -(m : Int) = -((m + 1 : Nat) : Int) by omega,
              Int.natAbs_neg]
            exact Int.natAbs_natCast (m + 1)
          have hnAbs : (-1 + -(n : Int)).natAbs = n + 1 := by
            rw [show -1 + -(n : Int) = -((n + 1 : Nat) : Int) by omega,
              Int.natAbs_neg]
            exact Int.natAbs_natCast (n + 1)
          simp [suzukiYoshidaCorrectedExplicitKernel, hm0, hn0,
            hmNotPos, hnNotPos, hmAbs, hnAbs]

end

end RiemannHypothesisProject.Experiments.M100
