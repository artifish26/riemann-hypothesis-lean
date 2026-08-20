import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFiniteProjection
import RiemannHypothesisProject.Experiments.M100.SuzukiProjectFormNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# M100-B2M endpoint Yoshida modes

This module starts the concrete endpoint-mode side of the B2M source-closure
pass.  It defines the normalized truncated complex exponentials on `[-r,r]`
as elements of the live global `L²(Real, Complex)` space and proves their
orthonormality.  The real cosine/sine Yoshida families are obtained from these
exponentials by the standard unitary two-mode change of coordinates.

Membership in the logarithmic radius completion is deliberately kept out of
this elementary `L²` layer.  That is the boundary-density theorem isolated by
B2 and remains visible in the later bridge.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

/-- The normalized periodic complex exponential on `[-r,r]`, extended by
zero to the real line. -/
def suzukiYoshidaExponentialFunction
    (r : Real) (n : Int) (x : Real) : Complex :=
  Set.indicator (Set.Icc (-r) r)
    (fun x =>
      ((Real.sqrt (2 * r))⁻¹ : Complex) *
        Complex.exp
          (Complex.I *
            ((n : Complex) * (Real.pi : Complex) / (r : Complex)) *
              (x : Complex))) x

theorem suzukiYoshidaExponentialFunction_memLp
    {r : Real} (_hr : 0 < r) (n : Int) :
    MemLp (suzukiYoshidaExponentialFunction r n)
      (2 : ENNReal) (volume : Measure Real) := by
  unfold suzukiYoshidaExponentialFunction
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  haveI : IsFiniteMeasure
      ((volume : Measure Real).restrict (Set.Icc (-r) r)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_Icc_lt_top : volume (Set.Icc (-r) r) < ⊤)⟩
  refine MemLp.of_bound (C :=
    ‖((Real.sqrt (2 * r))⁻¹ : Complex)‖) (by fun_prop) ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [norm_mul, Complex.norm_exp]
    simp

/-- The global `L²` class of the normalized endpoint exponential. -/
def suzukiYoshidaExponentialL2
    (r : Real) (hr : 0 < r) (n : Int) : SuzukiL2 :=
  (suzukiYoshidaExponentialFunction_memLp hr n).toLp
    (suzukiYoshidaExponentialFunction r n)

theorem suzukiYoshidaExponentialL2_coeFn
    {r : Real} (hr : 0 < r) (n : Int) :
    (suzukiYoshidaExponentialL2 r hr n : Real → Complex) =ᵐ[volume]
      suzukiYoshidaExponentialFunction r n :=
  (suzukiYoshidaExponentialFunction_memLp hr n).coeFn_toLp

private theorem integral_yoshida_exponential_difference
    {r : Real} (hr : 0 < r) (k : Int) :
    (∫ x in -r..r,
      Complex.exp
        (Complex.I *
          ((k : Complex) * (Real.pi : Complex) / (r : Complex)) *
            (x : Complex))) =
      if k = 0 then (2 * r : Real) else 0 := by
  by_cases hk : k = 0
  · subst k
    norm_num
    ring
  · rw [if_neg hk]
    let c : Complex :=
      Complex.I * ((k : Complex) * (Real.pi : Complex) / (r : Complex))
    have hc : c ≠ 0 := by
      unfold c
      apply mul_ne_zero Complex.I_ne_zero
      exact div_ne_zero
        (mul_ne_zero (Int.cast_ne_zero.mpr hk)
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        (Complex.ofReal_ne_zero.mpr hr.ne')
    have hform :
        (∫ x in -r..r,
          Complex.exp
            (Complex.I *
              ((k : Complex) * (Real.pi : Complex) / (r : Complex)) *
                (x : Complex))) =
          (Complex.exp (c * r) - Complex.exp (c * (-r))) / c := by
      simpa only [c, mul_assoc, Complex.ofReal_neg] using
        (integral_exp_mul_complex (a := -r) (b := r) hc)
    rw [hform]
    have hpos :
        Complex.exp (c * r) =
          ((-1 : Complex) ^ k) := by
      calc
        Complex.exp (c * r) =
            Complex.exp ((k : Complex) *
              ((Real.pi : Complex) * Complex.I)) := by
          congr 1
          unfold c
          field_simp [hr.ne']
        _ = Complex.exp
              ((Real.pi : Complex) * Complex.I) ^ k :=
          Complex.exp_int_mul _ _
        _ = ((-1 : Complex) ^ k) := by
          rw [Complex.exp_pi_mul_I]
    have hneg' :
        Complex.exp (c * (-r)) =
          ((-1 : Complex) ^ (-k)) := by
      calc
        Complex.exp (c * (-r)) =
            Complex.exp ((-k : Complex) *
              ((Real.pi : Complex) * Complex.I)) := by
          congr 1
          unfold c
          field_simp [hr.ne']
        _ = Complex.exp
              ((Real.pi : Complex) * Complex.I) ^ (-k) :=
          by
            simpa using
              (Complex.exp_int_mul
                ((Real.pi : Complex) * Complex.I) (-k))
        _ = ((-1 : Complex) ^ (-k)) := by
          rw [Complex.exp_pi_mul_I]
    have hneg :
        Complex.exp (c * (-r)) =
          ((-1 : Complex) ^ k) := by
      rw [hneg', zpow_neg]
      rw [← inv_zpow]
      norm_num
    rw [hpos, hneg, sub_self, zero_div]
    norm_num

private theorem inner_suzukiYoshidaExponentialL2
    {r : Real} (hr : 0 < r) (m n : Int) :
    inner Complex
        (suzukiYoshidaExponentialL2 r hr m)
        (suzukiYoshidaExponentialL2 r hr n) =
      if m = n then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hm := suzukiYoshidaExponentialL2_coeFn hr m
  have hn := suzukiYoshidaExponentialL2_coeFn hr n
  have hinner :
      (fun x : Real =>
        inner Complex
          ((suzukiYoshidaExponentialL2 r hr m : SuzukiL2) x)
          ((suzukiYoshidaExponentialL2 r hr n : SuzukiL2) x)) =ᵐ[volume]
        fun x =>
          inner Complex
            (suzukiYoshidaExponentialFunction r m x)
            (suzukiYoshidaExponentialFunction r n x) := by
    filter_upwards [hm, hn] with x hmx hnx
    rw [hmx, hnx]
  rw [integral_congr_ae hinner]
  simp only [RCLike.inner_apply]
  have hpoint :
      (fun x =>
        suzukiYoshidaExponentialFunction r n x *
          (starRingEnd Complex)
            (suzukiYoshidaExponentialFunction r m x)) =
        Set.indicator (Set.Icc (-r) r)
          (fun x =>
            ((Real.sqrt (2 * r))⁻¹ : Complex) ^ 2 *
              Complex.exp
                (Complex.I *
                  ((n - m : Complex) * (Real.pi : Complex) /
                    (r : Complex)) *
                    (x : Complex))) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-r) r
    · simp only [suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx]
      rw [map_mul, map_inv₀, Complex.conj_ofReal, ← Complex.exp_conj]
      have hstar :
          (starRingEnd Complex)
              (Complex.I *
                ((m : Complex) * (Real.pi : Complex) /
                  (r : Complex)) *
                (x : Complex)) =
            -(Complex.I *
                ((m : Complex) * (Real.pi : Complex) /
                  (r : Complex)) *
                (x : Complex)) := by
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im]
      rw [hstar]
      have hexp (a A B : Complex) :
          a * Complex.exp A * (a * Complex.exp (-B)) =
            a ^ 2 * Complex.exp (A - B) := by
        calc
          a * Complex.exp A * (a * Complex.exp (-B)) =
              a ^ 2 * (Complex.exp A * Complex.exp (-B)) := by
                ring
          _ = a ^ 2 * Complex.exp (A + (-B)) := by
                rw [Complex.exp_add]
          _ = a ^ 2 * Complex.exp (A - B) := by
                rw [sub_eq_add_neg]
      convert hexp
        (((Real.sqrt (2 * r))⁻¹ : Complex))
        (Complex.I *
          ((n : Complex) * (Real.pi : Complex) / (r : Complex)) *
            (x : Complex))
        (Complex.I *
          ((m : Complex) * (Real.pi : Complex) / (r : Complex)) *
            (x : Complex)) using 1
      all_goals ring_nf
    · simp [suzukiYoshidaExponentialFunction, hx]
  rw [hpoint]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  rw [intervalIntegral.integral_const_mul]
  rw [show
      (∫ x in -r..r,
        Complex.exp
          (Complex.I *
            (((n : Complex) - (m : Complex)) *
              (Real.pi : Complex) / (r : Complex)) *
              (x : Complex))) =
        if n - m = 0 then (2 * r : Real) else 0 by
      simpa only [Int.cast_sub] using
        (integral_yoshida_exponential_difference hr (n - m))]
  by_cases hmn : m = n
  · subst n
    simp only [sub_self, if_pos]
    have hsqrt : Real.sqrt (2 * r) ≠ 0 := by positivity
    have hsquare : Real.sqrt (2 * r) ^ 2 = 2 * r :=
      Real.sq_sqrt (by positivity)
    have hsqrtC : ((Real.sqrt (2 * r) : Real) : Complex) ≠ 0 := by
      exact_mod_cast hsqrt
    have hsquareC :
        (((Real.sqrt (2 * r) : Real) : Complex) ^ 2) =
          ((2 * r : Real) : Complex) := by
      exact_mod_cast hsquare
    rw [← hsquareC]
    field_simp [hsqrtC]
  · rw [if_neg hmn]
    have hsub : n - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
    rw [if_neg hsub]
    simp

/-- The normalized truncated complex exponentials are orthonormal in the live
global `L²` space. -/
theorem orthonormal_suzukiYoshidaExponentialL2
    {r : Real} (hr : 0 < r) :
    Orthonormal Complex (suzukiYoshidaExponentialL2 r hr) := by
  rw [orthonormal_iff_ite]
  exact inner_suzukiYoshidaExponentialL2 hr

theorem suzukiL2Reflection_exponential
    {r : Real} (hr : 0 < r) (n : Int) :
    suzukiL2Reflection (suzukiYoshidaExponentialL2 r hr n) =
      suzukiYoshidaExponentialL2 r hr (-n) := by
  apply Lp.ext
  have hn := suzukiYoshidaExponentialL2_coeFn hr n
  have hnneg :
      ∀ᵐ x ∂(volume : Measure Real),
        (suzukiYoshidaExponentialL2 r hr n : Real → Complex) (-x) =
          suzukiYoshidaExponentialFunction r n (-x) :=
    (Measure.measurePreserving_neg
      (volume : Measure Real)).quasiMeasurePreserving.ae hn
  filter_upwards [suzukiL2Reflection_coeFn
      (suzukiYoshidaExponentialL2 r hr n),
    hnneg, suzukiYoshidaExponentialL2_coeFn hr (-n)] with
      x hreflect hnx hminus
  rw [hreflect, hnx, hminus]
  unfold suzukiYoshidaExponentialFunction
  have hmem :
      -x ∈ Set.Icc (-r) r ↔ x ∈ Set.Icc (-r) r := by
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  by_cases hx : x ∈ Set.Icc (-r) r
  · rw [Set.indicator_of_mem (hmem.mpr hx),
      Set.indicator_of_mem hx]
    congr 2
    push_cast
    ring
  · simp [hx, hmem]

/-- The normalized real-even Yoshida mode. Physical mode zero is the constant
mode; positive physical modes are the standard two-exponential cosine
combinations. -/
def suzukiYoshidaEvenL2
    (r : Real) (hr : 0 < r) (n : Nat) : SuzukiL2 :=
  if _hn : n = 0 then
    suzukiYoshidaExponentialL2 r hr 0
  else
    ((Real.sqrt 2)⁻¹ : Complex) •
      (suzukiYoshidaExponentialL2 r hr (n : Int) +
        suzukiYoshidaExponentialL2 r hr (-(n : Int)))

/-- The normalized real-odd Yoshida mode for a positive physical index.  The
phase `1 / I` turns the two-exponential difference into the real sine mode. -/
def suzukiYoshidaOddL2
    (r : Real) (hr : 0 < r) (n : Nat) : SuzukiL2 :=
  ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) •
    (suzukiYoshidaExponentialL2 r hr (n : Int) -
      suzukiYoshidaExponentialL2 r hr (-(n : Int)))

theorem suzukiYoshidaEvenL2_even
    {r : Real} (hr : 0 < r) (n : Nat) :
    SuzukiL2Even (suzukiYoshidaEvenL2 r hr n) := by
  unfold SuzukiL2Even suzukiYoshidaEvenL2
  split_ifs with hn
  · rw [suzukiL2Reflection_exponential]
    simp
  · rw [map_smul, map_add, suzukiL2Reflection_exponential,
      suzukiL2Reflection_exponential]
    simp only [neg_neg]
    module

theorem suzukiYoshidaOddL2_odd
    {r : Real} (hr : 0 < r) (n : Nat) :
    SuzukiL2Odd (suzukiYoshidaOddL2 r hr n) := by
  unfold SuzukiL2Odd suzukiYoshidaOddL2
  rw [map_smul, map_sub, suzukiL2Reflection_exponential,
    suzukiL2Reflection_exponential]
  simp only [neg_neg]
  module

private theorem yoshida_sqrt_two_ne_zero :
    Real.sqrt 2 ≠ 0 := by
  positivity

private theorem yoshida_even_scalar_normalization :
    (starRingEnd Complex) (((Real.sqrt 2)⁻¹ : Complex)) *
        (((Real.sqrt 2)⁻¹ : Complex) * 2) = 1 := by
  rw [map_inv₀, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquareC :
      (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [yoshida_sqrt_two_ne_zero]

private theorem yoshida_odd_scalar_normalization :
    (starRingEnd Complex)
          (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) * 2) = 1 := by
  rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquareC :
      (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [yoshida_sqrt_two_ne_zero, Complex.I_ne_zero]
  rw [Complex.I_sq]

private theorem inner_suzukiYoshidaEvenL2
    {r : Real} (hr : 0 < r) (m n : Nat) :
    inner Complex (suzukiYoshidaEvenL2 r hr m)
        (suzukiYoshidaEvenL2 r hr n) =
      if m = n then 1 else 0 := by
  by_cases hm : m = 0
  · subst m
    by_cases hn : n = 0
    · subst n
      simpa [suzukiYoshidaEvenL2] using
        inner_suzukiYoshidaExponentialL2 hr 0 0
    · have h0n : (0 : Int) ≠ (n : Int) := by omega
      have h0neg : (0 : Int) ≠ -(n : Int) := by omega
      unfold suzukiYoshidaEvenL2
      rw [dif_pos rfl, dif_neg hn, inner_smul_right,
        inner_add_right, inner_suzukiYoshidaExponentialL2,
        inner_suzukiYoshidaExponentialL2, if_neg h0n,
        if_neg h0neg, if_neg (Ne.symm hn)]
      simp
  · by_cases hn : n = 0
    · subst n
      have hm0 : (m : Int) ≠ 0 := by omega
      have hneg0 : -(m : Int) ≠ 0 := by omega
      unfold suzukiYoshidaEvenL2
      rw [dif_neg hm, dif_pos rfl, inner_smul_left,
        inner_add_left, inner_suzukiYoshidaExponentialL2,
        inner_suzukiYoshidaExponentialL2, if_neg hm0,
        if_neg hneg0, if_neg hm]
      simp
    · by_cases hmn : m = n
      · subst n
        have hmInt : (m : Int) ≠ 0 := by omega
        have hcross₁ : (m : Int) ≠ -(m : Int) := by omega
        have hcross₂ : -(m : Int) ≠ (m : Int) := by omega
        unfold suzukiYoshidaEvenL2
        rw [dif_neg hm, inner_smul_left, inner_smul_right]
        simp_rw [inner_add_left, inner_add_right,
          inner_suzukiYoshidaExponentialL2]
        simp only [if_true, if_false, hcross₁, hcross₂,
          add_zero, zero_add]
        convert yoshida_even_scalar_normalization using 1
        all_goals norm_num
      · have hsame : (m : Int) ≠ (n : Int) := by exact_mod_cast hmn
        have hnegSame : -(m : Int) ≠ -(n : Int) := by omega
        have hcross₁ : (m : Int) ≠ -(n : Int) := by omega
        have hcross₂ : -(m : Int) ≠ (n : Int) := by omega
        unfold suzukiYoshidaEvenL2
        rw [dif_neg hm, dif_neg hn, inner_smul_left,
          inner_smul_right]
        simp_rw [inner_add_left, inner_add_right,
          inner_suzukiYoshidaExponentialL2]
        rw [if_neg hsame, if_neg hcross₁, if_neg hcross₂,
          if_neg hnegSame, if_neg hmn]
        simp

/-- Public all-index pairing formula for the normalized even Yoshida
family. -/
theorem inner_suzukiYoshidaEvenL2_eq_ite
    {r : Real} (hr : 0 < r) (m n : Nat) :
    inner Complex (suzukiYoshidaEvenL2 r hr m)
        (suzukiYoshidaEvenL2 r hr n) =
      if m = n then 1 else 0 :=
  inner_suzukiYoshidaEvenL2 hr m n

private theorem inner_suzukiYoshidaOddL2
    {r : Real} (hr : 0 < r) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    inner Complex (suzukiYoshidaOddL2 r hr m)
        (suzukiYoshidaOddL2 r hr n) =
      if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    have hmInt : (m : Int) ≠ 0 := by omega
    have hcross₁ : (m : Int) ≠ -(m : Int) := by omega
    have hcross₂ : -(m : Int) ≠ (m : Int) := by omega
    unfold suzukiYoshidaOddL2
    rw [inner_smul_left, inner_smul_right]
    simp_rw [inner_sub_left, inner_sub_right,
      inner_suzukiYoshidaExponentialL2]
    simp only [if_true, if_false, hcross₁, hcross₂,
      sub_zero, zero_sub, sub_neg_eq_add]
    convert yoshida_odd_scalar_normalization using 1
    all_goals norm_num
  · have hsame : (m : Int) ≠ (n : Int) := by exact_mod_cast hmn
    have hnegSame : -(m : Int) ≠ -(n : Int) := by omega
    have hcross₁ : (m : Int) ≠ -(n : Int) := by omega
    have hcross₂ : -(m : Int) ≠ (n : Int) := by omega
    unfold suzukiYoshidaOddL2
    rw [inner_smul_left, inner_smul_right]
    simp_rw [inner_sub_left, inner_sub_right,
      inner_suzukiYoshidaExponentialL2]
    rw [if_neg hsame, if_neg hcross₁, if_neg hcross₂,
      if_neg hnegSame, if_neg hmn]
    simp

/-- Public positive-index pairing formula for the normalized odd Yoshida
family. -/
theorem inner_suzukiYoshidaOddL2_eq_ite
    {r : Real} (hr : 0 < r) {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) :
    inner Complex (suzukiYoshidaOddL2 r hr m)
        (suzukiYoshidaOddL2 r hr n) =
      if m = n then 1 else 0 :=
  inner_suzukiYoshidaOddL2 hr hm hn

theorem orthonormal_suzukiYoshidaEvenL2_fin45
    {r : Real} (hr : 0 < r) :
    Orthonormal Complex
      (fun i : Fin 45 => suzukiYoshidaEvenL2 r hr i.1) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_suzukiYoshidaEvenL2 hr]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    simp [hij, hval]

theorem orthonormal_suzukiYoshidaOddL2_fin44
    {r : Real} (hr : 0 < r) :
    Orthonormal Complex
      (fun i : Fin 44 => suzukiYoshidaOddL2 r hr (i.1 + 1)) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi : 0 < i.1 + 1 := Nat.zero_lt_succ i.1
  have hj : 0 < j.1 + 1 := Nat.zero_lt_succ j.1
  rw [inner_suzukiYoshidaOddL2 hr hi hj]
  by_cases hij : i = j
  · subst j
    simp
  · have hval : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    simp [hij, hval]

/-! ## Exact B2M source-closure boundary -/

/-- The B2 endpoint certificate follows once the two finite raw Yoshida
families are individually lifted through the live completion-to-`L²` map.

These two hypotheses are the exact remaining analytic source-closure inputs;
they are intentionally displayed rather than bundled with unrelated block or
positivity assumptions. -/
noncomputable def suzukiB2EndpointModeCertificateOfMembership
    {r : Real} (hr : 0 < r)
    (hEven :
      ∀ i : Fin 45, ∃ v : SuzukiLogRadiusLinearCompletion r,
        suzukiLogRadiusLinearCompletionToL2 v =
          suzukiYoshidaEvenL2 r hr i.1)
    (hOdd :
      ∀ i : Fin 44, ∃ v : SuzukiLogRadiusLinearCompletion r,
        suzukiLogRadiusLinearCompletionToL2 v =
          suzukiYoshidaOddL2 r hr (i.1 + 1)) :
    SuzukiB2EndpointModeCertificate r := by
  classical
  let evenMode : Fin 45 → SuzukiLogRadiusLinearCompletion r :=
    fun i => Classical.choose (hEven i)
  let oddMode : Fin 44 → SuzukiLogRadiusLinearCompletion r :=
    fun i => Classical.choose (hOdd i)
  have hEvenImage :
      (fun i => suzukiLogRadiusLinearCompletionToL2 (evenMode i)) =
        fun i => suzukiYoshidaEvenL2 r hr i.1 := by
    funext i
    exact Classical.choose_spec (hEven i)
  have hOddImage :
      (fun i => suzukiLogRadiusLinearCompletionToL2 (oddMode i)) =
        fun i => suzukiYoshidaOddL2 r hr (i.1 + 1) := by
    funext i
    exact Classical.choose_spec (hOdd i)
  refine
    { evenMode := evenMode
      oddMode := oddMode
      evenOrthonormal := ?_
      oddOrthonormal := ?_
      evenParity := ?_
      oddParity := ?_ }
  · rw [hEvenImage]
    exact orthonormal_suzukiYoshidaEvenL2_fin45 hr
  · rw [hOddImage]
    exact orthonormal_suzukiYoshidaOddL2_fin44 hr
  · intro i
    rw [congrFun hEvenImage i]
    exact suzukiYoshidaEvenL2_even hr i.1
  · intro i
    rw [congrFun hOddImage i]
    exact suzukiYoshidaOddL2_odd hr (i.1 + 1)

/-- Fixed-endpoint form of the B2M consumer.  Its two displayed premises are
precisely the finite graph-closure membership theorem family still required
before B2 can be closed. -/
noncomputable def suzukiProjectB2EndpointModeCertificateOfMembership
    (hEven :
      ∀ i : Fin 45,
        ∃ v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar,
          suzukiLogRadiusLinearCompletionToL2 v =
            suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos i.1)
    (hOdd :
      ∀ i : Fin 44,
        ∃ v : SuzukiLogRadiusLinearCompletion suzukiProjectAStar,
          suzukiLogRadiusLinearCompletionToL2 v =
            suzukiYoshidaOddL2 suzukiProjectAStar
              suzukiProjectAStar_pos (i.1 + 1)) :
    SuzukiB2EndpointModeCertificate suzukiProjectAStar :=
  suzukiB2EndpointModeCertificateOfMembership
    suzukiProjectAStar_pos hEven hOdd

end

end M100
end Experiments
end RiemannHypothesisProject
