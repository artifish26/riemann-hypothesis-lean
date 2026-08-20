import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointOppositeModeEvaluation
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointComparisonFormAssembly

/-!
# Parity assembly for the Yoshida endpoint source pairing

This module converts the all-integer endpoint source pairings into the
normalized even and odd source-variable products.  The constant even mode is
kept as a separate branch.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

def suzukiYoshidaEndpointEvenSourceVariableIntegrand
    (r : Real) (left right : Nat) (z : Real) : Complex :=
  ((suzukiYoshidaEndpointSourceVariableWeight z : Real) : Complex) *
    (suzukiYoshidaEndpointEvenSourceVariableProfile r right z *
      conj (suzukiYoshidaEndpointEvenSourceVariableProfile r left z))

def suzukiYoshidaEndpointOddSourceVariableIntegrand
    (r : Real) (left right : Nat) (z : Real) : Complex :=
  ((suzukiYoshidaEndpointSourceVariableWeight z : Real) : Complex) *
    (suzukiYoshidaEndpointOddSourceVariableProfile r right z *
      conj (suzukiYoshidaEndpointOddSourceVariableProfile r left z))

private theorem integral_four_sourceVariableIntegrands
    {r : Real} (hr : 0 < r) (left right : Nat) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (right : Int) (left : Int) z) +
      (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (-(right : Int)) (left : Int) z) +
      (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (right : Int) (-(left : Int)) z) +
      (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (-(right : Int)) (-(left : Int)) z) =
      ∫ z : Real,
        (suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (left : Int) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (left : Int) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (-(left : Int)) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (-(left : Int)) z) := by
  have hpp := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (right : Int) (left : Int)
  have hnp := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (-(right : Int)) (left : Int)
  have hpn := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (right : Int) (-(left : Int))
  have hnn := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (-(right : Int)) (-(left : Int))
  symm
  calc
    (∫ z : Real,
        (suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (left : Int) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (left : Int) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (-(left : Int)) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (-(left : Int)) z)) =
        ∫ z : Real,
          ((suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z) +
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) := by
          apply integral_congr_ae
          filter_upwards with z
          ring
    _ = (∫ z : Real,
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z)) +
        ∫ z : Real,
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z) :=
      integral_add (hpp.add hnp) (hpn.add hnn)
    _ = _ := by
      rw [integral_add hpp hnp, integral_add hpn hnn]
      ring

private theorem integral_signed_four_sourceVariableIntegrands
    {r : Real} (hr : 0 < r) (left right : Nat) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (right : Int) (left : Int) z) -
      (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (-(right : Int)) (left : Int) z) -
      (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (right : Int) (-(left : Int)) z) +
      (∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand
          r (-(right : Int)) (-(left : Int)) z) =
      ∫ z : Real,
        (suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (left : Int) z -
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (left : Int) z -
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (-(left : Int)) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (-(left : Int)) z) := by
  have hpp := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (right : Int) (left : Int)
  have hnp := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (-(right : Int)) (left : Int)
  have hpn := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (right : Int) (-(left : Int))
  have hnn := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (-(right : Int)) (-(left : Int))
  have hsecond :
      (∫ z : Real,
          (-suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) =
        -(∫ z : Real,
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (-(left : Int)) z) +
          ∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z := by
    have h := integral_add hpn.neg hnn
    rw [integral_neg'] at h
    simpa only [Pi.neg_apply] using h
  symm
  calc
    (∫ z : Real,
        (suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (left : Int) z -
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (left : Int) z -
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (right : Int) (-(left : Int)) z +
          suzukiYoshidaEndpointSourceVariableIntegrand
            r (-(right : Int)) (-(left : Int)) z)) =
        ∫ z : Real,
          ((suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z -
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z) +
          (-suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) := by
          apply integral_congr_ae
          filter_upwards with z
          ring
    _ = (∫ z : Real,
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z -
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z)) +
        ∫ z : Real,
          (-suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z) :=
      integral_add (hpp.sub hnp) (hpn.neg.add hnn)
    _ = _ := by
      rw [integral_sub hpp hnp]
      rw [hsecond]
      ring

private theorem integral_evenSourceVariableIntegrand_eq_four_of_pos
    {r : Real} (hr : 0 < r) (left right : Nat)
    (hleft : 0 < left) (hright : 0 < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointEvenSourceVariableIntegrand r left right z) =
      conj (((Real.sqrt 2)⁻¹ : Complex)) *
        (((Real.sqrt 2)⁻¹ : Complex)) *
        ((∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z) +
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z) +
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z) +
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) := by
  calc
    (∫ z : Real,
        suzukiYoshidaEndpointEvenSourceVariableIntegrand r left right z) =
        ∫ z : Real,
          (conj (((Real.sqrt 2)⁻¹ : Complex)) *
            (((Real.sqrt 2)⁻¹ : Complex))) *
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z) := by
          apply integral_congr_ae
          filter_upwards with z
          unfold suzukiYoshidaEndpointEvenSourceVariableIntegrand
            suzukiYoshidaEndpointSourceVariableIntegrand
            suzukiYoshidaEndpointEvenSourceVariableProfile
          simp only [if_neg hleft.ne', if_neg hright.ne', map_inv₀,
            Complex.conj_ofReal, map_add, map_mul]
          ring
    _ = (conj (((Real.sqrt 2)⁻¹ : Complex)) *
          (((Real.sqrt 2)⁻¹ : Complex))) *
        (∫ z : Real,
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) :=
      by rw [integral_const_mul]
    _ = _ := by
      rw [← integral_four_sourceVariableIntegrands hr left right]

private theorem integral_oddSourceVariableIntegrand_eq_four
    {r : Real} (hr : 0 < r) (left right : Nat) :
    (∫ z : Real,
        suzukiYoshidaEndpointOddSourceVariableIntegrand r left right z) =
      conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) *
        ((∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z) -
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z) -
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z) +
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) := by
  calc
    (∫ z : Real,
        suzukiYoshidaEndpointOddSourceVariableIntegrand r left right z) =
        ∫ z : Real,
          (conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
            ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z -
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z -
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z) := by
          apply integral_congr_ae
          filter_upwards with z
          unfold suzukiYoshidaEndpointOddSourceVariableIntegrand
            suzukiYoshidaEndpointSourceVariableIntegrand
            suzukiYoshidaEndpointOddSourceVariableProfile
          simp only [map_inv₀, map_mul, map_sub, Complex.conj_I,
            Complex.conj_ofReal]
          ring
    _ = (conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
          ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        (∫ z : Real,
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (left : Int) z -
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (left : Int) z -
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) (-(left : Int)) z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) (-(left : Int)) z)) :=
      by rw [integral_const_mul]
    _ = _ := by
      rw [← integral_signed_four_sourceVariableIntegrands hr left right]

theorem suzukiYoshidaEvenSourceKernelPairing_eq_sourceVariable_of_pos
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) (hleft : 0 < left) (hright : 0 < right) :
    suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) left right =
      (((2 * Real.pi : Real) : Complex)⁻¹) *
        ∫ z : Real,
          suzukiYoshidaEndpointEvenSourceVariableIntegrand
            suzukiProjectAStar left right z := by
  unfold suzukiYoshidaEvenSourceKernelPairing
  split_ifs with hm hn hn
  all_goals try omega
  simp_rw [suzukiYoshidaComparisonLimitKernel_eq_endpointSourceFourierPairing,
    suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
      suzukiProjectAStar_pos]
  rw [integral_evenSourceVariableIntegrand_eq_four_of_pos
    suzukiProjectAStar_pos left right hleft hright]
  ring

theorem suzukiYoshidaOddSourceKernelPairing_eq_sourceVariable
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) :
    suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) left right =
      (((2 * Real.pi : Real) : Complex)⁻¹) *
        ∫ z : Real,
          suzukiYoshidaEndpointOddSourceVariableIntegrand
            suzukiProjectAStar left right z := by
  unfold suzukiYoshidaOddSourceKernelPairing
  simp_rw [suzukiYoshidaComparisonLimitKernel_eq_endpointSourceFourierPairing,
    suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
      suzukiProjectAStar_pos]
  rw [integral_oddSourceVariableIntegrand_eq_four
    suzukiProjectAStar_pos left right]
  ring

private theorem integral_evenZeroSourceVariableIntegrand_eq_two
    {r : Real} (hr : 0 < r) (right : Nat) (hright : 0 < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointEvenSourceVariableIntegrand r 0 right z) =
      (((Real.sqrt 2)⁻¹ : Complex)) *
        ((∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) 0 z) +
          (∫ z : Real,
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) 0 z)) := by
  have hpos := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (right : Int) 0
  have hneg := integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    hr (-(right : Int)) 0
  calc
    (∫ z : Real,
        suzukiYoshidaEndpointEvenSourceVariableIntegrand r 0 right z) =
        ∫ z : Real,
          (((Real.sqrt 2)⁻¹ : Complex)) *
            (suzukiYoshidaEndpointSourceVariableIntegrand
                r (right : Int) 0 z +
              suzukiYoshidaEndpointSourceVariableIntegrand
                r (-(right : Int)) 0 z) := by
          apply integral_congr_ae
          filter_upwards with z
          unfold suzukiYoshidaEndpointEvenSourceVariableIntegrand
            suzukiYoshidaEndpointSourceVariableIntegrand
            suzukiYoshidaEndpointEvenSourceVariableProfile
          simp [hright.ne']
          ring
    _ = (((Real.sqrt 2)⁻¹ : Complex)) *
        ∫ z : Real,
          (suzukiYoshidaEndpointSourceVariableIntegrand
              r (right : Int) 0 z +
            suzukiYoshidaEndpointSourceVariableIntegrand
              r (-(right : Int)) 0 z) := by
          rw [integral_const_mul]
    _ = _ := by
      rw [integral_add hpos hneg]

theorem suzukiYoshidaEvenZeroSourceKernelPairing_eq_sourceVariable
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (right : Nat) (hright : 0 < right) :
    suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) 0 right =
      (((2 * Real.pi : Real) : Complex)⁻¹) *
        ∫ z : Real,
          suzukiYoshidaEndpointEvenSourceVariableIntegrand
            suzukiProjectAStar 0 right z := by
  unfold suzukiYoshidaEvenSourceKernelPairing
  rw [dif_pos rfl, dif_neg hright.ne']
  simp_rw [suzukiYoshidaComparisonLimitKernel_eq_endpointSourceFourierPairing,
    suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
      suzukiProjectAStar_pos]
  rw [integral_evenZeroSourceVariableIntegrand_eq_two
    suzukiProjectAStar_pos right hright]
  ring

private theorem suzukiYoshida_positiveParity_coefficient
    {r : Real} (hr : 0 < r) :
    (((Real.sqrt 2 : Complex)⁻¹) ^ 2 *
        ((Real.sqrt (r * 2) : Complex)⁻¹) ^ 2 * 4) =
      (r : Complex)⁻¹ := by
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtR : Real.sqrt (r * 2) ≠ 0 := by positivity
  have hsquareTwo : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsquareR : Real.sqrt (r * 2) ^ 2 = r * 2 :=
    Real.sq_sqrt (by positivity)
  field_simp [hsqrtTwo, hsqrtR, hr.ne']
  norm_cast
  rw [hsquareTwo, hsquareR]
  ring

theorem suzukiYoshidaEndpointEvenSourceVariableIntegrand_eq_rationalProduct_of_pos
    {r : Real} (hr : 0 < r) (left right : Nat)
    (hleft : 0 < left) (hright : 0 < right) (z : Real) :
    suzukiYoshidaEndpointEvenSourceVariableIntegrand r left right z =
      ((((-1 : Real) ^ (left + right)) / r : Real) : Complex) *
        (suzukiYoshidaEndpointSourceEvenRationalProduct
          r left right z : Real) := by
  unfold suzukiYoshidaEndpointEvenSourceVariableIntegrand
  rw [suzukiYoshidaEndpointEvenSourceVariableProfile_of_pos right hright,
    suzukiYoshidaEndpointEvenSourceVariableProfile_of_pos left hleft]
  unfold suzukiYoshidaEndpointSourceEvenRationalProduct
    suzukiYoshidaEndpointSourceEvenRationalProfile
    suzukiYoshidaEndpointSourceModeFrequency
  simp only [map_inv₀, map_add, map_mul, Complex.conj_ofReal]
  push_cast
  have hcoefficient := suzukiYoshida_positiveParity_coefficient hr
  ring_nf at hcoefficient ⊢
  rw [← hcoefficient]
  ring

private theorem suzukiYoshida_positiveOddParity_coefficient
    {r : Real} (hr : 0 < r) :
    (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ *
        ((Real.sqrt (r * 2))⁻¹ : Complex) * 2) *
      conj ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ *
        ((Real.sqrt (r * 2))⁻¹ : Complex) * 2)) =
      (r : Complex)⁻¹ := by
  rw [Complex.mul_conj]
  simp only [Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_I, Complex.normSq_ofReal]
  norm_num [Complex.normSq_apply]
  norm_cast
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtR : Real.sqrt r ≠ 0 := by positivity
  have hsquareTwo : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsquareR : Real.sqrt r ^ 2 = r :=
    Real.sq_sqrt hr.le
  field_simp [hsqrtTwo, hsqrtR, hr.ne']
  rw [hsquareTwo, hsquareR]
  norm_cast
  push_cast
  ring

private theorem suzukiYoshidaEndpointOddSourceVariableProfile_factor_of_pos
    {r : Real} (n : Nat) (z : Real) :
    suzukiYoshidaEndpointOddSourceVariableProfile r n z =
      ((((-1 : Real) ^ n : Real) : Complex) *
          ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ *
            ((Real.sqrt (r * 2))⁻¹ : Complex) * 2)) *
        ((Real.sin (r * z) : Real) : Complex) *
        (suzukiYoshidaEndpointSourceOddRationalProfile r n z : Real) := by
  rw [suzukiYoshidaEndpointOddSourceVariableProfile_eq]
  unfold suzukiYoshidaEndpointSourceOddRationalProfile
    suzukiYoshidaEndpointSourceModeFrequency
  push_cast
  ring

theorem suzukiYoshidaEndpointOddSourceVariableIntegrand_eq_rationalProduct_of_pos
    {r : Real} (hr : 0 < r) (left right : Nat)
    (_hleft : 0 < left) (_hright : 0 < right) (z : Real) :
    suzukiYoshidaEndpointOddSourceVariableIntegrand r left right z =
      ((((-1 : Real) ^ (left + right)) / r : Real) : Complex) *
        (suzukiYoshidaEndpointSourceOddRationalProduct
          r left right z : Real) := by
  unfold suzukiYoshidaEndpointOddSourceVariableIntegrand
  rw [suzukiYoshidaEndpointOddSourceVariableProfile_factor_of_pos,
    suzukiYoshidaEndpointOddSourceVariableProfile_factor_of_pos]
  unfold suzukiYoshidaEndpointSourceOddRationalProduct
  simp only [map_inv₀, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  push_cast
  have hcoefficient := suzukiYoshida_positiveOddParity_coefficient hr
  simp only [map_inv₀, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat] at hcoefficient
  ring_nf at hcoefficient ⊢
  rw [← hcoefficient]
  ring

private theorem suzukiYoshidaEndpointEvenZeroSourceVariableIntegrand_ae_eq_master
    {r : Real} (hr : 0 < r) (right : Nat) (hright : 0 < right) :
    suzukiYoshidaEndpointEvenSourceVariableIntegrand r 0 right =ᵐ[volume]
      fun z =>
        (((-(((-1 : Real) ^ right) * Real.sqrt 2) /
            ((right : Real) * Real.pi) : Real) : Complex) *
          (suzukiYoshidaEndpointSourceModeMasterIntegrand r right z : Real)) := by
  let q := suzukiYoshidaEndpointSourceModeFrequency r right
  have hq : 0 < q :=
    suzukiYoshidaEndpointSourceModeFrequency_pos hr hright
  filter_upwards [volume.ae_ne (0 : Real), volume.ae_ne (-q),
      volume.ae_ne q] with z hz hznq hzq
  unfold suzukiYoshidaEndpointEvenSourceVariableIntegrand
  rw [suzukiYoshidaEndpointEvenSourceVariableProfile_of_pos right hright]
  rw [show suzukiYoshidaEndpointEvenSourceVariableProfile r 0 z =
      suzukiYoshidaEndpointSourceVariableProfile r 0 z by
    simp [suzukiYoshidaEndpointEvenSourceVariableProfile]]
  unfold suzukiYoshidaEndpointSourceVariableProfile
    suzukiYoshidaEndpointSourceModeMasterIntegrand
    suzukiYoshidaEndpointSourceOddRationalProfile
  change _ =
    (((-(((-1 : Real) ^ right) * Real.sqrt 2) /
        ((right : Real) * Real.pi) : Real) : Complex) *
      ((suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
        ((z + q)⁻¹ - (z - q)⁻¹) : Real) : Complex))
  simp only [Int.cast_zero, CharP.cast_eq_zero, zero_mul, add_zero,
    map_inv₀, map_add, map_mul, map_div₀, map_pow, map_neg,
    map_ofNat, Complex.conj_ofReal]
  norm_cast
  have hzqPlus : z + q ≠ 0 := by
    intro h
    apply hznq
    linarith
  have hzqMinus : z - q ≠ 0 := sub_ne_zero.mpr hzq
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsqrtR : Real.sqrt (2 * r) ≠ 0 := by positivity
  have hrightReal : (right : Real) ≠ 0 := by positivity
  have hqFormula : q = (right : Real) * Real.pi / r := rfl
  rw [hqFormula] at hzqPlus hzqMinus ⊢
  have hzqPlusScaled : r * z + (right : Real) * Real.pi ≠ 0 := by
    intro h
    apply hzqPlus
    field_simp [hr.ne']
    nlinarith
  have hzqMinusScaled : r * z - (right : Real) * Real.pi ≠ 0 := by
    intro h
    apply hzqMinus
    field_simp [hr.ne']
    nlinarith
  field_simp [hz, hzqPlus, hzqMinus, hsqrtTwo, hsqrtR,
    hzqPlusScaled, hzqMinusScaled, hrightReal, Real.pi_ne_zero, hr.ne']
  rw [Real.sq_sqrt (by positivity : (0 : Real) ≤ 2),
    Real.sq_sqrt (by positivity : (0 : Real) ≤ 2 * r)]
  push_cast
  ring

private theorem integral_suzukiYoshidaEndpointEvenSourceVariableIntegrand_of_pos
    {r : Real} (hr : 0 < r) (left right : Nat)
    (hleft : 0 < left) (hright : 0 < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointEvenSourceVariableIntegrand r left right z) =
      ((((-1 : Real) ^ (left + right)) / r : Real) : Complex) *
        ((∫ z : Real,
          suzukiYoshidaEndpointSourceEvenRationalProduct r left right z) :
            Real) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
    suzukiYoshidaEndpointEvenSourceVariableIntegrand_eq_rationalProduct_of_pos
      hr left right hleft hright z)]
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal

private theorem integral_suzukiYoshidaEndpointOddSourceVariableIntegrand_of_pos
    {r : Real} (hr : 0 < r) (left right : Nat)
    (hleft : 0 < left) (hright : 0 < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointOddSourceVariableIntegrand r left right z) =
      ((((-1 : Real) ^ (left + right)) / r : Real) : Complex) *
        ((∫ z : Real,
          suzukiYoshidaEndpointSourceOddRationalProduct r left right z) :
            Real) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
    suzukiYoshidaEndpointOddSourceVariableIntegrand_eq_rationalProduct_of_pos
      hr left right hleft hright z)]
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal

private theorem integral_suzukiYoshidaEndpointEvenZeroSourceVariableIntegrand
    {r : Real} (hr : 0 < r) (right : Nat) (hright : 0 < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointEvenSourceVariableIntegrand r 0 right z) =
      (((-(((-1 : Real) ^ right) * Real.sqrt 2) /
          ((right : Real) * Real.pi) : Real) : Complex) *
        ((∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) : Real)) := by
  rw [integral_congr_ae
    (suzukiYoshidaEndpointEvenZeroSourceVariableIntegrand_ae_eq_master
      hr right hright)]
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal

private theorem neg_one_pow_left_add_right_eq_right_sub_left
    {left right : Nat} (hle : left ≤ right) :
    (-1 : Real) ^ (left + right) = (-1 : Real) ^ (right - left) := by
  rw [show left + right = (right - left) + 2 * left by omega, pow_add,
    pow_mul]
  norm_num

private theorem suzukiYoshida_positiveEvenSourceIntegral_normalization
    (hmaster : SuzukiYoshidaEndpointSourceModeMasterEvaluation)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    (2 * Real.pi : Real)⁻¹ *
        (((-1 : Real) ^ (left + right)) / suzukiProjectAStar) *
        (∫ z : Real,
          suzukiYoshidaEndpointSourceEvenRationalProduct
            suzukiProjectAStar left right z) =
      suzukiYoshidaComparisonEvenSourceIntegral left right := by
  rw [suzukiYoshidaEndpointSourceEvenRationalProduct_integral_eq_source
    hmaster hleft hlt]
  unfold suzukiYoshidaComparisonEvenSourceIntegral
    suzukiDF6D4EvenModeScale
    suzukiYoshidaEndpointSourceModeFrequency
  dsimp only
  rw [if_neg hleft.ne', if_neg (hleft.trans hlt).ne']
  push_cast
  rw [
    suzukiDF6D4AlternatingSign_cast_real,
    suzukiDF6D4AlternatingSign_cast_real,
    neg_one_pow_left_add_right_eq_right_sub_left hlt.le]
  have hdifferenceNat : right - left ≠ 0 :=
    (Nat.sub_pos_iff_lt.mpr hlt).ne'
  have hdifferenceReal : ((right - left : Nat) : Real) ≠ 0 := by
    exact_mod_cast hdifferenceNat
  have hdifferenceCast :
      ((right - left : Nat) : Real) = (right : Real) - (left : Real) := by
    exact Nat.cast_sub hlt.le
  have htotalReal : ((left + right : Nat) : Real) ≠ 0 := by positivity
  rw [hdifferenceCast]
  field_simp [suzukiProjectAStar_pos.ne', Real.pi_ne_zero,
    hdifferenceReal, htotalReal]
  ring

private theorem suzukiYoshida_positiveOddSourceIntegral_normalization
    (hmaster : SuzukiYoshidaEndpointSourceModeMasterEvaluation)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    (2 * Real.pi : Real)⁻¹ *
        (((-1 : Real) ^ (left + right)) / suzukiProjectAStar) *
        (∫ z : Real,
          suzukiYoshidaEndpointSourceOddRationalProduct
            suzukiProjectAStar left right z) =
      suzukiYoshidaComparisonOddSourceIntegral left right := by
  rw [suzukiYoshidaEndpointSourceOddRationalProduct_integral_eq_source
    hmaster hleft hlt]
  unfold suzukiYoshidaComparisonOddSourceIntegral
    suzukiYoshidaEndpointSourceModeFrequency
  dsimp only
  push_cast
  rw [suzukiDF6D4AlternatingSign_cast_real,
    suzukiDF6D4AlternatingSign_cast_real,
    neg_one_pow_left_add_right_eq_right_sub_left hlt.le]
  have hdifferenceNat : right - left ≠ 0 :=
    (Nat.sub_pos_iff_lt.mpr hlt).ne'
  have hdifferenceReal : ((right - left : Nat) : Real) ≠ 0 := by
    exact_mod_cast hdifferenceNat
  have hdifferenceCast :
      ((right - left : Nat) : Real) = (right : Real) - (left : Real) := by
    exact Nat.cast_sub hlt.le
  have htotalReal : ((left + right : Nat) : Real) ≠ 0 := by positivity
  rw [hdifferenceCast]
  field_simp [suzukiProjectAStar_pos.ne', Real.pi_ne_zero,
    hdifferenceReal, htotalReal]
  ring

private theorem suzukiYoshida_evenZeroSourceIntegral_normalization
    (hmaster : SuzukiYoshidaEndpointSourceModeMasterEvaluation)
    (right : Nat) (hright : 0 < right) :
    (2 * Real.pi : Real)⁻¹ *
        (-(((-1 : Real) ^ right) * Real.sqrt 2) /
          ((right : Real) * Real.pi)) *
        (∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand
            suzukiProjectAStar right z) =
      suzukiYoshidaComparisonEvenSourceIntegral 0 right := by
  rw [(hmaster right hright).2]
  unfold suzukiYoshidaComparisonEvenSourceIntegral
    suzukiDF6D4EvenModeScale
  dsimp only
  rw [if_pos rfl, if_neg hright.ne']
  simp only [Nat.cast_zero, zero_add, Nat.sub_zero]
  push_cast
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquareTwo : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hrightReal : (right : Real) ≠ 0 := by positivity
  field_simp [hsqrtTwo, hrightReal, Real.pi_ne_zero]
  rw [hsquareTwo]
  rw [suzukiDF6D4AlternatingSign_cast_real]
  ring

theorem suzukiYoshidaEvenSourceKernelPairing_eq_sourceIntegral_of_pos
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) left right =
      (suzukiYoshidaComparisonEvenSourceIntegral left right : Complex) := by
  rw [suzukiYoshidaEvenSourceKernelPairing_eq_sourceVariable_of_pos
    hsource left right hleft (hleft.trans hlt)]
  rw [integral_suzukiYoshidaEndpointEvenSourceVariableIntegrand_of_pos
    suzukiProjectAStar_pos left right hleft (hleft.trans hlt)]
  have hnormalization := congrArg (fun x : Real => (x : Complex))
    (suzukiYoshida_positiveEvenSourceIntegral_normalization
      (suzukiYoshidaEndpointSourceModeMasterEvaluation_of_source hsource)
      hleft hlt)
  push_cast at hnormalization
  push_cast
  simpa only [mul_assoc] using hnormalization

theorem suzukiYoshidaOddSourceKernelPairing_eq_sourceIntegral_of_pos
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) left right =
      (suzukiYoshidaComparisonOddSourceIntegral left right : Complex) := by
  rw [suzukiYoshidaOddSourceKernelPairing_eq_sourceVariable hsource left right]
  rw [integral_suzukiYoshidaEndpointOddSourceVariableIntegrand_of_pos
    suzukiProjectAStar_pos left right hleft (hleft.trans hlt)]
  have hnormalization := congrArg (fun x : Real => (x : Complex))
    (suzukiYoshida_positiveOddSourceIntegral_normalization
      (suzukiYoshidaEndpointSourceModeMasterEvaluation_of_source hsource)
      hleft hlt)
  push_cast at hnormalization
  push_cast
  simpa only [mul_assoc] using hnormalization

theorem suzukiYoshidaEvenZeroSourceKernelPairing_eq_sourceIntegral
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (right : Nat) (hright : 0 < right) :
    suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) 0 right =
      (suzukiYoshidaComparisonEvenSourceIntegral 0 right : Complex) := by
  rw [suzukiYoshidaEvenZeroSourceKernelPairing_eq_sourceVariable
    hsource right hright]
  rw [integral_suzukiYoshidaEndpointEvenZeroSourceVariableIntegrand
    suzukiProjectAStar_pos right hright]
  have hnormalization := congrArg (fun x : Real => (x : Complex))
    (suzukiYoshida_evenZeroSourceIntegral_normalization
      (suzukiYoshidaEndpointSourceModeMasterEvaluation_of_source hsource)
      right hright)
  push_cast at hnormalization
  push_cast
  simpa only [mul_assoc] using hnormalization

theorem suzukiYoshidaComparisonLimitKernelSourceIntegralNormalization_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiYoshidaComparisonLimitKernelSourceIntegralNormalization hsource := by
  constructor
  · intro left right hlt
    by_cases hleft : left = 0
    · subst left
      exact suzukiYoshidaEvenZeroSourceKernelPairing_eq_sourceIntegral
        hsource right hlt
    · exact suzukiYoshidaEvenSourceKernelPairing_eq_sourceIntegral_of_pos
        hsource (Nat.pos_of_ne_zero hleft) hlt
  · intro left right hleft hlt
    exact suzukiYoshidaOddSourceKernelPairing_eq_sourceIntegral_of_pos
      hsource hleft hlt

theorem suzukiEquation25OffDiagonalComparisonEvaluations_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25EvenOffDiagonalComparisonEvaluation hsource ∧
      SuzukiEquation25OddOffDiagonalComparisonEvaluation hsource :=
  suzukiEquation25OffDiagonalComparisonEvaluations_of_limitKernel hsource
    (suzukiYoshidaComparisonLimitKernelSourceIntegralNormalization_of_source
      hsource)

end

end RiemannHypothesisProject.Experiments.M100
