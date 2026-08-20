import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25GammaTailKernel

/-!
# Finite pairing cancellation in Suzuki's equation (2.5)

This module lifts the pointwise rational-multiplier cancellation to the
actual finite-square source pairings.  It first records the undifferentiated
version of the exponential-kernel autocorrelation bridge.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set SchwartzLineTestFunction
open scoped BigOperators ComplexConjugate FourierTransform

/-- A physical exponential Gamma summand against an undifferentiated
autocorrelation is its compact finite-square kernel pairing. -/
theorem integral_suzukiGammaExponentialKernel_mul_autocorrelation_eq_pairing_self
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (n : Nat) :
    (∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation v x) =
      suzukiFiniteKernelPairingComplex
        (suzukiGammaExponentialKernel n) a v := by
  let F : Real → Real → Complex := fun x y =>
    (suzukiGammaExponentialKernel n (x - y) : Complex) *
      v y * conj (v x)
  let G : Real → Real → Complex := fun y s =>
    (suzukiGammaExponentialKernel n s : Complex) *
      v y * conj (v (s + y))
  have hv : Integrable v := v.integrable
  have hconj : Integrable (fun x : Real => conj (v x)) := by
    have hcomp :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hv
    change Integrable (fun x : Real => Complex.conjCLE (v x))
    exact hcomp
  have hseparable : Integrable (fun p : Real × Real =>
      v p.2 * conj (v p.1)) (volume.prod volume) := by
    have hprod := hconj.mul_prod hv
    apply hprod.congr
    filter_upwards with p
    ring
  have hFraw : Integrable (fun p : Real × Real =>
      (suzukiGammaExponentialKernel n (p.1 - p.2) : Complex) *
        (v p.2 * conj (v p.1))) (volume.prod volume) := by
    apply hseparable.bdd_mul
    · change AEStronglyMeasurable (fun p : Real × Real =>
        (suzukiGammaExponentialKernel n (p.1 - p.2) : Complex))
      exact (Complex.continuous_ofReal.comp
        ((continuous_suzukiGammaExponentialKernel n).comp
          (by fun_prop : Continuous (fun p : Real × Real => p.1 - p.2))))
            |>.aestronglyMeasurable
    · filter_upwards with p
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiGammaExponentialKernel_nonneg n _)]
      exact suzukiGammaExponentialKernel_le_basePoint n _
  have hF : Integrable (fun p : Real × Real => F p.1 p.2)
      (volume.prod volume) := by
    simpa only [F, mul_assoc] using hFraw
  have hcoupled : Integrable (fun p : Real × Real =>
      v p.1 * conj (v (p.2 + p.1))) (volume.prod volume) := by
    let H : Real × Real → Complex := fun p => v p.1 * conj (v p.2)
    have hH : Integrable H := hv.mul_prod hconj
    have hcomp :=
      (measurePreserving_prod_add_right
        (volume : Measure Real) (volume : Measure Real)).integrable_comp_of_integrable hH
    change Integrable (fun p : Real × Real =>
      v p.1 * conj (v (p.2 + p.1))) (volume.prod volume) at hcomp
    exact hcomp
  have hGraw : Integrable (fun p : Real × Real =>
      (suzukiGammaExponentialKernel n p.2 : Complex) *
        (v p.1 * conj (v (p.2 + p.1)))) (volume.prod volume) := by
    apply hcoupled.bdd_mul
    · change AEStronglyMeasurable (fun p : Real × Real =>
        (suzukiGammaExponentialKernel n p.2 : Complex))
      exact (Complex.continuous_ofReal.comp
        ((continuous_suzukiGammaExponentialKernel n).comp
          (by fun_prop : Continuous (fun p : Real × Real => p.2))))
            |>.aestronglyMeasurable
    · filter_upwards with p
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiGammaExponentialKernel_nonneg n _)]
      exact suzukiGammaExponentialKernel_le_basePoint n _
  have hG : Integrable (fun p : Real × Real => G p.1 p.2)
      (volume.prod volume) := by
    simpa only [G, mul_assoc] using hGraw
  have hrestrict :
      (∫ p in suzukiFiniteSquare a, F p.1 p.2) =
        ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    by_cases hx : p.1 ∈ Set.Icc (-a) a
    · have hy : p.2 ∉ Set.Icc (-a) a := fun hy => hp ⟨hx, hy⟩
      have hvy : v p.2 = 0 := by
        by_contra hne
        exact hy (hsupport hne)
      simp [F, hvy]
    · have hvx : v p.1 = 0 := by
        by_contra hne
        exact hx (hsupport hne)
      simp [F, hvx]
  have hfiber (y : Real) :
      (∫ x : Real, F x y) = ∫ s : Real, G y s := by
    have htranslate := integral_sub_right_eq_self
      (fun s : Real => G y s) y (μ := volume)
    simpa only [F, G, sub_add_cancel] using htranslate
  have hphysicalNeg :
      (∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume)) =
        ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation v (-s) := by
    rw [MeasureTheory.integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards with s
    simp only [G]
    rw [show (fun x : Real =>
        (suzukiGammaExponentialKernel n s : Complex) *
            v x * conj (v (s + x))) =
          fun x : Real =>
            (suzukiGammaExponentialKernel n s : Complex) *
              (v x * conj (v (s + x))) by
        funext x
        ring]
    rw [integral_const_mul]
    apply congrArg (fun z : Complex =>
      (suzukiGammaExponentialKernel n s : Complex) * z)
    rw [autocorrelation_apply, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with y
    simp only [star_apply]
    congr 2
    ring
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex) *
        autocorrelation v x) volume
  have hphysical :
      (∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation v (-s)) =
        ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation v s := by
    simpa only [suzukiGammaExponentialKernel_neg, neg_neg] using hreflect
  calc
    (∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation v x) =
        ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation v (-s) := hphysical.symm
    _ = ∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume) :=
      hphysicalNeg.symm
    _ = ∫ y : Real, ∫ s : Real, G y s :=
      MeasureTheory.integral_prod (fun p : Real × Real => G p.1 p.2) hG
    _ = ∫ y : Real, ∫ x : Real, F x y := by
      apply integral_congr_ae
      filter_upwards with y
      exact (hfiber y).symm
    _ = ∫ x : Real, ∫ y : Real, F x y :=
      (MeasureTheory.integral_integral_swap hF).symm
    _ = ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) :=
      MeasureTheory.integral_integral hF
    _ = ∫ p in suzukiFiniteSquare a, F p.1 p.2 := hrestrict.symm
    _ = suzukiFiniteKernelPairingComplex
        (suzukiGammaExponentialKernel n) a v := by rfl

/-- Fourier self-adjointness for the same undifferentiated source. -/
theorem integral_suzukiGammaMultiplier_mul_fourierAutocorrelation_self
    (n : Nat) (v : SchwartzLineTestFunction) :
    (∫ t : Real,
        (suzukiEquation25GammaRationalMultiplier n t : Complex) *
          fourierAutocorrelation v t) =
      ∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation v x := by
  have hself :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ Real)
        Real.continuous_fourierChar continuous_inner
        (integrable_coe_suzukiGammaExponentialKernel n)
        (fourierAutocorrelation v).integrable
  rw [flip_innerₗ] at hself
  change
    (∫ t : Real,
        (𝓕 (fun x : Real =>
          (suzukiGammaExponentialKernel n x : Complex))) t •
            fourierAutocorrelation v t) =
      ∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) •
          (𝓕 (fourierAutocorrelation v : Real → Complex)) x at hself
  have hraw :
      (∫ t : Real,
          (suzukiEquation25GammaRationalMultiplier n t : Complex) *
            fourierAutocorrelation v t) =
        ∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation v (-x) := by
    simpa only [smul_eq_mul,
      fourier_suzukiGammaExponentialKernel_eq_equation25Multiplier,
      ← SchwartzMap.fourier_coe,
      fourier_fourierAutocorrelation_apply] using hself
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex) *
        autocorrelation v x) volume
  have hphysical :
      (∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation v (-x)) =
        ∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation v x := by
    simpa only [suzukiGammaExponentialKernel_neg, neg_neg] using hreflect
  exact hraw.trans hphysical

theorem norm_suzukiEquation25GammaRationalMultiplier_le
    (n : Nat) (xi : Real) :
    ‖(suzukiEquation25GammaRationalMultiplier n xi : Complex)‖ ≤ 16 := by
  let d : Real := (n : Real) + 1 / 4
  have hd : 1 / 4 ≤ d := by
    dsimp only [d]
    have hn : 0 ≤ (n : Real) := Nat.cast_nonneg n
    linarith
  have hden : 0 < d * (4 * d ^ 2 + (2 * Real.pi * xi) ^ 2) := by
    positivity
  have hdenLower : 1 / 16 ≤
      d * (4 * d ^ 2 + (2 * Real.pi * xi) ^ 2) := by
    nlinarith [sq_nonneg (2 * Real.pi * xi), sq_nonneg (d - 1 / 4)]
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold suzukiEquation25GammaRationalMultiplier
  change |1 / (d * (4 * d ^ 2 + (2 * Real.pi * xi) ^ 2))| ≤ 16
  rw [abs_of_pos (div_pos zero_lt_one hden)]
  rw [div_le_iff₀ hden]
  nlinarith

theorem integrable_suzukiEquation25GammaRationalMultiplier_mul_fourierAutocorrelation
    (n : Nat) (v : SchwartzLineTestFunction) :
    Integrable (fun xi : Real =>
      (suzukiEquation25GammaRationalMultiplier n xi : Complex) *
        fourierAutocorrelation v xi) := by
  apply (fourierAutocorrelation v).integrable.bdd_mul (c := 16)
  · have hcontinuousReal : Continuous
        (suzukiEquation25GammaRationalMultiplier n) := by
      unfold suzukiEquation25GammaRationalMultiplier
      apply continuous_const.div
      · fun_prop
      · intro xi
        positivity
    exact (Complex.continuous_ofReal.comp hcontinuousReal).aestronglyMeasurable
  · filter_upwards with xi
    exact norm_suzukiEquation25GammaRationalMultiplier_le n xi

/-- The integral of the Fourier autocorrelation is the real
zero-displacement autocorrelation mass. -/
theorem integral_fourierAutocorrelation_eq_autocorrelation_zero_re
    (v : SchwartzLineTestFunction) :
    (∫ xi : Real, fourierAutocorrelation v xi) =
      ((autocorrelation v 0).re : Complex) := by
  have henergy := integral_cos_two_pi_mul_fourierEnergyDensity v 0
  simp only [mul_zero, Real.cos_zero, one_mul] at henergy
  calc
    (∫ xi : Real, fourierAutocorrelation v xi) =
        ∫ xi : Real, (fourierEnergyDensity v xi : Complex) := by
          apply integral_congr_ae
          filter_upwards with xi
          rw [fourierAutocorrelation_apply, Complex.mul_conj]
          simp [fourierEnergyDensity]
    _ = ((autocorrelation v 0).re : Complex) := by
      rw [integral_complex_ofReal, henergy]

/-- One Gamma/Lerch derivative mode plus its raw exponential mode is exactly
the shifted-harmonic cusp mass. -/
theorem suzukiEquation25GammaPairingMode_cancellation
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) (n : Nat) :
    (suzukiFiniteKernelPairingComplex
        (suzukiGammaLerchKernelSummand n) a
        (SchwartzMap.derivCLM Complex Complex v.1)).re +
      (suzukiFiniteKernelPairingComplex
        (suzukiEquation25RawGammaExponentialKernel n) a v.1).re =
      (1 / ((n : Real) + 1 / 4)) *
        ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  have hsupport : Function.support v.1 ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v.1
  let m : Real → Complex := fun xi =>
    (suzukiEquation25GammaRationalMultiplier n xi : Complex)
  have hlerch :
      suzukiFiniteKernelPairingComplex
          (suzukiGammaLerchKernelSummand n) a u =
        ∫ xi : Real, m xi * fourierAutocorrelation u xi := by
    rw [← suzukiFiniteKernelPairingComplex_gammaExponential_eq_lerch
      ha hsupport n]
    rw [← integral_suzukiGammaExponentialKernel_mul_autocorrelation_eq_pairing
      hsupport n]
    exact (integral_suzukiGammaMultiplier_mul_fourierAutocorrelation_deriv
      n v.1).symm
  have hraw :
      suzukiFiniteKernelPairingComplex
          (suzukiEquation25RawGammaExponentialKernel n) a v.1 =
        ∫ xi : Real,
          (4 * ((n : Real) + 1 / 4) ^ 2 : Real) *
            m xi * fourierAutocorrelation v.1 xi := by
    have hkernel := funext
      (suzukiEquation25RawGammaExponentialKernel_eq_scaled n)
    rw [hkernel, suzukiFiniteKernelPairingComplex_const_mul]
    rw [← integral_suzukiGammaExponentialKernel_mul_autocorrelation_eq_pairing_self
      hsupport n]
    rw [← integral_suzukiGammaMultiplier_mul_fourierAutocorrelation_self
      n v.1, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with xi
    push_cast
    ring
  have hm :=
    integrable_suzukiEquation25GammaRationalMultiplier_mul_fourierAutocorrelation
      n v.1
  have hmu :=
    integrable_suzukiEquation25GammaRationalMultiplier_mul_fourierAutocorrelation
      n u
  have hrawIntegrable : Integrable (fun xi : Real =>
      ((4 * ((n : Real) + 1 / 4) ^ 2 : Real) : Complex) *
        m xi * fourierAutocorrelation v.1 xi) := by
    simpa only [m, mul_assoc] using
      hm.const_mul ((4 * ((n : Real) + 1 / 4) ^ 2 : Real) : Complex)
  have hcombined :
      (∫ xi : Real, m xi * fourierAutocorrelation u xi) +
          ∫ xi : Real,
            ((4 * ((n : Real) + 1 / 4) ^ 2 : Real) : Complex) *
              m xi * fourierAutocorrelation v.1 xi =
        ∫ xi : Real,
          ((1 / ((n : Real) + 1 / 4) : Real) : Complex) *
            fourierAutocorrelation v.1 xi := by
    rw [← integral_add hmu hrawIntegrable]
    apply integral_congr_ae
    filter_upwards with xi
    change
      (suzukiEquation25GammaRationalMultiplier n xi : Complex) *
          fourierAutocorrelation u xi +
        ((4 * ((n : Real) + 1 / 4) ^ 2 : Real) : Complex) *
          (suzukiEquation25GammaRationalMultiplier n xi : Complex) *
            fourierAutocorrelation v.1 xi = _
    rw [show fourierAutocorrelation u xi =
        ((2 * Real.pi * xi) ^ 2 : Real) *
          fourierAutocorrelation v.1 xi by
      exact fourierAutocorrelation_derivCLM_apply v.1 xi]
    have hcancel :=
      suzukiEquation25GammaRationalMultiplier_cancellation n xi
    have hcancelComplex := congrArg (fun x : Real => (x : Complex)) hcancel
    push_cast at hcancelComplex ⊢
    linear_combination hcancelComplex * fourierAutocorrelation v.1 xi
  have hmass := norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re v
  rw [hlerch, hraw, ← Complex.add_re, hcombined,
    integral_const_mul,
    integral_fourierAutocorrelation_eq_autocorrelation_zero_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [← hmass]

/-- The first `N` cancellation-safe Lerch kernels. -/
def suzukiEquation25GammaLerchKernelPartial
    (N : Nat) (x : Real) : Real :=
  ∑ n ∈ Finset.range N, suzukiGammaLerchKernelSummand n x

theorem continuous_suzukiEquation25GammaLerchKernelPartial (N : Nat) :
    Continuous (suzukiEquation25GammaLerchKernelPartial N) := by
  unfold suzukiEquation25GammaLerchKernelPartial
  exact continuous_finsetSum _ fun n _ =>
    continuous_suzukiGammaLerchKernelSummand n

/-- Summing the mode identity gives the exact finite shifted-harmonic mass. -/
theorem suzukiEquation25GammaPairingPartial_cancellation
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) (N : Nat) :
    ∑ n ∈ Finset.range N,
        ((suzukiFiniteKernelPairingComplex
            (suzukiGammaLerchKernelSummand n) a
            (SchwartzMap.derivCLM Complex Complex v.1)).re +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25RawGammaExponentialKernel n) a v.1).re) =
      suzukiEquation25ShiftedHarmonicPartial N *
        ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
  calc
    ∑ n ∈ Finset.range N,
        ((suzukiFiniteKernelPairingComplex
            (suzukiGammaLerchKernelSummand n) a
            (SchwartzMap.derivCLM Complex Complex v.1)).re +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25RawGammaExponentialKernel n) a v.1).re) =
        ∑ n ∈ Finset.range N,
          (1 / ((n : Real) + 1 / 4)) *
            ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact suzukiEquation25GammaPairingMode_cancellation ha v n
    _ = suzukiEquation25ShiftedHarmonicPartial N *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
          rw [← Finset.sum_mul]
          rfl

/-- After finite cancellation, the Lerch partial plus the full `r1''`
pairing is exactly the shifted-harmonic mass plus the continuous Gamma tail
pairing.  This is the finite identity whose limit remains to be taken. -/
theorem suzukiEquation25FinitePairing_eq_shiftedHarmonic_add_tail
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) (N : Nat) :
    (suzukiFiniteKernelPairingComplex
        (suzukiEquation25GammaLerchKernelPartial N) a
        (SchwartzMap.derivCLM Complex Complex v.1)).re +
      (suzukiFiniteKernelPairingComplex
        suzukiR1SecondKernel a v.1).re =
      suzukiEquation25ShiftedHarmonicPartial N *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
        (suzukiFiniteKernelPairingComplex
          (suzukiEquation25GammaTailKernel N) a v.1).re := by
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v.1
  have hlerchComplex :=
    suzukiFiniteKernelPairingComplex_finsetSum
      (Finset.range N) suzukiGammaLerchKernelSummand a u
      (fun n _ => continuous_suzukiGammaLerchKernelSummand n)
      u.continuous
  have hrawComplex :=
    suzukiFiniteKernelPairingComplex_finsetSum
      (Finset.range N) suzukiEquation25RawGammaExponentialKernel a v.1
      (fun n _ => continuous_suzukiEquation25RawGammaExponentialKernel n)
      v.1.continuous
  have hlerch := congrArg Complex.re hlerchComplex
  have hraw := congrArg Complex.re hrawComplex
  conv_rhs at hlerch => rw [← Complex.reCLM_apply, map_sum]
  conv_rhs at hraw => rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply] at hlerch hraw
  change
    (suzukiFiniteKernelPairingComplex
      (suzukiEquation25GammaLerchKernelPartial N) a u).re = _ at hlerch
  change
    (suzukiFiniteKernelPairingComplex
      (suzukiEquation25RawGammaExponentialPartial N) a v.1).re = _ at hraw
  have hcancel :=
    suzukiEquation25GammaPairingPartial_cancellation ha v N
  rw [Finset.sum_add_distrib, ← hlerch, ← hraw] at hcancel
  have htailAdd :
      (suzukiFiniteKernelPairingComplex
          (suzukiEquation25GammaTailKernel N) a v.1).re +
        (suzukiFiniteKernelPairingComplex
          (suzukiEquation25RawGammaExponentialPartial N) a v.1).re =
        (suzukiFiniteKernelPairingComplex
          suzukiR1SecondKernel a v.1).re := by
    have hadd := suzukiFiniteKernelPairingComplex_add
      (a := a) (u := v.1)
      (continuous_suzukiEquation25GammaTailKernel N)
      (continuous_suzukiEquation25RawGammaExponentialPartial N)
      v.1.continuous
    have hkernel : (fun t =>
        suzukiEquation25GammaTailKernel N t +
          suzukiEquation25RawGammaExponentialPartial N t) =
        suzukiR1SecondKernel := by
      funext t
      unfold suzukiEquation25GammaTailKernel
      ring
    rw [hkernel] at hadd
    have hre := congrArg Complex.re hadd
    rw [Complex.add_re] at hre
    exact hre.symm
  change
    (suzukiFiniteKernelPairingComplex
        (suzukiEquation25GammaLerchKernelPartial N) a u).re + _ = _
  linear_combination hcancel - htailAdd

end

end M100
end Experiments
end RiemannHypothesisProject
