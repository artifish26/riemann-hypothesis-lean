import RiemannHypothesisProject.WeilPositivity.BurnolFormulaBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# M100-X14 Suzuki scalar kernel normalization

This experimental module implements the source-to-project coordinate change
identified by X13.  Suzuki uses `exp (i*z*x)` while Mathlib uses
`exp (-2*pi*i*x*t)`, so the project base test corresponding to a source test
`v` is

`T(v)(x) = 2*pi*v(-2*pi*x)`.

The declarations in this file are sign-free normalization identities.  They
assert no positivity, zero-location, spectral, or operator conclusion.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open MeasureTheory
open SchwartzLineTestFunction
open scoped ComplexConjugate Convolution FourierTransform

noncomputable section

/-- The positive Fourier scale relating Suzuki's convention to Mathlib's. -/
def suzukiTwoPi : Real := 2 * Real.pi

/-- The reflected spatial scale in `T(v)(x) = 2*pi*v(-2*pi*x)`. -/
def suzukiCoordinateScale : Real := -suzukiTwoPi

theorem suzukiTwoPi_pos : 0 < suzukiTwoPi := by
  unfold suzukiTwoPi
  positivity

theorem suzukiTwoPi_ne_zero : suzukiTwoPi ≠ 0 :=
  suzukiTwoPi_pos.ne'

theorem suzukiCoordinateScale_ne_zero : suzukiCoordinateScale ≠ 0 := by
  unfold suzukiCoordinateScale
  exact neg_ne_zero.mpr suzukiTwoPi_ne_zero

private theorem abs_inv_suzukiCoordinateScale :
    |suzukiCoordinateScale⁻¹| = suzukiTwoPi⁻¹ := by
  rw [abs_inv, suzukiCoordinateScale, abs_neg,
    abs_of_pos suzukiTwoPi_pos]

private theorem suzukiTwoPi_mul_abs_inv_coordinateScale :
    suzukiTwoPi * |suzukiCoordinateScale⁻¹| = 1 := by
  rw [abs_inv_suzukiCoordinateScale]
  exact mul_inv_cancel₀ suzukiTwoPi_ne_zero

private theorem suzukiTwoPi_sq_mul_abs_inv_coordinateScale :
    suzukiTwoPi ^ 2 * |suzukiCoordinateScale⁻¹| = suzukiTwoPi := by
  calc
    suzukiTwoPi ^ 2 * |suzukiCoordinateScale⁻¹| =
        suzukiTwoPi *
          (suzukiTwoPi * |suzukiCoordinateScale⁻¹|) := by ring
    _ = suzukiTwoPi := by
      rw [suzukiTwoPi_mul_abs_inv_coordinateScale]
      ring

/-- Multiplication by `-2*pi` as a continuous real-linear equivalence. -/
def suzukiProjectScaleEquiv : Real ≃L[Real] Real :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 suzukiCoordinateScale suzukiCoordinateScale_ne_zero)

@[simp]
theorem suzukiProjectScaleEquiv_apply (x : Real) :
    suzukiProjectScaleEquiv x = suzukiCoordinateScale * x := by
  rfl

/-- The exact project-coordinate base test selected by the X13 audit. -/
def suzukiProjectBase
    (v : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  (suzukiTwoPi : Complex) •
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      suzukiProjectScaleEquiv v

@[simp]
theorem suzukiProjectBase_apply
    (v : SchwartzLineTestFunction) (x : Real) :
    suzukiProjectBase v x =
      (suzukiTwoPi : Complex) * v (suzukiCoordinateScale * x) := by
  rfl

/-- Suzuki's `exp (i*z*x)` Fourier-Laplace source.  Compact support will be
made explicit when this source is used at non-real `z`. -/
def suzukiFourierSource
    (v : SchwartzLineTestFunction) (z : Complex) : Complex :=
  ∫ x : Real,
    Complex.exp ((x : Complex) * Complex.I * z) * v x

/-- Change of variables from the project coordinate to Suzuki's coordinate.
The amplitude `2*pi` cancels the absolute Jacobian exactly. -/
theorem integral_exp_mul_suzukiProjectBase
    (v : SchwartzLineTestFunction) (z : Complex) :
    (∫ x : Real,
        Complex.exp
            (((suzukiCoordinateScale * x : Real) : Complex) * Complex.I * z) *
          suzukiProjectBase v x) =
      suzukiFourierSource v z := by
  have hscale := Measure.integral_comp_mul_left
    (g := fun y : Real =>
      Complex.exp ((y : Complex) * Complex.I * z) * v y)
    suzukiCoordinateScale
  have hscale' :
      (∫ x : Real,
          Complex.exp
              (((suzukiCoordinateScale * x : Real) : Complex) * Complex.I * z) *
            v (suzukiCoordinateScale * x)) =
        |suzukiCoordinateScale⁻¹| •
          ∫ y : Real,
            Complex.exp ((y : Complex) * Complex.I * z) * v y := by
    simpa using hscale
  rw [suzukiFourierSource]
  calc
    (∫ x : Real,
        Complex.exp
            (((suzukiCoordinateScale * x : Real) : Complex) * Complex.I * z) *
          suzukiProjectBase v x) =
        (suzukiTwoPi : Complex) *
          ∫ x : Real,
            Complex.exp
                (((suzukiCoordinateScale * x : Real) : Complex) * Complex.I * z) *
              v (suzukiCoordinateScale * x) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          rw [suzukiProjectBase_apply]
          ring
    _ = (suzukiTwoPi : Complex) *
        (|suzukiCoordinateScale⁻¹| •
          ∫ y : Real,
            Complex.exp ((y : Complex) * Complex.I * z) * v y) := by
          rw [hscale']
    _ = ∫ y : Real,
        Complex.exp ((y : Complex) * Complex.I * z) * v y := by
          simp only [Complex.real_smul]
          rw [← mul_assoc]
          have hcoefficient :
              (suzukiTwoPi : Complex) *
                  ((|suzukiCoordinateScale⁻¹| : Real) : Complex) = 1 := by
            rw [← Complex.ofReal_mul,
              suzukiTwoPi_mul_abs_inv_coordinateScale]
            norm_num
          rw [hcoefficient, one_mul]

/-- At real frequency, the Fourier transform of the scaled project base is
exactly Suzuki's Fourier transform, with no residual factor. -/
theorem fourier_suzukiProjectBase_apply
    (v : SchwartzLineTestFunction) (t : Real) :
    (𝓕 (suzukiProjectBase v)) t = suzukiFourierSource v (t : Complex) := by
  rw [SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  convert integral_exp_mul_suzukiProjectBase v (t : Complex) using 1
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg (fun w : Complex => Complex.exp w * suzukiProjectBase v x)
  unfold suzukiCoordinateScale suzukiTwoPi
  push_cast
  ring

/-- The amplitude in the source-to-project scaling is exactly the convolution
Jacobian, so autocorrelation commutes with `suzukiProjectBase`. -/
theorem autocorrelation_suzukiProjectBase
    (v : SchwartzLineTestFunction) :
    autocorrelation (suzukiProjectBase v) =
      suzukiProjectBase (autocorrelation v) := by
  ext x
  rw [suzukiProjectBase_apply, autocorrelation_apply,
    autocorrelation_apply, MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  have hscale := Measure.integral_comp_mul_left
    (g := fun y : Real =>
      v y * star v (suzukiCoordinateScale * x - y))
    suzukiCoordinateScale
  have hscale' :
      (∫ y : Real,
          v (suzukiCoordinateScale * y) *
            star v
              (suzukiCoordinateScale * x -
                suzukiCoordinateScale * y)) =
        |suzukiCoordinateScale⁻¹| •
          ∫ y : Real,
            v y * star v (suzukiCoordinateScale * x - y) := by
    simpa using hscale
  calc
    (∫ y : Real,
        suzukiProjectBase v y *
          star (suzukiProjectBase v) (x - y)) =
        (suzukiTwoPi : Complex) ^ 2 *
          ∫ y : Real,
            v (suzukiCoordinateScale * y) *
              star v
                (suzukiCoordinateScale * x -
                  suzukiCoordinateScale * y) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          simp only [suzukiProjectBase_apply, star_apply, map_mul,
            Complex.conj_ofReal]
          have harg :
              suzukiCoordinateScale * (-(x - y)) =
                -(suzukiCoordinateScale * x -
                  suzukiCoordinateScale * y) := by
            ring
          rw [harg]
          ring
    _ = (suzukiTwoPi : Complex) ^ 2 *
        (|suzukiCoordinateScale⁻¹| •
          ∫ y : Real,
            v y * star v (suzukiCoordinateScale * x - y)) := by
          rw [hscale']
    _ = (suzukiTwoPi : Complex) *
        ∫ y : Real,
          v y * star v (suzukiCoordinateScale * x - y) := by
          simp only [Complex.real_smul]
          rw [← mul_assoc]
          have hcoefficient :
              (suzukiTwoPi : Complex) ^ 2 *
                  ((|suzukiCoordinateScale⁻¹| : Real) : Complex) =
                (suzukiTwoPi : Complex) := by
            rw [← Complex.ofReal_pow, ← Complex.ofReal_mul,
              suzukiTwoPi_sq_mul_abs_inv_coordinateScale]
          rw [hcoefficient]

/-- The concrete Burnol Fourier-Laplace source of the scaled autocorrelation
is exactly Suzuki's Fourier-Laplace source of the source autocorrelation. -/
theorem burnolFourierLaplaceSource_suzukiProjectBase
    (v : SchwartzLineTestFunction) (z : Complex) :
    burnolFourierLaplaceSource (suzukiProjectBase v) z =
      suzukiFourierSource (autocorrelation v) z := by
  rw [burnolFourierLaplaceSource, autocorrelation_suzukiProjectBase]
  convert integral_exp_mul_suzukiProjectBase (autocorrelation v) z using 1
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg
    (fun w : Complex =>
      Complex.exp w * suzukiProjectBase (autocorrelation v) x)
  unfold suzukiCoordinateScale suzukiTwoPi
  push_cast
  ring

/-- On the real line, the project formula-facing autocorrelation is Suzuki's
Fourier transform of the genuine source autocorrelation. -/
theorem fourierAutocorrelation_suzukiProjectBase_apply
    (v : SchwartzLineTestFunction) (t : Real) :
    fourierAutocorrelation (suzukiProjectBase v) t =
      suzukiFourierSource (autocorrelation v) (t : Complex) := by
  rw [← burnolFourierLaplaceSource_ofReal]
  exact burnolFourierLaplaceSource_suzukiProjectBase v (t : Complex)

/-- Exact support membership under the reflected `-2*pi` coordinate. -/
theorem mem_support_suzukiProjectBase_iff
    (v : SchwartzLineTestFunction) (x : Real) :
    x ∈ Function.support (suzukiProjectBase v) ↔
      suzukiCoordinateScale * x ∈ Function.support v := by
  simp only [Function.mem_support, suzukiProjectBase_apply]
  rw [mul_ne_zero_iff_left]
  exact_mod_cast suzukiTwoPi_ne_zero

/-- Source support radius `a` becomes project support radius `a/(2*pi)`. -/
theorem support_suzukiProjectBase_subset_Icc
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    Function.support (suzukiProjectBase v) ⊆
      Set.Icc (-a / suzukiTwoPi) (a / suzukiTwoPi) := by
  intro x hx
  have hscaled :=
    hsupport ((mem_support_suzukiProjectBase_iff v x).mp hx)
  unfold suzukiCoordinateScale at hscaled
  constructor
  · apply (div_le_iff₀ suzukiTwoPi_pos).2
    nlinarith [hscaled.2]
  · apply (le_div_iff₀ suzukiTwoPi_pos).2
    nlinarith [hscaled.1]

/-- The `s = 2` Hurwitz--Lerch series used in Suzuki's displayed screw
function.  X14 defines it directly because mathlib currently has no named
Hurwitz--Lerch `Phi` receiving surface. -/
def suzukiLerchPhiTwo (q a : Real) : Real :=
  ∑' n : Nat, q ^ n / ((n : Real) + a) ^ 2

private theorem summable_suzukiInverseSquare :
    Summable (fun n : Nat => 1 / ((n : Real) + 1 / 4) ^ 2) := by
  have h :=
    (Real.summable_one_div_nat_add_rpow (1 / 4) 2).2 (by norm_num)
  apply h.congr
  intro n
  rw [abs_of_pos (by
    have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
    linarith), Real.rpow_two]

private theorem summable_suzukiLerchPhiTwo_terms
    {q : Real} (hq : |q| ≤ 1) :
    Summable (fun n : Nat => q ^ n / ((n : Real) + 1 / 4) ^ 2) := by
  apply summable_suzukiInverseSquare.of_norm_bounded
  intro n
  have hden : 0 < ((n : Real) + 1 / 4) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hden]
  apply (div_le_div_iff_of_pos_right hden).2
  simpa using pow_le_one₀ (abs_nonneg q) hq

/-- The convergent combined Lerch contribution.  Keeping the cancellation
inside each summand exposes a uniform inverse-square majorant, including at
`t = 0`. -/
def suzukiLerchDifference (t : Real) : Real :=
  ∑' n : Nat,
    (1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |t|))) /
      ((n : Real) + 1 / 4) ^ 2

private theorem norm_suzukiLerchDifference_summand_le
    (n : Nat) (t : Real) :
    ‖(1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |t|))) /
        ((n : Real) + 1 / 4) ^ 2‖ ≤
      1 / ((n : Real) + 1 / 4) ^ 2 := by
  have hcoefficient : 0 ≤ 2 * (n : Real) + 1 / 2 := by positivity
  have hexponent :
      -((2 * (n : Real) + 1 / 2) * |t|) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg hcoefficient (abs_nonneg t))
  have hexp_le_one :
      Real.exp (-((2 * (n : Real) + 1 / 2) * |t|)) ≤ 1 :=
    (Real.exp_le_one_iff).2 hexponent
  have hnum_nonneg :
      0 ≤ 1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |t|)) :=
    sub_nonneg.mpr hexp_le_one
  have hnum_le_one :
      1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |t|)) ≤ 1 := by
    linarith [Real.exp_pos (-((2 * (n : Real) + 1 / 2) * |t|))]
  have hden : 0 < ((n : Real) + 1 / 4) ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum_nonneg hden.le)]
  exact (div_le_div_iff_of_pos_right hden).2 hnum_le_one

/-- The cancellation-safe Lerch difference is continuous by the Weierstrass
test with the shifted inverse-square majorant. -/
theorem continuous_suzukiLerchDifference :
    Continuous suzukiLerchDifference := by
  unfold suzukiLerchDifference
  apply continuous_tsum
  · intro n
    fun_prop
  · exact summable_suzukiInverseSquare
  · exact norm_suzukiLerchDifference_summand_le

/-- The cancellation-safe series is exactly Suzuki's displayed
Hurwitz--Lerch difference. -/
theorem suzukiLerchDifference_eq_sourceFormula (t : Real) :
    suzukiLerchDifference t =
      suzukiLerchPhiTwo 1 (1 / 4) -
        Real.exp (-|t| / 2) *
          suzukiLerchPhiTwo (Real.exp (-2 * |t|)) (1 / 4) := by
  have hone :
      Summable (fun n : Nat =>
        (1 : Real) ^ n / ((n : Real) + 1 / 4) ^ 2) :=
    summable_suzukiLerchPhiTwo_terms (by norm_num)
  have hqabs : |Real.exp (-2 * |t|)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_le_one_iff).2 (by nlinarith [abs_nonneg t])
  have hq :
      Summable (fun n : Nat =>
        Real.exp (-2 * |t|) ^ n / ((n : Real) + 1 / 4) ^ 2) :=
    summable_suzukiLerchPhiTwo_terms hqabs
  have hscaled := hq.mul_left (Real.exp (-|t| / 2))
  unfold suzukiLerchDifference suzukiLerchPhiTwo
  rw [← tsum_mul_left, ← hone.tsum_sub hscaled]
  apply tsum_congr
  intro n
  have hexp :
      Real.exp (-((2 * (n : Real) + 1 / 2) * |t|)) =
        Real.exp (-|t| / 2) * Real.exp (-2 * |t|) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  norm_num
  ring

/-- The finite von-Mangoldt prefix in Suzuki's screw function. -/
def suzukiPrimeScrewTerm (t : Real) : Real :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp |t|⌋₊,
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
      (|t| - Real.log n)

/-- A continuous individual prime contribution.  The positive part makes the
vanishing at the moving cutoff explicit. -/
def suzukiPrimeScrewSummand (n : Nat) (t : Real) : Real :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    max (|t| - Real.log n) 0

private theorem suzukiPrimeScrewSummand_eq_of_mem_cutoff
    {n : Nat} {t : Real} (hn : n ∈ Finset.Icc 2 ⌊Real.exp |t|⌋₊) :
    suzukiPrimeScrewSummand n t =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (|t| - Real.log n) := by
  rw [Finset.mem_Icc] at hn
  unfold suzukiPrimeScrewSummand
  rw [max_eq_left]
  apply sub_nonneg.mpr
  have hnpos : (0 : Real) < n := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn.1)
  apply (Real.log_le_iff_le_exp hnpos).2
  exact (Nat.le_floor_iff (Real.exp_nonneg _)).1 hn.2

private theorem suzukiPrimeScrewSummand_eq_zero_of_not_mem_cutoff
    {n : Nat} {t : Real} (hnpos : 0 < n)
    (hn : n ∉ Finset.Icc 2 ⌊Real.exp |t|⌋₊)
    (hnlower : 2 ≤ n) :
    suzukiPrimeScrewSummand n t = 0 := by
  have hfloor : ⌊Real.exp |t|⌋₊ < n := by
    rw [Finset.mem_Icc] at hn
    exact Nat.lt_of_not_ge (fun hle => hn ⟨hnlower, hle⟩)
  have hexp : Real.exp |t| < (n : Real) :=
    (Nat.floor_lt' hnpos.ne').1 hfloor
  have habslog : |t| < Real.log n :=
    (Real.lt_log_iff_exp_lt (by exact_mod_cast hnpos)).2 hexp
  unfold suzukiPrimeScrewSummand
  rw [max_eq_right (sub_nonpos.mpr habslog.le), mul_zero]

theorem suzukiPrimeScrewTerm_eq_fixed_sum
    {t R : Real} (htR : |t| ≤ R) :
    suzukiPrimeScrewTerm t =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp R⌋₊,
        suzukiPrimeScrewSummand n t := by
  have hfloor : ⌊Real.exp |t|⌋₊ ≤ ⌊Real.exp R⌋₊ :=
    Nat.floor_mono (Real.exp_le_exp.mpr htR)
  have hsubset :
      Finset.Icc 2 ⌊Real.exp |t|⌋₊ ⊆
        Finset.Icc 2 ⌊Real.exp R⌋₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hfloor⟩
  rw [suzukiPrimeScrewTerm]
  calc
    (∑ n ∈ Finset.Icc 2 ⌊Real.exp |t|⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (|t| - Real.log n)) =
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp |t|⌋₊,
          suzukiPrimeScrewSummand n t := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (suzukiPrimeScrewSummand_eq_of_mem_cutoff hn).symm
    _ = ∑ n ∈ Finset.Icc 2 ⌊Real.exp R⌋₊,
          suzukiPrimeScrewSummand n t := by
      apply Finset.sum_subset hsubset
      intro n hnlarge hnsmall
      rw [Finset.mem_Icc] at hnlarge
      exact suzukiPrimeScrewSummand_eq_zero_of_not_mem_cutoff
        (lt_of_lt_of_le (by norm_num) hnlarge.1) hnsmall hnlarge.1

/-- The moving von-Mangoldt prefix is continuous: on every bounded
neighborhood it is a fixed finite sum of continuous positive-part terms. -/
theorem continuous_suzukiPrimeScrewTerm :
    Continuous suzukiPrimeScrewTerm := by
  rw [continuous_iff_continuousAt]
  intro t₀
  let R : Real := |t₀| + 1
  let fixedSum : Real → Real := fun t =>
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp R⌋₊,
      suzukiPrimeScrewSummand n t
  have hfixed : Continuous fixedSum := by
    dsimp only [fixedSum, suzukiPrimeScrewSummand]
    fun_prop
  have hball : ∀ᶠ t in nhds t₀, t ∈ Metric.ball t₀ 1 :=
    Metric.ball_mem_nhds t₀ (by norm_num)
  have heq : suzukiPrimeScrewTerm =ᶠ[nhds t₀] fixedSum := by
    filter_upwards [hball] with t ht
    apply suzukiPrimeScrewTerm_eq_fixed_sum
    dsimp only [R]
    rw [Metric.mem_ball, Real.dist_eq] at ht
    calc
      |t| = |(t - t₀) + t₀| := by ring_nf
      _ ≤ |t - t₀| + |t₀| := abs_add_le _ _
      _ ≤ |t₀| + 1 := by linarith
  exact (continuousAt_congr heq).2 hfixed.continuousAt

/-- Suzuki's explicit real screw function, equation (1.3), with every sign
and numerical factor retained from the X13 convention audit.  No positivity
property is built into this definition. -/
def suzukiScrewFunction (t : Real) : Real :=
  -4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
    suzukiPrimeScrewTerm t -
      |t| / 2 *
        ((Complex.digamma (1 / 4 : Complex)).re - Real.log Real.pi) -
      1 / 4 *
        (suzukiLerchPhiTwo 1 (1 / 4) -
          Real.exp (-|t| / 2) *
            suzukiLerchPhiTwo (Real.exp (-2 * |t|)) (1 / 4))

/-- Suzuki's displayed explicit screw function is continuous.  The moving
prime cutoff is locally finite, while the apparent endpoint issue in the
Lerch terms is resolved by their cancellation-safe combined series. -/
theorem continuous_suzukiScrewFunction :
    Continuous suzukiScrewFunction := by
  have hformula : suzukiScrewFunction = fun t : Real =>
      -4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) +
        suzukiPrimeScrewTerm t -
          |t| / 2 *
            ((Complex.digamma (1 / 4 : Complex)).re - Real.log Real.pi) -
          1 / 4 * suzukiLerchDifference t := by
    funext t
    rw [suzukiScrewFunction, suzukiLerchDifference_eq_sourceFormula]
  rw [hformula]
  have hprime : Continuous (fun t : Real => suzukiPrimeScrewTerm t) :=
    continuous_suzukiPrimeScrewTerm
  have hlerch : Continuous (fun t : Real => suzukiLerchDifference t) :=
    continuous_suzukiLerchDifference
  fun_prop

/-- Evenness is visible directly in the explicit arithmetic formula. -/
theorem suzukiScrewFunction_neg (t : Real) :
    suzukiScrewFunction (-t) = suzukiScrewFunction t := by
  simp only [suzukiScrewFunction, suzukiPrimeScrewTerm, abs_neg,
    neg_div, neg_neg]
  ring

/-- The explicit screw function is normalized to vanish at the origin. -/
@[simp]
theorem suzukiScrewFunction_zero : suzukiScrewFunction 0 = 0 := by
  simp [suzukiScrewFunction, suzukiPrimeScrewTerm]
  norm_num

/-- Suzuki's differential operator `D = i d/dx` on the smooth experimental
source class.  This remains a Schwartz function, so no Sobolev or operator
domain is introduced in X14. -/
def suzukiDifferential
    (v : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  Complex.I • SchwartzMap.derivCLM Complex Complex v

@[simp]
theorem suzukiDifferential_apply
    (v : SchwartzLineTestFunction) (x : Real) :
    suzukiDifferential v x =
      Complex.I * SchwartzMap.derivCLM Complex Complex v x := by
  rfl

/-- Differentiation and multiplication by `i` preserve a compact support
window.  The proof passes through topological support so endpoint behavior is
not assumed. -/
theorem support_suzukiDifferential_subset_Icc
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    Function.support (suzukiDifferential v) ⊆ Set.Icc (-a) a := by
  have hvTSupport : tsupport v ⊆ Set.Icc (-a) a :=
    closure_minimal hsupport isClosed_Icc
  intro x hx
  have hxDeriv :
      x ∈ Function.support (SchwartzMap.derivCLM Complex Complex v) := by
    intro hzero
    exact hx (by simp [suzukiDifferential_apply, hzero])
  exact hvTSupport
    (SchwartzMap.tsupport_derivCLM_subset Complex v
      (subset_closure hxDeriv))

/-- For a compactly supported source, the interval mean of `D v` is the same
as the endpoint difference and therefore vanishes. -/
theorem setIntegral_suzukiDifferential_eq_zero
    {a : Real} {v : SchwartzLineTestFunction}
    (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    (∫ x in Set.Icc (-a) a, suzukiDifferential v x) = 0 := by
  have hopen : IsOpen (Function.support v) := v.continuous.isOpen_support
  have hsupportInterior :
      Function.support v ⊆ interior (Set.Icc (-a) a) :=
    (hopen.subset_interior_iff).2 hsupport
  have hright : v a = 0 := by
    by_contra hne
    have hmem := hsupportInterior hne
    rw [interior_Icc] at hmem
    exact (lt_irrefl a) hmem.2
  have hleft : v (-a) = 0 := by
    by_contra hne
    have hmem := hsupportInterior hne
    rw [interior_Icc] at hmem
    exact (lt_irrefl (-a)) hmem.1
  have hfundamental :
      (∫ x in (-a)..a,
          SchwartzMap.derivCLM Complex Complex v x) =
        v a - v (-a) := by
    apply intervalIntegral.integral_deriv_eq_sub'
      (f := fun x : Real => v x)
    · funext x
      exact (SchwartzMap.derivCLM_apply Complex v x).symm
    · exact fun x _ => v.differentiableAt
    · exact (SchwartzMap.derivCLM Complex Complex v).continuous.continuousOn
  simp only [suzukiDifferential_apply]
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  simpa [hleft, hright] using congrArg (fun z : Complex => Complex.I * z) hfundamental

/-- The compact square on which Suzuki's scalar kernel form is evaluated. -/
def suzukiFiniteSquare (a : Real) : Set (Real × Real) :=
  Set.Icc (-a) a ×ˢ Set.Icc (-a) a

theorem isCompact_suzukiFiniteSquare (a : Real) :
    IsCompact (suzukiFiniteSquare a) := by
  exact isCompact_Icc.prod isCompact_Icc

/-- The translation-kernel integrand with Suzuki's linear-in-the-first
pairing convention.  The first product coordinate is `x`, the second is `y`.
-/
def suzukiKernelPairingIntegrand
    (kernel : Real → Real) (u : Real → Complex)
    (p : Real × Real) : Complex :=
  (kernel (p.1 - p.2) : Complex) * u p.2 * conj (u p.1)

/-- The finite-square complex kernel pairing.  Its real part below is the
scalar surface consumed by the formula residual. -/
def suzukiFiniteKernelPairingComplex
    (kernel : Real → Real) (a : Real) (u : Real → Complex) : Complex :=
  ∫ p in suzukiFiniteSquare a,
    suzukiKernelPairingIntegrand kernel u p

/-- The real scalar finite-interval kernel form, with no positivity claim. -/
def suzukiFiniteKernelPairing
    (kernel : Real → Real) (a : Real) (u : Real → Complex) : Real :=
  (suzukiFiniteKernelPairingComplex kernel a u).re

theorem continuous_suzukiKernelPairingIntegrand
    {kernel : Real → Real} {u : Real → Complex}
    (hkernel : Continuous kernel) (hu : Continuous u) :
    Continuous (suzukiKernelPairingIntegrand kernel u) := by
  unfold suzukiKernelPairingIntegrand
  fun_prop

/-- A continuous scalar kernel gives an integrable finite-square pairing for
every continuous source. -/
theorem integrableOn_suzukiKernelPairingIntegrand
    {kernel : Real → Real} {u : Real → Complex} {a : Real}
    (hkernel : Continuous kernel) (hu : Continuous u) :
    IntegrableOn (suzukiKernelPairingIntegrand kernel u)
      (suzukiFiniteSquare a) := by
  exact (continuous_suzukiKernelPairingIntegrand hkernel hu).continuousOn
    |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)

/-- The product-measure definition is exactly the requested iterated double
integral whenever the kernel and source are continuous. -/
theorem suzukiFiniteKernelPairingComplex_eq_iterated
    {kernel : Real → Real} {u : Real → Complex} {a : Real}
    (hkernel : Continuous kernel) (hu : Continuous u) :
    suzukiFiniteKernelPairingComplex kernel a u =
      ∫ x in Set.Icc (-a) a,
        ∫ y in Set.Icc (-a) a,
          (kernel (x - y) : Complex) * u y * conj (u x) := by
  have hintegrable :=
    integrableOn_suzukiKernelPairingIntegrand
      (a := a) hkernel hu
  rw [MeasureTheory.Measure.volume_eq_prod] at hintegrable
  rw [suzukiFiniteKernelPairingComplex, suzukiFiniteSquare,
    MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.setIntegral_prod
      (suzukiKernelPairingIntegrand kernel u) hintegrable]
  rfl

/-- Multiplication of both derivative slots by `i` cancels on the diagonal
kernel pairing.  This is the exact scalar bridge between Suzuki's displayed
`v'` integral and the operator-facing `D v` notation. -/
theorem suzukiFiniteKernelPairingComplex_differential_eq_deriv
    (kernel : Real → Real) (a : Real)
    (v : SchwartzLineTestFunction) :
    suzukiFiniteKernelPairingComplex kernel a (suzukiDifferential v) =
      suzukiFiniteKernelPairingComplex kernel a
        (SchwartzMap.derivCLM Complex Complex v) := by
  unfold suzukiFiniteKernelPairingComplex suzukiKernelPairingIntegrand
  apply integral_congr_ae
  filter_upwards with p
  simp [suzukiDifferential_apply]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem suzukiFiniteKernelPairing_differential_eq_deriv
    (kernel : Real → Real) (a : Real)
    (v : SchwartzLineTestFunction) :
    suzukiFiniteKernelPairing kernel a (suzukiDifferential v) =
      suzukiFiniteKernelPairing kernel a
        (SchwartzMap.derivCLM Complex Complex v) := by
  exact congrArg Complex.re
    (suzukiFiniteKernelPairingComplex_differential_eq_deriv kernel a v)

/-- The standard centered screw kernel.  Centering changes neither the raw
form nor its sign on a zero-mean source; that fact is proved below. -/
def suzukiCenteredKernel
    (kernel : Real → Real) (x y : Real) : Real :=
  kernel (x - y) - kernel x - kernel (-y) + kernel 0

/-- The finite-square pairing for the centered two-variable kernel. -/
def suzukiFiniteCenteredKernelPairingComplex
    (kernel : Real → Real) (a : Real) (u : Real → Complex) : Complex :=
  ∫ p in suzukiFiniteSquare a,
    (suzukiCenteredKernel kernel p.1 p.2 : Complex) *
      u p.2 * conj (u p.1)

/-- Centering is algebraically invisible on zero-mean continuous sources.
The proof expands all three correction terms and factors their product
integrals; it assumes no sign or positive-definiteness property of `kernel`.
-/
theorem suzukiFiniteCenteredKernelPairingComplex_eq_raw_of_zeroMean
    {kernel : Real → Real} {u : Real → Complex} {a : Real}
    (hkernel : Continuous kernel) (hu : Continuous u)
    (hzero : (∫ x in Set.Icc (-a) a, u x) = 0) :
    suzukiFiniteCenteredKernelPairingComplex kernel a u =
      suzukiFiniteKernelPairingComplex kernel a u := by
  let raw : Real × Real → Complex :=
    fun p => (kernel (p.1 - p.2) : Complex) * u p.2 * conj (u p.1)
  let rowCorrection : Real × Real → Complex :=
    fun p => ((kernel p.1 : Complex) * conj (u p.1)) * u p.2
  let columnCorrection : Real × Real → Complex :=
    fun p => conj (u p.1) * ((kernel (-p.2) : Complex) * u p.2)
  let constantCorrection : Real × Real → Complex :=
    fun p => conj (u p.1) * ((kernel 0 : Complex) * u p.2)
  have hraw : IntegrableOn raw (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous raw).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hrow : IntegrableOn rowCorrection (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous rowCorrection).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hcolumn : IntegrableOn columnCorrection (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous columnCorrection).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hconstant : IntegrableOn constantCorrection (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous constantCorrection).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hzeroConj : (∫ x in Set.Icc (-a) a, conj (u x)) = 0 := by
    rw [integral_conj, hzero, map_zero]
  rw [suzukiFiniteCenteredKernelPairingComplex,
    suzukiFiniteKernelPairingComplex]
  have hexpand :
      (fun p : Real × Real =>
        (suzukiCenteredKernel kernel p.1 p.2 : Complex) *
          u p.2 * conj (u p.1)) =
        fun p => raw p - rowCorrection p - columnCorrection p +
          constantCorrection p := by
    funext p
    simp only [suzukiCenteredKernel, raw, rowCorrection,
      columnCorrection, constantCorrection]
    push_cast
    ring
  rw [hexpand]
  change
    (∫ p in suzukiFiniteSquare a,
      (raw - rowCorrection - columnCorrection + constantCorrection) p) =
      ∫ p in suzukiFiniteSquare a, raw p
  simp only [Pi.add_apply, Pi.sub_apply]
  have hSubRow :
      (∫ p in suzukiFiniteSquare a, raw p - rowCorrection p) =
        (∫ p in suzukiFiniteSquare a, raw p) -
          ∫ p in suzukiFiniteSquare a, rowCorrection p := by
    simpa only [Pi.sub_apply] using integral_sub hraw hrow
  have hSubColumn :
      (∫ p in suzukiFiniteSquare a,
          raw p - rowCorrection p - columnCorrection p) =
        (∫ p in suzukiFiniteSquare a,
          raw p - rowCorrection p) -
            ∫ p in suzukiFiniteSquare a, columnCorrection p := by
    simpa only [Pi.sub_apply] using
      integral_sub (hraw.sub hrow) hcolumn
  have hAddConstant :
      (∫ p in suzukiFiniteSquare a,
          raw p - rowCorrection p - columnCorrection p +
            constantCorrection p) =
        (∫ p in suzukiFiniteSquare a,
          raw p - rowCorrection p - columnCorrection p) +
            ∫ p in suzukiFiniteSquare a, constantCorrection p := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add ((hraw.sub hrow).sub hcolumn) hconstant
  rw [hAddConstant, hSubColumn, hSubRow]
  rw [show (∫ p in suzukiFiniteSquare a, rowCorrection p) =
      (∫ x in Set.Icc (-a) a,
          (kernel x : Complex) * conj (u x)) *
        ∫ y in Set.Icc (-a) a, u y by
      simpa [suzukiFiniteSquare, rowCorrection,
        MeasureTheory.Measure.volume_eq_prod] using
        (MeasureTheory.setIntegral_prod_mul
          (fun x : Real => (kernel x : Complex) * conj (u x)) u
          (Set.Icc (-a) a) (Set.Icc (-a) a)),
    show (∫ p in suzukiFiniteSquare a, columnCorrection p) =
      (∫ x in Set.Icc (-a) a, conj (u x)) *
        ∫ y in Set.Icc (-a) a,
          (kernel (-y) : Complex) * u y by
      simpa [suzukiFiniteSquare, columnCorrection,
        MeasureTheory.Measure.volume_eq_prod] using
        (MeasureTheory.setIntegral_prod_mul
          (fun x : Real => conj (u x))
          (fun y : Real => (kernel (-y) : Complex) * u y)
          (Set.Icc (-a) a) (Set.Icc (-a) a)),
    show (∫ p in suzukiFiniteSquare a, constantCorrection p) =
      (∫ x in Set.Icc (-a) a, conj (u x)) *
        ∫ y in Set.Icc (-a) a,
          (kernel 0 : Complex) * u y by
      simpa [suzukiFiniteSquare, constantCorrection,
        MeasureTheory.Measure.volume_eq_prod] using
        (MeasureTheory.setIntegral_prod_mul
          (fun x : Real => conj (u x))
          (fun y : Real => (kernel 0 : Complex) * u y)
          (Set.Icc (-a) a) (Set.Icc (-a) a))]
  simp [hzero, hzeroConj]

/-- The centered and raw Suzuki pairings agree on `D v` for every compactly
supported smooth source. -/
theorem suzukiFiniteCenteredKernelPairingComplex_differential_eq_raw
    {kernel : Real → Real} {a : Real} {v : SchwartzLineTestFunction}
    (hkernel : Continuous kernel) (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFiniteCenteredKernelPairingComplex kernel a
        (suzukiDifferential v) =
      suzukiFiniteKernelPairingComplex kernel a
        (suzukiDifferential v) := by
  exact suzukiFiniteCenteredKernelPairingComplex_eq_raw_of_zeroMean
    hkernel (suzukiDifferential v).continuous
    (setIntegral_suzukiDifferential_eq_zero ha hsupport)

/-- The exact remaining X14 arithmetic normalization obligation.  It is a
plain proposition, not a positivity-bearing package and not an assumption
hidden inside a local criterion record. -/
def SuzukiScalarKernelIdentityAt
    (a : Real) (v : SchwartzLineTestFunction) : Prop :=
  guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v) =
    suzukiFiniteKernelPairing suzukiScrewFunction a
      (SchwartzMap.derivCLM Complex Complex v)

/-- Compatibility with the structural Weil-form interface needs only the
promised one-test functional agreement.  No global concrete distribution
instance is manufactured from Suzuki's compact-support theorem. -/
theorem quadraticForm_suzukiProjectBase_eq_residual_of_agreement
    (data : SchwartzWeilQuadraticFormData)
    (v : SchwartzLineTestFunction)
    (hagrees :
      data.formulaFunctional
          (autocorrelation (suzukiProjectBase v)) =
        guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v)) :
    data.quadraticForm (suzukiProjectBase v) =
      guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v) := by
  simpa [SchwartzWeilQuadraticFormData.quadraticForm,
    SchwartzWeilQuadraticFormData.formulaTest] using hagrees

/-- Once the concrete arithmetic identity is discharged, the structural
quadratic form inherits exactly the same scalar kernel representation under
the explicit one-test agreement hypothesis. -/
theorem quadraticForm_suzukiProjectBase_eq_kernelPairing
    (data : SchwartzWeilQuadraticFormData)
    (a : Real) (v : SchwartzLineTestFunction)
    (hagrees :
      data.formulaFunctional
          (autocorrelation (suzukiProjectBase v)) =
        guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v))
    (hidentity : SuzukiScalarKernelIdentityAt a v) :
    data.quadraticForm (suzukiProjectBase v) =
      suzukiFiniteKernelPairing suzukiScrewFunction a
        (SchwartzMap.derivCLM Complex Complex v) := by
  exact (quadraticForm_suzukiProjectBase_eq_residual_of_agreement
    data v hagrees).trans hidentity

end

end M100
end Experiments
end RiemannHypothesisProject
