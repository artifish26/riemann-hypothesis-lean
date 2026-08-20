import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierIntegrability
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierL1L2Bridge

/-!
# One-extra-log Fourier domain for endpoint modes

The B3R-E residual functional pairs a fixed endpoint-mode combination against
the logarithmic graph coordinate of a variable vector.  Ambient `L²`
continuity therefore requires one additional logarithmic multiplier on the
fixed vector.  This module proves that requirement directly from the exact
endpoint Fourier transform and its `1 / |ξ|` decay.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal FourierTransform

/-- A quarter-power bound for the positive logarithm.  After squaring the
graph weight, this leaves the same integrable `|ξ|⁻³ᐟ²` tail used by QF2. -/
theorem posLog_abs_le_four_mul_rpow_quarter_abs
    {ξ : Real} (hξ : 1 ≤ |ξ|) :
    Real.posLog |ξ| ≤ 4 * |ξ| ^ (1 / 4 : Real) := by
  rw [Real.posLog_eq_log (by simpa only [abs_abs] using hξ)]
  have hlog := Real.log_le_rpow_div (abs_nonneg ξ)
    (show 0 < (1 / 4 : Real) by norm_num)
  norm_num [div_eq_mul_inv] at hlog ⊢
  simpa [mul_comm] using hlog

/-- On a positive high-frequency tail, the square of the graph weight times
the endpoint Fourier square is integrable. -/
theorem integrableOn_suzukiLogFourierWeight_sq_mul_endpointFourierSq_Ioi
    {r : Real} (hr : 0 < r) (n : Int) :
    IntegrableOn (fun ξ : Real =>
      suzukiLogFourierWeight ξ ^ 2 *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2)
      (Ioi (max 1 (|(n : Real)| / r))) := by
  let R : Real := max 1 (|(n : Real)| / r)
  let A : Real := 2 / (Real.sqrt (2 * r) * Real.pi)
  let C : Real := 25 * A ^ 2
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hmajor : IntegrableOn (fun ξ : Real =>
      C * (Real.sqrt ξ / ξ ^ 2)) (Ioi R) :=
    (integrableOn_sqrt_div_sq_Ioi hR).const_mul C
  apply hmajor.mono'
  · exact
      ((continuous_suzukiLogFourierWeight.pow 2).mul
        (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
          hr n)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ξ hξ
    have hξR : R ≤ |ξ| := by
      rw [abs_of_pos (hR.trans hξ)]
      exact hξ.le
    have hξOne : 1 ≤ ξ :=
      (le_max_left _ _).trans (show R ≤ ξ from hξ.le)
    have hquarterOne : 1 ≤ ξ ^ (1 / 4 : Real) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1) hξOne
          (by norm_num : (0 : Real) ≤ 1 / 4)
    have hweight : suzukiLogFourierWeight ξ ≤
        5 * ξ ^ (1 / 4 : Real) := by
      unfold suzukiLogFourierWeight
      have hlog := posLog_abs_le_four_mul_rpow_quarter_abs
        (show 1 ≤ |ξ| by
          simpa [abs_of_nonneg (zero_le_one.trans hξOne)] using hξOne)
      rw [abs_of_nonneg (zero_le_one.trans hξOne)] at hlog
      rw [abs_of_nonneg (zero_le_one.trans hξOne)]
      linarith
    have hweightSq : suzukiLogFourierWeight ξ ^ 2 ≤
        25 * Real.sqrt ξ := by
      have hsq := (sq_le_sq₀ (suzukiLogFourierWeight_nonneg ξ)
        (by positivity)).2 hweight
      calc
        suzukiLogFourierWeight ξ ^ 2 ≤
            (5 * ξ ^ (1 / 4 : Real)) ^ 2 := hsq
        _ = 25 * Real.sqrt ξ := by
          rw [mul_pow, show (5 : Real) ^ 2 = 25 by norm_num,
            Real.sqrt_eq_rpow, ← Real.rpow_natCast]
          rw [← Real.rpow_mul (zero_le_one.trans hξOne)]
          norm_num
    have hfourier :=
      norm_fourier_suzukiYoshidaExponentialFunction_le_highFrequency
        hr n ξ hξR
    rw [abs_of_pos (hR.trans hξ)] at hfourier
    have hfourierA :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ≤ A / ξ := by
      dsimp only [A]
      convert hfourier using 1 <;> ring
    have hfourierSq :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2 ≤
          (A / ξ) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hfourierA
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc
      suzukiLogFourierWeight ξ ^ 2 *
          ‖FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2 ≤
          (25 * Real.sqrt ξ) *
            ‖FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hweightSq (sq_nonneg _)
      _ ≤ (25 * Real.sqrt ξ) * (A / ξ) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourierSq (by positivity)
      _ = C * (Real.sqrt ξ / ξ ^ 2) := by
        dsimp only [C]
        ring

/-- Negative-tail counterpart of the squared graph-weight estimate. -/
theorem integrableOn_suzukiLogFourierWeight_sq_mul_endpointFourierSq_Iio
    {r : Real} (hr : 0 < r) (n : Int) :
    IntegrableOn (fun ξ : Real =>
      suzukiLogFourierWeight ξ ^ 2 *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2)
      (Iio (-(max 1 (|(n : Real)| / r)))) := by
  let R : Real := max 1 (|(n : Real)| / r)
  let A : Real := 2 / (Real.sqrt (2 * r) * Real.pi)
  let C : Real := 25 * A ^ 2
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hmajor : IntegrableOn (fun ξ : Real =>
      C * (Real.sqrt (-ξ) / (-ξ) ^ 2)) (Iio (-R)) := by
    let f : Real → Real := fun x => Real.sqrt x / x ^ 2
    have hpositive : IntegrableOn f (Ioi (-(-R))) := by
      simpa only [f, neg_neg] using integrableOn_sqrt_div_sq_Ioi hR
    have hreflected : IntegrableOn (fun ξ : Real => f (-ξ))
        (Iio (-R)) :=
      MeasureTheory.IntegrableOn.comp_neg_Iio
        (G := Real) (F := Real) (μ := volume) (c := -R) hpositive
    dsimp only [f] at hreflected
    exact hreflected.const_mul C
  apply hmajor.mono'
  · exact
      ((continuous_suzukiLogFourierWeight.pow 2).mul
        (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
          hr n)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with ξ hξ
    have hξneg : ξ < 0 := hξ.trans (neg_lt_zero.mpr hR)
    have hξR : R ≤ |ξ| := by
      rw [abs_of_neg hξneg]
      exact (lt_neg.mp hξ).le
    have hξOne : 1 ≤ -ξ := by
      exact (le_max_left _ _).trans (lt_neg.mp hξ).le
    have hquarterOne : 1 ≤ (-ξ) ^ (1 / 4 : Real) := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 1) hξOne
          (by norm_num : (0 : Real) ≤ 1 / 4)
    have hweight : suzukiLogFourierWeight ξ ≤
        5 * (-ξ) ^ (1 / 4 : Real) := by
      unfold suzukiLogFourierWeight
      have hlog := posLog_abs_le_four_mul_rpow_quarter_abs
        (show 1 ≤ |ξ| by simpa [abs_of_neg hξneg] using hξOne)
      rw [abs_of_neg hξneg] at hlog
      rw [abs_of_neg hξneg]
      linarith
    have hweightSq : suzukiLogFourierWeight ξ ^ 2 ≤
        25 * Real.sqrt (-ξ) := by
      have hsq := (sq_le_sq₀ (suzukiLogFourierWeight_nonneg ξ)
        (by positivity)).2 hweight
      calc
        suzukiLogFourierWeight ξ ^ 2 ≤
            (5 * (-ξ) ^ (1 / 4 : Real)) ^ 2 := hsq
        _ = 25 * Real.sqrt (-ξ) := by
          rw [mul_pow, show (5 : Real) ^ 2 = 25 by norm_num,
            Real.sqrt_eq_rpow, ← Real.rpow_natCast]
          rw [← Real.rpow_mul (zero_le_one.trans hξOne)]
          norm_num
    have hfourier :=
      norm_fourier_suzukiYoshidaExponentialFunction_le_highFrequency
        hr n ξ hξR
    rw [abs_of_neg hξneg] at hfourier
    have hfourierA :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ≤ A / (-ξ) := by
      dsimp only [A]
      convert hfourier using 1 <;> ring
    have hfourierSq :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2 ≤
          (A / (-ξ)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hfourierA
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    calc
      suzukiLogFourierWeight ξ ^ 2 *
          ‖FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2 ≤
          (25 * Real.sqrt (-ξ)) *
            ‖FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hweightSq (sq_nonneg _)
      _ ≤ (25 * Real.sqrt (-ξ)) * (A / (-ξ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourierSq (by positivity)
      _ = C * (Real.sqrt (-ξ) / (-ξ) ^ 2) := by
        dsimp only [C]
        ring

/-- On compact frequency windows the squared-weight integrand is continuous,
hence integrable. -/
theorem integrableOn_suzukiLogFourierWeight_sq_mul_endpointFourierSq_Icc
    {r : Real} (hr : 0 < r) (n : Int) (R : Real) :
    IntegrableOn (fun ξ : Real =>
      suzukiLogFourierWeight ξ ^ 2 *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2)
      (Icc (-R) R) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact
    ((continuous_suzukiLogFourierWeight.pow 2).mul
      (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
        hr n)).continuousOn

/-- Every endpoint exponential has an integrable Fourier square after two
factors of the logarithmic graph weight. -/
theorem integrable_suzukiLogFourierWeight_sq_mul_endpointFourierSq
    {r : Real} (hr : 0 < r) (n : Int) :
    Integrable (fun ξ : Real =>
      suzukiLogFourierWeight ξ ^ 2 *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ‖ ^ 2) := by
  let R : Real := max 1 (|(n : Real)| / r)
  have hnegative :=
    integrableOn_suzukiLogFourierWeight_sq_mul_endpointFourierSq_Iio hr n
  have hcompact :=
    integrableOn_suzukiLogFourierWeight_sq_mul_endpointFourierSq_Icc hr n R
  have hpositive :=
    integrableOn_suzukiLogFourierWeight_sq_mul_endpointFourierSq_Ioi hr n
  have hall := (hnegative.union hcompact).union hpositive
  have hcover : (Iio (-R) ∪ Icc (-R) R) ∪ Ioi R = univ := by
    ext ξ
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    rcases lt_or_ge ξ (-R) with hleft | hmiddle
    · exact Or.inl (Or.inl hleft)
    rcases le_or_gt ξ R with hright | hright
    · exact Or.inl (Or.inr ⟨hmiddle, hright⟩)
    · exact Or.inr hright
  rw [hcover] at hall
  simpa only [integrableOn_univ] using hall

/-- The one-extra-log Fourier representative of an ambient `L²` class. -/
def suzukiExtraLogWeightedFourier (v : SuzukiL2) : Real → Complex :=
  fun ξ =>
    (suzukiLogFourierWeight ξ : Complex) *
      ((FourierTransform.fourier v : SuzukiL2) ξ)

/-- The fixed-vector domain required to pair the graph multiplier against an
arbitrary ambient `L²` vector. -/
def SuzukiExtraLogFourierDomain : Set SuzukiL2 :=
  {v | MemLp (suzukiExtraLogWeightedFourier v) (2 : ENNReal)
    (volume : Measure Real)}

theorem suzukiExtraLogWeightedFourier_zero_ae :
    suzukiExtraLogWeightedFourier (0 : SuzukiL2) =ᵐ[volume]
      (0 : Real → Complex) := by
  have hcoe : ((0 : SuzukiL2) : Real → Complex) =ᵐ[volume] 0 :=
    Lp.coeFn_zero Complex (2 : ENNReal) (volume : Measure Real)
  filter_upwards [hcoe] with ξ hξ
  unfold suzukiExtraLogWeightedFourier
  rw [FourierTransform.fourier_zero, hξ]
  simp

theorem suzukiExtraLogWeightedFourier_add_ae (u v : SuzukiL2) :
    suzukiExtraLogWeightedFourier (u + v) =ᵐ[volume]
      (suzukiExtraLogWeightedFourier u + suzukiExtraLogWeightedFourier v) := by
  have hcoe := Lp.coeFn_add
    (FourierTransform.fourier u : SuzukiL2)
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with ξ hξ
  unfold suzukiExtraLogWeightedFourier
  rw [FourierTransform.fourier_add, hξ]
  simp only [Pi.add_apply, mul_add]

theorem suzukiExtraLogWeightedFourier_smul_ae
    (c : Complex) (v : SuzukiL2) :
    suzukiExtraLogWeightedFourier (c • v) =ᵐ[volume]
      (c • suzukiExtraLogWeightedFourier v) := by
  have hcoe := Lp.coeFn_smul c
    (FourierTransform.fourier v : SuzukiL2)
  filter_upwards [hcoe] with ξ hξ
  unfold suzukiExtraLogWeightedFourier
  rw [FourierTransform.fourier_smul]
  change (suzukiLogFourierWeight ξ : Complex) *
      ((c • (FourierTransform.fourier v : SuzukiL2)) ξ) =
    c * ((suzukiLogFourierWeight ξ : Complex) *
      ((FourierTransform.fourier v : SuzukiL2) ξ))
  rw [hξ]
  change (suzukiLogFourierWeight ξ : Complex) *
      (c * ((FourierTransform.fourier v : SuzukiL2) ξ)) = _
  ring

theorem suzukiExtraLogFourierDomain_zero :
    SuzukiExtraLogFourierDomain (0 : SuzukiL2) :=
  MemLp.zero.ae_eq suzukiExtraLogWeightedFourier_zero_ae.symm

theorem suzukiExtraLogFourierDomain_add {u v : SuzukiL2}
    (hu : SuzukiExtraLogFourierDomain u)
    (hv : SuzukiExtraLogFourierDomain v) :
    SuzukiExtraLogFourierDomain (u + v) :=
  (hu.add hv).ae_eq (suzukiExtraLogWeightedFourier_add_ae u v).symm

theorem suzukiExtraLogFourierDomain_smul (c : Complex) {v : SuzukiL2}
    (hv : SuzukiExtraLogFourierDomain v) :
    SuzukiExtraLogFourierDomain (c • v) :=
  (hv.const_smul c).ae_eq
    (suzukiExtraLogWeightedFourier_smul_ae c v).symm

/-- The one-extra-log domain is a complex linear subspace. -/
def SuzukiExtraLogFourierSubmodule : Submodule Complex SuzukiL2 where
  carrier := SuzukiExtraLogFourierDomain
  zero_mem' := suzukiExtraLogFourierDomain_zero
  add_mem' := suzukiExtraLogFourierDomain_add
  smul_mem' := suzukiExtraLogFourierDomain_smul

/-- Each endpoint exponential lies in the one-extra-log domain. -/
theorem suzukiYoshidaExponentialL2_mem_extraLogFourierDomain
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    SuzukiExtraLogFourierDomain
      (suzukiYoshidaExponentialL2 r hr n) := by
  let ordinary : Real → Complex := fun ξ =>
    (suzukiLogFourierWeight ξ : Complex) *
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) ξ
  have hmeas : AEStronglyMeasurable ordinary volume := by
    exact
      ((Complex.continuous_ofReal.comp
          continuous_suzukiLogFourierWeight).mul
        (continuous_fourier_suzukiYoshidaExponentialFunction hr n)).aestronglyMeasurable
  have hint : Integrable (fun ξ : Real => ‖ordinary ξ‖ ^ 2) := by
    have h :=
      integrable_suzukiLogFourierWeight_sq_mul_endpointFourierSq hr n
    apply h.congr
    filter_upwards with ξ
    dsimp only [ordinary]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (suzukiLogFourierWeight_nonneg ξ), mul_pow]
  have hordinary : MemLp ordinary (2 : ENNReal) volume := by
    apply (integrable_norm_rpow_iff hmeas (by norm_num) (by simp)).mp
    simpa using hint
  apply hordinary.ae_eq
  filter_upwards [fourier_suzukiYoshidaExponentialL2_coe_ae
    hsource hr n] with ξ hξ
  unfold suzukiExtraLogWeightedFourier
  dsimp only [ordinary]
  rw [hξ]

/-- Every normalized even endpoint mode has one extra logarithm. -/
theorem suzukiYoshidaEvenL2_mem_extraLogFourierDomain
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    SuzukiExtraLogFourierDomain (suzukiYoshidaEvenL2 r hr n) := by
  unfold suzukiYoshidaEvenL2
  split_ifs with hn
  · exact suzukiYoshidaExponentialL2_mem_extraLogFourierDomain
      hsource hr 0
  · apply suzukiExtraLogFourierDomain_smul
    exact suzukiExtraLogFourierDomain_add
      (suzukiYoshidaExponentialL2_mem_extraLogFourierDomain
        hsource hr (n : Int))
      (suzukiYoshidaExponentialL2_mem_extraLogFourierDomain
        hsource hr (-(n : Int)))

/-- Every normalized odd endpoint mode has one extra logarithm. -/
theorem suzukiYoshidaOddL2_mem_extraLogFourierDomain
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Nat) :
    SuzukiExtraLogFourierDomain (suzukiYoshidaOddL2 r hr n) := by
  unfold suzukiYoshidaOddL2
  rw [sub_eq_add_neg]
  apply suzukiExtraLogFourierDomain_smul
  exact suzukiExtraLogFourierDomain_add
    (suzukiYoshidaExponentialL2_mem_extraLogFourierDomain
      hsource hr (n : Int))
    (by
      simpa using
        (suzukiExtraLogFourierDomain_smul (-1)
          (suzukiYoshidaExponentialL2_mem_extraLogFourierDomain
            hsource hr (-(n : Int)))))

end

end RiemannHypothesisProject.Experiments.M100
