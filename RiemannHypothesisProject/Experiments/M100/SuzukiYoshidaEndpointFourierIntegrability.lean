import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierTransforms
import RiemannHypothesisProject.Experiments.M100.SuzukiSingularShiftedCompletion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Weighted integrability of the endpoint Fourier transforms

This module continues QF2 after the exact endpoint transform and its sharp
high-frequency decay have been checked.  It separates the integrable
low-frequency logarithm from the compact regular part before assembling the
power-decaying tails.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal FourierTransform

/-- The ordinary Fourier transform of an endpoint exponential is continuous.
This uses only its independently checked `L¹` membership. -/
theorem continuous_fourier_suzukiYoshidaExponentialFunction
    {r : Real} (hr : 0 < r) (n : Int) :
    Continuous (FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r n)) := by
  have hmem := suzukiYoshidaExponentialFunction_memLp_one hr n
  have heq := Real.fourierTransform_toLp hmem
  rw [← heq]
  exact (Real.Lp.fourierTransform hmem.toLp).continuous

/-- The squared norm of the explicit endpoint transform is continuous. -/
theorem continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
    {r : Real} (hr : 0 < r) (n : Int) :
    Continuous (fun xi : Real =>
      ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) :=
  (continuous_fourier_suzukiYoshidaExponentialFunction hr n).norm.pow 2

/-- The source multiplier's low-frequency logarithmic loss remains
integrable after multiplication by the endpoint Fourier square. -/
theorem integrable_suzukiLowFrequencyLogLoss_mul_endpointFourierSq
    {r : Real} (hr : 0 < r) (n : Int) :
    Integrable (fun xi : Real =>
      suzukiLowFrequencyLogLoss xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) := by
  have hloss : IntegrableOn suzukiLowFrequencyLogLoss
      (Icc (-1 : Real) 1) :=
    integrable_suzukiLowFrequencyLogLoss.integrableOn
  have hproduct : IntegrableOn (fun xi : Real =>
      suzukiLowFrequencyLogLoss xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2)
      (Icc (-1 : Real) 1) :=
    hloss.mul_continuousOn
      (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
        hr n).continuousOn isCompact_Icc
  have hindicator := hproduct.integrable_indicator measurableSet_Icc
  apply hindicator.congr
  filter_upwards with xi
  by_cases hxi : xi ∈ Icc (-1 : Real) 1
  · simp [hxi]
  · rw [Set.indicator_of_notMem hxi]
    unfold suzukiLowFrequencyLogLoss
    rw [Set.indicator_of_notMem hxi, zero_mul]

/-- A sublinear power bound for the positive logarithm.  The factor `2` is
deliberately coarse; it turns the checked Fourier `1/|xi|` tail into an
integrable `|xi|^(-3/2)` majorant. -/
theorem posLog_abs_le_two_mul_sqrt_abs
    {xi : Real} (hxi : 1 ≤ |xi|) :
    Real.posLog |xi| ≤ 2 * Real.sqrt |xi| := by
  have hlog := Real.log_le_self (Real.sqrt_nonneg |xi|)
  rw [Real.log_sqrt (abs_nonneg xi)] at hlog
  rw [Real.posLog_eq_log]
  · linarith
  · simpa only [abs_abs] using hxi

/-- The power majorant produced by the logarithmic and Fourier tail bounds is
integrable on every positive tail. -/
theorem integrableOn_sqrt_div_sq_Ioi
    {R : Real} (hR : 0 < R) :
    IntegrableOn (fun x : Real => Real.sqrt x / x ^ 2) (Ioi R) := by
  have hpower : IntegrableOn (fun x : Real => x ^ (-3 / 2 : Real))
      (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  apply hpower.congr_fun
  · intro x hx
    have hxpos : 0 < x := hR.trans hx
    change x ^ (-3 / 2 : Real) = Real.sqrt x / x ^ 2
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
    rw [← Real.rpow_sub hxpos]
    norm_num
  · exact measurableSet_Ioi

/-- The graph-weighted endpoint Fourier square is integrable on its positive
high-frequency tail. -/
theorem integrableOn_suzukiLogFourierWeight_mul_endpointFourierSq_Ioi
    {r : Real} (hr : 0 < r) (n : Int) :
    IntegrableOn (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2)
      (Ioi (max 1 (|(n : Real)| / r))) := by
  let R : Real := max 1 (|(n : Real)| / r)
  let A : Real := 2 / (Real.sqrt (2 * r) * Real.pi)
  let C : Real := 3 * A ^ 2
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hmajor : IntegrableOn (fun xi : Real =>
      C * (Real.sqrt xi / xi ^ 2)) (Ioi R) :=
    (integrableOn_sqrt_div_sq_Ioi hR).const_mul C
  apply hmajor.mono'
  · exact
      ((continuous_suzukiLogFourierWeight.mul
        (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
          hr n))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with xi hxi
    have hxiR : R ≤ |xi| := by
      rw [abs_of_pos (hR.trans hxi)]
      exact hxi.le
    have hxiOne : 1 ≤ xi :=
      (le_max_left _ _).trans (show R ≤ xi from hxi.le)
    have hsqrtOne : 1 ≤ Real.sqrt xi :=
      Real.one_le_sqrt.mpr hxiOne
    have hweight : suzukiLogFourierWeight xi ≤
        3 * Real.sqrt xi := by
      unfold suzukiLogFourierWeight
      rw [Real.posLog_abs]
      have hlog : Real.posLog xi ≤ 2 * Real.sqrt xi := by
        simpa only [abs_of_nonneg (zero_le_one.trans hxiOne)] using
          (posLog_abs_le_two_mul_sqrt_abs
            (show 1 ≤ |xi| by
              simpa [abs_of_nonneg (zero_le_one.trans hxiOne)] using hxiOne))
      linarith
    have hfourier :=
      norm_fourier_suzukiYoshidaExponentialFunction_le_highFrequency
        hr n xi hxiR
    rw [abs_of_pos (hR.trans hxi)] at hfourier
    have hfourierA :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ≤ A / xi := by
      dsimp only [A]
      convert hfourier using 1 <;> ring
    have hfourierSq :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2 ≤
          (A / xi) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hfourierA
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (suzukiLogFourierWeight_nonneg xi) (sq_nonneg _))]
    calc
      suzukiLogFourierWeight xi *
          ‖FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2 ≤
          (3 * Real.sqrt xi) *
            ‖FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ ≤ (3 * Real.sqrt xi) * (A / xi) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourierSq (by positivity)
      _ = C * (Real.sqrt xi / xi ^ 2) := by
        dsimp only [C]
        ring

/-- The graph-weighted endpoint Fourier square is integrable on its negative
high-frequency tail. -/
theorem integrableOn_suzukiLogFourierWeight_mul_endpointFourierSq_Iio
    {r : Real} (hr : 0 < r) (n : Int) :
    IntegrableOn (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2)
      (Iio (-(max 1 (|(n : Real)| / r)))) := by
  let R : Real := max 1 (|(n : Real)| / r)
  let A : Real := 2 / (Real.sqrt (2 * r) * Real.pi)
  let C : Real := 3 * A ^ 2
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hmajor : IntegrableOn (fun xi : Real =>
      C * (Real.sqrt (-xi) / (-xi) ^ 2)) (Iio (-R)) := by
    let f : Real → Real := fun x => Real.sqrt x / x ^ 2
    have hpositive : IntegrableOn f (Ioi (-(-R))) := by
      simpa only [f, neg_neg] using integrableOn_sqrt_div_sq_Ioi hR
    have hreflected : IntegrableOn (fun xi : Real => f (-xi))
        (Iio (-R)) :=
      MeasureTheory.IntegrableOn.comp_neg_Iio
        (G := Real) (F := Real) (μ := volume) (c := -R) hpositive
    dsimp only [f] at hreflected
    exact hreflected.const_mul C
  apply hmajor.mono'
  · exact
      ((continuous_suzukiLogFourierWeight.mul
        (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
          hr n))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Iio] with xi hxi
    have hxi' : xi < -R := hxi
    have hxineg : xi < 0 := hxi'.trans (neg_lt_zero.mpr hR)
    have hxiR : R ≤ |xi| := by
      rw [abs_of_neg hxineg]
      exact (lt_neg.mp hxi').le
    have hxiOne : 1 ≤ -xi := by
      have : R < -xi := lt_neg.mp hxi'
      exact (le_max_left _ _).trans this.le
    have hsqrtOne : 1 ≤ Real.sqrt (-xi) :=
      Real.one_le_sqrt.mpr hxiOne
    have hweight : suzukiLogFourierWeight xi ≤
        3 * Real.sqrt (-xi) := by
      unfold suzukiLogFourierWeight
      have hlog := posLog_abs_le_two_mul_sqrt_abs
        (show 1 ≤ |xi| by simpa [abs_of_neg hxineg] using hxiOne)
      rw [abs_of_neg hxineg] at hlog ⊢
      linarith
    have hfourier :=
      norm_fourier_suzukiYoshidaExponentialFunction_le_highFrequency
        hr n xi hxiR
    rw [abs_of_neg hxineg] at hfourier
    have hfourierA :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ≤ A / (-xi) := by
      dsimp only [A]
      convert hfourier using 1 <;> ring
    have hfourierSq :
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2 ≤
          (A / (-xi)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hfourierA
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (suzukiLogFourierWeight_nonneg xi) (sq_nonneg _))]
    calc
      suzukiLogFourierWeight xi *
          ‖FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2 ≤
          (3 * Real.sqrt (-xi)) *
            ‖FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ ≤ (3 * Real.sqrt (-xi)) * (A / (-xi)) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourierSq (by positivity)
      _ = C * (Real.sqrt (-xi) / (-xi) ^ 2) := by
        dsimp only [C]
        ring

/-- On any compact interval, the graph-weighted endpoint Fourier square is
integrable. -/
theorem integrableOn_suzukiLogFourierWeight_mul_endpointFourierSq_Icc
    {r : Real} (hr : 0 < r) (n : Int) (R : Real) :
    IntegrableOn (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2)
      (Icc (-R) R) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact
    ((continuous_suzukiLogFourierWeight.mul
      (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
        hr n))).continuousOn

/-- The graph-weighted endpoint Fourier square is globally integrable.  This
is the two-tail assembly needed before passing from the graph multiplier to
the exact source multiplier. -/
theorem integrable_suzukiLogFourierWeight_mul_endpointFourierSq
    {r : Real} (hr : 0 < r) (n : Int) :
    Integrable (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) := by
  let R : Real := max 1 (|(n : Real)| / r)
  have hnegative : IntegrableOn (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) (Iio (-R)) :=
    integrableOn_suzukiLogFourierWeight_mul_endpointFourierSq_Iio hr n
  have hcompact : IntegrableOn (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) (Icc (-R) R) :=
    integrableOn_suzukiLogFourierWeight_mul_endpointFourierSq_Icc hr n R
  have hpositive : IntegrableOn (fun xi : Real =>
      suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) (Ioi R) :=
    integrableOn_suzukiLogFourierWeight_mul_endpointFourierSq_Ioi hr n
  have hall := (hnegative.union hcompact).union hpositive
  have hcover : (Iio (-R) ∪ Icc (-R) R) ∪ Ioi R = univ := by
    ext xi
    simp only [mem_union, mem_Iio, mem_Icc, mem_Ioi, mem_univ, iff_true]
    rcases lt_or_ge xi (-R) with hleft | hmiddle
    · exact Or.inl (Or.inl hleft)
    rcases le_or_gt xi R with hright | hright
    · exact Or.inl (Or.inr ⟨hmiddle, hright⟩)
    · exact Or.inr hright
  rw [hcover] at hall
  simpa only [integrableOn_univ] using hall

/-- The unweighted endpoint Fourier square is integrable as a direct
consequence of the graph weight's pointwise lower bound by one. -/
theorem integrable_normSq_fourier_suzukiYoshidaExponentialFunction
    {r : Real} (hr : 0 < r) (n : Int) :
    Integrable (fun xi : Real =>
      ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) := by
  have hgraph :=
    integrable_suzukiLogFourierWeight_mul_endpointFourierSq hr n
  apply hgraph.mono'
  · exact
      (continuous_norm_sq_fourier_suzukiYoshidaExponentialFunction
        hr n).aestronglyMeasurable
  · filter_upwards with xi
    have hweightOne : 1 ≤ suzukiLogFourierWeight xi := by
      unfold suzukiLogFourierWeight
      exact le_add_of_nonneg_right Real.posLog_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hweightOne (sq_nonneg
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖)

/-- The exact project-normalized source multiplier is absolutely integrable
against every endpoint Fourier square.  The equality with the graph
multiplier is used only away from the null singleton. -/
theorem integrable_suzukiSourceLogFourierWeight_mul_endpointFourierSq
    {r : Real} (hr : 0 < r) (n : Int) :
    Integrable (fun xi : Real =>
      suzukiSourceLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2) := by
  let fourierSq : Real → Real := fun xi =>
    ‖FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r n) xi‖ ^ 2
  have hgraph : Integrable (fun xi : Real =>
      suzukiLogFourierWeight xi * fourierSq xi) := by
    simpa only [fourierSq] using
      integrable_suzukiLogFourierWeight_mul_endpointFourierSq hr n
  have hfourier : Integrable fourierSq := by
    simpa only [fourierSq] using
      integrable_normSq_fourier_suzukiYoshidaExponentialFunction hr n
  have hloss : Integrable (fun xi : Real =>
      suzukiLowFrequencyLogLoss xi * fourierSq xi) := by
    simpa only [fourierSq] using
      integrable_suzukiLowFrequencyLogLoss_mul_endpointFourierSq hr n
  have hdecomposition : Integrable (fun xi : Real =>
      suzukiLogFourierWeight xi * fourierSq xi +
        (suzukiSourceLogNormalizationConstant - 1) * fourierSq xi -
        suzukiLowFrequencyLogLoss xi * fourierSq xi) :=
    (hgraph.add
      (hfourier.const_mul
        (suzukiSourceLogNormalizationConstant - 1))).sub hloss
  apply hdecomposition.congr
  filter_upwards [volume.ae_ne (0 : Real)] with xi hxi
  rw [suzukiSourceLogFourierWeight_eq_graph_sub_loss hxi]
  dsimp only [fourierSq]
  ring

end

end RiemannHypothesisProject.Experiments.M100
