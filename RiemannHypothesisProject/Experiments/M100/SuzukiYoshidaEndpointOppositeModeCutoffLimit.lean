import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointOppositeModeCorrelation
import RiemannHypothesisProject.Experiments.M100.SuzukiCosineIntegralConstant
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Renormalized cutoff limit for endpoint Fourier pairings

This module lifts the checked scalar cosine-integral asymptotic to the
polarized endpoint Fourier products.  The proof uses the unconditional
endpoint square-integrability and source-weight integrability estimates, so
it applies to every ordered integer-mode pair.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate Topology

/-- The renormalized finite-cutoff multiplier applied to an ordered endpoint
Fourier product. -/
def suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    (r : Real) (m n : Int) (ε R xi : Real) : Complex :=
  ((suzukiRenormalizedCutoffMultiplier ε R xi : Real) : Complex) *
    (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r m) xi *
      conj (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi))

/-- A common integrable majorant for the eventual endpoint cutoff family. -/
def suzukiYoshidaEndpointRenormalizedCutoffMajorant
    (r : Real) (m n : Int) (xi : Real) : Real :=
  (8 + 4 *
      (abs (suzukiSourceLogFourierWeight xi) +
        abs Real.eulerMascheroniConstant)) *
    (‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r m) xi‖ *
      ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi‖)

theorem integrable_suzukiYoshidaEndpointFourierNormProduct
    {r : Real} (hr : 0 < r) (m n : Int) :
    Integrable (fun xi : Real =>
      ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r m) xi‖ *
        ‖FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖) := by
  let fm : Real → Complex := fun xi =>
    FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r m) xi
  let fn : Real → Complex := fun xi =>
    FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r n) xi
  have hm : Integrable (fun xi : Real => ‖fm xi‖ ^ 2) := by
    simpa only [fm] using
      integrable_normSq_fourier_suzukiYoshidaExponentialFunction hr m
  have hn : Integrable (fun xi : Real => ‖fn xi‖ ^ 2) := by
    simpa only [fn] using
      integrable_normSq_fourier_suzukiYoshidaExponentialFunction hr n
  apply (hm.add hn).mono'
  · exact
      ((continuous_fourier_suzukiYoshidaExponentialFunction hr m).norm.mul
        (continuous_fourier_suzukiYoshidaExponentialFunction hr n).norm)
          |>.aestronglyMeasurable
  · filter_upwards with xi
    dsimp only [fm, fn]
    rw [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    nlinarith [sq_nonneg (‖fm xi‖ - ‖fn xi‖)]

theorem integrable_abs_suzukiSourceLogFourierWeight_mul_endpointFourierNormProduct
    {r : Real} (hr : 0 < r) (m n : Int) :
    Integrable (fun xi : Real =>
      abs (suzukiSourceLogFourierWeight xi) *
        (‖FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r m) xi‖ *
          ‖FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi‖)) := by
  have hsource :=
    (integrable_suzukiYoshidaEndpointSourceFourierIntegrand hr m n).norm
  apply hsource.congr
  filter_upwards with xi
  unfold suzukiYoshidaEndpointSourceFourierIntegrand
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_conj]

theorem integrable_suzukiYoshidaEndpointRenormalizedCutoffMajorant
    {r : Real} (hr : 0 < r) (m n : Int) :
    Integrable
      (suzukiYoshidaEndpointRenormalizedCutoffMajorant r m n) := by
  let p : Real → Real := fun xi =>
    ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r m) xi‖ *
      ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi‖
  have hp : Integrable p := by
    simpa only [p] using
      integrable_suzukiYoshidaEndpointFourierNormProduct hr m n
  have hw : Integrable (fun xi : Real =>
      abs (suzukiSourceLogFourierWeight xi) * p xi) := by
    simpa only [p] using
      integrable_abs_suzukiSourceLogFourierWeight_mul_endpointFourierNormProduct
        hr m n
  have hsum : Integrable (fun xi : Real =>
      8 * p xi +
        4 * (abs (suzukiSourceLogFourierWeight xi) * p xi) +
        (4 * abs Real.eulerMascheroniConstant) * p xi) :=
    ((hp.const_mul 8).add (hw.const_mul 4)).add
      (hp.const_mul (4 * abs Real.eulerMascheroniConstant))
  apply hsum.congr
  filter_upwards with xi
  unfold suzukiYoshidaEndpointRenormalizedCutoffMajorant
  dsimp only [p]
  ring

theorem continuous_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    {r ε R : Real} (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R)
    (m n : Int) :
    Continuous
      (suzukiYoshidaEndpointRenormalizedCutoffIntegrand r m n ε R) := by
  have hmultiplier : Continuous (fun xi : Real =>
      suzukiRenormalizedCutoffMultiplier ε R xi) := by
    unfold suzukiRenormalizedCutoffMultiplier
    exact continuous_const.sub
      (continuous_suzukiReciprocalCutoffCosineMultiplier hε hεR)
  unfold suzukiYoshidaEndpointRenormalizedCutoffIntegrand
  exact (Complex.continuous_ofReal.comp hmultiplier).mul
    ((continuous_fourier_suzukiYoshidaExponentialFunction hr m).mul
      (Complex.continuous_conj.comp
        (continuous_fourier_suzukiYoshidaExponentialFunction hr n)))

/-- Dominated convergence carries the proved scalar cosine-integral
asymptotic to every polarized endpoint source pairing. -/
theorem tendsto_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    {r : Real} (hr : 0 < r) (m n : Int) :
    Tendsto
      (fun p : Real × Real =>
        ∫ xi : Real,
          suzukiYoshidaEndpointRenormalizedCutoffIntegrand
            r m n p.1 p.2 xi)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (2 * suzukiYoshidaEndpointSourceFourierPairing r m n)) := by
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεOneScalar : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ 1 := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < 1 :=
      mem_inf_of_left (Iio_mem_nhds zero_lt_one)
    exact hlt.mono fun ε hε => hε.le
  have hεOne : ∀ᶠ p in l, p.1 ≤ 1 :=
    tendsto_fst.eventually hεOneScalar
  have hROne : ∀ᶠ p in l, 1 ≤ p.2 :=
    tendsto_snd.eventually (eventually_ge_atTop 1)
  have hmeas : ∀ᶠ p in l,
      AEStronglyMeasurable
        (suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r m n p.1 p.2) volume := by
    filter_upwards [hεpos, hεOne, hROne] with p hp hεp hRp
    exact (continuous_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      hr hp (hεp.trans hRp) m n).aestronglyMeasurable
  have hbound : ∀ᶠ p in l, ∀ᵐ xi ∂volume,
      ‖suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r m n p.1 p.2 xi‖ ≤
        suzukiYoshidaEndpointRenormalizedCutoffMajorant r m n xi := by
    filter_upwards [hεpos, hεOne, hROne] with p hp hεp hRp
    filter_upwards [volume.ae_ne (0 : Real)] with xi hxi
    have hscalar :=
      abs_suzukiRenormalizedCutoffMultiplier_le_sourceWeight
        hp hεp hRp hxi
    unfold suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      suzukiYoshidaEndpointRenormalizedCutoffMajorant
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right hscalar
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hlimit : ∀ᵐ xi ∂volume,
      Tendsto
        (fun p : Real × Real =>
          suzukiYoshidaEndpointRenormalizedCutoffIntegrand
            r m n p.1 p.2 xi)
        l
        (𝓝 (((2 * suzukiSourceLogFourierWeight xi : Real) : Complex) *
          (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r m) xi *
            conj (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi)))) := by
    filter_upwards [volume.ae_ne (0 : Real)] with xi hxi
    unfold suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    exact (((suzukiCosineIntegralAsymptotic_of_constantIdentity
      suzukiCosineIntegralConstantIdentity) xi hxi).ofReal.mul_const _)
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (suzukiYoshidaEndpointRenormalizedCutoffMajorant r m n)
    hmeas hbound
    (integrable_suzukiYoshidaEndpointRenormalizedCutoffMajorant hr m n)
    hlimit
  change Tendsto _ l _
  have htarget :
      (∫ xi : Real,
        (((2 * suzukiSourceLogFourierWeight xi : Real) : Complex) *
          (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r m) xi *
            conj (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi)))) =
        2 * suzukiYoshidaEndpointSourceFourierPairing r m n := by
    unfold suzukiYoshidaEndpointSourceFourierPairing
      suzukiYoshidaEndpointSourceFourierIntegrand
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with xi
    push_cast
    ring
  rw [htarget] at hdct
  exact hdct

end

end RiemannHypothesisProject.Experiments.M100
