import RiemannHypothesisProject.Experiments.M100.SuzukiCosineIntegralAsymptotic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# M100-DF6D2 reciprocal-kernel Fourier limit

This module passes the finite reciprocal-kernel multiplier to Suzuki's exact
logarithmic Fourier form.  The cutoff multiplier has a uniform logarithmic
majorant, so the scalar cosine-integral asymptotic can be integrated against
the squared Fourier transform of every Schwartz test.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- Real Fourier integrand associated with the renormalized finite cutoff. -/
def suzukiRenormalizedCutoffFourierIntegrand
    (ε R : Real) (v : SchwartzLineTestFunction) (ξ : Real) : Real :=
  suzukiRenormalizedCutoffMultiplier ε R ξ *
    ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2

/-- Integrable majorant for the whole eventual cutoff family. -/
def suzukiRenormalizedCutoffFourierMajorant
    (v : SchwartzLineTestFunction) (ξ : Real) : Real :=
  (8 + 4 *
      (abs (suzukiSourceLogFourierWeight ξ) +
        abs Real.eulerMascheroniConstant)) *
    ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2

theorem integrable_suzukiRenormalizedCutoffFourierMajorant
    (v : SchwartzLineTestFunction) :
    Integrable (suzukiRenormalizedCutoffFourierMajorant v) := by
  let f : SchwartzLineTestFunction :=
    SchwartzMap.fourierTransformCLM Complex v
  have hsq : Integrable (fun ξ : Real => ‖f ξ‖ ^ 2) :=
    (f.memLp (2 : ENNReal) (volume : Measure Real)).integrable_norm_pow
      (by norm_num)
  have hsource := integrable_suzukiSourceLogFourierFormIntegrand v
  have hsourceAbs :
      Integrable (fun ξ : Real =>
        abs (suzukiSourceLogFourierWeight ξ) * ‖f ξ‖ ^ 2) := by
    simpa [f, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using hsource.norm
  have hsum : Integrable (fun ξ : Real =>
      8 * ‖f ξ‖ ^ 2 +
        4 * (abs (suzukiSourceLogFourierWeight ξ) * ‖f ξ‖ ^ 2) +
        (4 * abs Real.eulerMascheroniConstant) * ‖f ξ‖ ^ 2) :=
    ((hsq.const_mul 8).add (hsourceAbs.const_mul 4)).add
      (hsq.const_mul (4 * abs Real.eulerMascheroniConstant))
  apply hsum.congr
  filter_upwards with ξ
  unfold suzukiRenormalizedCutoffFourierMajorant
  dsimp only [f]
  ring

/-- Each honest finite-cutoff Fourier integrand is continuous in frequency. -/
theorem continuous_suzukiRenormalizedCutoffFourierIntegrand
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (v : SchwartzLineTestFunction) :
    Continuous (suzukiRenormalizedCutoffFourierIntegrand ε R v) := by
  have hmultiplier :
      Continuous (fun ξ : Real =>
        suzukiRenormalizedCutoffMultiplier ε R ξ) := by
    unfold suzukiRenormalizedCutoffMultiplier
    exact continuous_const.sub
      (continuous_suzukiReciprocalCutoffCosineMultiplier hε hεR)
  unfold suzukiRenormalizedCutoffFourierIntegrand
  exact hmultiplier.mul (by fun_prop)

/-- In the cutoff geometry used for the joint limit, every renormalized
Fourier integrand is absolutely integrable. -/
theorem integrable_suzukiRenormalizedCutoffFourierIntegrand
    {ε R : Real} (hε : 0 < ε) (hεOne : ε ≤ 1) (hROne : 1 ≤ R)
    (v : SchwartzLineTestFunction) :
    Integrable (suzukiRenormalizedCutoffFourierIntegrand ε R v) := by
  apply (integrable_suzukiRenormalizedCutoffFourierMajorant v).mono'
    ((continuous_suzukiRenormalizedCutoffFourierIntegrand
      hε (hεOne.trans hROne) v).aestronglyMeasurable)
  filter_upwards [volume.ae_ne (0 : Real)] with ξ hξ
  have hscalar :=
    abs_suzukiRenormalizedCutoffMultiplier_le_sourceWeight
      hε hεOne hROne hξ
  unfold suzukiRenormalizedCutoffFourierIntegrand
    suzukiRenormalizedCutoffFourierMajorant
  simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
  exact mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)

/-- Dominated convergence upgrades Suzuki's scalar cutoff asymptotic to the
exact logarithmic Fourier quadratic form. -/
theorem tendsto_integral_suzukiRenormalizedCutoffFourierIntegrand
    (hasymptotic : SuzukiCosineIntegralAsymptotic)
    (v : SchwartzLineTestFunction) :
    Tendsto
      (fun p : Real × Real =>
        ∫ ξ : Real,
          suzukiRenormalizedCutoffFourierIntegrand p.1 p.2 v ξ)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (2 * suzukiSourceLogFourierForm v)) := by
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
        (suzukiRenormalizedCutoffFourierIntegrand p.1 p.2 v) volume := by
    filter_upwards [hεpos, hεOne, hROne] with p hp hεp hRp
    exact (continuous_suzukiRenormalizedCutoffFourierIntegrand
      hp (hεp.trans hRp) v).aestronglyMeasurable
  have hbound : ∀ᶠ p in l, ∀ᵐ ξ ∂volume,
      ‖suzukiRenormalizedCutoffFourierIntegrand p.1 p.2 v ξ‖ ≤
        suzukiRenormalizedCutoffFourierMajorant v ξ := by
    filter_upwards [hεpos, hεOne, hROne] with p hp hεp hRp
    filter_upwards [volume.ae_ne (0 : Real)] with ξ hξ
    have hscalar :=
      abs_suzukiRenormalizedCutoffMultiplier_le_sourceWeight
        hp hεp hRp hξ
    unfold suzukiRenormalizedCutoffFourierIntegrand
      suzukiRenormalizedCutoffFourierMajorant
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm]
    exact mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)
  have hlimit : ∀ᵐ ξ ∂volume,
      Tendsto
        (fun p : Real × Real =>
          suzukiRenormalizedCutoffFourierIntegrand p.1 p.2 v ξ)
        l
        (𝓝 (2 * suzukiSourceLogFourierWeight ξ *
          ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2)) := by
    filter_upwards [volume.ae_ne (0 : Real)] with ξ hξ
    unfold suzukiRenormalizedCutoffFourierIntegrand
    convert (hasymptotic ξ hξ).mul_const
      (‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2) using 1 <;>
      ring
  have hdct := tendsto_integral_filter_of_dominated_convergence
    (suzukiRenormalizedCutoffFourierMajorant v)
    hmeas hbound
    (integrable_suzukiRenormalizedCutoffFourierMajorant v)
    hlimit
  change Tendsto _ l _
  have htarget :
      (∫ ξ : Real, 2 * suzukiSourceLogFourierWeight ξ *
          ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2) =
        2 * suzukiSourceLogFourierForm v := by
    unfold suzukiSourceLogFourierForm
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    ring
  rw [htarget] at hdct
  exact hdct

end

end M100
end Experiments
end RiemannHypothesisProject
