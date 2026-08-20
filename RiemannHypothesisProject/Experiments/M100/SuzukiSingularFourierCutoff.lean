import RiemannHypothesisProject.Experiments.M100.SuzukiSingularLocalForm
import RiemannHypothesisProject.WeilPositivity.SchwartzFourierAutocorrelation
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# M100-DF6D2 reciprocal-kernel cutoff

This module exposes the cutoff used in Suzuki's proof of the equivalence
between equations (2.3) and (2.6).  We use a finite outer cutoff `R` as well
as the source's inner cutoff `ε`.  The finite kernel is genuinely `L¹`, so
all Fourier and Fubini operations below can be carried out with ordinary
Bochner integrals.  The outer cutoff is removed only after the finite
Plancherel identity has been established.

The remaining scalar source input is stated separately as the convergence of
the renormalized cosine multiplier.  It is the precise cosine-integral
asymptotic cited by Suzuki, not an assumption about the quadratic form.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter FourierTransform
open scoped Interval Topology

/-- The symmetric annulus on which the finite reciprocal kernel is active. -/
def suzukiReciprocalCutoffSet (ε R : Real) : Set Real :=
  Icc (-R) (-ε) ∪ Icc ε R

/-- The finite complex-valued reciprocal kernel.  Endpoint choices are
irrelevant to all integrals but closed intervals make compactness explicit. -/
def suzukiReciprocalCutoffKernel (ε R : Real) (t : Real) : Complex :=
  (suzukiReciprocalCutoffSet ε R).indicator
    (fun s : Real => ((|s|⁻¹ : Real) : Complex)) t

theorem measurableSet_suzukiReciprocalCutoffSet (ε R : Real) :
    MeasurableSet (suzukiReciprocalCutoffSet ε R) := by
  exact measurableSet_Icc.union measurableSet_Icc

theorem isCompact_suzukiReciprocalCutoffSet (ε R : Real) :
    IsCompact (suzukiReciprocalCutoffSet ε R) := by
  exact isCompact_Icc.union isCompact_Icc

/-- Membership in the cutoff set forces distance at least `ε` from the
origin. -/
theorem le_abs_of_mem_suzukiReciprocalCutoffSet
    {ε R t : Real} (ht : t ∈ suzukiReciprocalCutoffSet ε R) :
    ε ≤ |t| := by
  rcases ht with ht | ht
  · have : t ≤ -ε := ht.2
    exact le_trans (by linarith) (neg_le_abs t)
  · exact ht.1.trans (le_abs_self t)

/-- The finite reciprocal kernel is integrable whenever the inner cutoff is
strictly positive. -/
theorem integrable_suzukiReciprocalCutoffKernel
    {ε R : Real} (hε : 0 < ε) :
    Integrable (suzukiReciprocalCutoffKernel ε R) := by
  change Integrable
    ((suzukiReciprocalCutoffSet ε R).indicator
      (fun s : Real => ((|s|⁻¹ : Real) : Complex)))
  rw [integrable_indicator_iff
    (measurableSet_suzukiReciprocalCutoffSet ε R)]
  apply Measure.integrableOn_of_bounded
    (isCompact_suzukiReciprocalCutoffSet ε R).measure_ne_top
    (by
      apply Measurable.aestronglyMeasurable
      fun_prop)
  filter_upwards [ae_restrict_mem
    (measurableSet_suzukiReciprocalCutoffSet ε R)] with t ht
  have htε : ε ≤ |t| :=
    le_abs_of_mem_suzukiReciprocalCutoffSet ht
  have htpos : 0 < |t| := hε.trans_le htε
  have hinv : |t|⁻¹ ≤ ε⁻¹ := by
    exact inv_anti₀ hε htε
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs,
    abs_of_pos (inv_pos.mpr hε)] using hinv

/-- The cutoff kernel is even. -/
theorem suzukiReciprocalCutoffKernel_neg
    (ε R t : Real) :
    suzukiReciprocalCutoffKernel ε R (-t) =
      suzukiReciprocalCutoffKernel ε R t := by
  have hmem :
      -t ∈ suzukiReciprocalCutoffSet ε R ↔
        t ∈ suzukiReciprocalCutoffSet ε R := by
    constructor
    · intro ht
      rcases ht with ht | ht
      · right
        constructor <;> linarith [ht.1, ht.2]
      · left
        constructor <;> linarith [ht.1, ht.2]
    · intro ht
      rcases ht with ht | ht
      · right
        constructor <;> linarith [ht.1, ht.2]
      · left
        constructor <;> linarith [ht.1, ht.2]
  by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
  · have hnt : -t ∈ suzukiReciprocalCutoffSet ε R := hmem.2 ht
    simp [suzukiReciprocalCutoffKernel, ht, hnt, abs_neg]
  · have hnt : -t ∉ suzukiReciprocalCutoffSet ε R := by
      simpa only [hmem] using ht
    simp [suzukiReciprocalCutoffKernel, ht, hnt]

/-- The ordinary Fourier multiplier of the finite reciprocal kernel. -/
def suzukiReciprocalCutoffFourierMultiplier
    (ε R ξ : Real) : Complex :=
  𝓕 (suzukiReciprocalCutoffKernel ε R) ξ

/-- The real cosine expression expected for the Fourier transform of the
finite even kernel in Mathlib's `exp (-2*pi*i*x*xi)` normalization. -/
def suzukiReciprocalCutoffCosineMultiplier
    (ε R ξ : Real) : Real :=
  2 * ∫ t in ε..R, Real.cos (2 * Real.pi * t * ξ) / t

/-- Fourier transform of the finite reciprocal kernel.  This is the honest
finite-cutoff calculation preceding Suzuki's cosine-integral limit. -/
theorem suzukiReciprocalCutoffFourierMultiplier_eq_cosine
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : Real) :
    suzukiReciprocalCutoffFourierMultiplier ε R ξ =
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) := by
  let f : Real → Complex := fun t =>
    Complex.exp (((-2 * Real.pi * t * ξ : Real) : Complex) * Complex.I) *
      ((|t|⁻¹ : Real) : Complex)
  have hset : MeasurableSet (suzukiReciprocalCutoffSet ε R) :=
    measurableSet_suzukiReciprocalCutoffSet ε R
  have hk := integrable_suzukiReciprocalCutoffKernel (R := R) hε
  have hfourierIntegrable : Integrable (fun t : Real =>
      Complex.exp (((-2 * Real.pi * t * ξ : Real) : Complex) * Complex.I) *
        suzukiReciprocalCutoffKernel ε R t) := by
    apply hk.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with t
      rw [Complex.norm_exp]
      simp
  have hfSet : IntegrableOn f (suzukiReciprocalCutoffSet ε R) := by
    rw [← integrable_indicator_iff hset]
    apply hfourierIntegrable.congr
    filter_upwards with t
    simp only [f, suzukiReciprocalCutoffKernel]
    by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
    · simp [ht]
    · simp [ht]
  have hdisj : Disjoint (Icc (-R) (-ε)) (Icc ε R) := by
    refine Set.disjoint_left.2 ?_
    intro t htleft htright
    linarith [htleft.2, htright.1]
  have hfLeft : IntegrableOn f (Icc (-R) (-ε)) :=
    hfSet.mono_set subset_union_left
  have hfRight : IntegrableOn f (Icc ε R) :=
    hfSet.mono_set subset_union_right
  have hfourierSet :
      (∫ t : Real,
        Complex.exp (((-2 * Real.pi * t * ξ : Real) : Complex) * Complex.I) *
          suzukiReciprocalCutoffKernel ε R t) =
        ∫ t in suzukiReciprocalCutoffSet ε R, f t := by
    rw [← integral_indicator hset]
    apply integral_congr_ae
    filter_upwards with t
    simp only [f, suzukiReciprocalCutoffKernel]
    by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
    · simp [ht]
    · simp [ht]
  have hleftInterval :
      (∫ t in Icc (-R) (-ε), f t) = ∫ t in (-R)..(-ε), f t := by
    rw [integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (neg_le_neg hεR)]
  have hrightInterval :
      (∫ t in Icc ε R, f t) = ∫ t in ε..R, f t := by
    rw [integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hεR]
  have hnegInterval :
      (∫ t in (-R)..(-ε), f t) = ∫ t in ε..R, f (-t) := by
    exact (intervalIntegral.integral_comp_neg (f := f)).symm
  have hfRightInterval : IntervalIntegrable f volume ε R := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hεR]
    exact hfRight
  have hfNegRightInterval :
      IntervalIntegrable (fun t : Real => f (-t)) volume ε R := by
    have hfLeftIntervalInt :
        IntervalIntegrable f volume (-R) (-ε) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le
        (neg_le_neg hεR)]
      exact hfLeft
    simpa only [neg_neg] using
      (IntervalIntegrable.iff_comp_neg).1 hfLeftIntervalInt.symm
  have hpointwise :
      EqOn (fun t : Real => f (-t) + f t)
        (fun t : Real =>
          ((2 * (Real.cos (2 * Real.pi * t * ξ) / t) : Real) : Complex))
        [[ε, R]] := by
    intro t ht
    have htε : ε ≤ t := by
      rw [uIcc_of_le hεR] at ht
      exact ht.1
    have htpos : 0 < t := hε.trans_le htε
    dsimp only [f]
    rw [abs_neg, abs_of_pos htpos,
      show (-2 * Real.pi * (-t) * ξ : Real) =
          2 * Real.pi * t * ξ by ring,
      show (-2 * Real.pi * t * ξ : Real) =
          -(2 * Real.pi * t * ξ) by ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  unfold suzukiReciprocalCutoffFourierMultiplier
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [hfourierSet]
  rw [suzukiReciprocalCutoffSet,
    setIntegral_union hdisj measurableSet_Icc hfLeft hfRight,
    hleftInterval, hrightInterval, hnegInterval]
  rw [← intervalIntegral.integral_add hfNegRightInterval hfRightInterval]
  rw [intervalIntegral.integral_congr hpointwise]
  unfold suzukiReciprocalCutoffCosineMultiplier
  rw [intervalIntegral.integral_ofReal]
  rw [intervalIntegral.integral_const_mul]

/-- The finite cosine multiplier is continuous in frequency.  This is most
cleanly inherited from the Fourier transform of the honest `L¹` cutoff
kernel. -/
theorem continuous_suzukiReciprocalCutoffCosineMultiplier
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) :
    Continuous (suzukiReciprocalCutoffCosineMultiplier ε R) := by
  have hfourier :
      Continuous (suzukiReciprocalCutoffFourierMultiplier ε R) := by
    unfold suzukiReciprocalCutoffFourierMultiplier
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL Real).continuous₂
      (integrable_suzukiReciprocalCutoffKernel (R := R) hε)
  have hre :
      suzukiReciprocalCutoffCosineMultiplier ε R =
        fun ξ : Real =>
          (suzukiReciprocalCutoffFourierMultiplier ε R ξ).re := by
    funext ξ
    rw [suzukiReciprocalCutoffFourierMultiplier_eq_cosine hε hεR]
    simp
  rw [hre]
  exact Complex.continuous_re.comp hfourier

/-- The finite cosine multiplier is even in frequency. -/
theorem suzukiReciprocalCutoffCosineMultiplier_neg
    (ε R ξ : Real) :
    suzukiReciprocalCutoffCosineMultiplier ε R (-ξ) =
      suzukiReciprocalCutoffCosineMultiplier ε R ξ := by
  unfold suzukiReciprocalCutoffCosineMultiplier
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  change Real.cos (2 * Real.pi * t * (-ξ)) / t =
    Real.cos (2 * Real.pi * t * ξ) / t
  rw [show 2 * Real.pi * t * (-ξ) =
      -(2 * Real.pi * t * ξ) by ring, Real.cos_neg]

/-- The positive-sign oscillatory integral is the same real multiplier.
This is the form used after Fourier inversion of the autocorrelation. -/
theorem integral_suzukiReciprocalCutoffKernel_mul_exp
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : Real) :
    (∫ t : Real,
      suzukiReciprocalCutoffKernel ε R t *
        Complex.exp (((2 * Real.pi * t * ξ : Real) : Complex) * Complex.I)) =
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) := by
  have hfourier :=
    suzukiReciprocalCutoffFourierMultiplier_eq_cosine hε hεR (-ξ)
  rw [suzukiReciprocalCutoffCosineMultiplier_neg] at hfourier
  unfold suzukiReciprocalCutoffFourierMultiplier at hfourier
  rw [Real.fourier_real_eq_integral_exp_smul] at hfourier
  simp only [smul_eq_mul] at hfourier
  calc
    (∫ t : Real,
      suzukiReciprocalCutoffKernel ε R t *
        Complex.exp (((2 * Real.pi * t * ξ : Real) : Complex) * Complex.I)) =
        ∫ t : Real,
          Complex.exp (((-2 * Real.pi * t * (-ξ) : Real) : Complex) *
              Complex.I) *
            suzukiReciprocalCutoffKernel ε R t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [show (-2 * Real.pi * t * (-ξ) : Real) =
          2 * Real.pi * t * ξ by ring]
      ring
    _ = (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) :=
      hfourier

/-- Physical-side pairing of the finite reciprocal kernel with the Schwartz
autocorrelation. -/
def suzukiReciprocalCutoffAutocorrelationPairing
    (ε R : Real) (v : SchwartzLineTestFunction) : Complex :=
  ∫ t : Real,
    suzukiReciprocalCutoffKernel ε R t *
      SchwartzLineTestFunction.autocorrelation v t

/-- Fourier-side pairing of the finite cosine multiplier with the squared
Fourier transform, expressed first through the normalized autocorrelation. -/
def suzukiReciprocalCutoffFourierPairing
    (ε R : Real) (v : SchwartzLineTestFunction) : Complex :=
  ∫ ξ : Real,
    (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
      SchwartzLineTestFunction.fourierAutocorrelation v ξ

/-- Finite-cutoff Plancherel identity.  No improper integral or
special-function asymptotic is used here. -/
theorem suzukiReciprocalCutoffAutocorrelationPairing_eq_fourier
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (v : SchwartzLineTestFunction) :
    suzukiReciprocalCutoffAutocorrelationPairing ε R v =
      suzukiReciprocalCutoffFourierPairing ε R v := by
  let A : SchwartzLineTestFunction :=
    SchwartzLineTestFunction.autocorrelation v
  let B : SchwartzLineTestFunction :=
    SchwartzLineTestFunction.fourierAutocorrelation v
  have hinverse : (𝓕⁻ B : SchwartzLineTestFunction) = A := by
    simp [A, B, SchwartzLineTestFunction.fourierAutocorrelation]
  have hinversePoint (t : Real) :
      A t = ∫ ξ : Real,
        Complex.exp (((2 * Real.pi * ξ * t : Real) : Complex) * Complex.I) *
          B ξ := by
    rw [← hinverse]
    rw [SchwartzMap.fourierInv_coe]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    apply congrArg (fun z : Complex => z * B ξ)
    apply congrArg Complex.exp
    push_cast
    ring
  have hk := integrable_suzukiReciprocalCutoffKernel (R := R) hε
  have hbase : Integrable (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R p.1 * B p.2)
      (volume.prod volume) :=
    hk.mul_prod B.integrable
  have hbounded : Integrable (fun p : Real × Real =>
      Complex.exp
          (((2 * Real.pi * p.2 * p.1 : Real) : Complex) * Complex.I) *
        (suzukiReciprocalCutoffKernel ε R p.1 * B p.2))
      (volume.prod volume) := by
    apply hbase.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with p
      rw [Complex.norm_exp]
      simp
  have hprod : Integrable (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R p.1 *
        (Complex.exp
            (((2 * Real.pi * p.2 * p.1 : Real) : Complex) * Complex.I) *
          B p.2)) (volume.prod volume) := by
    apply hbounded.congr
    filter_upwards with p
    ring
  unfold suzukiReciprocalCutoffAutocorrelationPairing
    suzukiReciprocalCutoffFourierPairing
  change (∫ t : Real,
      suzukiReciprocalCutoffKernel ε R t * A t) = _
  calc
    (∫ t : Real,
        suzukiReciprocalCutoffKernel ε R t * A t) =
        ∫ t : Real, ∫ ξ : Real,
          suzukiReciprocalCutoffKernel ε R t *
            (Complex.exp
                (((2 * Real.pi * ξ * t : Real) : Complex) * Complex.I) *
              B ξ) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hinversePoint]
      rw [integral_const_mul]
    _ = ∫ ξ : Real, ∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            (Complex.exp
                (((2 * Real.pi * ξ * t : Real) : Complex) * Complex.I) *
              B ξ) :=
      integral_integral_swap hprod
    _ = ∫ ξ : Real,
        (∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            Complex.exp
              (((2 * Real.pi * t * ξ : Real) : Complex) * Complex.I)) *
          B ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with t
      rw [show 2 * Real.pi * ξ * t =
          2 * Real.pi * t * ξ by ring]
      ring
    _ = ∫ ξ : Real,
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
          B ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [integral_suzukiReciprocalCutoffKernel_mul_exp hε hεR]

/-- The renormalized finite multiplier appearing after expansion of the
difference square. -/
def suzukiRenormalizedCutoffMultiplier
    (ε R ξ : Real) : Real :=
  -2 * Real.log ε -
    suzukiReciprocalCutoffCosineMultiplier ε R ξ

/-- The exact scalar special-function theorem needed by the cutoff proof.
This is Suzuki's cosine-integral asymptotic after conversion to Mathlib's
Fourier normalization. -/
def SuzukiCosineIntegralAsymptotic : Prop :=
  ∀ ξ : Real, ξ ≠ 0 →
    Tendsto
      (fun p : Real × Real =>
        suzukiRenormalizedCutoffMultiplier p.1 p.2 ξ)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (2 * suzukiSourceLogFourierWeight ξ))

/-- The finite Fourier identity is kept independent of the cosine-integral
limit.  It says only that the transform of the honest `L¹` kernel is the
displayed finite cosine integral. -/
def SuzukiFiniteReciprocalKernelFourierIdentity : Prop :=
  ∀ ε R ξ : Real, 0 < ε → ε ≤ R →
    suzukiReciprocalCutoffFourierMultiplier ε R ξ =
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex)

end

end M100
end Experiments
end RiemannHypothesisProject
