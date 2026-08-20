import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFiniteCutoff
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointOppositeModeCorrelation

/-!
# Symmetric translation form of endpoint cutoff pairings

This module converts the real part of the ordered physical cutoff pairing to
one half of the symmetric translation energy.  The factor of two is obtained
from the even reciprocal kernel and the adjoint relation for translation.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Topology

theorem inner_suzukiL2Translate_neg_eq_inner_translate_right
    (t : Real) (u v : SuzukiL2) :
    inner Complex (suzukiL2Translate (-t) u) v =
      inner Complex u (suzukiL2Translate t v) := by
  rw [← suzukiL2TranslateCLM_apply]
  rw [← suzukiL2Translate_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

theorem re_suzukiReciprocalCutoffKernel_mul_conj
    (ε R t : Real) (z : Complex) :
    RCLike.re (suzukiReciprocalCutoffKernel ε R t * conj z) =
      RCLike.re (suzukiReciprocalCutoffKernel ε R t) * RCLike.re z := by
  unfold suzukiReciprocalCutoffKernel
  by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
  · simp [Set.indicator_of_mem ht]
  · simp [Set.indicator_of_notMem ht]

theorem re_suzukiL2SymmetricTranslationEnergy_eq
    (t : Real) (u v : SuzukiL2) :
    (suzukiL2SymmetricTranslationEnergy t u v).re =
      (inner Complex (suzukiL2Translate t u) v).re +
        (inner Complex (suzukiL2Translate (-t) u) v).re := by
  unfold suzukiL2SymmetricTranslationEnergy
  rw [suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply]
  rw [inner_suzukiL2Translate_neg_eq_inner_translate_right]
  simp

theorem suzukiL2SymmetricTranslationEnergy_neg
    (t : Real) (u v : SuzukiL2) :
    suzukiL2SymmetricTranslationEnergy (-t) u v =
      suzukiL2SymmetricTranslationEnergy t u v := by
  unfold suzukiL2SymmetricTranslationEnergy
  rw [suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply,
    suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply]
  rw [inner_suzukiL2Translate_neg_eq_inner_translate_right t u v]
  rw [← inner_suzukiL2Translate_neg_eq_inner_translate_right (-t) u v]
  simp only [neg_neg]
  ring

/-- Integrating an even real function against the symmetric reciprocal
cutoff kernel reduces to twice the positive cutoff interval. -/
theorem integral_re_suzukiReciprocalCutoffKernel_mul_even
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (g : Real → Real) (hgEven : ∀ t, g (-t) = g t)
    (hint : Integrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel ε R t).re * g t)) :
    (∫ t : Real,
      (suzukiReciprocalCutoffKernel ε R t).re * g t) =
      2 * ∫ t in ε..R, g t / t := by
  let f : Real → Real := fun t => |t|⁻¹ * g t
  have hset : MeasurableSet (suzukiReciprocalCutoffSet ε R) :=
    measurableSet_suzukiReciprocalCutoffSet ε R
  have hfSet : IntegrableOn f (suzukiReciprocalCutoffSet ε R) := by
    rw [← integrable_indicator_iff hset]
    apply hint.congr
    filter_upwards with t
    unfold f suzukiReciprocalCutoffKernel
    by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
    · simp only [Set.indicator_of_mem ht, Complex.ofReal_re]
    · simp only [Set.indicator_of_notMem ht, Complex.zero_re, zero_mul,
        Set.indicator_of_notMem ht]
  have hdisj : Disjoint (Icc (-R) (-ε)) (Icc ε R) := by
    refine Set.disjoint_left.2 ?_
    intro t htleft htright
    linarith [htleft.2, htright.1]
  have hfLeft : IntegrableOn f (Icc (-R) (-ε)) :=
    hfSet.mono_set subset_union_left
  have hfRight : IntegrableOn f (Icc ε R) :=
    hfSet.mono_set subset_union_right
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
        (fun t : Real => 2 * (g t / t)) (Set.uIcc ε R) := by
    intro t ht
    have htε : ε ≤ t := by
      rw [uIcc_of_le hεR] at ht
      exact ht.1
    have htpos : 0 < t := hε.trans_le htε
    dsimp only [f]
    rw [abs_neg, abs_of_pos htpos, hgEven]
    field_simp
    ring
  have hcutoffSet :
      (∫ t : Real,
        (suzukiReciprocalCutoffKernel ε R t).re * g t) =
        ∫ t in suzukiReciprocalCutoffSet ε R, f t := by
    rw [← integral_indicator hset]
    apply integral_congr_ae
    filter_upwards with t
    unfold f suzukiReciprocalCutoffKernel
    by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
    · simp only [Set.indicator_of_mem ht, Complex.ofReal_re]
    · simp only [Set.indicator_of_notMem ht, Complex.zero_re, zero_mul]
  rw [hcutoffSet, suzukiReciprocalCutoffSet,
    setIntegral_union hdisj measurableSet_Icc hfLeft hfRight,
    hleftInterval, hrightInterval, hnegInterval]
  rw [← intervalIntegral.integral_add hfNegRightInterval hfRightInterval]
  rw [intervalIntegral.integral_congr hpointwise]
  rw [intervalIntegral.integral_const_mul]

/-- Endpoint translations have no overlap once the shift exceeds twice the
support radius. -/
theorem inner_suzukiL2Translate_yoshidaExponential_eq_zero_of_two_mul_lt
    {r t : Real} (hr : 0 < r) (ht : 2 * r < t) (m n : Int) :
    inner Complex
      (suzukiL2Translate t (suzukiYoshidaExponentialL2 r hr m))
      (suzukiYoshidaExponentialL2 r hr n) = 0 := by
  rw [inner_suzukiL2Translate_eq_integral_of_ae_two t
    (suzukiYoshidaExponentialL2 r hr m)
    (suzukiYoshidaExponentialL2 r hr n)
    (suzukiYoshidaExponentialFunction r m)
    (suzukiYoshidaExponentialFunction r n)
    (suzukiYoshidaExponentialL2_coeFn hr m)
    (suzukiYoshidaExponentialL2_coeFn hr n)]
  unfold suzukiYoshidaExponentialFunction
  rw [integral_symmetric_indicator_overlap_two (by linarith [hr])]
  rw [Set.Icc_eq_empty (by linarith)]
  simp

theorem suzukiL2SymmetricTranslationEnergy_yoshidaExponential_eq_zero_of_two_mul_lt
    {r t : Real} (hr : 0 < r) (ht : 2 * r < t) (m n : Int) :
    suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaExponentialL2 r hr m)
      (suzukiYoshidaExponentialL2 r hr n) = 0 := by
  unfold suzukiL2SymmetricTranslationEnergy
  rw [suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply]
  rw [inner_suzukiL2Translate_yoshidaExponential_eq_zero_of_two_mul_lt
    hr ht m n]
  have hreverse :=
    inner_suzukiL2Translate_yoshidaExponential_eq_zero_of_two_mul_lt
      hr ht n m
  have hsecond :
      inner Complex
        (suzukiYoshidaExponentialL2 r hr m)
        (suzukiL2Translate t (suzukiYoshidaExponentialL2 r hr n)) = 0 := by
    rw [← inner_conj_symm]
    rw [hreverse]
    simp
  rw [hsecond]
  simp

/-- For opposite positive modes, the real symmetric correlation vanishes on
and beyond the endpoint of the support overlap. -/
theorem re_suzukiL2SymmetricTranslationEnergy_exponential_opposite_eq_zero_of_two_mul_le
    {r t : Real} (hr : 0 < r) (ht : 2 * r ≤ t)
    (n : Nat) (hn : 0 < n) :
    (suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaExponentialL2 r hr (n : Int))
      (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re = 0 := by
  rcases ht.eq_or_lt with hEq | hLt
  · subst t
    rw [re_suzukiL2SymmetricTranslationEnergy_exponential_opposite
      hr (by positivity) le_rfl n hn]
    have hsin : Real.sin ((n : Real) * 2 * Real.pi) = 0 := by
      have h := Real.sin_nat_mul_two_pi_sub 0 n
      simpa only [sub_zero, Real.sin_zero, neg_zero,
        show (n : Real) * (2 * Real.pi) =
          (n : Real) * 2 * Real.pi by ring] using h
    rw [show ((n : Real) * Real.pi / r) * (2 * r) =
        (n : Real) * 2 * Real.pi by field_simp [hr.ne'] <;> ring,
      hsin]
    simp
  · rw [suzukiL2SymmetricTranslationEnergy_yoshidaExponential_eq_zero_of_two_mul_lt
      hr hLt (n : Int) (-(n : Int))]
    simp

theorem continuous_suzukiL2SymmetricTranslationEnergy_orbit
    (u v : SuzukiL2) :
    Continuous (fun t : Real => suzukiL2SymmetricTranslationEnergy t u v) := by
  unfold suzukiL2SymmetricTranslationEnergy
  exact ((continuous_suzukiL2Translate_orbit u).inner continuous_const).add
    (continuous_const.inner (continuous_suzukiL2Translate_orbit v))

theorem integrable_re_suzukiReciprocalCutoffKernel_mul_symmetric
    {ε R : Real} (hε : 0 < ε) (u v : SuzukiL2) :
    Integrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel ε R t).re *
        (suzukiL2SymmetricTranslationEnergy t u v).re) := by
  let A : Real → Real := fun t =>
    (suzukiReciprocalCutoffKernel ε R t).re *
      (inner Complex (suzukiL2Translate t u) v).re
  have hcomplex :=
    integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
      (R := R) hε u v
  have hA : Integrable A := by
    apply hcomplex.re.congr
    filter_upwards with t
    unfold A
    rw [re_suzukiReciprocalCutoffKernel_mul_conj]
    rfl
  have hAneg : Integrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel ε R t).re *
        (inner Complex (suzukiL2Translate (-t) u) v).re) := by
    apply hA.comp_neg.congr
    filter_upwards with t
    unfold A
    rw [suzukiReciprocalCutoffKernel_neg]
  apply (hA.add hAneg).congr
  filter_upwards with t
  simp only [Pi.add_apply]
  rw [re_suzukiL2SymmetricTranslationEnergy_eq]
  unfold A
  ring

/-- Against the even reciprocal kernel, the real ordered cross-correlation
pairing is one half of the real symmetric translation-energy pairing. -/
theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_symmetric
    {ε R : Real} (hε : 0 < ε) (u v : SuzukiL2) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v).re =
      (2 : Real)⁻¹ * ∫ t : Real,
        (suzukiReciprocalCutoffKernel ε R t).re *
          (suzukiL2SymmetricTranslationEnergy t u v).re := by
  let A : Real → Real := fun t =>
    (suzukiReciprocalCutoffKernel ε R t).re *
      (inner Complex (suzukiL2Translate t u) v).re
  have hcomplex :=
    integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
      (R := R) hε u v
  have hA : Integrable A := by
    apply hcomplex.re.congr
    filter_upwards with t
    unfold A
    rw [re_suzukiReciprocalCutoffKernel_mul_conj]
    rfl
  have hAneg : Integrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel ε R t).re *
        (inner Complex (suzukiL2Translate (-t) u) v).re) := by
    apply hA.comp_neg.congr
    filter_upwards with t
    unfold A
    rw [suzukiReciprocalCutoffKernel_neg]
  have hnegIntegral :
      (∫ t : Real,
        (suzukiReciprocalCutoffKernel ε R t).re *
          (inner Complex (suzukiL2Translate (-t) u) v).re) =
        ∫ t : Real,
          (suzukiReciprocalCutoffKernel ε R t).re *
            (inner Complex (suzukiL2Translate t u) v).re := by
    calc
      _ = ∫ t : Real, A (-t) := by
        apply integral_congr_ae
        filter_upwards with t
        unfold A
        rw [suzukiReciprocalCutoffKernel_neg]
      _ = ∫ t : Real, A t := integral_neg_eq_self A volume
      _ = _ := rfl
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  change RCLike.re (∫ t : Real,
    suzukiReciprocalCutoffKernel ε R t *
      conj (inner Complex (suzukiL2Translate t u) v)) = _
  rw [← integral_re hcomplex]
  have hleft :
      (∫ t : Real,
        RCLike.re (suzukiReciprocalCutoffKernel ε R t *
          conj (inner Complex (suzukiL2Translate t u) v))) =
        ∫ t : Real, A t := by
    apply integral_congr_ae
    filter_upwards with t
    unfold A
    rw [re_suzukiReciprocalCutoffKernel_mul_conj]
    rfl
  rw [hleft]
  have hsymmetric :
      (∫ t : Real,
        (suzukiReciprocalCutoffKernel ε R t).re *
          (suzukiL2SymmetricTranslationEnergy t u v).re) =
        (∫ t : Real, A t) +
          ∫ t : Real,
            (suzukiReciprocalCutoffKernel ε R t).re *
              (inner Complex (suzukiL2Translate (-t) u) v).re := by
    rw [← integral_add hA hAneg]
    apply integral_congr_ae
    filter_upwards with t
    rw [re_suzukiL2SymmetricTranslationEnergy_eq]
    unfold A
    ring
  rw [hsymmetric, hnegIntegral]
  ring

/-- The real ordered physical pairing is the positive-interval integral of
the real symmetric translation energy divided by the shift. -/
theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (u v : SuzukiL2) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v).re =
      ∫ t in ε..R,
        (suzukiL2SymmetricTranslationEnergy t u v).re / t := by
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_symmetric
    hε]
  rw [integral_re_suzukiReciprocalCutoffKernel_mul_even hε hεR
    (fun t => (suzukiL2SymmetricTranslationEnergy t u v).re)]
  · ring
  · intro t
    rw [suzukiL2SymmetricTranslationEnergy_neg]
  · exact integrable_re_suzukiReciprocalCutoffKernel_mul_symmetric hε u v

/-- For a positive opposite-mode pair, every outer cutoff beyond the support
radius gives the same explicit sine-kernel integral. -/
theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_exponential_opposite
    {r ε R : Real} (hr : 0 < r) (hε : 0 < ε)
    (hεr : ε ≤ 2 * r) (hrR : 2 * r ≤ R)
    (n : Nat) (hn : 0 < n) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
      (suzukiYoshidaExponentialL2 r hr (n : Int))
      (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re =
      -((n : Real) * Real.pi)⁻¹ *
        ∫ t in ε..(2 * r),
          Real.sin (((n : Real) * Real.pi / r) * t) / t := by
  let g : Real → Real := fun t =>
    (suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaExponentialL2 r hr (n : Int))
      (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re / t
  have hεR : ε ≤ R := hεr.trans hrR
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval
    hε hεR]
  change (∫ t in ε..R, g t) = _
  have hcontEnergy : Continuous (fun t : Real =>
      (suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaExponentialL2 r hr (n : Int))
        (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re) :=
    Complex.continuous_re.comp
      (continuous_suzukiL2SymmetricTranslationEnergy_orbit _ _)
  have hleft : IntervalIntegrable g volume ε (2 * r) := by
    apply ContinuousOn.intervalIntegrable
    apply hcontEnergy.continuousOn.div continuous_id.continuousOn
    intro t ht
    have htε : ε ≤ t := by
      rw [uIcc_of_le hεr] at ht
      exact ht.1
    exact ne_of_gt (hε.trans_le htε)
  have hright : IntervalIntegrable g volume (2 * r) R := by
    apply ContinuousOn.intervalIntegrable
    apply hcontEnergy.continuousOn.div continuous_id.continuousOn
    intro t ht
    have htr : 2 * r ≤ t := by
      rw [uIcc_of_le hrR] at ht
      exact ht.1
    simpa only [id_eq] using (ne_of_gt (by linarith [hr]) : t ≠ 0)
  have htail : (∫ t in (2 * r)..R, g t) = 0 := by
    rw [intervalIntegral.integral_congr
      (g := fun _ : Real => 0)]
    · simp
    · intro t ht
      unfold g
      rw [re_suzukiL2SymmetricTranslationEnergy_exponential_opposite_eq_zero_of_two_mul_le
        hr (by
          rw [uIcc_of_le hrR] at ht
          exact ht.1) n hn]
      simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [← hadd, htail, add_zero]
  rw [intervalIntegral.integral_congr]
  · rw [intervalIntegral.integral_const_mul]
  · intro t ht
    unfold g
    have htBounds : t ∈ Icc ε (2 * r) := by
      simpa [uIcc_of_le hεr] using ht
    rw [re_suzukiL2SymmetricTranslationEnergy_exponential_opposite
      hr (hε.trans_le htBounds.1).le htBounds.2 n hn]
    ring

end

end RiemannHypothesisProject.Experiments.M100
