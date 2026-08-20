import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25GeometricRemainder
import RiemannHypothesisProject.Experiments.M100.SuzukiSingularFourierIdentity

/-!
# Soft/hard reciprocal-cutoff comparison

This module compares the exponential soft cutoff with the hard reciprocal
cutoff used in DF6D2.  Their rescaled difference is exactly the symmetric
Abel/hard profile, whose mass was evaluated as Euler's constant.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter MeasureTheory Set Topology SchwartzLineTestFunction
open scoped Topology

/-- Reciprocal kernel with only the inner cutoff. -/
def suzukiEquation25InnerReciprocalKernel (lam t : Real) : Real :=
  if 1 / lam ≤ |t| then |t|⁻¹ else 0

theorem suzukiEquation25InnerReciprocalKernel_neg (lam t : Real) :
    suzukiEquation25InnerReciprocalKernel lam (-t) =
      suzukiEquation25InnerReciprocalKernel lam t := by
  simp [suzukiEquation25InnerReciprocalKernel]

theorem suzukiEquation25SymmetricAbelHardProfile_neg (u : Real) :
    suzukiEquation25SymmetricAbelHardProfile (-u) =
      suzukiEquation25SymmetricAbelHardProfile u := by
  unfold suzukiEquation25SymmetricAbelHardProfile
  simp only [neg_neg]
  ring

private theorem suzukiEquation25_soft_add_inner_eq_profile_of_pos
    {lam t : Real} (hlam : 0 < lam) (ht : 0 < t)
    (hboundary : lam * t ≠ 1) :
    suzukiEquation25SoftReciprocalKernel lam t +
        (1 / 2) * suzukiEquation25InnerReciprocalKernel lam t =
      -lam * suzukiEquation25SymmetricAbelHardProfile (lam * t) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hprod : 0 < lam * t := mul_pos hlam ht
  rw [suzukiEquation25SoftReciprocalKernel_eq_of_ne ht0]
  rw [abs_of_pos ht]
  rcases lt_or_gt_of_ne hboundary with hlt | hgt
  · have hcut : ¬1 / lam ≤ t := by
      rw [div_le_iff₀ hlam]
      simpa only [mul_comm] using not_le.mpr hlt
    have hcond : ¬1 ≤ lam * |t| := by
      rw [abs_of_pos ht]
      exact not_le.mpr hlt
    have hcutAbs : ¬1 / lam ≤ |t| := by
      simpa only [abs_of_pos ht] using hcut
    have hlocal : lam * t ∈ Ioc (0 : Real) 1 := ⟨hprod, hlt.le⟩
    have hlocalNeg : -(lam * t) ∉ Ioc (0 : Real) 1 := by
      intro h
      linarith [h.1]
    have htail : lam * t ∉ Ioi (1 : Real) := not_lt.mpr hlt.le
    have htailNeg : -(lam * t) ∉ Ioi (1 : Real) := by
      intro h
      change 1 < -(lam * t) at h
      linarith
    simp [suzukiEquation25InnerReciprocalKernel, hcutAbs,
      hcond,
      suzukiEquation25SymmetricAbelHardProfile,
      suzukiEquation25AbelHardProfile, hlocal, hlocalNeg,
      htail, htailNeg]
    field_simp [hlam.ne', ht0]
    rw [if_neg hcond]
    ring
  · have hcut : 1 / lam ≤ t := by
      rw [div_le_iff₀ hlam]
      simpa only [mul_comm] using hgt.le
    have hcond : 1 ≤ lam * |t| := by
      rw [abs_of_pos ht]
      exact hgt.le
    have hcutAbs : 1 / lam ≤ |t| := by
      simpa only [abs_of_pos ht] using hcut
    have hlocal : lam * t ∉ Ioc (0 : Real) 1 := by
      intro h
      linarith [h.2]
    have hlocalNeg : -(lam * t) ∉ Ioc (0 : Real) 1 := by
      intro h
      linarith [h.1]
    have htail : lam * t ∈ Ioi (1 : Real) := hgt
    have htailNeg : -(lam * t) ∉ Ioi (1 : Real) := by
      intro h
      change 1 < -(lam * t) at h
      linarith
    simp [suzukiEquation25InnerReciprocalKernel, hcutAbs,
      hcond,
      suzukiEquation25SymmetricAbelHardProfile,
      suzukiEquation25AbelHardProfile, hlocal, hlocalNeg,
      htail, htailNeg]
    field_simp [hlam.ne', ht0]
    rw [if_pos hcond]
    rw [abs_of_pos ht]
    field_simp [ht0]
    ring

/-- Pointwise soft/hard comparison away from the origin and the two hard
cutoff boundary points. -/
theorem suzukiEquation25_soft_add_inner_eq_profile
    {lam t : Real} (hlam : 0 < lam) (ht : t ≠ 0)
    (hboundary : lam * |t| ≠ 1) :
    suzukiEquation25SoftReciprocalKernel lam t +
        (1 / 2) * suzukiEquation25InnerReciprocalKernel lam t =
      -lam * suzukiEquation25SymmetricAbelHardProfile (lam * t) := by
  by_cases htpos : 0 < t
  · exact suzukiEquation25_soft_add_inner_eq_profile_of_pos
      hlam htpos (by simpa [abs_of_pos htpos] using hboundary)
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
    have hpos := suzukiEquation25_soft_add_inner_eq_profile_of_pos
      hlam (neg_pos.mpr htneg)
      (by simpa [abs_of_neg htneg] using hboundary)
    simpa only [suzukiEquation25SoftReciprocalKernel_neg,
      suzukiEquation25InnerReciprocalKernel_neg,
      mul_neg, suzukiEquation25SymmetricAbelHardProfile_neg] using hpos

/-- Change of variables for the dilated symmetric profile. -/
theorem integral_suzukiEquation25SymmetricAbelHardProfile_scale
    {lam : Real} (hlam : 0 < lam) (g : Real → Real) (C : Real)
    (hg : Continuous g) (hC : ∀ x, |g x| ≤ C) :
    (∫ t : Real, lam *
        suzukiEquation25SymmetricAbelHardProfile (lam * t) * g t) =
      ∫ u : Real,
        suzukiEquation25SymmetricAbelHardProfile u * g (u / lam) := by
  let H : Real → Real := fun u =>
    suzukiEquation25SymmetricAbelHardProfile u * g (u / lam)
  have hH : Integrable H := by
    apply integrable_suzukiEquation25SymmetricAbelHardProfile.mul_bdd
    · exact (hg.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with u
      exact hC (u / lam)
  have hscale := Measure.integral_comp_mul_left H lam
  have hlam0 : lam ≠ 0 := hlam.ne'
  have habsInv : |lam⁻¹| = lam⁻¹ := abs_of_pos (inv_pos.mpr hlam)
  have hpoint : (fun t : Real => H (lam * t)) =
      fun t : Real =>
        suzukiEquation25SymmetricAbelHardProfile (lam * t) * g t := by
    funext t
    unfold H
    rw [mul_div_cancel_left₀ t hlam0]
  rw [hpoint, habsInv] at hscale
  simp only [smul_eq_mul] at hscale
  calc
    (∫ t : Real, lam *
        suzukiEquation25SymmetricAbelHardProfile (lam * t) * g t) =
        lam * ∫ t : Real,
          suzukiEquation25SymmetricAbelHardProfile (lam * t) * g t := by
      rw [show (fun t : Real => lam *
          suzukiEquation25SymmetricAbelHardProfile (lam * t) * g t) =
        fun t : Real => lam *
          (suzukiEquation25SymmetricAbelHardProfile (lam * t) * g t) by
            funext t
            ring]
      rw [integral_const_mul]
    _ = lam * (lam⁻¹ * ∫ u : Real, H u) := by rw [hscale]
    _ = ∫ u : Real, H u := by field_simp [hlam0]
    _ = ∫ u : Real,
        suzukiEquation25SymmetricAbelHardProfile u * g (u / lam) := rfl

/-- The dilated symmetric profile samples the zero-displacement real
autocorrelation, with total mass Euler's constant. -/
theorem tendsto_integral_suzukiEquation25SymmetricAbelHardProfile_autocorrelation
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun lam : Real => ∫ t : Real, lam *
        suzukiEquation25SymmetricAbelHardProfile (lam * t) *
          (autocorrelation v.1 t).re)
      atTop
      (nhds (Real.eulerMascheroniConstant *
        (autocorrelation v.1 0).re)) := by
  let g : Real → Real := fun t => (autocorrelation v.1 t).re
  let C : Real := SchwartzMap.seminorm Complex 0 0 (autocorrelation v.1)
  have hg : Continuous g := by
    exact Complex.continuous_re.comp (autocorrelation v.1).continuous
  have hgEven : ∀ x, g (-x) = g x := by
    intro x
    have h := congrArg Complex.re (conj_autocorrelation_neg_smoothCore v x)
    simpa [g] using h
  have hC : ∀ x, |g x| ≤ C := by
    intro x
    exact (Complex.abs_re_le_norm (autocorrelation v.1 x)).trans (by
      simpa [C, Real.norm_eq_abs] using
        SchwartzMap.norm_le_seminorm Complex (autocorrelation v.1) x)
  have hprofile :=
    tendsto_integral_suzukiEquation25SymmetricAbelHardProfile_mul_scale
      g hg hgEven C hC
  apply hprofile.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with lam hlam
  simpa [g] using
    (integral_suzukiEquation25SymmetricAbelHardProfile_scale
      hlam g C hg hC).symm

/-- At a radius containing the autocorrelation support, the soft pairing plus
half the hard reciprocal pairing is exactly the negative dilated profile
pairing. -/
theorem suzukiEquation25_softPairing_add_hardPairing_eq_profile
    {a lam : Real} (hlam : 0 < lam) (haR : 2 * a ≤ lam)
    (v : SuzukiSmoothCore a) :
    (suzukiFiniteKernelPairingComplex
        (suzukiEquation25SoftReciprocalKernel lam) a v.1).re +
      (1 / 2) *
        (suzukiReciprocalCutoffAutocorrelationPairing
          (1 / lam) lam v.1).re =
      -(∫ t : Real, lam *
        suzukiEquation25SymmetricAbelHardProfile (lam * t) *
          (autocorrelation v.1 t).re) := by
  let g : Real → Real := fun t => (autocorrelation v.1 t).re
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hsoftInt : Integrable (fun t : Real =>
      (suzukiEquation25SoftReciprocalKernel lam t : Complex) *
        autocorrelation v.1 t) := by
    apply (autocorrelation v.1).integrable.bdd_mul (c := lam / 2)
    · exact (Complex.continuous_ofReal.comp
        (continuous_suzukiEquation25SoftReciprocalKernel lam))
          |>.aestronglyMeasurable
    · filter_upwards with t
      simpa only [Complex.norm_real] using
        norm_suzukiEquation25SoftReciprocalKernel_le hlam.le t
  have hhardInt : Integrable (fun t : Real =>
      suzukiReciprocalCutoffKernel (1 / lam) lam t *
        autocorrelation v.1 t) := by
    apply (autocorrelation v.1).integrable.bdd_mul (c := lam)
    · exact (measurable_suzukiReciprocalCutoffKernel (1 / lam) lam)
        |>.aestronglyMeasurable
    · filter_upwards with t
      have hinv : (1 / lam)⁻¹ = lam := by field_simp [hlam.ne']
      simpa only [hinv] using
        norm_suzukiReciprocalCutoffKernel_le
          (div_pos zero_lt_one hlam) t
  have hsoft :=
    integral_softReciprocalKernel_mul_autocorrelation_eq_pairing
      hlam.le v
  have hhardMulRe (t : Real) :
      (suzukiReciprocalCutoffKernel (1 / lam) lam t *
          autocorrelation v.1 t).re =
        (suzukiReciprocalCutoffKernel (1 / lam) lam t).re * g t := by
    have him :
        (suzukiReciprocalCutoffKernel (1 / lam) lam t).im = 0 := by
      unfold suzukiReciprocalCutoffKernel
      change ((suzukiReciprocalCutoffSet (1 / lam) lam).indicator
        (fun s : Real => ((|s|⁻¹ : Real) : Complex)) t).im = 0
      by_cases ht : t ∈ suzukiReciprocalCutoffSet (1 / lam) lam
      · rw [Set.indicator_of_mem ht]
        exact Complex.ofReal_im _
      · rw [Set.indicator_of_notMem ht]
        exact Complex.zero_im
    rw [Complex.mul_re, him]
    simp [g]
  have hsoftRe :
      (suzukiFiniteKernelPairingComplex
          (suzukiEquation25SoftReciprocalKernel lam) a v.1).re =
        ∫ t : Real,
          suzukiEquation25SoftReciprocalKernel lam t * g t := by
    calc
      _ = (∫ t : Real,
          (suzukiEquation25SoftReciprocalKernel lam t : Complex) *
            autocorrelation v.1 t).re := congrArg Complex.re hsoft.symm
      _ = ∫ t : Real,
          ((suzukiEquation25SoftReciprocalKernel lam t : Complex) *
            autocorrelation v.1 t).re := (integral_re hsoftInt).symm
      _ = _ := integral_congr_ae (by
        filter_upwards with t
        simp [g])
  have hhardRe :
      (suzukiReciprocalCutoffAutocorrelationPairing
          (1 / lam) lam v.1).re =
        ∫ t : Real,
          (suzukiReciprocalCutoffKernel (1 / lam) lam t).re * g t := by
    unfold suzukiReciprocalCutoffAutocorrelationPairing
    calc
      _ = ∫ t : Real,
          (suzukiReciprocalCutoffKernel (1 / lam) lam t *
            autocorrelation v.1 t).re := (integral_re hhardInt).symm
      _ = _ := integral_congr_ae (ae_of_all _ hhardMulRe)
  rw [hsoftRe, hhardRe, ← integral_const_mul]
  have hsoftReal : Integrable (fun t : Real =>
      suzukiEquation25SoftReciprocalKernel lam t * g t) := by
    exact hsoftInt.re.congr (by
      filter_upwards with t
      simp [g])
  have hhardReal : Integrable (fun t : Real =>
      (suzukiReciprocalCutoffKernel (1 / lam) lam t).re * g t) := by
    exact hhardInt.re.congr (ae_of_all _ hhardMulRe)
  rw [← integral_add hsoftReal (hhardReal.const_mul (1 / 2))]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : Real),
    volume.ae_ne (1 / lam), volume.ae_ne (-(1 / lam))]
      with t ht0 htpos htneg
  have hboundary : lam * |t| ≠ 1 := by
    intro h
    rcases le_total 0 t with ht | ht
    · have : t = 1 / lam := by
        rw [abs_of_nonneg ht] at h
        apply (eq_div_iff hlam.ne').2
        nlinarith
      exact htpos this
    · have : t = -(1 / lam) := by
        rw [abs_of_nonpos ht] at h
        apply (eq_neg_iff_add_eq_zero).2
        field_simp [hlam.ne']
        nlinarith
      exact htneg this
  have hinnerActual :
      (suzukiReciprocalCutoffKernel (1 / lam) lam t).re * g t =
        suzukiEquation25InnerReciprocalKernel lam t * g t := by
    by_cases houter : |t| ≤ lam
    · rw [re_suzukiReciprocalCutoffKernel_eq_innerCutoff houter]
      rfl
    · have hout : lam < |t| := lt_of_not_ge houter
      have hg0 : g t = 0 := by
        unfold g
        rw [autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
          hsupport (haR.trans_lt hout)]
        rfl
      simp [hg0]
  rw [hinnerActual]
  have hpoint := suzukiEquation25_soft_add_inner_eq_profile
    hlam ht0 hboundary
  unfold g
  change
    suzukiEquation25SoftReciprocalKernel lam t * _ +
        (1 / 2) *
          (suzukiEquation25InnerReciprocalKernel lam t * _) =
      - (lam * suzukiEquation25SymmetricAbelHardProfile (lam * t) * _)
  linear_combination hpoint * (autocorrelation v.1 t).re

/-- The soft reciprocal pairing plus half the hard pairing converges to the
negative Euler-constant mass correction. -/
theorem tendsto_suzukiEquation25_softPairing_add_hardPairing
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun lam : Real =>
        (suzukiFiniteKernelPairingComplex
          (suzukiEquation25SoftReciprocalKernel lam) a v.1).re +
        (1 / 2) *
          (suzukiReciprocalCutoffAutocorrelationPairing
            (1 / lam) lam v.1).re)
      atTop
      (nhds (-(Real.eulerMascheroniConstant *
        (autocorrelation v.1 0).re))) := by
  have hprofile :=
    (tendsto_integral_suzukiEquation25SymmetricAbelHardProfile_autocorrelation
      v).neg
  apply hprofile.congr'
  filter_upwards [eventually_gt_atTop (0 : Real),
    eventually_ge_atTop (2 * a)] with lam hlam haR
  exact (suzukiEquation25_softPairing_add_hardPairing_eq_profile
    hlam haR v).symm

/-- After adding the Euler-constant mass counterterm, the soft/hard cutoff
comparison tends to zero. -/
theorem tendsto_suzukiEquation25_softHardComparison_zero
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun lam : Real =>
        Real.eulerMascheroniConstant * (autocorrelation v.1 0).re +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25SoftReciprocalKernel lam) a v.1).re +
          (1 / 2) *
            (suzukiReciprocalCutoffAutocorrelationPairing
              (1 / lam) lam v.1).re)
      atTop (nhds 0) := by
  have hconst : Tendsto
      (fun _ : Real => Real.eulerMascheroniConstant *
        (autocorrelation v.1 0).re)
      atTop
      (nhds (Real.eulerMascheroniConstant *
        (autocorrelation v.1 0).re)) := tendsto_const_nhds
  have h := hconst.add
    (tendsto_suzukiEquation25_softPairing_add_hardPairing v)
  convert h using 1 <;> ring

/-- Along the reciprocal diagonal `(1 / λ, λ)`, half the renormalized hard
pairing converges to the source logarithmic Fourier form. -/
theorem tendsto_suzukiEquation25_hardPath_to_logFourier
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun lam : Real =>
        Real.log lam * (autocorrelation v.1 0).re -
          (1 / 2) *
            (suzukiReciprocalCutoffAutocorrelationPairing
              (1 / lam) lam v.1).re)
      atTop
      (nhds (suzukiSourceLogFourierForm v.1)) := by
  have hinv : Tendsto (fun lam : Real => lam⁻¹) atTop (𝓝[>] (0 : Real)) :=
    tendsto_inv_atTop_nhdsGT_zero
  have hfirst : Tendsto (fun lam : Real => 1 / lam) atTop
      (𝓝[>] (0 : Real)) := by
    simpa [one_div] using hinv
  have hpath : Tendsto (fun lam : Real => (1 / lam, lam)) atTop
      (𝓝[>] (0 : Real) ×ˢ atTop) := by
    exact hfirst.prodMk tendsto_id
  have hphysical :=
    (tendsto_suzukiRenormalizedCutoffPhysicalPairing_to_fourier
      (suzukiCosineIntegralAsymptotic_of_constantIdentity
        suzukiCosineIntegralConstantIdentity) v.1).comp hpath
  have hhalfConst : Tendsto (fun _ : Real => (1 / 2 : Real)) atTop
      (nhds (1 / 2 : Real)) := tendsto_const_nhds
  have hhalf := hhalfConst.mul hphysical
  have hmass :
      (∫ x : Real, ‖v.1 x‖ ^ 2) = (autocorrelation v.1 0).re := by
    calc
      _ = ‖suzukiSmoothCoreToL2 v‖ ^ 2 := by
        symm
        exact norm_sq_toLp_eq_integral_norm_sq v.1
          (v.1.memLp (2 : ENNReal) volume)
      _ = _ := norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re v
  have hhalf' : Tendsto
      (fun lam : Real =>
        Real.log lam * (autocorrelation v.1 0).re -
          (1 / 2) *
            (suzukiReciprocalCutoffAutocorrelationPairing
              (1 / lam) lam v.1).re)
      atTop
      (nhds ((1 / 2 : Real) *
        (2 * suzukiSourceLogFourierForm v.1))) := by
    apply hhalf.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with lam hlam
    unfold suzukiRenormalizedCutoffPhysicalPairing
    rw [hmass]
    simp only [Function.comp_apply, one_div, Real.log_inv]
    ring
  convert hhalf' using 1 <;> ring

/-- The Euler- and logarithm-renormalized soft reciprocal pairing converges to
the source logarithmic Fourier form. -/
theorem tendsto_suzukiEquation25_softPairing_to_logFourier
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun lam : Real =>
        (Real.log lam + Real.eulerMascheroniConstant) *
            (autocorrelation v.1 0).re +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25SoftReciprocalKernel lam) a v.1).re)
      atTop
      (nhds (suzukiSourceLogFourierForm v.1)) := by
  have hsum := (tendsto_suzukiEquation25_softHardComparison_zero v).add
    (tendsto_suzukiEquation25_hardPath_to_logFourier v)
  have hsum' : Tendsto
      (fun lam : Real =>
        (Real.log lam + Real.eulerMascheroniConstant) *
            (autocorrelation v.1 0).re +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25SoftReciprocalKernel lam) a v.1).re)
      atTop
      (nhds (0 + suzukiSourceLogFourierForm v.1)) := by
    apply hsum.congr'
    filter_upwards with lam
    ring
  simpa only [zero_add] using hsum'

end

end M100
end Experiments
end RiemannHypothesisProject
