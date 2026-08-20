import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointOppositeModeCutoffLimit
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointOppositeModeReduction
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointSymmetricCutoff

/-!
# Evaluation of the opposite Yoshida endpoint pairing

This module compares the renormalized endpoint Fourier cutoff with the honest
finite reciprocal-kernel pairing.  Orthogonality removes the scalar logarithmic
term, while the checked opposite-mode translation correlation leaves the
source sine transform.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

/-- The apparent singularity in the opposite-mode sine kernel is removable
for interval integration, so positive lower cutoffs converge to zero. -/
theorem tendsto_intervalIntegral_sine_div_zero
    {k b : Real} (hk : k ≠ 0) (hb : 0 < b) :
    Tendsto
      (fun ε : Real => ∫ t in ε..b, Real.sin (k * t) / t)
      (𝓝[>] (0 : Real))
      (𝓝 (∫ t in (0 : Real)..b, Real.sin (k * t) / t)) := by
  let g : Real → Real := fun t => k * Real.sinc (k * t)
  have hg : Continuous g := by
    exact continuous_const.mul
      (Real.continuous_sinc.comp (continuous_const.mul continuous_id))
  have hgInt : IntegrableOn g (uIcc (0 : Real) b) volume :=
    hg.continuousOn.integrableOn_compact isCompact_uIcc
  have hprimitive : ContinuousOn
      (fun ε : Real => ∫ t in ε..b, g t) (uIcc (0 : Real) b) :=
    intervalIntegral.continuousOn_primitive_interval_left hgInt
  have hzero : (0 : Real) ∈ uIcc (0 : Real) b := by
    rw [uIcc_of_le hb.le]
    exact ⟨le_rfl, hb.le⟩
  have hsinc : Tendsto
      (fun ε : Real => ∫ t in ε..b, g t)
      (𝓝[>] (0 : Real))
      (𝓝 (∫ t in (0 : Real)..b, g t)) := by
    have htend := (hprimitive 0 hzero).tendsto
    apply htend.mono_left
    rw [uIcc_of_le hb.le, nhdsWithin, nhdsWithin, le_inf_iff]
    constructor
    · exact inf_le_left
    · rw [le_principal_iff]
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
        ⟨Iio b, Iio_mem_nhds hb, ?_⟩
      intro ε hε
      exact ⟨hε.2.le, hε.1.le⟩
  have hkernel (a c : Real) :
      (∫ t in a..c, Real.sin (k * t) / t) = ∫ t in a..c, g t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (0 : Real)] with t ht
    intro _htInterval
    unfold g
    rw [Real.sinc_of_ne_zero (mul_ne_zero hk ht)]
    field_simp
  rw [hkernel 0 b]
  apply hsinc.congr'
  exact Filter.Eventually.of_forall fun ε => (hkernel ε b).symm

/-- The full opposite-mode sine-kernel interval is the negative of the
source-side comparison transform in the frozen project normalization. -/
theorem integral_sine_div_zero_two_mul_suzukiProjectAStar
    (n : Nat) (hn : 0 < n) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.sin
          (((n : Real) * Real.pi / suzukiProjectAStar) * t) / t) =
      -suzukiYoshidaComparisonSourceSineTransform n := by
  rw [suzukiYoshidaComparisonSourceSineTransform, if_neg hn.ne']
  rw [show -(-2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (1 / (2 * t)) *
        Real.sin (((n : Real) * Real.pi / suzukiProjectAStar) * t))) =
      2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (1 / (2 * t)) *
          Real.sin (((n : Real) * Real.pi / suzukiProjectAStar) * t)) by ring]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  ring

/-- For opposite nonzero modes, orthogonality removes the scalar logarithmic
term from the renormalized multiplier.  The remaining real part is the
negative of the honest physical reciprocal-kernel pairing. -/
theorem re_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand_opposite
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R)
    (n : Nat) (hn : 0 < n) :
    (∫ ξ : Real,
        suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r (n : Int) (-(n : Int)) ε R ξ).re =
      -(suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
        (suzukiYoshidaExponentialL2 r hr (n : Int))
        (suzukiYoshidaExponentialL2 r hr (-(n : Int)))).re := by
  let P : Real → Complex := fun ξ =>
    FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r (n : Int)) ξ *
      conj (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r (-(n : Int))) ξ)
  have hprod : Integrable P := by
    simpa only [P] using
      (integrable_suzukiYoshidaEndpointFourierPairing
        hsource hr (-(n : Int)) (n : Int))
  have hconst : Integrable (fun ξ : Real =>
      (((-2 * Real.log ε : Real) : Complex)) * P ξ) :=
    hprod.const_mul _
  have hcos : Integrable (fun ξ : Real =>
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) * P ξ) := by
    exact hprod.bdd_mul
      (c := suzukiReciprocalCutoffMultiplierBound ε R)
      ((Complex.continuous_ofReal.comp
        (continuous_suzukiReciprocalCutoffCosineMultiplier hε hεR)
          ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ =>
        norm_suzukiReciprocalCutoffCosineMultiplier_le hε hεR ξ)
  have hdistinct : (-(n : Int)) ≠ (n : Int) := by omega
  have horth := (orthonormal_iff_ite.mp
    (orthonormal_suzukiYoshidaExponentialL2 hr))
      (-(n : Int)) (n : Int)
  rw [if_neg hdistinct] at horth
  have hunweighted : (∫ ξ : Real, P ξ) = 0 := by
    rw [← inner_suzukiYoshidaExponentialL2_eq_fourierIntegral
      hsource hr (-(n : Int)) (n : Int)]
    exact horth
  have hrenormalized :
      (∫ ξ : Real,
        suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r (n : Int) (-(n : Int)) ε R ξ) =
        -suzukiYoshidaEndpointReciprocalCutoffFourierPairing
          r ε R (n : Int) (-(n : Int)) := by
    unfold suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      suzukiYoshidaEndpointReciprocalCutoffFourierPairing
      suzukiRenormalizedCutoffMultiplier
    change (∫ ξ : Real,
        (((-2 * Real.log ε -
          suzukiReciprocalCutoffCosineMultiplier ε R ξ : Real) : Complex) *
            P ξ)) =
      -(∫ ξ : Real,
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) * P ξ)
    calc
      (∫ ξ : Real,
          (((-2 * Real.log ε -
            suzukiReciprocalCutoffCosineMultiplier ε R ξ : Real) : Complex) *
              P ξ)) =
          ∫ ξ : Real,
            (((-2 * Real.log ε : Real) : Complex) * P ξ -
              (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
                P ξ) := by
            apply integral_congr_ae
            filter_upwards with ξ
            push_cast
            ring
      _ = (∫ ξ : Real,
            (((-2 * Real.log ε : Real) : Complex) * P ξ)) -
          ∫ ξ : Real,
            (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
              P ξ := integral_sub hconst hcos
      _ = (((-2 * Real.log ε : Real) : Complex) *
            (∫ ξ : Real, P ξ)) -
          ∫ ξ : Real,
            (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
              P ξ := by rw [integral_const_mul]
      _ = -(∫ ξ : Real,
            (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
              P ξ) := by rw [hunweighted]; simp
  rw [suzukiYoshidaEndpointReciprocalCutoffPairing_eq_fourier
    hsource hr hε hεR]
  simpa using congrArg Complex.re hrenormalized

/-- The renormalized endpoint cutoff has the explicit opposite-mode limit
dictated by the physical sine correlation. -/
theorem tendsto_re_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand_opposite
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (n : Nat) (hn : 0 < n) :
    Tendsto
      (fun p : Real × Real =>
        (∫ ξ : Real,
          suzukiYoshidaEndpointRenormalizedCutoffIntegrand
            suzukiProjectAStar (n : Int) (-(n : Int)) p.1 p.2 ξ).re)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (((n : Real) * Real.pi)⁻¹ *
        (-suzukiYoshidaComparisonSourceSineTransform n))) := by
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  have hnReal : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  have hk : ((n : Real) * Real.pi / suzukiProjectAStar) ≠ 0 :=
    div_ne_zero (mul_ne_zero hnReal Real.pi_ne_zero)
      suzukiProjectAStar_pos.ne'
  have hsine := tendsto_intervalIntegral_sine_div_zero
    (k := (n : Real) * Real.pi / suzukiProjectAStar)
    (b := 2 * suzukiProjectAStar) hk
    (mul_pos (by norm_num) suzukiProjectAStar_pos)
  rw [integral_sine_div_zero_two_mul_suzukiProjectAStar n hn] at hsine
  have hscaled : Tendsto
      (fun ε : Real => ((n : Real) * Real.pi)⁻¹ *
        ∫ t in ε..2 * suzukiProjectAStar,
          Real.sin
            (((n : Real) * Real.pi / suzukiProjectAStar) * t) / t)
      (𝓝[>] (0 : Real))
      (𝓝 (((n : Real) * Real.pi)⁻¹ *
        (-suzukiYoshidaComparisonSourceSineTransform n))) :=
    hsine.const_mul _
  have hscaledProd : Tendsto
      (fun p : Real × Real => ((n : Real) * Real.pi)⁻¹ *
        ∫ t in p.1..2 * suzukiProjectAStar,
          Real.sin
            (((n : Real) * Real.pi / suzukiProjectAStar) * t) / t)
      l
      (𝓝 (((n : Real) * Real.pi)⁻¹ *
        (-suzukiYoshidaComparisonSourceSineTransform n))) :=
    hscaled.comp tendsto_fst
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεrScalar : ∀ᶠ ε in 𝓝[>] (0 : Real),
      ε ≤ 2 * suzukiProjectAStar := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real),
        ε < 2 * suzukiProjectAStar :=
      mem_inf_of_left (Iio_mem_nhds
        (mul_pos (by norm_num) suzukiProjectAStar_pos))
    exact hlt.mono fun ε hε => hε.le
  have hεr : ∀ᶠ p in l, p.1 ≤ 2 * suzukiProjectAStar :=
    tendsto_fst.eventually hεrScalar
  have hrR : ∀ᶠ p in l, 2 * suzukiProjectAStar ≤ p.2 :=
    tendsto_snd.eventually
      (eventually_ge_atTop (2 * suzukiProjectAStar))
  apply hscaledProd.congr'
  filter_upwards [hεpos, hεr, hrR] with p hp hpr hpR
  rw [re_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand_opposite
    hsource suzukiProjectAStar_pos hp (hpr.trans hpR) n hn]
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_exponential_opposite
    suzukiProjectAStar_pos hp hpr hpR n hn]
  ring

/-- The remaining opposite-mode source-pairing proposition is unconditional
once the existing source-selected endpoint approximation is supplied. -/
theorem suzukiYoshidaEndpointOppositeModeSourcePairingEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiYoshidaEndpointOppositeModeSourcePairingEvaluation := by
  intro n hn
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  have hcomplex :=
    tendsto_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      suzukiProjectAStar_pos (n : Int) (-(n : Int))
  have hreal : Tendsto
      (fun p : Real × Real =>
        (∫ ξ : Real,
          suzukiYoshidaEndpointRenormalizedCutoffIntegrand
            suzukiProjectAStar (n : Int) (-(n : Int)) p.1 p.2 ξ).re)
      l
      (𝓝 (2 *
        (suzukiYoshidaEndpointSourceFourierPairing
          suzukiProjectAStar (n : Int) (-(n : Int))).re)) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
    simpa [Function.comp_def] using hre
  have hexplicit :=
    tendsto_re_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand_opposite
      hsource n hn
  have hvalue := tendsto_nhds_unique hreal hexplicit
  have hnReal : (n : Real) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnReal, Real.pi_ne_zero] at hvalue ⊢
  linarith

/-- Exact value of every positive paired-pole master integral. -/
theorem suzukiYoshidaEndpointSourceModeMasterIntegralEvaluation_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiYoshidaEndpointSourceModeMasterIntegralEvaluation :=
  suzukiYoshidaEndpointSourceModeMasterIntegralEvaluation_of_pairing
    (suzukiYoshidaEndpointOppositeModeSourcePairingEvaluation hsource)

/-- Combined integrability-and-value package consumed by the endpoint
rational-product partial fractions. -/
theorem suzukiYoshidaEndpointSourceModeMasterEvaluation_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiYoshidaEndpointSourceModeMasterEvaluation :=
  suzukiYoshidaEndpointSourceModeMasterEvaluation_of_integralEvaluation
    (suzukiYoshidaEndpointSourceModeMasterIntegralEvaluation_of_source hsource)

end

end RiemannHypothesisProject.Experiments.M100
