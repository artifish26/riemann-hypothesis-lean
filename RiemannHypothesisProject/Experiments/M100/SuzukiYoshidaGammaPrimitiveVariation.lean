import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointSmoothWitnessPositivity
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaHighModePrimitive
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaGammaOperatorBridge
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Primitive/variation bridge for the Yoshida Gamma remainder

This module isolates the scalar integration-by-parts estimate behind the
remaining B3F-F Gamma bound.  If the symmetric translation energy has an
endpoint-zero correlation primitive, monotonicity of Suzuki's `r''` kernel
gives the exact DF0 variation constant.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

/-- Correlation primitive associated with a weak spatial primitive `H` of
`v`.  The sign is chosen so that its derivative is the negative symmetric
translation energy. -/
def suzukiL2SymmetricCorrelationPrimitive
    (H v : SuzukiL2) (t : Real) : Complex :=
  -(inner Complex (suzukiL2Translate t H) v +
    inner Complex v (suzukiL2Translate t H))

theorem continuous_suzukiL2SymmetricCorrelationPrimitive
    (H v : SuzukiL2) :
    Continuous (suzukiL2SymmetricCorrelationPrimitive H v) := by
  unfold suzukiL2SymmetricCorrelationPrimitive
  exact (((continuous_suzukiL2Translate_orbit H).inner continuous_const).add
    (continuous_const.inner (continuous_suzukiL2Translate_orbit H))).neg

theorem norm_suzukiL2SymmetricCorrelationPrimitive_le
    (H v : SuzukiL2) (t : Real) :
    ‖suzukiL2SymmetricCorrelationPrimitive H v t‖ ≤
      2 * ‖H‖ * ‖v‖ := by
  unfold suzukiL2SymmetricCorrelationPrimitive
  rw [norm_neg]
  calc
    ‖inner Complex (suzukiL2Translate t H) v +
        inner Complex v (suzukiL2Translate t H)‖ ≤
      ‖inner Complex (suzukiL2Translate t H) v‖ +
        ‖inner Complex v (suzukiL2Translate t H)‖ := norm_add_le _ _
    _ ≤ (‖suzukiL2Translate t H‖ * ‖v‖) +
        (‖v‖ * ‖suzukiL2Translate t H‖) := by
      gcongr <;> exact norm_inner_le_norm _ _
    _ = 2 * ‖H‖ * ‖v‖ := by
      rw [suzukiL2Translate_norm]
      ring

/-- The sole Sobolev/translation input needed by the correlation route: the
translation orbit of `H` differentiates to the translation orbit of `v`. -/
def SuzukiL2TranslationPrimitiveDerivative (H v : SuzukiL2) : Prop :=
  ∀ t : Real,
    HasDerivAt (fun s => suzukiL2Translate s H)
      (suzukiL2Translate t v) t

theorem suzukiL2TranslationPrimitiveDerivative_zero :
    SuzukiL2TranslationPrimitiveDerivative 0 0 := by
  intro t
  simpa only [← suzukiL2TranslateCLM_apply, map_zero] using
    (hasDerivAt_const t (0 : SuzukiL2))

theorem SuzukiL2TranslationPrimitiveDerivative.add
    {H₁ H₂ v₁ v₂ : SuzukiL2}
    (h₁ : SuzukiL2TranslationPrimitiveDerivative H₁ v₁)
    (h₂ : SuzukiL2TranslationPrimitiveDerivative H₂ v₂) :
    SuzukiL2TranslationPrimitiveDerivative (H₁ + H₂) (v₁ + v₂) := by
  intro t
  have h := (h₁ t).add (h₂ t)
  simp only [← suzukiL2TranslateCLM_apply, map_add]
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with s
  rfl

theorem SuzukiL2TranslationPrimitiveDerivative.smul
    {H v : SuzukiL2}
    (h : SuzukiL2TranslationPrimitiveDerivative H v) (c : Complex) :
    SuzukiL2TranslationPrimitiveDerivative (c • H) (c • v) := by
  intro t
  have hc := (h t).const_smul c
  simp only [← suzukiL2TranslateCLM_apply, map_smul]
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards with s
  rfl

/-- A compactly supported Lipschitz representative whose almost-everywhere
derivative is `g` differentiates strongly under the global `L²` translation
action.  This is the analytic engine used below for one endpoint-zero mode. -/
theorem hasDerivAt_suzukiL2Translate_zero_of_lipschitz
    {C : NNReal} {f g : Real → Complex}
    (hf : LipschitzWith C f) (hfc : HasCompactSupport f)
    (hg : MemLp g (2 : ENNReal) volume)
    (hgBound : ∀ᵐ x ∂(volume : Measure Real), ‖g x‖ ≤ (C : Real))
    (hderiv : ∀ᵐ x ∂(volume : Measure Real), HasDerivAt f (g x) x) :
    HasDerivAt
      (fun t => suzukiL2Translate t
        ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f))
      (hg.toLp g) 0 := by
  let hfLp : MemLp f (2 : ENNReal) volume :=
    hf.continuous.memLp_of_hasCompactSupport hfc
  let F : SuzukiL2 := hfLp.toLp f
  let G : SuzukiL2 := hg.toLp g
  let K : Set Real := Metric.cthickening 1 (tsupport f)
  let Q : Real → Real → Real := fun h x =>
    ‖h⁻¹ • (f (x + h) - f x) - g x‖ ^ 2
  let B : Real → Real := K.indicator (fun _ => (2 * (C : Real)) ^ 2)
  have hgSupport : ∀ᵐ x ∂(volume : Measure Real),
      x ∉ tsupport f → g x = 0 := by
    filter_upwards [hderiv] with x hx hxNot
    exact hx.unique (HasDerivAt.of_notMem_tsupport hxNot)
  have hKCompact : IsCompact K := by
    exact IsCompact.cthickening hfc
  have hBIntegrable : Integrable B volume := by
    simp only [B, integrable_indicator_iff hKCompact.measurableSet]
    exact integrableOn_const hKCompact.measure_ne_top
  have hQMeasurable : ∀ᶠ h in nhdsWithin (0 : Real) ({0} : Set Real)ᶜ,
      AEStronglyMeasurable (Q h) volume := by
    filter_upwards with h
    apply AEStronglyMeasurable.pow
    apply AEStronglyMeasurable.norm
    apply AEStronglyMeasurable.sub _ hg.aestronglyMeasurable
    have hm : AEStronglyMeasurable (fun x => f (x + h) - f x) volume := by
      exact ((hf.continuous.measurable.comp
        (measurable_id.add_const h)).sub hf.continuous.measurable).aestronglyMeasurable
    exact hm.const_smul h⁻¹
  have hQBound : ∀ᶠ h in nhdsWithin (0 : Real) ({0} : Set Real)ᶜ,
      ∀ᵐ x ∂(volume : Measure Real), ‖Q h x‖ ≤ B x := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (Metric.ball_mem_nhds (0 : Real) one_pos) :
        ∀ᶠ h in nhdsWithin (0 : Real) ({0} : Set Real)ᶜ,
          h ∈ Metric.ball 0 1)] with h hne hball
    simp only [mem_compl_iff, mem_singleton_iff] at hne
    have habs : |h| < 1 := by simpa [Real.dist_eq] using hball
    filter_upwards [hgBound, hgSupport] with x hgx hgsupport
    by_cases hx : x ∈ K
    · have hslope : ‖h⁻¹ • (f (x + h) - f x)‖ ≤ (C : Real) := by
        have hLip := hf.norm_sub_le (x + h) x
        have habs0 : |h| ≠ 0 := abs_ne_zero.mpr hne
        calc
          ‖h⁻¹ • (f (x + h) - f x)‖ =
              |h|⁻¹ * ‖f (x + h) - f x‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_inv]
          _ ≤ |h|⁻¹ * ((C : Real) * |h|) := by
                gcongr
                simpa [Real.dist_eq] using hLip
          _ = (C : Real) := by field_simp
      have herror : ‖h⁻¹ • (f (x + h) - f x) - g x‖ ≤
          2 * (C : Real) := by
        calc
          ‖h⁻¹ • (f (x + h) - f x) - g x‖ ≤
              ‖h⁻¹ • (f (x + h) - f x)‖ + ‖g x‖ := norm_sub_le _ _
          _ ≤ (C : Real) + (C : Real) := add_le_add hslope hgx
          _ = 2 * (C : Real) := by ring
      simp only [Q, B, indicator_of_mem hx, Real.norm_eq_abs]
      rw [abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq₀ (norm_nonneg _) (by positivity) |>.2 herror
    · have hfx : f x = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        exact Metric.self_subset_cthickening (tsupport f) (subset_tsupport f hx)
      have hfxh : f (x + h) = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        apply Metric.mem_cthickening_of_dist_le x (x + h) 1 (tsupport f)
          (subset_tsupport f hx)
        simpa [Real.dist_eq] using habs.le
      have hgzero : g x = 0 := hgsupport fun hxt =>
        hx (Metric.self_subset_cthickening (tsupport f) hxt)
      simp only [Q, B, indicator_of_notMem hx, hfx, hfxh, hgzero]
      norm_num
  have hQLimit : ∀ᵐ x ∂(volume : Measure Real),
      Filter.Tendsto (fun h => Q h x)
        (nhdsWithin (0 : Real) ({0} : Set Real)ᶜ) (nhds 0) := by
    filter_upwards [hderiv] with x hx
    have hslope := hx.tendsto_slope_zero
    have hsub : Filter.Tendsto
        (fun h => h⁻¹ • (f (x + h) - f x) - g x)
        (nhdsWithin (0 : Real) ({0} : Set Real)ᶜ) (nhds 0) := by
      simpa using hslope.sub_const (g x)
    simpa [Q] using (hsub.norm.pow 2)
  have hIntegral : Filter.Tendsto (fun h => ∫ x, Q h x)
      (nhdsWithin (0 : Real) ({0} : Set Real)ᶜ) (nhds 0) := by
    have hdom := tendsto_integral_filter_of_dominated_convergence
      B hQMeasurable hQBound hBIntegrable hQLimit
    simpa using hdom
  have htranslateCoe (h : Real) :
      (suzukiL2Translate h F : Real → Complex) =ᵐ[volume]
        fun x => f (x + h) := by
    have hcomp :
        (suzukiL2Translate h F : Real → Complex) =ᵐ[volume]
          (F : Real → Complex) ∘ fun x ↦ x + h := by
      simpa only [suzukiL2Translate] using
        (Lp.coeFn_compMeasurePreserving F
          (measurePreserving_add_right (volume : Measure Real) h))
    have hfcoe : (F : Real → Complex) =ᵐ[volume] f := by
      exact hfLp.coeFn_toLp
    have hfshift := (measurePreserving_add_right
      (volume : Measure Real) h).quasiMeasurePreserving.ae_eq_comp hfcoe
    exact hcomp.trans hfshift
  have hGcoe : (G : Real → Complex) =ᵐ[volume] g := hg.coeFn_toLp
  have hnormSq (h : Real) :
      ‖h⁻¹ • (suzukiL2Translate h F - F) - G‖ ^ 2 = ∫ x, Q h x := by
    let W : SuzukiL2 := h⁻¹ • (suzukiL2Translate h F - F) - G
    have hnorm := norm_sq_toLp_eq_integral_norm_sq
      (fun x : Real => W x) (Lp.memLp W)
    rw [Lp.toLp_coeFn] at hnorm
    rw [hnorm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (suzukiL2Translate h F) F,
      Lp.coeFn_smul h⁻¹ (suzukiL2Translate h F - F),
      Lp.coeFn_sub (h⁻¹ • (suzukiL2Translate h F - F)) G,
      htranslateCoe h, hfLp.coeFn_toLp, hGcoe] with
      x hsub hsmul houter htranslate hfcoe hgcoe
    change ‖((W : Real → Complex) x)‖ ^ 2 = _
    rw [houter]
    change ‖((h⁻¹ • (suzukiL2Translate h F - F) : SuzukiL2) :
      Real → Complex) x - (G : Real → Complex) x‖ ^ 2 = _
    rw [hsmul]
    change ‖h⁻¹ • ((suzukiL2Translate h F - F : SuzukiL2) :
      Real → Complex) x - (G : Real → Complex) x‖ ^ 2 = _
    rw [hsub]
    change ‖h⁻¹ • ((suzukiL2Translate h F : Real → Complex) x -
      (F : Real → Complex) x) - (G : Real → Complex) x‖ ^ 2 = _
    rw [htranslate, hfcoe, hgcoe]
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsq : Filter.Tendsto
      (fun h => ‖h⁻¹ • (suzukiL2Translate h F - F) - G‖ ^ 2)
      (nhdsWithin (0 : Real) ({0} : Set Real)ᶜ) (nhds 0) := by
    simpa only [hnormSq] using hIntegral
  have hsqrt := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _), F, G, suzukiL2Translate_zero] using hsqrt

/-- A strong translation derivative at zero propagates to every translation
parameter by the translation group law. -/
theorem hasDerivAt_suzukiL2Translate_of_zero
    {H v : SuzukiL2}
    (hzero : HasDerivAt (fun t => suzukiL2Translate t H) v 0)
    (t : Real) :
    HasDerivAt (fun s => suzukiL2Translate s H)
      (suzukiL2Translate t v) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hlim := hzero.tendsto_slope_zero
  have htranslated :=
    (suzukiL2TranslateCLM t).continuous.continuousAt.tendsto.comp hlim
  refine htranslated.congr' (Filter.Eventually.of_forall fun e => ?_)
  simp only [Function.comp_apply, zero_add, suzukiL2TranslateCLM_apply,
    RCLike.real_smul_eq_coe_smul (K := Complex), ← suzukiL2TranslateCLM_apply,
    map_smul, map_sub, suzukiL2Translate_add, suzukiL2Translate_zero]
  congr 1
  simp only [suzukiL2TranslateCLM_apply, suzukiL2Translate_add,
    suzukiL2Translate_zero]

/-- Compact-support Lipschitz data therefore give the strong translation
derivative at every parameter, not only at the identity translation. -/
theorem hasDerivAt_suzukiL2Translate_of_lipschitz
    {C : NNReal} {f g : Real → Complex}
    (hf : LipschitzWith C f) (hfc : HasCompactSupport f)
    (hg : MemLp g (2 : ENNReal) volume)
    (hgBound : ∀ᵐ x ∂(volume : Measure Real), ‖g x‖ ≤ (C : Real))
    (hderiv : ∀ᵐ x ∂(volume : Measure Real), HasDerivAt f (g x) x)
    (t : Real) :
    HasDerivAt
      (fun s => suzukiL2Translate s
        ((hf.continuous.memLp_of_hasCompactSupport hfc).toLp f))
      (suzukiL2Translate t (hg.toLp g)) t :=
  hasDerivAt_suzukiL2Translate_of_zero
    (hasDerivAt_suzukiL2Translate_zero_of_lipschitz
      hf hfc hg hgBound hderiv) t

/-- The smooth normalized physical mode `-j` before it is cut off to the
Suzuki interval. -/
def cutoff44HighExponentialCore
    (j : Cutoff44HighIndex) (x : Real) : Complex :=
  (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) *
    Complex.exp
      (Complex.I *
        (((-j.1 : Int) : Complex) * (Real.pi : Complex) /
          (suzukiProjectAStar : Complex)) * (x : Complex))

/-- Smooth endpoint-zero primitive before clamping to the Suzuki interval. -/
def cutoff44HighEndpointPrimitiveCore
    (j : Cutoff44HighIndex) (x : Real) : Complex :=
  cutoff44HighPrimitiveMultiplier j *
    (cutoff44HighExponentialCore j x -
      cutoff44HighEndpointPhase j *
        (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex))

theorem hasDerivAt_cutoff44HighEndpointPrimitiveCore
    (j : Cutoff44HighIndex) (x : Real) :
    HasDerivAt (cutoff44HighEndpointPrimitiveCore j)
      (cutoff44HighExponentialCore j x) x := by
  let c : Complex := Complex.I *
    (((-j.1 : Int) : Complex) * (Real.pi : Complex) /
      (suzukiProjectAStar : Complex))
  have hlin : HasDerivAt (fun y : Real => c * (y : Complex)) c x := by
    simpa using (((hasDerivAt_id (x : Complex)).const_mul c).comp_ofReal)
  have hexp : HasDerivAt (fun y : Real => Complex.exp (c * (y : Complex)))
      (Complex.exp (c * (x : Complex)) * c) x :=
    (Complex.hasDerivAt_exp (c * (x : Complex))).comp x hlin
  have hscaled := hexp.const_mul
    (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex)
  have hprimitive := (hscaled.sub_const
    (cutoff44HighEndpointPhase j *
      (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex))).const_mul
        (cutoff44HighPrimitiveMultiplier j)
  have hj0 : ((j.1 : Int) : Complex) ≠ 0 := by
    exact_mod_cast cutoff44HighIndex_ne_zero j
  have ha0 : ((suzukiProjectAStar : Real) : Complex) ≠ 0 := by
    exact_mod_cast suzukiProjectAStar_pos.ne'
  have hpi0 : ((Real.pi : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hmc : cutoff44HighPrimitiveMultiplier j * c = 1 := by
    simp only [cutoff44HighPrimitiveMultiplier, c]
    push_cast
    field_simp [hj0, ha0, hpi0]
    rw [Complex.I_sq]
    field_simp [hj0]
  have hfactor : cutoff44HighPrimitiveMultiplier j *
        ((((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) *
          (Complex.exp (c * (x : Complex)) * c)) =
      cutoff44HighExponentialCore j x := by
    rw [show cutoff44HighPrimitiveMultiplier j *
        ((((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) *
          (Complex.exp (c * (x : Complex)) * c)) =
        ((((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) *
          Complex.exp (c * (x : Complex))) *
            (cutoff44HighPrimitiveMultiplier j * c) by ring]
    rw [hmc, mul_one]
    simp only [cutoff44HighExponentialCore, c]
  rw [hfactor] at hprimitive
  unfold cutoff44HighEndpointPrimitiveCore
  change HasDerivAt
    (fun y : Real => cutoff44HighPrimitiveMultiplier j *
      (cutoff44HighExponentialCore j y -
        cutoff44HighEndpointPhase j *
          (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex)))
    (cutoff44HighExponentialCore j x) x
  simpa only [cutoff44HighExponentialCore, c] using hprimitive

theorem cutoff44HighExponentialCore_right_endpoint
    (j : Cutoff44HighIndex) :
    cutoff44HighExponentialCore j suzukiProjectAStar =
      cutoff44HighEndpointPhase j *
        (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) := by
  let c : Complex := Complex.I *
    (((-j.1 : Int) : Complex) * (Real.pi : Complex) /
      (suzukiProjectAStar : Complex))
  have hexp : Complex.exp (c * suzukiProjectAStar) =
      ((-1 : Complex) ^ (-j.1 : Int)) := by
    calc
      Complex.exp (c * suzukiProjectAStar) =
          Complex.exp (((-j.1 : Int) : Complex) *
            ((Real.pi : Complex) * Complex.I)) := by
        congr 1
        simp only [c]
        field_simp [suzukiProjectAStar_pos.ne']
      _ = Complex.exp ((Real.pi : Complex) * Complex.I) ^ (-j.1 : Int) :=
        Complex.exp_int_mul _ _
      _ = ((-1 : Complex) ^ (-j.1 : Int)) := by
        rw [Complex.exp_pi_mul_I]
  change (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) *
    Complex.exp (c * (suzukiProjectAStar : Complex)) = _
  rw [hexp]
  rw [← Int.cast_negOnePow Complex (-j.1), Int.negOnePow_neg]
  simp [cutoff44HighEndpointPhase, mul_comm]

theorem cutoff44HighExponentialCore_left_endpoint
    (j : Cutoff44HighIndex) :
    cutoff44HighExponentialCore j (-suzukiProjectAStar) =
      cutoff44HighEndpointPhase j *
        (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) := by
  let c : Complex := Complex.I *
    (((-j.1 : Int) : Complex) * (Real.pi : Complex) /
      (suzukiProjectAStar : Complex))
  have hexp : Complex.exp (c * (-suzukiProjectAStar)) =
      ((-1 : Complex) ^ (j.1 : Int)) := by
    calc
      Complex.exp (c * (-suzukiProjectAStar)) =
          Complex.exp (((j.1 : Int) : Complex) *
            ((Real.pi : Complex) * Complex.I)) := by
        congr 1
        simp only [c]
        push_cast
        field_simp [suzukiProjectAStar_pos.ne']
      _ = Complex.exp ((Real.pi : Complex) * Complex.I) ^ (j.1 : Int) :=
        Complex.exp_int_mul _ _
      _ = ((-1 : Complex) ^ (j.1 : Int)) := by
        rw [Complex.exp_pi_mul_I]
  unfold cutoff44HighExponentialCore
  rw [Complex.ofReal_neg]
  change (((Real.sqrt (2 * suzukiProjectAStar))⁻¹ : Real) : Complex) *
    Complex.exp (c * (-(suzukiProjectAStar : Complex))) = _
  rw [hexp]
  rw [← Int.cast_negOnePow Complex j.1]
  simp [cutoff44HighEndpointPhase, mul_comm]

@[simp] theorem cutoff44HighEndpointPrimitiveCore_right_endpoint
    (j : Cutoff44HighIndex) :
    cutoff44HighEndpointPrimitiveCore j suzukiProjectAStar = 0 := by
  rw [cutoff44HighEndpointPrimitiveCore,
    cutoff44HighExponentialCore_right_endpoint, sub_self, mul_zero]

@[simp] theorem cutoff44HighEndpointPrimitiveCore_left_endpoint
    (j : Cutoff44HighIndex) :
    cutoff44HighEndpointPrimitiveCore j (-suzukiProjectAStar) = 0 := by
  rw [cutoff44HighEndpointPrimitiveCore,
    cutoff44HighExponentialCore_left_endpoint, sub_self, mul_zero]

/-- The common pointwise norm of the normalized physical modes. -/
def cutoff44HighModeAmplitude : NNReal :=
  ⟨(Real.sqrt (2 * suzukiProjectAStar))⁻¹,
    inv_nonneg.mpr (Real.sqrt_nonneg _)⟩

@[simp] theorem norm_cutoff44HighExponentialCore
    (j : Cutoff44HighIndex) (x : Real) :
    ‖cutoff44HighExponentialCore j x‖ =
      (cutoff44HighModeAmplitude : Real) := by
  unfold cutoff44HighExponentialCore
  rw [norm_mul, Complex.norm_exp]
  have hre : (Complex.I *
      (((-j.1 : Int) : Complex) * (Real.pi : Complex) /
        (suzukiProjectAStar : Complex)) * (x : Complex)).re = 0 := by
    simp
  rw [hre, Real.exp_zero, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |(Real.sqrt (2 * suzukiProjectAStar))⁻¹| =
    (cutoff44HighModeAmplitude : Real)
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rfl

theorem lipschitzWith_cutoff44HighEndpointPrimitiveCore
    (j : Cutoff44HighIndex) :
    LipschitzWith cutoff44HighModeAmplitude
      (cutoff44HighEndpointPrimitiveCore j) := by
  rw [← lipschitzOnWith_univ]
  apply convex_univ.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro x hx
    exact (hasDerivAt_cutoff44HighEndpointPrimitiveCore j x).hasDerivWithinAt
  · intro x hx
    rw [← NNReal.coe_le_coe]
    change ‖cutoff44HighExponentialCore j x‖ ≤
      (cutoff44HighModeAmplitude : Real)
    rw [norm_cutoff44HighExponentialCore]

/-- The endpoint-zero primitive extended constantly from the closed Suzuki
interval.  Both endpoint constants are zero, so this is also its compactly
supported zero extension. -/
theorem cutoff44HighInterval_order :
    -suzukiProjectAStar ≤ suzukiProjectAStar := by
  linarith [suzukiProjectAStar_pos]

def cutoff44HighEndpointPrimitiveRepresentative
    (j : Cutoff44HighIndex) (x : Real) : Complex :=
  Set.IccExtend cutoff44HighInterval_order
    (fun y : Set.Icc (-suzukiProjectAStar) suzukiProjectAStar =>
      cutoff44HighEndpointPrimitiveCore j y.1) x

theorem cutoff44HighEndpointPrimitiveRepresentative_eq_indicator
    (j : Cutoff44HighIndex) (x : Real) :
    cutoff44HighEndpointPrimitiveRepresentative j x =
      (Set.Icc (-suzukiProjectAStar) suzukiProjectAStar).indicator
        (cutoff44HighEndpointPrimitiveCore j) x := by
  let h : -suzukiProjectAStar ≤ suzukiProjectAStar := by
    linarith [suzukiProjectAStar_pos]
  by_cases hx : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
  · rw [Set.indicator_of_mem hx]
    unfold cutoff44HighEndpointPrimitiveRepresentative
    rw [Set.IccExtend_of_mem h _ hx]
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · unfold cutoff44HighEndpointPrimitiveRepresentative
      rw [Set.IccExtend_of_le_left h _ hx.le]
      exact cutoff44HighEndpointPrimitiveCore_left_endpoint j
    · unfold cutoff44HighEndpointPrimitiveRepresentative
      rw [Set.IccExtend_of_right_le h _ hx.le]
      exact cutoff44HighEndpointPrimitiveCore_right_endpoint j

theorem lipschitzWith_cutoff44HighEndpointPrimitiveRepresentative
    (j : Cutoff44HighIndex) :
    LipschitzWith cutoff44HighModeAmplitude
      (cutoff44HighEndpointPrimitiveRepresentative j) := by
  have hrestricted : LipschitzWith cutoff44HighModeAmplitude
      (fun y : Set.Icc (-suzukiProjectAStar) suzukiProjectAStar =>
        cutoff44HighEndpointPrimitiveCore j y.1) := by
    simpa only [Function.comp_def, mul_one] using
      (lipschitzWith_cutoff44HighEndpointPrimitiveCore j).comp
        (LipschitzWith.subtype_val
          (Set.Icc (-suzukiProjectAStar) suzukiProjectAStar))
  have hextended := hrestricted.comp
    (LipschitzWith.projIcc cutoff44HighInterval_order)
  change LipschitzWith cutoff44HighModeAmplitude
    (fun x : Real => cutoff44HighEndpointPrimitiveCore j
      (Set.projIcc (-suzukiProjectAStar) suzukiProjectAStar
        cutoff44HighInterval_order x).1)
  simpa only [Function.comp_def, mul_one] using hextended

theorem hasCompactSupport_cutoff44HighEndpointPrimitiveRepresentative
    (j : Cutoff44HighIndex) :
    HasCompactSupport (cutoff44HighEndpointPrimitiveRepresentative j) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  rw [cutoff44HighEndpointPrimitiveRepresentative_eq_indicator,
    Set.indicator_of_notMem hx]

theorem suzukiYoshidaExponentialFunction_neg_high_eq_indicator_core
    (j : Cutoff44HighIndex) (x : Real) :
    suzukiYoshidaExponentialFunction suzukiProjectAStar (-j.1) x =
      (Set.Icc (-suzukiProjectAStar) suzukiProjectAStar).indicator
        (cutoff44HighExponentialCore j) x := by
  by_cases hx : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
  · simp only [suzukiYoshidaExponentialFunction, Set.indicator_of_mem hx,
      cutoff44HighExponentialCore]
    push_cast
    rfl
  · simp [suzukiYoshidaExponentialFunction, hx]

theorem ae_hasDerivAt_cutoff44HighEndpointPrimitiveRepresentative
    (j : Cutoff44HighIndex) :
    ∀ᵐ x ∂(volume : Measure Real),
      HasDerivAt (cutoff44HighEndpointPrimitiveRepresentative j)
        (suzukiYoshidaExponentialFunction suzukiProjectAStar (-j.1) x) x := by
  filter_upwards [(volume : Measure Real).ae_ne (-suzukiProjectAStar),
    (volume : Measure Real).ae_ne suzukiProjectAStar] with x hxLeft hxRight
  rw [suzukiYoshidaExponentialFunction_neg_high_eq_indicator_core]
  by_cases hx : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
  · rw [Set.indicator_of_mem hx]
    have hxOpen : x ∈ Set.Ioo (-suzukiProjectAStar) suzukiProjectAStar :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxLeft),
        lt_of_le_of_ne hx.2 hxRight⟩
    have heq : cutoff44HighEndpointPrimitiveRepresentative j =ᶠ[nhds x]
        cutoff44HighEndpointPrimitiveCore j := by
      filter_upwards [isOpen_Ioo.mem_nhds hxOpen] with y hy
      unfold cutoff44HighEndpointPrimitiveRepresentative
      rw [Set.IccExtend_of_mem cutoff44HighInterval_order _
        ⟨hy.1.le, hy.2.le⟩]
    exact (hasDerivAt_cutoff44HighEndpointPrimitiveCore j x).congr_of_eventuallyEq heq
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have heq : cutoff44HighEndpointPrimitiveRepresentative j =ᶠ[nhds x]
          (fun _ : Real => (0 : Complex)) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
        unfold cutoff44HighEndpointPrimitiveRepresentative
        rw [Set.IccExtend_of_le_left cutoff44HighInterval_order _ hy.le,
          cutoff44HighEndpointPrimitiveCore_left_endpoint]
      exact (hasDerivAt_const x (0 : Complex)).congr_of_eventuallyEq heq
    · have heq : cutoff44HighEndpointPrimitiveRepresentative j =ᶠ[nhds x]
          (fun _ : Real => (0 : Complex)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        unfold cutoff44HighEndpointPrimitiveRepresentative
        rw [Set.IccExtend_of_right_le cutoff44HighInterval_order _ hy.le,
          cutoff44HighEndpointPrimitiveCore_right_endpoint]
      exact (hasDerivAt_const x (0 : Complex)).congr_of_eventuallyEq heq

theorem cutoff44HighEndpointPrimitiveRepresentative_eq_modeFunction
    (j : Cutoff44HighIndex) (x : Real) :
    cutoff44HighEndpointPrimitiveRepresentative j x =
      cutoff44HighPrimitiveMultiplier j *
        (suzukiYoshidaExponentialFunction suzukiProjectAStar (-j.1) x -
          cutoff44HighEndpointPhase j *
            suzukiYoshidaExponentialFunction suzukiProjectAStar 0 x) := by
  rw [cutoff44HighEndpointPrimitiveRepresentative_eq_indicator]
  by_cases hx : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
  · simp only [Set.indicator_of_mem hx, cutoff44HighEndpointPrimitiveCore,
      suzukiYoshidaExponentialFunction, cutoff44HighExponentialCore]
    push_cast
    simp
  · simp [suzukiYoshidaExponentialFunction, hx]

theorem cutoff44HighEndpointPrimitiveRepresentative_memLp
    (j : Cutoff44HighIndex) :
    MemLp (cutoff44HighEndpointPrimitiveRepresentative j)
      (2 : ENNReal) (volume : Measure Real) :=
  (lipschitzWith_cutoff44HighEndpointPrimitiveRepresentative j).continuous
    |>.memLp_of_hasCompactSupport
      (hasCompactSupport_cutoff44HighEndpointPrimitiveRepresentative j)

theorem norm_suzukiYoshidaExponentialFunction_neg_high_le_amplitude
    (j : Cutoff44HighIndex) :
    ∀ᵐ x ∂(volume : Measure Real),
      ‖suzukiYoshidaExponentialFunction suzukiProjectAStar (-j.1) x‖ ≤
        (cutoff44HighModeAmplitude : Real) := by
  filter_upwards with x
  rw [suzukiYoshidaExponentialFunction_neg_high_eq_indicator_core]
  by_cases hx : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
  · rw [Set.indicator_of_mem hx, norm_cutoff44HighExponentialCore]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact cutoff44HighModeAmplitude.coe_nonneg

theorem cutoff44HighEndpointPrimitiveRepresentative_toLp_eq
    (j : Cutoff44HighIndex) :
    (cutoff44HighEndpointPrimitiveRepresentative_memLp j).toLp
        (cutoff44HighEndpointPrimitiveRepresentative j) =
      cutoff44HighEndpointPrimitiveMode j := by
  let E0 : SuzukiL2 := suzukiYoshidaExponentialL2 suzukiProjectAStar
    suzukiProjectAStar_pos 0
  have hrep := (cutoff44HighEndpointPrimitiveRepresentative_memLp j).coeFn_toLp
  have houter := Lp.coeFn_smul (cutoff44HighPrimitiveMultiplier j)
    (cutoff44HighExponential j - cutoff44HighEndpointPhase j • E0)
  have hsub := Lp.coeFn_sub (cutoff44HighExponential j)
    (cutoff44HighEndpointPhase j • E0)
  have hphase := Lp.coeFn_smul (cutoff44HighEndpointPhase j) E0
  have hhigh := suzukiYoshidaExponentialL2_coeFn
    suzukiProjectAStar_pos (-j.1)
  have hzero := suzukiYoshidaExponentialL2_coeFn
    suzukiProjectAStar_pos 0
  apply Lp.ext
  filter_upwards [hrep, houter, hsub, hphase, hhigh, hzero] with x
      hxRep hxOuter hxSub hxPhase hxHigh hxZero
  rw [cutoff44HighEndpointPrimitiveMode]
  rw [hxRep, hxOuter]
  change cutoff44HighEndpointPrimitiveRepresentative j x =
    cutoff44HighPrimitiveMultiplier j *
      ((cutoff44HighExponential j - cutoff44HighEndpointPhase j • E0 : SuzukiL2) :
        Real → Complex) x
  rw [hxSub]
  change cutoff44HighEndpointPrimitiveRepresentative j x =
    cutoff44HighPrimitiveMultiplier j *
      ((cutoff44HighExponential j : Real → Complex) x -
        ((cutoff44HighEndpointPhase j • E0 : SuzukiL2) : Real → Complex) x)
  rw [hxPhase]
  change cutoff44HighEndpointPrimitiveRepresentative j x =
    cutoff44HighPrimitiveMultiplier j *
      ((cutoff44HighExponential j : Real → Complex) x -
        cutoff44HighEndpointPhase j * (E0 : Real → Complex) x)
  rw [show (cutoff44HighExponential j : Real → Complex) x =
      suzukiYoshidaExponentialFunction suzukiProjectAStar (-j.1) x by
        exact hxHigh,
    show (E0 : Real → Complex) x =
      suzukiYoshidaExponentialFunction suzukiProjectAStar 0 x by
        exact hxZero]
  exact cutoff44HighEndpointPrimitiveRepresentative_eq_modeFunction j x

/-- Every single endpoint-zero cutoff-44 mode is a strong spatial primitive
of its corresponding physical exponential under the global translation
action. -/
theorem suzukiL2TranslationPrimitiveDerivative_cutoff44HighEndpointPrimitiveMode
    (j : Cutoff44HighIndex) :
    SuzukiL2TranslationPrimitiveDerivative
      (cutoff44HighEndpointPrimitiveMode j) (cutoff44HighExponential j) := by
  intro t
  have h := hasDerivAt_suzukiL2Translate_of_lipschitz
    (lipschitzWith_cutoff44HighEndpointPrimitiveRepresentative j)
    (hasCompactSupport_cutoff44HighEndpointPrimitiveRepresentative j)
    (suzukiYoshidaExponentialFunction_memLp suzukiProjectAStar_pos (-j.1))
    (norm_suzukiYoshidaExponentialFunction_neg_high_le_amplitude j)
    (ae_hasDerivAt_cutoff44HighEndpointPrimitiveRepresentative j) t
  rw [cutoff44HighEndpointPrimitiveRepresentative_toLp_eq] at h
  simpa only [cutoff44HighExponential, suzukiYoshidaExponentialL2] using h

theorem suzukiL2TranslationPrimitiveDerivative_finset_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (H v : ι → SuzukiL2)
    (h : ∀ i ∈ s, SuzukiL2TranslationPrimitiveDerivative (H i) (v i)) :
    SuzukiL2TranslationPrimitiveDerivative
      (∑ i ∈ s, H i) (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using suzukiL2TranslationPrimitiveDerivative_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The finite translation-derivative problem reduces to the corresponding
single endpoint-zero mode statement. -/
theorem suzukiL2TranslationPrimitiveDerivative_finite_of_modes
    (l : Cutoff44HighIndex →₀ Complex)
    (hmodes : ∀ j ∈ l.support,
      SuzukiL2TranslationPrimitiveDerivative
        (cutoff44HighEndpointPrimitiveMode j) (cutoff44HighExponential j)) :
    SuzukiL2TranslationPrimitiveDerivative
      (cutoff44HighEndpointPrimitive l)
      (Finsupp.linearCombination Complex cutoff44HighExponential l) := by
  have hsum := suzukiL2TranslationPrimitiveDerivative_finset_sum l.support
    (fun j => l j • cutoff44HighEndpointPrimitiveMode j)
    (fun j => l j • cutoff44HighExponential j)
    (fun j hj => (hmodes j hj).smul (l j))
  change SuzukiL2TranslationPrimitiveDerivative
    (Finsupp.linearCombination Complex cutoff44HighEndpointPrimitiveMode l)
    (Finsupp.linearCombination Complex cutoff44HighExponential l) at hsum
  change SuzukiL2TranslationPrimitiveDerivative
    (cutoff44HighEndpointPrimitiveLinearMap l)
    (Finsupp.linearCombination Complex cutoff44HighExponential l) at hsum
  rw [cutoff44HighEndpointPrimitiveLinearMap_apply] at hsum
  exact hsum

theorem suzukiL2TranslationPrimitiveDerivative_finite
    (l : Cutoff44HighIndex →₀ Complex) :
    SuzukiL2TranslationPrimitiveDerivative
      (cutoff44HighEndpointPrimitive l)
      (Finsupp.linearCombination Complex cutoff44HighExponential l) :=
  suzukiL2TranslationPrimitiveDerivative_finite_of_modes l
    (fun j hj =>
      suzukiL2TranslationPrimitiveDerivative_cutoff44HighEndpointPrimitiveMode j)

theorem hasDerivAt_suzukiL2SymmetricCorrelationPrimitive
    {H v : SuzukiL2}
    (hprimitive : SuzukiL2TranslationPrimitiveDerivative H v)
    (t : Real) :
    HasDerivAt (suzukiL2SymmetricCorrelationPrimitive H v)
      (-suzukiL2SymmetricTranslationEnergy t v v) t := by
  have htranslateH := hprimitive t
  have hfirst := htranslateH.inner Complex
    (hasDerivAt_const t v)
  have hsecond := (hasDerivAt_const t v).inner Complex htranslateH
  change HasDerivAt
    (fun s => -(inner Complex (suzukiL2Translate s H) v +
      inner Complex v (suzukiL2Translate s H)))
    (-(inner Complex (suzukiL2Translate t v) v +
      inner Complex v (suzukiL2Translate t v))) t
  refine (((hfirst.add hsecond).neg).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [inner_zero_right, inner_zero_left, zero_add, add_zero]
  · filter_upwards with s
    rfl

/-- Two `L²` functions supported in the same symmetric interval have zero
inner product after a positive translation by at least the interval diameter.
At equality the supports meet only at the left endpoint, a null set. -/
theorem inner_suzukiL2Translate_eq_zero_of_supportedAt_of_two_mul_le
    {r t : Real} (hrt : 2 * r ≤ t) {u v : SuzukiL2}
    (hu : suzukiL2SupportedAt r u) (hv : suzukiL2SupportedAt r v) :
    inner Complex (suzukiL2Translate t u) v = 0 := by
  have huShift :
      ∀ᵐ x ∂(volume : Measure Real),
        x + t ∉ Icc (-r) r → u (x + t) = 0 :=
    (measurePreserving_add_right
      (volume : Measure Real) t).quasiMeasurePreserving.ae hu
  have htranslate :
      (suzukiL2Translate t u : Real → Complex) =ᵐ[volume]
        (u : Real → Complex) ∘ fun x ↦ x + t := by
    simpa only [suzukiL2Translate] using
      (Lp.coeFn_compMeasurePreserving u
        (measurePreserving_add_right (volume : Measure Real) t))
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [huShift, hv, htranslate, volume.ae_ne (-r)] with
    x hux hvx htx hxEndpoint
  rw [htx]
  simp only [Function.comp_apply]
  by_cases hx : x ∈ Icc (-r) r
  · have hxShift : x + t ∉ Icc (-r) r := by
      intro hxt
      have hxEq : x = -r := by
        linarith [hx.1, hxt.2]
      exact hxEndpoint hxEq
    rw [hux hxShift]
    simp
  · rw [hvx hx]
    simp

theorem cutoff44HighFiniteCombination_mem_supportedSubmodule
    (l : Cutoff44HighIndex →₀ Complex) :
    Finsupp.linearCombination Complex cutoff44HighExponential l ∈
      suzukiL2SupportedSubmodule suzukiProjectAStar := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro j hj
  apply (suzukiL2SupportedSubmodule suzukiProjectAStar).smul_mem
  exact suzukiYoshidaExponentialL2_mem_supportedSubmodule
    suzukiProjectAStar_pos (-j.1)

theorem cutoff44HighEndpointPrimitive_mem_supportedSubmodule
    (l : Cutoff44HighIndex →₀ Complex) :
    cutoff44HighEndpointPrimitive l ∈
      suzukiL2SupportedSubmodule suzukiProjectAStar := by
  unfold cutoff44HighEndpointPrimitive cutoff44HighPeriodicPrimitive
  apply (suzukiL2SupportedSubmodule suzukiProjectAStar).sub_mem
  · exact cutoff44HighFiniteCombination_mem_supportedSubmodule _
  · apply (suzukiL2SupportedSubmodule suzukiProjectAStar).smul_mem
    exact suzukiYoshidaExponentialL2_mem_supportedSubmodule
      suzukiProjectAStar_pos 0

theorem inner_cutoff44HighConstant_finiteCombination
    (l : Cutoff44HighIndex →₀ Complex) :
    inner Complex
        (suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos 0)
        (Finsupp.linearCombination Complex cutoff44HighExponential l) = 0 := by
  have hortho := orthonormal_iff_ite.mp
    (orthonormal_suzukiYoshidaExponentialL2 suzukiProjectAStar_pos)
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [inner_sum, inner_smul_right]
  apply Finset.sum_eq_zero
  intro j hj
  have hmode : (0 : Int) ≠ -j.1 := by
    intro h
    exact cutoff44HighIndex_ne_zero j (neg_eq_zero.mp h.symm)
  have hinner := hortho 0 (-j.1)
  rw [if_neg hmode] at hinner
  rw [cutoff44HighExponential, hinner, mul_zero]

theorem re_inner_cutoff44HighPeriodicPrimitive_finiteCombination
    (l : Cutoff44HighIndex →₀ Complex) :
    (inner Complex (cutoff44HighPeriodicPrimitive l)
      (Finsupp.linearCombination Complex cutoff44HighExponential l)).re = 0 := by
  have hinner :=
    orthonormal_cutoff44HighExponential.inner_finsupp_eq_sum_left
      (cutoff44HighPrimitiveCoefficients l) l
  change inner Complex (cutoff44HighPeriodicPrimitive l)
    (Finsupp.linearCombination Complex cutoff44HighExponential l) = _ at hinner
  rw [hinner, Finsupp.sum, Complex.re_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [cutoff44HighPrimitiveCoefficients_apply]
  unfold cutoff44HighPrimitiveMultiplier
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.neg_re,
    Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, one_mul, neg_mul, sub_zero, add_zero, zero_add]
  ring

theorem suzukiL2SymmetricCorrelationPrimitive_zero
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiL2SymmetricCorrelationPrimitive
        (cutoff44HighEndpointPrimitive l)
        (Finsupp.linearCombination Complex cutoff44HighExponential l) 0 = 0 := by
  let v : SuzukiL2 :=
    Finsupp.linearCombination Complex cutoff44HighExponential l
  let H : SuzukiL2 := cutoff44HighEndpointPrimitive l
  have hconstant :
      inner Complex
        (cutoff44HighPrimitiveEndpointCoefficient l •
          suzukiYoshidaExponentialL2 suzukiProjectAStar
            suzukiProjectAStar_pos 0) v = 0 := by
    rw [inner_smul_left,
      inner_cutoff44HighConstant_finiteCombination l, mul_zero]
  have hHre : (inner Complex H v).re = 0 := by
    unfold H v cutoff44HighEndpointPrimitive
    rw [inner_sub_left, hconstant, sub_zero]
    exact re_inner_cutoff44HighPeriodicPrimitive_finiteCombination l
  unfold suzukiL2SymmetricCorrelationPrimitive
  rw [suzukiL2Translate_zero]
  rw [← inner_conj_symm v H]
  rw [Complex.add_conj, hHre]
  simp

theorem suzukiL2SymmetricCorrelationPrimitive_two_mul_aStar
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiL2SymmetricCorrelationPrimitive
        (cutoff44HighEndpointPrimitive l)
        (Finsupp.linearCombination Complex cutoff44HighExponential l)
        (2 * suzukiProjectAStar) = 0 := by
  have hinner :=
    inner_suzukiL2Translate_eq_zero_of_supportedAt_of_two_mul_le
      (r := suzukiProjectAStar) (t := 2 * suzukiProjectAStar) le_rfl
      (cutoff44HighEndpointPrimitive_mem_supportedSubmodule l)
      (cutoff44HighFiniteCombination_mem_supportedSubmodule l)
  unfold suzukiL2SymmetricCorrelationPrimitive
  rw [hinner]
  have hreverse :
      inner Complex
        (Finsupp.linearCombination Complex cutoff44HighExponential l)
        (suzukiL2Translate (2 * suzukiProjectAStar)
          (cutoff44HighEndpointPrimitive l)) = 0 := by
    rw [← inner_conj_symm, hinner]
    simp
  rw [hreverse]
  simp

/-! ## Finite high-mode global-operator identification -/

/-- The globally smooth trigonometric polynomial underlying a finite
cutoff-44 combination before zero extension to the Suzuki interval. -/
def cutoff44HighExponentialLinearCombinationCore
    (l : Cutoff44HighIndex →₀ Complex) (x : Real) : Complex :=
  ∑ j ∈ l.support, l j * cutoff44HighExponentialCore j x

theorem continuous_cutoff44HighExponentialCore
    (j : Cutoff44HighIndex) :
    Continuous (cutoff44HighExponentialCore j) := by
  unfold cutoff44HighExponentialCore
  fun_prop

theorem continuous_cutoff44HighExponentialLinearCombinationCore
    (l : Cutoff44HighIndex →₀ Complex) :
    Continuous (cutoff44HighExponentialLinearCombinationCore l) := by
  unfold cutoff44HighExponentialLinearCombinationCore
  exact continuous_finset_sum _ fun j _ =>
    continuous_const.mul (continuous_cutoff44HighExponentialCore j)

/-- The same polynomial bundled on the compact interval. -/
def cutoff44HighExponentialFiniteIntervalContinuous
    (l : Cutoff44HighIndex →₀ Complex) :
    C(SuzukiFiniteInterval suzukiProjectAStar, Complex) :=
  suzukiFiniteIntervalRestriction suzukiProjectAStar
    (cutoff44HighExponentialLinearCombinationCore l)
    (continuous_cutoff44HighExponentialLinearCombinationCore l)

/-- A finite high-mode combination is the zero extension of its smooth
trigonometric polynomial representative. -/
theorem cutoff44HighExponential_linearCombination_coe_ae
    (l : Cutoff44HighIndex →₀ Complex) :
    ((Finsupp.linearCombination Complex cutoff44HighExponential l : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      Set.indicator (Set.Icc (-suzukiProjectAStar) suzukiProjectAStar)
        (cutoff44HighExponentialLinearCombinationCore l) := by
  rw [Finsupp.linearCombination_apply]
  change
    (((∑ j ∈ l.support, l j • cutoff44HighExponential j : SuzukiL2) :
        Real → Complex)) =ᵐ[volume] _
  have hsum := MeasureTheory.Lp.coeFn_finsetSum l.support
    (fun j => l j • cutoff44HighExponential j)
  have hsmul : ∀ᵐ x ∂(volume : Measure Real), ∀ j,
      ((l j • cutoff44HighExponential j : SuzukiL2) x) =
        l j * (cutoff44HighExponential j x) := by
    apply ae_all_iff.mpr
    intro j
    exact MeasureTheory.Lp.coeFn_smul (l j) (cutoff44HighExponential j)
  have hmodes : ∀ᵐ x ∂(volume : Measure Real), ∀ j,
      cutoff44HighExponential j x =
        Set.indicator (Set.Icc (-suzukiProjectAStar) suzukiProjectAStar)
          (cutoff44HighExponentialCore j) x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(suzukiYoshidaExponentialL2_coeFn
      suzukiProjectAStar_pos (-j.1))] with x hx
    rw [cutoff44HighExponential, hx]
    unfold suzukiYoshidaExponentialFunction cutoff44HighExponentialCore
    by_cases hxi : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
    · simp only [Set.indicator_of_mem hxi]
      push_cast
      rfl
    · simp [Set.indicator_of_notMem hxi]
  filter_upwards [hsum, hsmul, hmodes] with x hsumx hsmulx hmodesx
  rw [hsumx]
  simp only [Finset.sum_apply]
  unfold cutoff44HighExponentialLinearCombinationCore
  by_cases hx : x ∈ Set.Icc (-suzukiProjectAStar) suzukiProjectAStar
  · rw [Set.indicator_of_mem hx]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsmulx j, hmodesx j, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_eq_zero
    intro j hj
    rw [hsmulx j, hmodesx j, Set.indicator_of_notMem hx, mul_zero]

/-- Restriction forgets the endpoint jumps and recovers the literal
continuous trigonometric polynomial on the compact interval. -/
theorem suzukiL2RestrictToFiniteInterval_cutoff44HighLinearCombination
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiL2RestrictToFiniteInterval suzukiProjectAStar
        (Finsupp.linearCombination Complex cutoff44HighExponential l) =
      suzukiFiniteIntervalContinuousToL2 suzukiProjectAStar
        (cutoff44HighExponentialFiniteIntervalContinuous l) := by
  apply suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
    (u := Finsupp.linearCombination Complex cutoff44HighExponential l)
    (g := Set.indicator
      (Set.Icc (-suzukiProjectAStar) suzukiProjectAStar)
      (cutoff44HighExponentialLinearCombinationCore l))
    (f := cutoff44HighExponentialFiniteIntervalContinuous l)
    (cutoff44HighExponential_linearCombination_coe_ae l)
  intro x
  rw [Set.indicator_of_mem x.2]
  rfl

/-- On a finite cutoff-44 combination, the live global `r''` energy is the
conjugate finite-square kernel polarization of its smooth interval
representative. -/
theorem suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighLinearCombination
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (Finsupp.linearCombination Complex cutoff44HighExponential l)
        (Finsupp.linearCombination Complex cutoff44HighExponential l) =
      conj (suzukiFiniteKernelPolarizationComplex suzukiRSecondKernel
        suzukiProjectAStar
        (cutoff44HighExponentialLinearCombinationCore l)
        (cutoff44HighExponentialLinearCombinationCore l)) := by
  unfold suzukiL2BoundedOperatorEnergy
  rw [inner_suzukiRSecondGlobalL2Operator,
    suzukiL2RestrictToFiniteInterval_cutoff44HighLinearCombination]
  unfold cutoff44HighExponentialFiniteIntervalContinuous
  rw [inner_suzukiRSecondFiniteIntervalL2Operator_continuous,
    suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
      continuous_suzukiRSecondKernel
      (continuous_cutoff44HighExponentialLinearCombinationCore l)
      (continuous_cutoff44HighExponentialLinearCombinationCore l),
    suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiRSecondKernel
      (continuous_cutoff44HighExponentialLinearCombinationCore l)
      (continuous_cutoff44HighExponentialLinearCombinationCore l)]

/-- For a continuous function cut off to `[-a,a]`, the compact physical
translation pairing is exactly the finite-square kernel polarization.  This
is the endpoint-jump version of the smooth-core bridge. -/
theorem suzukiRSecondCompactL2CrossCorrelationPairing_eq_finiteKernel_of_indicator
    {a : Real} (ha : 0 ≤ a) (u : SuzukiL2) (f : Real → Complex)
    (hf : Continuous f)
    (hu : (u : Real → Complex) =ᵐ[volume]
      Set.indicator (Set.Icc (-a) a) f) :
    suzukiRSecondCompactL2CrossCorrelationPairing a u u =
      suzukiFiniteKernelPolarizationComplex suzukiRSecondKernel a f f := by
  let U : Real → Complex := Set.indicator (Set.Icc (-a) a) f
  let F : Real → Real → Complex := fun x y =>
    suzukiRSecondCompactKernel a (x - y) * U y * conj (U x)
  let G : Real → Real → Complex := fun y t =>
    suzukiRSecondCompactKernel a t * U y * conj (U (t + y))
  let C : Real → Complex := fun t =>
    ∫ y : Real, U y * conj (U (y - t))
  have hU : Integrable U := by
    unfold U
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hf.continuousOn.integrableOn_compact isCompact_Icc
  have hconjU : Integrable (fun x : Real => conj (U x)) := by
    have hcomp := Complex.conjCLE.toContinuousLinearMap.integrable_comp hU
    change Integrable (fun x : Real => Complex.conjCLE (U x))
    exact hcomp
  have hseparable : Integrable (fun p : Real × Real =>
      U p.2 * conj (U p.1)) (volume.prod volume) := by
    have hprod := hconjU.mul_prod hU
    apply hprod.congr
    filter_upwards with p
    ring
  have hFraw : Integrable (fun p : Real × Real =>
      suzukiRSecondCompactKernel a (p.1 - p.2) *
        (U p.2 * conj (U p.1))) (volume.prod volume) := by
    apply hseparable.bdd_mul
        (c := ‖suzukiRSecondCompactKernelContinuousMap a‖)
    · exact ((measurable_suzukiRSecondCompactKernel a).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.1 - p.2)))
          |>.aestronglyMeasurable
    · filter_upwards with p
      exact norm_suzukiRSecondCompactKernel_le a (p.1 - p.2)
  have hF : Integrable (fun p : Real × Real => F p.1 p.2)
      (volume.prod volume) := by
    simpa only [F, mul_assoc] using hFraw
  have hcoupled : Integrable (fun p : Real × Real =>
      U p.1 * conj (U (p.2 + p.1))) (volume.prod volume) := by
    let H : Real × Real → Complex := fun p => U p.1 * conj (U p.2)
    have hH : Integrable H := hU.mul_prod hconjU
    have hcomp :=
      (measurePreserving_prod_add_right
        (volume : Measure Real) (volume : Measure Real))
          |>.integrable_comp_of_integrable hH
    change Integrable (fun p : Real × Real =>
      U p.1 * conj (U (p.2 + p.1))) (volume.prod volume) at hcomp
    exact hcomp
  have hGraw : Integrable (fun p : Real × Real =>
      suzukiRSecondCompactKernel a p.2 *
        (U p.1 * conj (U (p.2 + p.1))))
      (volume.prod volume) := by
    apply hcoupled.bdd_mul
        (c := ‖suzukiRSecondCompactKernelContinuousMap a‖)
    · exact ((measurable_suzukiRSecondCompactKernel a).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.2)))
          |>.aestronglyMeasurable
    · filter_upwards with p
      exact norm_suzukiRSecondCompactKernel_le a p.2
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
      simp [F, U, hy]
    · simp [F, U, hx]
  have hfiber (y : Real) :
      (∫ x : Real, F x y) = ∫ t : Real, G y t := by
    have htranslate := integral_sub_right_eq_self
      (fun t : Real => G y t) y (μ := volume)
    simpa only [F, G, sub_add_cancel] using htranslate
  have hphysicalNeg :
      (∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume)) =
        ∫ t : Real, suzukiRSecondCompactKernel a t * C (-t) := by
    rw [MeasureTheory.integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G]
    rw [show (fun y : Real =>
        suzukiRSecondCompactKernel a t * U y * conj (U (t + y))) =
          fun y : Real => suzukiRSecondCompactKernel a t *
            (U y * conj (U (t + y))) by
        funext y
        ring]
    rw [integral_const_mul]
    apply congrArg (fun z : Complex => suzukiRSecondCompactKernel a t * z)
    unfold C
    apply integral_congr_ae
    filter_upwards with y
    congr 3
    ring
  have hcorrelation (t : Real) :
      conj (inner Complex (suzukiL2Translate t u) u) = C t := by
    rw [inner_suzukiL2Translate_eq_integral_of_ae_two t u u U U hu hu,
      ← integral_conj]
    have htranslate := integral_add_right_eq_self
      (fun y : Real => U y * conj (U (y - t))) t (μ := volume)
    calc
      (∫ x : Real, conj (U x * conj (U (x + t)))) =
          ∫ x : Real, U (x + t) * conj (U x) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [map_mul, map_star, star_star, Complex.conj_conj]
        ring
      _ = ∫ y : Real, U y * conj (U (y - t)) := by
        simpa only [add_sub_cancel_right] using htranslate
      _ = C t := rfl
  have hreflect := integral_neg_eq_self
    (f := fun t : Real => suzukiRSecondCompactKernel a t * C t) volume
  have hphysical :
      (∫ t : Real, suzukiRSecondCompactKernel a t * C (-t)) =
        ∫ t : Real, suzukiRSecondCompactKernel a t * C t := by
    simpa only [suzukiRSecondCompactKernel_neg, neg_neg] using hreflect
  unfold suzukiRSecondCompactL2CrossCorrelationPairing
  calc
    (∫ t : Real, suzukiRSecondCompactKernel a t *
        conj (inner Complex (suzukiL2Translate t u) u)) =
        ∫ t : Real, suzukiRSecondCompactKernel a t * C t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [hcorrelation]
    _ = ∫ t : Real, suzukiRSecondCompactKernel a t * C (-t) :=
      hphysical.symm
    _ = ∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume) :=
      hphysicalNeg.symm
    _ = ∫ y : Real, ∫ t : Real, G y t :=
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
    _ = suzukiFiniteKernelPolarizationComplex suzukiRSecondKernel a f f := by
      unfold suzukiFiniteKernelPolarizationComplex
      apply setIntegral_congr_fun
        (isCompact_suzukiFiniteSquare a).measurableSet
      intro p hp
      change F p.1 p.2 =
        (suzukiRSecondKernel (p.1 - p.2) : Complex) *
          f p.2 * conj (f p.1)
      dsimp only [F]
      rw [suzukiRSecondCompactKernel_sub_eq ha hp.1 hp.2]
      simp only [U, Set.indicator_of_mem hp.1,
        Set.indicator_of_mem hp.2]

/-- The global bounded-operator energy and the positive-interval symmetric
translation integral agree on every finite cutoff-44 combination. -/
theorem suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighLinearCombination_eq_interval
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (Finsupp.linearCombination Complex cutoff44HighExponential l)
        (Finsupp.linearCombination Complex cutoff44HighExponential l) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (Finsupp.linearCombination Complex cutoff44HighExponential l)
            (Finsupp.linearCombination Complex cutoff44HighExponential l) := by
  rw [suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighLinearCombination,
    ← suzukiRSecondCompactL2CrossCorrelationPairing_eq_finiteKernel_of_indicator
      suzukiProjectAStar_pos.le
      (Finsupp.linearCombination Complex cutoff44HighExponential l)
      (cutoff44HighExponentialLinearCombinationCore l)
      (continuous_cutoff44HighExponentialLinearCombinationCore l)
      (cutoff44HighExponential_linearCombination_coe_ae l),
    conj_suzukiRSecondCompactL2CrossCorrelationPairing_eq_interval]

theorem intervalIntegrable_suzukiRThirdKernel_project :
    IntervalIntegrable suzukiRThirdKernel volume 0
      (2 * suzukiProjectAStar) := by
  have hL : (0 : Real) ≤ 2 * suzukiProjectAStar := by
    exact mul_nonneg (by norm_num) suzukiProjectAStar_pos.le
  have hfU : ContinuousOn suzukiRSecondKernel
      (uIcc (0 : Real) (2 * suzukiProjectAStar)) :=
    continuous_suzukiRSecondKernel.continuousOn
  have hderivU : ∀ x ∈ Ioo
      (min (0 : Real) (2 * suzukiProjectAStar))
      (max (0 : Real) (2 * suzukiProjectAStar)),
      HasDerivAt suzukiRSecondKernel (suzukiRThirdKernel x) x := by
    intro x hx
    apply hasDerivAt_suzukiRSecondKernel_of_pos
    rw [min_eq_left hL, max_eq_right hL] at hx
    exact hx.1
  have hnonposU : ∀ x ∈ Ioo
      (min (0 : Real) (2 * suzukiProjectAStar))
      (max (0 : Real) (2 * suzukiProjectAStar)),
      suzukiRThirdKernel x ≤ 0 := by
    intro x hx
    apply suzukiRThirdKernel_nonpos_on_project_interval
    rw [min_eq_left hL, max_eq_right hL] at hx
    exact ⟨hx.1, hx.2.le⟩
  have hcomposed :
      IntervalIntegrable
        (fun x : Real => ((fun _ : Real => 1) ∘ suzukiRSecondKernel) x *
          suzukiRThirdKernel x) volume 0 (2 * suzukiProjectAStar) :=
    (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
      (g := fun _ : Real => 1) hfU hderivU hnonposU).2
        intervalIntegrable_const
  simpa using hcomposed

theorem integral_neg_suzukiRThirdKernel_project :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        -suzukiRThirdKernel t) =
      suzukiDF6D4DF0RemainderVariation / 2 := by
  have hL : (0 : Real) ≤ 2 * suzukiProjectAStar := by
    exact mul_nonneg (by norm_num) suzukiProjectAStar_pos.le
  have hfundamental :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRThirdKernel t) =
        suzukiRSecondKernel (2 * suzukiProjectAStar) -
          suzukiRSecondKernel 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
      continuous_suzukiRSecondKernel.continuousOn
      (fun t ht => hasDerivAt_suzukiRSecondKernel_of_pos ht.1)
      intervalIntegrable_suzukiRThirdKernel_project
  rw [intervalIntegral.integral_neg, hfundamental,
    suzukiRSecondKernel_two_mul_aStar_eq_DF0RemainderSecondDerivative,
    suzukiRSecondKernel_zero]
  unfold suzukiDF6D4DF0RemainderVariation
  ring

/-- Scalar integration by parts with the exact project variation.  The
function `q` is the correlation primitive: its derivative is the negative
symmetric translation energy, it vanishes at the two support endpoints, and
its norm is controlled by Cauchy--Schwarz. -/
theorem norm_intervalIntegral_rSecond_mul_le_of_correlationPrimitive
    (G q : Real → Complex) (primitiveNorm vectorNorm : Real)
    (hqContinuous : ContinuousOn q
      (Icc (0 : Real) (2 * suzukiProjectAStar)))
    (hqDeriv : ∀ t ∈ Ioo (0 : Real) (2 * suzukiProjectAStar),
      HasDerivAt q (-G t) t)
    (hGIntegrable : IntervalIntegrable G volume 0
      (2 * suzukiProjectAStar))
    (hqZero : q 0 = 0)
    (hqEndpoint : q (2 * suzukiProjectAStar) = 0)
    (hqBound : ∀ t ∈ Icc (0 : Real) (2 * suzukiProjectAStar),
      ‖q t‖ ≤ 2 * primitiveNorm * vectorNorm) :
    ‖∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) * G t‖ ≤
      suzukiDF6D4DF0RemainderVariation * primitiveNorm * vectorNorm := by
  let f : Real → Complex := fun t => (suzukiRSecondKernel t : Complex)
  let f' : Real → Complex := fun t => (suzukiRThirdKernel t : Complex)
  have hL : (0 : Real) ≤ 2 * suzukiProjectAStar := by
    exact mul_nonneg (by norm_num) suzukiProjectAStar_pos.le
  have hfContinuous : ContinuousOn f
      (Icc (0 : Real) (2 * suzukiProjectAStar)) :=
    (Complex.continuous_ofReal.comp continuous_suzukiRSecondKernel).continuousOn
  have hfDeriv : ∀ t ∈ Ioo (0 : Real) (2 * suzukiProjectAStar),
      HasDerivAt f (f' t) t := by
    intro t ht
    exact Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_suzukiRSecondKernel_of_pos ht.1)
  have hf'Integrable : IntervalIntegrable f' volume 0
      (2 * suzukiProjectAStar) := by
    apply (IntervalIntegrable.intervalIntegrable_norm_iff ?_).mp
    · simpa only [f', Complex.norm_real, Real.norm_eq_abs] using
        intervalIntegrable_suzukiRThirdKernel_project.abs
    · exact (Complex.measurable_ofReal.comp
        (measurable_deriv suzukiRSecondKernel)).aestronglyMeasurable
  have hq'Integrable : IntervalIntegrable (fun t => -G t) volume 0
      (2 * suzukiProjectAStar) := hGIntegrable.neg
  have hfContinuousU : ContinuousOn f
      (uIcc (0 : Real) (2 * suzukiProjectAStar)) := by
    simpa [uIcc_of_le hL] using hfContinuous
  have hqContinuousU : ContinuousOn q
      (uIcc (0 : Real) (2 * suzukiProjectAStar)) := by
    simpa [uIcc_of_le hL] using hqContinuous
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hfContinuousU hqContinuousU (by
        intro t ht
        apply hfDeriv t
        simpa [min_eq_left hL, max_eq_right hL] using ht) (by
        intro t ht
        apply hqDeriv t
        simpa [min_eq_left hL, max_eq_right hL] using ht)
      hf'Integrable hq'Integrable
  have hidentity :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          (suzukiRSecondKernel t : Complex) * G t) =
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          (suzukiRThirdKernel t : Complex) * q t := by
    dsimp only [f, f'] at hparts
    simp only [mul_neg, hqZero, hqEndpoint, mul_zero, sub_self,
      zero_sub] at hparts
    rw [intervalIntegral.integral_neg] at hparts
    exact neg_inj.mp hparts
  rw [hidentity]
  have hmajorIntegrable : IntervalIntegrable
      (fun t : Real => (-suzukiRThirdKernel t) *
        (2 * primitiveNorm * vectorNorm)) volume 0
      (2 * suzukiProjectAStar) :=
    intervalIntegrable_suzukiRThirdKernel_project.neg.mul_const _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (μ := volume) hL
    (f := fun t : Real => (suzukiRThirdKernel t : Complex) * q t)
    (g := fun t : Real => (-suzukiRThirdKernel t) *
      (2 * primitiveNorm * vectorNorm))
    (by
      filter_upwards with t ht
      have hthird := suzukiRThirdKernel_nonpos_on_project_interval ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos hthird]
      exact mul_le_mul_of_nonneg_left (hqBound t ⟨ht.1.le, ht.2⟩)
        (neg_nonneg.mpr hthird))
    hmajorIntegrable
  calc
    ‖∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRThirdKernel t : Complex) * q t‖ ≤
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (-suzukiRThirdKernel t) *
          (2 * primitiveNorm * vectorNorm) := hnorm
    _ = (suzukiDF6D4DF0RemainderVariation / 2) *
        (2 * primitiveNorm * vectorNorm) := by
      rw [intervalIntegral.integral_mul_const,
        integral_neg_suzukiRThirdKernel_project]
    _ = suzukiDF6D4DF0RemainderVariation * primitiveNorm * vectorNorm := by
      ring

/-- The finite high-mode Gamma estimate with every endpoint, support, and
Sobolev translation input discharged. -/
theorem norm_intervalIntegral_rSecond_symmetricEnergy_finite_le
    (l : Cutoff44HighIndex →₀ Complex) :
    ‖∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (Finsupp.linearCombination Complex cutoff44HighExponential l)
            (Finsupp.linearCombination Complex cutoff44HighExponential l)‖ ≤
      suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighEndpointPrimitive l‖ *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ := by
  apply norm_intervalIntegral_rSecond_mul_le_of_correlationPrimitive
    (G := fun t => suzukiL2SymmetricTranslationEnergy t
      (Finsupp.linearCombination Complex cutoff44HighExponential l)
      (Finsupp.linearCombination Complex cutoff44HighExponential l))
    (q := suzukiL2SymmetricCorrelationPrimitive
      (cutoff44HighEndpointPrimitive l)
      (Finsupp.linearCombination Complex cutoff44HighExponential l))
  · exact (continuous_suzukiL2SymmetricCorrelationPrimitive _ _).continuousOn
  · intro t ht
    exact hasDerivAt_suzukiL2SymmetricCorrelationPrimitive
      (suzukiL2TranslationPrimitiveDerivative_finite l) t
  · exact (continuous_suzukiL2SymmetricTranslationEnergy_orbit _ _).intervalIntegrable
      0 (2 * suzukiProjectAStar)
  · exact suzukiL2SymmetricCorrelationPrimitive_zero l
  · exact suzukiL2SymmetricCorrelationPrimitive_two_mul_aStar l
  · intro t ht
    exact norm_suzukiL2SymmetricCorrelationPrimitive_le _ _ t

/-- The global Gamma bounded-operator energy satisfies the primitive-variation
estimate on every finite cutoff-44 high-mode combination. -/
theorem abs_re_suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighLinearCombination_le
    (l : Cutoff44HighIndex →₀ Complex) :
    abs
        (suzukiL2BoundedOperatorEnergy
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
          (Finsupp.linearCombination Complex cutoff44HighExponential l)
          (Finsupp.linearCombination Complex cutoff44HighExponential l)).re ≤
      suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighEndpointPrimitive l‖ *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ := by
  calc
    abs
        (suzukiL2BoundedOperatorEnergy
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
          (Finsupp.linearCombination Complex cutoff44HighExponential l)
          (Finsupp.linearCombination Complex cutoff44HighExponential l)).re ≤
        ‖suzukiL2BoundedOperatorEnergy
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
          (Finsupp.linearCombination Complex cutoff44HighExponential l)
          (Finsupp.linearCombination Complex cutoff44HighExponential l)‖ :=
      Complex.abs_re_le_norm _
    _ = ‖∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (Finsupp.linearCombination Complex cutoff44HighExponential l)
            (Finsupp.linearCombination Complex cutoff44HighExponential l)‖ := by
      rw [suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighLinearCombination_eq_interval]
    _ ≤ suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighEndpointPrimitive l‖ *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ :=
      norm_intervalIntegral_rSecond_symmetricEnergy_finite_le l

/-- The finite-combination estimate transported to the algebraic cutoff-44
high-mode subspace. -/
theorem abs_re_suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighSubspace_le
    (v : cutoff44HighExponentialSubspace) :
    abs
        (suzukiL2BoundedOperatorEnergy
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar) v.1 v.1).re ≤
      suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighSubspacePrimitive v‖ * ‖v‖ := by
  let l : Cutoff44HighIndex →₀ Complex :=
    linearIndependent_cutoff44HighExponential.repr v
  have hrepr :=
    linearIndependent_cutoff44HighExponential.linearCombination_repr v
  change Finsupp.linearCombination Complex cutoff44HighExponential l = v.1 at hrepr
  have hfinite :=
    abs_re_suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighLinearCombination_le l
  rw [hrepr] at hfinite
  have hprimitive :
      cutoff44HighSubspacePrimitive v =
        cutoff44HighEndpointPrimitive l := by
    change cutoff44HighSubspacePrimitiveLinearMap v = _
    exact cutoff44HighSubspacePrimitiveLinearMap_apply v
  rw [hprimitive]
  simpa only [Submodule.coe_norm] using hfinite

/-- The absolute real diagonal of any bounded `SuzukiL2` operator energy is
continuous.  Keeping the operator abstract avoids unfolding concrete integral
operators during dense-extension proofs. -/
theorem continuous_abs_re_suzukiL2BoundedOperatorEnergy_diagonal
    (K : SuzukiL2 →L[Complex] SuzukiL2) :
    Continuous (fun u : SuzukiL2 =>
      abs (suzukiL2BoundedOperatorEnergy K u u).re) := by
  exact continuous_abs.comp (Complex.continuous_re.comp
    ((suzukiL2BoundedOperatorEnergy_jointContinuous K).comp
      (continuous_id.prodMk continuous_id)))

set_option maxHeartbeats 800000 in
/-- The Gamma primitive-variation estimate on the entire closed cutoff-44
high-mode space, obtained from the finite estimate by dense continuity. -/
theorem abs_re_suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighClosure_le
    (v : cutoff44HighExponentialSubspace.topologicalClosure) :
    abs
        (suzukiL2BoundedOperatorEnergy
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar) v.1 v.1).re ≤
      suzukiDF6D4DF0RemainderVariation *
        ‖cutoff44HighClosurePrimitive v‖ * ‖v‖ := by
  let p : cutoff44HighExponentialSubspace.topologicalClosure → Prop :=
    fun w =>
      abs
          (suzukiL2BoundedOperatorEnergy
            (suzukiRSecondGlobalL2Operator suzukiProjectAStar) w.1 w.1).re ≤
        suzukiDF6D4DF0RemainderVariation *
          ‖cutoff44HighClosurePrimitive w‖ * ‖w‖
  apply DenseRange.induction_on
    (p := p) cutoff44HighSubspaceClosureInclusion_denseRange v
  · apply isClosed_le
    · exact
        (continuous_abs_re_suzukiL2BoundedOperatorEnergy_diagonal
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar)).comp
            continuous_subtype_val
    · exact (continuous_const.mul
        (continuous_norm.comp cutoff44HighClosurePrimitive.continuous)).mul
          continuous_norm
  · intro w
    dsimp only [p]
    have hcoe :
        (cutoff44HighSubspaceClosureInclusion w).1 = w.1 := rfl
    have hnorm :
        ‖cutoff44HighSubspaceClosureInclusion w‖ = ‖w‖ :=
      cutoff44HighSubspaceClosureInclusion.norm_map w
    rw [cutoff44HighClosurePrimitive_eq_on_subspace, hcoe, hnorm]
    exact abs_re_suzukiRSecondGlobalL2OperatorEnergy_cutoff44HighSubspace_le w

end

end RiemannHypothesisProject.Experiments.M100
