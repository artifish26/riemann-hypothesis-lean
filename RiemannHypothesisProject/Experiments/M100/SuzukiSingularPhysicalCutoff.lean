import RiemannHypothesisProject.Experiments.M100.SuzukiSingularFourierLimit

/-!
# M100-DF6D2 physical reciprocal-kernel cutoff

This module converts the finite reciprocal-kernel Plancherel pairing into the
real renormalized cutoff expression.  It is the algebraic interface between
the already checked Fourier cutoff limit and the remaining local singular-form
calculation.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate

/-- The real physical-side expression corresponding to the renormalized
reciprocal-kernel multiplier. -/
def suzukiRenormalizedCutoffPhysicalPairing
    (ε R : Real) (v : SchwartzLineTestFunction) : Real :=
  -2 * Real.log ε * (∫ x : Real, ‖v x‖ ^ 2) -
    (suzukiReciprocalCutoffAutocorrelationPairing ε R v).re

/-- The finite reciprocal kernel is uniformly bounded by the reciprocal inner
cutoff. -/
theorem norm_suzukiReciprocalCutoffKernel_le
    {ε R : Real} (hε : 0 < ε) (t : Real) :
    ‖suzukiReciprocalCutoffKernel ε R t‖ ≤ ε⁻¹ := by
  by_cases ht : t ∈ suzukiReciprocalCutoffSet ε R
  · have habs : ε ≤ |t| :=
      le_abs_of_mem_suzukiReciprocalCutoffSet ht
    simp only [suzukiReciprocalCutoffKernel, Set.indicator_of_mem ht,
      Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_abs]
    exact (inv_le_inv₀ (hε.trans_le habs) hε).2 habs
  · simp [suzukiReciprocalCutoffKernel, ht, inv_nonneg.mpr hε.le]

/-- The finite reciprocal kernel is measurable as a complex-valued function. -/
theorem measurable_suzukiReciprocalCutoffKernel (ε R : Real) :
    Measurable (suzukiReciprocalCutoffKernel ε R) := by
  unfold suzukiReciprocalCutoffKernel
  exact (by fun_prop : Measurable (fun t : Real =>
    (((|t|⁻¹ : Real) : Complex)))).indicator
      (measurableSet_suzukiReciprocalCutoffSet ε R)

/-- Square-side cross pairing obtained after opening the autocorrelation. -/
def suzukiReciprocalCutoffSquarePairing
    (ε R a : Real) (v : SchwartzLineTestFunction) : Complex :=
  ∫ p in suzukiFiniteSquare a,
    suzukiReciprocalCutoffKernel ε R (p.1 - p.2) *
      v p.2 * conj (v p.1)

/-- Opening the autocorrelation and using translation invariance converts the
physical reciprocal-kernel pairing into its finite-square cross pairing. -/
theorem suzukiReciprocalCutoffAutocorrelationPairing_eq_square
    {ε R a : Real} (hε : 0 < ε) (v : SuzukiSmoothCore a) :
    suzukiReciprocalCutoffAutocorrelationPairing ε R v.1 =
      suzukiReciprocalCutoffSquarePairing ε R a v.1 := by
  let F : Real → Real → Complex := fun x y =>
    suzukiReciprocalCutoffKernel ε R (x - y) *
      v.1 y * conj (v.1 x)
  let G : Real → Real → Complex := fun y t =>
    suzukiReciprocalCutoffKernel ε R t *
      v.1 y * conj (v.1 (t + y))
  have hv : Integrable (v.1 : Real → Complex) := v.1.integrable
  have hconj : Integrable (fun x : Real => conj (v.1 x)) := by
    have hcomp := Complex.conjCLE.toContinuousLinearMap.integrable_comp hv
    change Integrable (fun x : Real => Complex.conjCLE (v.1 x))
    exact hcomp
  have hseparable : Integrable (fun p : Real × Real =>
      v.1 p.2 * conj (v.1 p.1)) (volume.prod volume) := by
    have hprod := hconj.mul_prod hv
    apply hprod.congr
    filter_upwards with p
    ring
  have hFraw : Integrable (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R (p.1 - p.2) *
        (v.1 p.2 * conj (v.1 p.1))) (volume.prod volume) := by
    apply hseparable.bdd_mul
    · exact ((measurable_suzukiReciprocalCutoffKernel ε R).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.1 - p.2)))
          |>.aestronglyMeasurable
    · filter_upwards with p
      exact norm_suzukiReciprocalCutoffKernel_le hε (p.1 - p.2)
  have hF : Integrable (fun p : Real × Real => F p.1 p.2)
      (volume.prod volume) := by
    simpa only [F, mul_assoc] using hFraw
  have hcoupled : Integrable (fun p : Real × Real =>
      v.1 p.1 * conj (v.1 (p.2 + p.1))) (volume.prod volume) := by
    let H : Real × Real → Complex := fun p => v.1 p.1 * conj (v.1 p.2)
    have hH : Integrable H := hv.mul_prod hconj
    have hcomp :=
      (measurePreserving_prod_add_right
        (volume : Measure Real) (volume : Measure Real)).integrable_comp_of_integrable hH
    change Integrable (fun p : Real × Real =>
      v.1 p.1 * conj (v.1 (p.2 + p.1))) (volume.prod volume) at hcomp
    exact hcomp
  have hGraw : Integrable (fun p : Real × Real =>
      suzukiReciprocalCutoffKernel ε R p.2 *
        (v.1 p.1 * conj (v.1 (p.2 + p.1))))
      (volume.prod volume) := by
    apply hcoupled.bdd_mul
    · exact ((measurable_suzukiReciprocalCutoffKernel ε R).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.2)))
          |>.aestronglyMeasurable
    · filter_upwards with p
      exact norm_suzukiReciprocalCutoffKernel_le hε p.2
  have hG : Integrable (fun p : Real × Real => G p.1 p.2)
      (volume.prod volume) := by
    simpa only [G, mul_assoc] using hGraw
  have hsupport : Function.support v.1 ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hrestrict :
      (∫ p in suzukiFiniteSquare a, F p.1 p.2) =
        ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    by_cases hx : p.1 ∈ Set.Icc (-a) a
    · have hy : p.2 ∉ Set.Icc (-a) a := fun hy => hp ⟨hx, hy⟩
      have hvy : v.1 p.2 = 0 := by
        by_contra hne
        exact hy (hsupport hne)
      simp [F, hvy]
    · have hvx : v.1 p.1 = 0 := by
        by_contra hne
        exact hx (hsupport hne)
      simp [F, hvx]
  have hfiber (y : Real) :
      (∫ x : Real, F x y) = ∫ t : Real, G y t := by
    have htranslate := integral_sub_right_eq_self
      (fun t : Real => G y t) y (μ := volume)
    simpa only [F, G, sub_add_cancel] using htranslate
  have hphysicalNeg :
      (∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume)) =
        ∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            SchwartzLineTestFunction.autocorrelation v.1 (-t) := by
    rw [MeasureTheory.integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G]
    rw [show (fun x : Real =>
        suzukiReciprocalCutoffKernel ε R t * v.1 x *
            conj (v.1 (t + x))) =
          fun x : Real =>
            suzukiReciprocalCutoffKernel ε R t *
              (v.1 x * conj (v.1 (t + x))) by
        funext x
        ring]
    rw [integral_const_mul]
    apply congrArg (fun z : Complex =>
      suzukiReciprocalCutoffKernel ε R t * z)
    rw [SchwartzLineTestFunction.autocorrelation_apply,
      MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [SchwartzLineTestFunction.star_apply]
    congr 2
    ring
  have hreflect := integral_neg_eq_self
    (f := fun t : Real =>
      suzukiReciprocalCutoffKernel ε R t *
        SchwartzLineTestFunction.autocorrelation v.1 t) volume
  have hphysical :
      (∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            SchwartzLineTestFunction.autocorrelation v.1 (-t)) =
        ∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            SchwartzLineTestFunction.autocorrelation v.1 t := by
    simpa only [suzukiReciprocalCutoffKernel_neg, neg_neg] using hreflect
  unfold suzukiReciprocalCutoffAutocorrelationPairing
    suzukiReciprocalCutoffSquarePairing
  calc
    (∫ t : Real,
        suzukiReciprocalCutoffKernel ε R t *
          SchwartzLineTestFunction.autocorrelation v.1 t) =
        ∫ t : Real,
          suzukiReciprocalCutoffKernel ε R t *
            SchwartzLineTestFunction.autocorrelation v.1 (-t) := hphysical.symm
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

/-- The finite Fourier pairing is the complex coercion of the real cosine
multiplier paired with the squared Fourier transform. -/
theorem suzukiReciprocalCutoffFourierPairing_eq_realIntegral
    (ε R : Real) (v : SchwartzLineTestFunction) :
    suzukiReciprocalCutoffFourierPairing ε R v =
      ((∫ ξ : Real,
        suzukiReciprocalCutoffCosineMultiplier ε R ξ *
          ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2 : Real) :
        Complex) := by
  unfold suzukiReciprocalCutoffFourierPairing
  calc
    (∫ ξ : Real,
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
          SchwartzLineTestFunction.fourierAutocorrelation v ξ) =
        ∫ ξ : Real,
          ((suzukiReciprocalCutoffCosineMultiplier ε R ξ *
            ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2 : Real) :
              Complex) := by
      apply integral_congr_ae
      filter_upwards with ξ
      rw [SchwartzLineTestFunction.fourierAutocorrelation_apply,
        Complex.mul_conj']
      norm_cast
    _ = ((∫ ξ : Real,
        suzukiReciprocalCutoffCosineMultiplier ε R ξ *
          ‖SchwartzMap.fourierTransformCLM Complex v ξ‖ ^ 2 : Real) :
            Complex) := integral_ofReal

/-- Finite Plancherel converts the real physical cutoff pairing into the
integral of the renormalized Fourier multiplier. -/
theorem suzukiRenormalizedCutoffPhysicalPairing_eq_fourierIntegral
    {ε R : Real} (hε : 0 < ε) (hεOne : ε ≤ 1) (hROne : 1 ≤ R)
    (v : SchwartzLineTestFunction) :
    suzukiRenormalizedCutoffPhysicalPairing ε R v =
      ∫ ξ : Real, suzukiRenormalizedCutoffFourierIntegrand ε R v ξ := by
  let f : SchwartzLineTestFunction :=
    SchwartzMap.fourierTransformCLM Complex v
  have hsq : Integrable (fun ξ : Real => ‖f ξ‖ ^ 2) :=
    (f.memLp (2 : ENNReal) (volume : Measure Real)).integrable_norm_pow
      (by norm_num)
  have hrenormalized :=
    integrable_suzukiRenormalizedCutoffFourierIntegrand
      hε hεOne hROne v
  have hconstant : Integrable (fun ξ : Real =>
      (-2 * Real.log ε) * ‖f ξ‖ ^ 2) :=
    hsq.const_mul (-2 * Real.log ε)
  have hmultiplier : Integrable (fun ξ : Real =>
      suzukiReciprocalCutoffCosineMultiplier ε R ξ * ‖f ξ‖ ^ 2) := by
    apply (hconstant.sub hrenormalized).congr
    filter_upwards with ξ
    change
      (-2 * Real.log ε) * ‖f ξ‖ ^ 2 -
          ((-2 * Real.log ε -
              suzukiReciprocalCutoffCosineMultiplier ε R ξ) *
            ‖f ξ‖ ^ 2) =
        suzukiReciprocalCutoffCosineMultiplier ε R ξ * ‖f ξ‖ ^ 2
    ring
  have hpairing :=
    suzukiReciprocalCutoffAutocorrelationPairing_eq_fourier
      hε (hεOne.trans hROne) v
  rw [suzukiRenormalizedCutoffPhysicalPairing, hpairing,
    suzukiReciprocalCutoffFourierPairing_eq_realIntegral]
  simp only [Complex.ofReal_re]
  rw [← SchwartzMap.integral_norm_sq_fourier v]
  change
    -2 * Real.log ε * (∫ ξ : Real, ‖f ξ‖ ^ 2) -
        (∫ ξ : Real,
          suzukiReciprocalCutoffCosineMultiplier ε R ξ * ‖f ξ‖ ^ 2) = _
  rw [← integral_const_mul, ← integral_sub hconstant hmultiplier]
  apply integral_congr_ae
  filter_upwards with ξ
  unfold suzukiRenormalizedCutoffFourierIntegrand
    suzukiRenormalizedCutoffMultiplier
  dsimp only [f]
  ring

end

end M100
end Experiments
end RiemannHypothesisProject
