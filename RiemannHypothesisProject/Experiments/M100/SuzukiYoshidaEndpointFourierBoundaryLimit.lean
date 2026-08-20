import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierIntegrability

/-!
# Boundary limits for the endpoint Fourier source integrals

This module continues QF2 after absolute diagonal integrability.  It proves
absolute integrability of the genuinely polarized endpoint integrand for every
integer-mode pair, then removes symmetric frequency cutoffs.  It does not yet
identify the resulting ordinary integral with the form-core comparison limit.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate Topology

/-- The project-normalized source integrand for an ordered pair of endpoint
exponentials. -/
def suzukiYoshidaEndpointSourceFourierIntegrand
    (r : Real) (m n : Int) (xi : Real) : Complex :=
  ((suzukiSourceLogFourierWeight xi : Real) : Complex) *
    (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r m) xi *
      conj (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi))

/-- The ordinary project-normalized source pairing of two endpoint
exponentials. -/
def suzukiYoshidaEndpointSourceFourierPairing
    (r : Real) (m n : Int) : Complex :=
  ∫ xi : Real, suzukiYoshidaEndpointSourceFourierIntegrand r m n xi

/-- Every polarized endpoint source integrand is absolutely integrable.  The
proof uses the two checked diagonal estimates and the elementary inequality
`ab ≤ a² + b²`. -/
theorem integrable_suzukiYoshidaEndpointSourceFourierIntegrand
    {r : Real} (hr : 0 < r) (m n : Int) :
    Integrable (suzukiYoshidaEndpointSourceFourierIntegrand r m n) := by
  let diagonal : Int → Real → Real := fun j xi =>
    suzukiSourceLogFourierWeight xi *
      ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r j) xi‖ ^ 2
  have hm : Integrable (diagonal m) := by
    simpa only [diagonal] using
      integrable_suzukiSourceLogFourierWeight_mul_endpointFourierSq hr m
  have hn : Integrable (diagonal n) := by
    simpa only [diagonal] using
      integrable_suzukiSourceLogFourierWeight_mul_endpointFourierSq hr n
  have hmajor : Integrable (fun xi : Real =>
      ‖diagonal m xi‖ + ‖diagonal n xi‖) :=
    hm.norm.add hn.norm
  apply hmajor.mono'
  · have hweight : Measurable suzukiSourceLogFourierWeight := by
      unfold suzukiSourceLogFourierWeight
      fun_prop
    exact
      ((Complex.continuous_ofReal.measurable.comp hweight).mul
        ((continuous_fourier_suzukiYoshidaExponentialFunction hr m).mul
          (Complex.continuous_conj.comp
            (continuous_fourier_suzukiYoshidaExponentialFunction
              hr n))).measurable).aestronglyMeasurable
  · filter_upwards with xi
    let fm : Complex := FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r m) xi
    let fn : Complex := FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r n) xi
    have hproduct : ‖fm‖ * ‖fn‖ ≤ ‖fm‖ ^ 2 + ‖fn‖ ^ 2 := by
      nlinarith [sq_nonneg (‖fm‖ - ‖fn‖)]
    calc
      ‖suzukiYoshidaEndpointSourceFourierIntegrand r m n xi‖ =
          |suzukiSourceLogFourierWeight xi| * (‖fm‖ * ‖fn‖) := by
        simp only [suzukiYoshidaEndpointSourceFourierIntegrand, fm, fn,
          norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |suzukiSourceLogFourierWeight xi| *
          (‖fm‖ ^ 2 + ‖fn‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)
      _ = ‖diagonal m xi‖ + ‖diagonal n xi‖ := by
        simp only [diagonal, fm, fn, Real.norm_eq_abs, abs_mul,
          abs_sq]
        ring

/-- Symmetric real-frequency intervals exhaust the real line monotonically. -/
theorem iUnion_Icc_neg_self_real :
    (⋃ R : Real, Icc (-R) R) = (univ : Set Real) := by
  ext xi
  simp only [mem_iUnion, mem_Icc, mem_univ, iff_true]
  exact ⟨|xi|, neg_abs_le xi, le_abs_self xi⟩

/-- An absolutely integrable complex function is recovered by its symmetric
frequency cutoffs. -/
theorem tendsto_integral_Icc_neg_self_atTop
    {f : Real → Complex} (hf : Integrable f) :
    Tendsto (fun R : Real => ∫ xi in Icc (-R) R, f xi)
      atTop (𝓝 (∫ xi : Real, f xi)) := by
  have hmono : Monotone (fun R : Real => Icc (-R) R) := by
    intro R S hRS xi hxi
    constructor <;> linarith [hxi.1, hxi.2]
  have hlimit := tendsto_setIntegral_of_monotone
    (fun _ : Real => measurableSet_Icc) hmono (by
      rw [iUnion_Icc_neg_self_real]
      exact hf.integrableOn)
  rw [iUnion_Icc_neg_self_real] at hlimit
  simpa only [Measure.restrict_univ] using hlimit

/-- The symmetric frequency cutoffs of an endpoint source pairing converge
to its ordinary absolutely convergent integral. -/
theorem tendsto_integral_Icc_suzukiYoshidaEndpointSourceFourierIntegrand
    {r : Real} (hr : 0 < r) (m n : Int) :
    Tendsto
      (fun R : Real => ∫ xi in Icc (-R) R,
        suzukiYoshidaEndpointSourceFourierIntegrand r m n xi)
      atTop (𝓝 (suzukiYoshidaEndpointSourceFourierPairing r m n)) := by
  unfold suzukiYoshidaEndpointSourceFourierPairing
  exact tendsto_integral_Icc_neg_self_atTop
    (integrable_suzukiYoshidaEndpointSourceFourierIntegrand hr m n)

end

end RiemannHypothesisProject.Experiments.M100
