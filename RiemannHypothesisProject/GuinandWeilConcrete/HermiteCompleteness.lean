import Mathlib.Analysis.Fourier.Convolution
import RiemannHypothesisProject.GuinandWeilConcrete.HermiteSchwartzSeminormGrowth

/-!
# Completeness boundary for the `pi`-Hermite source

This module develops the remaining separation theorem behind Hermite density.
The first step is algebraic-functional: if every normalized oscillator-Hermite
coefficient of a Schwartz test vanishes, then its bilinear pairing with every
real polynomial times the `pi`-Gaussian vanishes.  The subsequent analytic
step will turn those Gaussian-weighted moments into vanishing of the Gaussian
convolution and then use Fourier injectivity.
-/

namespace RiemannHypothesisProject

open MeasureTheory Module Submodule Topology
open scoped Convolution FourierTransform

noncomputable section

/-- Pairing in the left Schwartz argument, regarded as a real-linear map. -/
noncomputable def guinandWeilPiSchwartzBilinearPairingLeftRealLinearMap
    (g : SchwartzLineTestFunction) :
    SchwartzLineTestFunction →ₗ[Real] Complex where
  toFun f := guinandWeilPiSchwartzBilinearPairing f g
  map_add' f h := by
    unfold guinandWeilPiSchwartzBilinearPairing
    have hf : Integrable (fun x : Real => f x * g x) :=
      (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f g).integrable
    have hh : Integrable (fun x : Real => h x * g x) :=
      (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) h g).integrable
    change (∫ x : Real, (f x + h x) * g x) = _
    simp_rw [add_mul]
    rw [integral_add hf hh]
  map_smul' c f := by
    simpa [Complex.real_smul] using
      guinandWeilPiSchwartzBilinearPairing_real_smul_left c f g

/-- Pairing after the real polynomial-Gaussian source map. -/
noncomputable def guinandWeilPiPolynomialGaussianPairingRealLinearMap
    (g : SchwartzLineTestFunction) : Polynomial Real →ₗ[Real] Complex :=
  (guinandWeilPiSchwartzBilinearPairingLeftRealLinearMap g).comp
    guinandWeilPiRealPolynomialGaussianSchwartzLinearMap

/-- Vanishing normalized coefficients imply vanishing unnormalized
oscillator-Hermite pairings. -/
theorem guinandWeilPiSchwartzBilinearPairing_oscillatorHermite_eq_zero_of_coefficients
    (g : SchwartzLineTestFunction)
    (hcoeff : ∀ n : Nat,
      guinandWeilPiNormalizedHermiteCoefficient n g = 0)
    (n : Nat) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorHermiteSchwartz n) g = 0 := by
  have h := hcoeff n
  unfold guinandWeilPiNormalizedHermiteCoefficient
    guinandWeilPiNormalizedHermiteSchwartz at h
  rw [guinandWeilPiSchwartzBilinearPairing_real_smul_left] at h
  have hsqrt : Real.sqrt (guinandWeilPiHermiteNormSq n) ≠ 0 :=
    (Real.sqrt_pos.2 (guinandWeilPiHermiteNormSq_pos n)).ne'
  have hfactor :
      (((Real.sqrt (guinandWeilPiHermiteNormSq n))⁻¹ : Real) : Complex) ≠ 0 := by
    exact_mod_cast inv_ne_zero hsqrt
  exact (mul_eq_zero.mp h).resolve_left hfactor

/-- If all normalized Hermite coefficients vanish, pairing with every real
polynomial-Gaussian source test vanishes. -/
theorem guinandWeilPiSchwartzBilinearPairing_polynomialGaussian_eq_zero_of_coefficients
    (g : SchwartzLineTestFunction)
    (hcoeff : ∀ n : Nat,
      guinandWeilPiNormalizedHermiteCoefficient n g = 0)
    (p : Polynomial Real) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiRealPolynomialGaussianSchwartzLinearMap p) g = 0 := by
  let L := guinandWeilPiPolynomialGaussianPairingRealLinearMap g
  have hbasis (n : Nat) :
      L (guinandWeilPiOscillatorHermiteRealPolynomialBasis n) = 0 := by
    change guinandWeilPiSchwartzBilinearPairing
      (guinandWeilPiRealPolynomialGaussianSchwartzLinearMap
        (guinandWeilPiOscillatorHermiteRealPolynomialBasis n)) g = 0
    rw [guinandWeilPiOscillatorHermiteRealPolynomialBasis_apply]
    exact
      guinandWeilPiSchwartzBilinearPairing_oscillatorHermite_eq_zero_of_coefficients
        g hcoeff n
  have hL : L = 0 := by
    apply guinandWeilPiOscillatorHermiteRealPolynomialBasis.ext
    intro n
    simpa only [LinearMap.zero_apply] using hbasis n
  have hp := LinearMap.congr_fun hL p
  change guinandWeilPiSchwartzBilinearPairing
    (guinandWeilPiRealPolynomialGaussianSchwartzLinearMap p) g = 0 at hp
  exact hp

/-- Vanishing Hermite coefficients give every Gaussian-weighted monomial
moment. -/
theorem integral_pow_mul_guinandWeilPiGaussianSource_mul_eq_zero_of_coefficients
    (g : SchwartzLineTestFunction)
    (hcoeff : ∀ n : Nat,
      guinandWeilPiNormalizedHermiteCoefficient n g = 0)
    (n : Nat) :
    (∫ x : Real,
      ((x : Complex) ^ n * guinandWeilPiGaussianSource (x : Complex)) *
        g x) = 0 := by
  have h :=
    guinandWeilPiSchwartzBilinearPairing_polynomialGaussian_eq_zero_of_coefficients
      g hcoeff (Polynomial.X ^ n)
  unfold guinandWeilPiSchwartzBilinearPairing at h
  simpa [guinandWeilPiRealPolynomialGaussianSchwartzLinearMap,
    guinandWeilPiPolynomialGaussianSchwartz_apply,
    guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def] using h

/-- A Gaussian absorbs an arbitrary real exponential in absolute value. -/
theorem integrable_exp_abs_mul_norm_guinandWeilPiGaussianSource
    (a : Real) :
    Integrable (fun x : Real =>
      Real.exp |a * x| * ‖guinandWeilPiGaussianSource (x : Complex)‖) := by
  have hpos : Integrable (fun x : Real =>
      Real.exp (-Real.pi * x ^ 2 + |a| * x)) := by
    have h := (integrable_cexp_quadratic
      (b := (Real.pi : Complex)) (by simpa using Real.pi_pos)
      ((|a| : Real) : Complex) 0).norm
    simpa [Complex.norm_exp, pow_two, sub_eq_add_neg] using h
  have hneg : Integrable (fun x : Real =>
      Real.exp (-Real.pi * x ^ 2 - |a| * x)) := by
    have h := (integrable_cexp_quadratic
      (b := (Real.pi : Complex)) (by simpa using Real.pi_pos)
      ((-(|a|) : Real) : Complex) 0).norm
    have h' : Integrable (fun x : Real =>
        Real.exp (-Real.pi * x ^ 2 + -(|a| * x))) := by
      simpa [Complex.norm_exp, pow_two] using h
    simpa only [sub_eq_add_neg] using h'
  have hsum : Integrable (fun x : Real =>
      Real.exp (-Real.pi * x ^ 2 + |a| * x) +
        Real.exp (-Real.pi * x ^ 2 - |a| * x)) := hpos.add hneg
  apply hsum.mono'
  · exact (((Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).abs)).mul
      ((differentiable_guinandWeilPiGaussianSource.continuous.comp
        Complex.continuous_ofReal).norm))).aestronglyMeasurable
  · filter_upwards [] with x
    have hgauss :
        ‖guinandWeilPiGaussianSource (x : Complex)‖ =
          Real.exp (-Real.pi * x ^ 2) := by
      simp [guinandWeilPiGaussianSource, Complex.norm_exp, pow_two]
    simp only [Real.norm_eq_abs, hgauss]
    have hax : |a * x| = |a| * |x| := abs_mul a x
    rw [hax, ← Real.exp_add]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      rw [abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (|a| * x + -Real.pi * x ^ 2) =
            Real.exp (-Real.pi * x ^ 2 + |a| * x) := by ring_nf
        _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos (le_of_not_ge hx)]
      rw [abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (|a| * -x + -Real.pi * x ^ 2) =
            Real.exp (-Real.pi * x ^ 2 - |a| * x) := by ring_nf
        _ ≤ _ := le_add_of_nonneg_left (Real.exp_pos _).le

/-- Adding a Schwartz factor preserves the exponential-Gaussian
integrability needed for the moment-generating series. -/
theorem integrable_exp_abs_mul_norm_guinandWeilPiGaussianSource_mul_schwartz
    (a : Real) (g : SchwartzLineTestFunction) :
    Integrable (fun x : Real =>
      Real.exp |a * x| *
        ‖guinandWeilPiGaussianSource (x : Complex) * g x‖) := by
  have hbase := integrable_exp_abs_mul_norm_guinandWeilPiGaussianSource a
  have hmul := hbase.mul_bdd g.continuous.norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x =>
      (by simpa [Real.norm_eq_abs] using
        SchwartzMap.norm_le_seminorm Complex g x))
  simpa [norm_mul, mul_assoc] using hmul

/-- Vanishing Gaussian moments sum to a vanishing real Laplace transform. -/
theorem integral_exp_mul_guinandWeilPiGaussianSource_mul_eq_zero_of_coefficients
    (g : SchwartzLineTestFunction)
    (hcoeff : ∀ n : Nat,
      guinandWeilPiNormalizedHermiteCoefficient n g = 0)
    (a : Real) :
    (∫ x : Real,
      Complex.exp ((a * x : Real) : Complex) *
        (guinandWeilPiGaussianSource (x : Complex) * g x)) = 0 := by
  let F : Nat → Real → Complex := fun n x =>
    ((((a * x : Real) : Complex) ^ n) / (Nat.factorial n : Complex)) *
      (guinandWeilPiGaussianSource (x : Complex) * g x)
  let bound : Nat → Real → Real := fun n x =>
    (|a * x| ^ n / (Nat.factorial n : Real)) *
      ‖guinandWeilPiGaussianSource (x : Complex) * g x‖
  have hF_meas (n : Nat) : AEStronglyMeasurable (F n) := by
    dsimp only [F]
    exact (((Complex.continuous_ofReal.comp
      (continuous_const.mul continuous_id)).pow n).div_const _ |>.mul
      ((differentiable_guinandWeilPiGaussianSource.continuous.comp
        Complex.continuous_ofReal).mul g.continuous)).aestronglyMeasurable
  have h_bound (n : Nat) : ∀ᵐ x : Real,
      ‖F n x‖ ≤ bound n x := by
    filter_upwards [] with x
    dsimp only [F, bound]
    simp [norm_pow, abs_mul]
  have h_bound_summable : ∀ᵐ x : Real,
      Summable (fun n : Nat => bound n x) := by
    filter_upwards [] with x
    dsimp only [bound]
    exact (NormedSpace.expSeries_div_summable (|a * x| : Real)).mul_right _
  have h_bound_integrable : Integrable (fun x : Real => ∑' n : Nat, bound n x) := by
    have hfun : (fun x : Real => ∑' n : Nat, bound n x) =
        fun x : Real => Real.exp |a * x| *
          ‖guinandWeilPiGaussianSource (x : Complex) * g x‖ := by
      funext x
      dsimp only [bound]
      simpa only [← Real.exp_eq_exp_ℝ] using
        ((NormedSpace.expSeries_div_hasSum_exp (|a * x| : Real)).mul_right
          ‖guinandWeilPiGaussianSource (x : Complex) * g x‖).tsum_eq
    rw [hfun]
    exact
      integrable_exp_abs_mul_norm_guinandWeilPiGaussianSource_mul_schwartz a g
  have h_lim : ∀ᵐ x : Real,
      HasSum (fun n : Nat => F n x)
        (Complex.exp ((a * x : Real) : Complex) *
          (guinandWeilPiGaussianSource (x : Complex) * g x)) := by
    filter_upwards [] with x
    dsimp only [F]
    simpa only [← Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp
        (((a * x : Real) : Complex))).mul_right
          (guinandWeilPiGaussianSource (x : Complex) * g x)
  have hseries := hasSum_integral_of_dominated_convergence
    bound hF_meas h_bound h_bound_summable h_bound_integrable h_lim
  have hintegral (n : Nat) : (∫ x : Real, F n x) = 0 := by
    have hmoment :=
      integral_pow_mul_guinandWeilPiGaussianSource_mul_eq_zero_of_coefficients
        g hcoeff n
    have hpoint : F n = fun x : Real =>
        (((a : Complex) ^ n) / (Nat.factorial n : Complex)) *
          (((x : Complex) ^ n *
            guinandWeilPiGaussianSource (x : Complex)) * g x) := by
      funext x
      dsimp only [F]
      push_cast
      ring
    rw [hpoint, integral_const_mul, hmoment, mul_zero]
  have hzero : HasSum (fun n : Nat => ∫ x : Real, F n x) 0 := by
    simpa only [hintegral] using (hasSum_zero : HasSum (fun _ : Nat => (0 : Complex)) 0)
  exact hseries.unique hzero

/-- The `pi`-Gaussian as a project Schwartz test for the completeness
argument. -/
noncomputable def guinandWeilPiCompletenessGaussianSchwartz :
    SchwartzLineTestFunction :=
  guinandWeilPiRealPolynomialGaussianSchwartzLinearMap 1

@[simp]
theorem guinandWeilPiCompletenessGaussianSchwartz_apply (x : Real) :
    guinandWeilPiCompletenessGaussianSchwartz x =
      guinandWeilPiGaussianSource (x : Complex) := by
  simp [guinandWeilPiCompletenessGaussianSchwartz,
    guinandWeilPiRealPolynomialGaussianSchwartzLinearMap,
    guinandWeilPiPolynomialGaussianSchwartz_apply,
    guinandWeilPiPolynomialGaussianSource]

/-- The completeness Gaussian is Fourier self-reciprocal. -/
theorem fourier_guinandWeilPiCompletenessGaussianSchwartz_apply
    (t : Real) :
    𝓕 guinandWeilPiCompletenessGaussianSchwartz t =
      guinandWeilPiGaussianSource (t : Complex) := by
  rw [SchwartzMap.fourier_coe]
  rw [show (⇑guinandWeilPiCompletenessGaussianSchwartz : Real → Complex) =
      fun x : Real => guinandWeilPiGaussianSource (x : Complex) by
    funext x
    exact guinandWeilPiCompletenessGaussianSchwartz_apply x]
  exact congrFun fourier_guinandWeilPiGaussianSource_real t

/-- Vanishing Hermite coefficients force convolution with the `pi`-Gaussian
to vanish identically. -/
theorem guinandWeilPiGaussian_convolution_eq_zero_of_coefficients
    (g : SchwartzLineTestFunction)
    (hcoeff : ∀ n : Nat,
      guinandWeilPiNormalizedHermiteCoefficient n g = 0) :
    SchwartzMap.convolution (ContinuousLinearMap.mul Complex Complex) g
        guinandWeilPiCompletenessGaussianSchwartz = 0 := by
  apply DFunLike.ext _ _
  intro y
  rw [SchwartzMap.convolution_apply]
  change (∫ x : Real,
    g x * guinandWeilPiCompletenessGaussianSchwartz (y - x)) = 0
  have hpoint : (fun x : Real =>
      g x * guinandWeilPiCompletenessGaussianSchwartz (y - x)) =
      fun x : Real =>
        guinandWeilPiGaussianSource (y : Complex) *
          (Complex.exp ((((2 * Real.pi * y) * x : Real) : Complex)) *
            (guinandWeilPiGaussianSource (x : Complex) * g x)) := by
    funext x
    rw [guinandWeilPiCompletenessGaussianSchwartz_apply]
    unfold guinandWeilPiGaussianSource
    have hexponent :
        -(Real.pi : Complex) * (((y - x : Real) : Complex) * (y - x : Real)) =
          (-(Real.pi : Complex) * ((y : Complex) * y) +
            (((2 * Real.pi * y) * x : Real) : Complex)) +
            (-(Real.pi : Complex) * ((x : Complex) * x)) := by
      push_cast
      ring
    rw [hexponent, Complex.exp_add, Complex.exp_add]
    ring
  rw [hpoint, integral_const_mul,
    integral_exp_mul_guinandWeilPiGaussianSource_mul_eq_zero_of_coefficients
      g hcoeff (2 * Real.pi * y), mul_zero]

/-- The normalized Hermite coefficients separate project Schwartz tests. -/
theorem eq_zero_of_guinandWeilPiNormalizedHermiteCoefficients
    (g : SchwartzLineTestFunction)
    (hcoeff : ∀ n : Nat,
      guinandWeilPiNormalizedHermiteCoefficient n g = 0) :
    g = 0 := by
  have hconv :=
    guinandWeilPiGaussian_convolution_eq_zero_of_coefficients g hcoeff
  have hproduct :
      SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex)
          (𝓕 g) (𝓕 guinandWeilPiCompletenessGaussianSchwartz) = 0 := by
    rw [← SchwartzMap.fourier_convolution, hconv]
    simp
  have hfourier : 𝓕 g = 0 := by
    apply DFunLike.ext _ _
    intro t
    have ht := congrArg (fun h : SchwartzLineTestFunction => h t) hproduct
    rw [SchwartzMap.pairing_apply_apply,
      fourier_guinandWeilPiCompletenessGaussianSchwartz_apply] at ht
    exact (mul_eq_zero.mp ht).resolve_right
      (guinandWeilPiGaussianSource_ne_zero (t : Complex))
  calc
    g = 𝓕⁻ (𝓕 g) := (FourierTransform.fourierInv_fourier_eq g).symm
    _ = 0 := by rw [hfourier]; simp

/-- Hermite completeness: the constructed Schwartz Hermite expansion is the
original test. -/
theorem guinandWeilPiHermiteSchwartzExpansion_eq
    (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteSchwartzExpansion f = f := by
  have hzero :
      f - guinandWeilPiHermiteSchwartzExpansion f = 0 := by
    apply eq_zero_of_guinandWeilPiNormalizedHermiteCoefficients
    intro n
    rw [← guinandWeilPiNormalizedHermiteCoefficientCLM_apply]
    simp only [map_sub,
      guinandWeilPiNormalizedHermiteCoefficientCLM_apply,
      guinandWeilPiNormalizedHermiteCoefficient_schwartzExpansion,
      sub_self]
  exact (sub_eq_zero.mp hzero).symm

/-- The actual Hermite truncations converge to every project Schwartz test. -/
theorem tendsto_guinandWeilPiHermiteTruncation_schwartz_self
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto (fun N : Nat => guinandWeilPiHermiteTruncation N f)
      Filter.atTop (𝓝 f) := by
  simpa only [guinandWeilPiHermiteSchwartzExpansion_eq] using
    tendsto_guinandWeilPiHermiteTruncation_schwartz f

end

end RiemannHypothesisProject
