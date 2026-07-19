import RiemannHypothesisProject.WeilPositivity.BurnolLocalCoefficient
import RiemannHypothesisProject.WeilPositivity.SchwartzFourierAutocorrelation

/-!
# Burnol fixed-support positivity

This module freezes the `2 * pi` normalization between Mathlib's Fourier
transform and Burnol's cosine correction. A base Schwartz function supported
in one fixed additive interval has autocorrelation zero at the corresponding
nonzero displacement, so the correction has zero covariance. The remaining
spectral integral is then nonnegative.

The support radius is fixed by the coefficient theorem. Nothing here asserts
that the resulting support class is dense or promotes its positivity to all
Schwartz tests.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open ComplexCompactExhaustion
open scoped ComplexConjugate Convolution FourierTransform

namespace SchwartzLineTestFunction

noncomputable section

/-- The real Fourier energy density of a Schwartz base test. -/
def fourierEnergyDensity (g : SchwartzLineTestFunction) (t : Real) : Real :=
  Complex.normSq ((𝓕 g) t)

/-- Burnol's fixed-support quadratic form in the formula-facing spectral
normalization. -/
def burnolLocalSpectralQuadraticForm (g : SchwartzLineTestFunction) : Real :=
  ∫ t : Real, burnolLocalCoefficient t * fourierEnergyDensity g t

theorem fourierEnergyDensity_nonneg (g : SchwartzLineTestFunction) (t : Real) :
    0 <= fourierEnergyDensity g t :=
  Complex.normSq_nonneg _

/-- Compatibility with the Q6 normalization: Burnol's energy density is the
real part of the same Fourier autocorrelation used as the formula test. -/
theorem burnolLocalSpectralQuadraticForm_eq_fourierAutocorrelation
    (g : SchwartzLineTestFunction) :
    burnolLocalSpectralQuadraticForm g =
      ∫ t : Real,
        burnolLocalCoefficient t * (fourierAutocorrelation g t).re := by
  unfold burnolLocalSpectralQuadraticForm
  apply integral_congr_ae
  filter_upwards with t
  rw [fourierAutocorrelation_apply, Complex.mul_conj]
  simp [fourierEnergyDensity]

/-- Fourier inversion identifies cosine covariance with the real part of the
autocorrelation at the Mathlib-normalized displacement. -/
theorem integral_cos_two_pi_mul_fourierEnergyDensity
    (g : SchwartzLineTestFunction) (x : Real) :
    ∫ t : Real, Real.cos (2 * Real.pi * t * x) * fourierEnergyDensity g t =
      (autocorrelation g x).re := by
  have hinverse :
      (𝓕⁻ (fourierAutocorrelation g) : SchwartzLineTestFunction) =
        autocorrelation g := by
    simp [fourierAutocorrelation]
  have hintegrable : Integrable (fun t : Real =>
      Complex.exp (((2 * Real.pi * t * x : Real) : Complex) * Complex.I) *
        fourierAutocorrelation g t) := by
    apply (fourierAutocorrelation g).integrable.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with t
      rw [Complex.norm_exp]
      simp
  calc
    ∫ t : Real, Real.cos (2 * Real.pi * t * x) * fourierEnergyDensity g t =
        (∫ t : Real,
          (Complex.exp (((2 * Real.pi * t * x : Real) : Complex) * Complex.I) *
            fourierAutocorrelation g t).re) := by
      apply integral_congr_ae
      filter_upwards with t
      have henergy : fourierAutocorrelation g t =
          (fourierEnergyDensity g t : Complex) := by
        rw [fourierAutocorrelation_apply, Complex.mul_conj]
        simp [fourierEnergyDensity]
      rw [henergy, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [show
        (Complex.exp (((2 * Real.pi * t * x : Real) : Complex) * Complex.I)).re =
          Real.cos (2 * Real.pi * t * x) by
        exact Complex.exp_ofReal_mul_I_re _]
    _ = (∫ t : Real,
          Complex.exp (((2 * Real.pi * t * x : Real) : Complex) * Complex.I) *
            fourierAutocorrelation g t).re := integral_re hintegrable
    _ = ((𝓕⁻ (fourierAutocorrelation g) : SchwartzLineTestFunction) x).re := by
      rw [SchwartzMap.fourierInv_coe]
      rw [Real.fourierInv_eq']
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
      apply congrArg (fun z : Complex => z * fourierAutocorrelation g t)
      apply congrArg Complex.exp
      push_cast
      ring
    _ = (autocorrelation g x).re := by rw [hinverse]

/-- Burnol's frequency parameter `epsilon` corresponds to displacement
`epsilon / (2*pi)` under Mathlib's Fourier convention. -/
theorem integral_cos_mul_fourierEnergyDensity
    (g : SchwartzLineTestFunction) (epsilon : Real) :
    ∫ t : Real, Real.cos (epsilon * t) * fourierEnergyDensity g t =
      (autocorrelation g (epsilon / (2 * Real.pi))).re := by
  rw [← integral_cos_two_pi_mul_fourierEnergyDensity]
  apply integral_congr_ae
  filter_upwards with t
  congr 2
  field_simp [Real.pi_ne_zero]

/-- If a base test is supported in `[-r,r]`, its autocorrelation vanishes at
every positive displacement strictly larger than `2*r`. -/
theorem autocorrelation_apply_eq_zero_of_support_subset_Icc
    {g : SchwartzLineTestFunction} {r x : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hx : 2 * r < x) :
    autocorrelation g x = 0 := by
  rw [autocorrelation_apply, MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases hgt : g t = 0
  · simp [hgt]
  · have ht := hsupport hgt
    have houtside : t - x ∉ Set.Icc (-r) r := by
      intro hmem
      linarith [ht.2, hmem.1]
    have hgshift : g (t - x) = 0 := by
      by_contra hne
      exact houtside (hsupport hne)
    simp [star_apply, hgshift]

/-- A fixed support interval with a strict margin kills exactly the cosine
covariance produced by Burnol's coefficient argument. -/
theorem integral_cos_mul_fourierEnergyDensity_eq_zero_of_fixedSupport
    {g : SchwartzLineTestFunction} {epsilon : Real}
    (hepsilon : 0 < epsilon)
    (hsupport : Function.support g ⊆
      Set.Icc (-(epsilon / (8 * Real.pi))) (epsilon / (8 * Real.pi))) :
    ∫ t : Real, Real.cos (epsilon * t) * fourierEnergyDensity g t = 0 := by
  rw [integral_cos_mul_fourierEnergyDensity]
  have hx :
      2 * (epsilon / (8 * Real.pi)) < epsilon / (2 * Real.pi) := by
    calc
      2 * (epsilon / (8 * Real.pi)) = epsilon / (4 * Real.pi) := by
        field_simp [Real.pi_ne_zero]
        ring
      _ < epsilon / (2 * Real.pi) := by
        rw [div_lt_div_iff₀ (by positivity : 0 < 4 * Real.pi)
          (by positivity : 0 < 2 * Real.pi)]
        nlinarith [Real.pi_pos]
  rw [autocorrelation_apply_eq_zero_of_support_subset_Icc hsupport hx]
  rfl

/-- A Schwartz base test written in multiplicative coordinates. Values at
nonpositive real inputs are set to zero; on the positive half-line this is the
inverse of additive logarithmic pullback. -/
def multiplicativeLogPushforward (g : SchwartzLineTestFunction) (x : Real) : Complex :=
  if 0 < x then g (Real.log x) else 0

/-- Additive support in `[-r,r]` becomes multiplicative support in
`[exp(-r), exp r]`. -/
theorem support_multiplicativeLogPushforward_subset
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r) :
    Function.support (multiplicativeLogPushforward g) ⊆
      Set.Icc (Real.exp (-r)) (Real.exp r) := by
  intro x hx
  have hxpos : 0 < x := by
    by_contra hnot
    have hxnonpos : ¬ 0 < x := hnot
    simp [multiplicativeLogPushforward, hxnonpos] at hx
  have hg : g (Real.log x) ≠ 0 := by
    simpa [multiplicativeLogPushforward, hxpos] using hx
  have hlog := hsupport hg
  constructor
  · rw [← Real.exp_log hxpos]
    exact Real.exp_le_exp.mpr hlog.1
  · rw [← Real.exp_log hxpos]
    exact Real.exp_le_exp.mpr hlog.2

/-- Multiplicative support of the log pushforward is exactly the same support
restriction as the additive interval used by the Fourier covariance proof. -/
theorem support_multiplicativeLogPushforward_subset_iff
    {g : SchwartzLineTestFunction} {r : Real} :
    Function.support (multiplicativeLogPushforward g) ⊆
        Set.Icc (Real.exp (-r)) (Real.exp r) ↔
      Function.support g ⊆ Set.Icc (-r) r := by
  constructor
  · intro hsupport u hu
    have hmul : multiplicativeLogPushforward g (Real.exp u) ≠ 0 := by
      simpa [multiplicativeLogPushforward, Real.exp_pos] using hu
    have hexp := hsupport hmul
    exact ⟨Real.exp_le_exp.mp hexp.1, Real.exp_le_exp.mp hexp.2⟩
  · exact support_multiplicativeLogPushforward_subset

/-- The cosine factor times Fourier energy is integrable for every Schwartz
base test. -/
theorem integrable_fourierEnergyDensity (g : SchwartzLineTestFunction) :
    Integrable (fun t : Real => fourierEnergyDensity g t) := by
  have hfourierIntegrable : Integrable
      (fourierAutocorrelation g : Real → Complex) (volume : Measure Real) :=
    (fourierAutocorrelation g).integrable
  convert hfourierIntegrable.re using 1
  ext t
  rw [fourierAutocorrelation_apply, Complex.mul_conj]
  simp [fourierEnergyDensity]

/-- First-moment integrability of the Fourier energy follows directly from
the Schwartz weighted-integrability theorem. -/
theorem integrable_abs_mul_fourierEnergyDensity (g : SchwartzLineTestFunction) :
    Integrable (fun t : Real => |t| * fourierEnergyDensity g t) := by
  have hweighted :=
    (fourierAutocorrelation g).integrable_pow_mul (volume : Measure Real) 1
  convert hweighted using 1
  ext t
  have henergy : fourierAutocorrelation g t =
      (fourierEnergyDensity g t : Complex) := by
    rw [fourierAutocorrelation_apply, Complex.mul_conj]
    simp [fourierEnergyDensity]
  rw [Real.norm_eq_abs, pow_one, henergy, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fourierEnergyDensity_nonneg g t)]

/-- Binet's linear coefficient bound discharges the local-term integrability
required by the fixed-support spectral argument. -/
theorem integrable_burnolLocalCoefficient_mul_fourierEnergyDensity_of_binet
    (hBinet : BennettGammaBinetDigammaFormula)
    (g : SchwartzLineTestFunction) :
    Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t) := by
  let K : Real :=
    20 + |Real.log Real.pi| + |Real.log (1 / 4)| + Real.pi
  have henergy := integrable_fourierEnergyDensity g
  have hweighted := integrable_abs_mul_fourierEnergyDensity g
  have hmajorant : Integrable (fun t : Real =>
      K * fourierEnergyDensity g t + |t| * fourierEnergyDensity g t) :=
    (henergy.const_mul K).add hweighted
  refine Integrable.mono' hmajorant ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply continuous_burnolLocalCoefficient.mul
    unfold fourierEnergyDensity
    fun_prop
  · filter_upwards with t
    have halpha := abs_burnolLocalCoefficient_le_of_binet hBinet t
    have hmul := mul_le_mul_of_nonneg_right halpha
      (fourierEnergyDensity_nonneg g t)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (fourierEnergyDensity_nonneg g t)]
    dsimp [K]
    nlinarith

theorem integrable_cos_mul_fourierEnergyDensity
    (g : SchwartzLineTestFunction) (epsilon : Real) :
    Integrable (fun t : Real =>
      Real.cos (epsilon * t) * fourierEnergyDensity g t) := by
  have henergy := integrable_fourierEnergyDensity g
  apply henergy.bdd_mul (c := 1)
  · fun_prop
  · filter_upwards with t
    exact abs_le.mpr (Real.cos_mem_Icc (epsilon * t))

/-- The integral form of Burnol's elementary argument. The only finiteness
input retained in the statement is integrability of the exact local term. -/
theorem integral_burnolLocalCoefficient_mul_fourierEnergyDensity_nonneg
    {g : SchwartzLineTestFunction} {epsilon A : Real}
    (hpointwise : ∀ t : Real,
      0 <= A * Real.cos (epsilon * t) + burnolLocalCoefficient t)
    (hsupport : Function.support g ⊆
      Set.Icc (-(epsilon / (8 * Real.pi))) (epsilon / (8 * Real.pi)))
    (hepsilon : 0 < epsilon)
    (hintegrable : Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t)) :
    0 <= burnolLocalSpectralQuadraticForm g := by
  unfold burnolLocalSpectralQuadraticForm
  have hcosInt := integrable_cos_mul_fourierEnergyDensity g epsilon
  have hnonneg : 0 <= ∫ t : Real,
      (A * Real.cos (epsilon * t) + burnolLocalCoefficient t) *
        fourierEnergyDensity g t := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (hpointwise t) (fourierEnergyDensity_nonneg g t)
  have hcosZero :=
    integral_cos_mul_fourierEnergyDensity_eq_zero_of_fixedSupport
      hepsilon hsupport
  have hdecomp :
      (∫ t : Real,
        (A * Real.cos (epsilon * t) + burnolLocalCoefficient t) *
          fourierEnergyDensity g t) =
        A * (∫ t : Real,
          Real.cos (epsilon * t) * fourierEnergyDensity g t) +
          (∫ t : Real,
            burnolLocalCoefficient t * fourierEnergyDensity g t) := by
    calc
      (∫ t : Real,
          (A * Real.cos (epsilon * t) + burnolLocalCoefficient t) *
            fourierEnergyDensity g t) =
          ∫ t : Real,
            A * (Real.cos (epsilon * t) * fourierEnergyDensity g t) +
              burnolLocalCoefficient t * fourierEnergyDensity g t := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = A * (∫ t : Real,
            Real.cos (epsilon * t) * fourierEnergyDensity g t) +
          (∫ t : Real,
            burnolLocalCoefficient t * fourierEnergyDensity g t) := by
        rw [integral_add (hcosInt.const_mul A) hintegrable, integral_const_mul]
  rw [hdecomp, hcosZero] at hnonneg
  simpa using hnonneg

/-- Burnol fixed-support positivity with the support radius and Binet source
theorem both explicit. This is deliberately not a whole-Schwartz theorem. -/
theorem exists_burnolFixedSupport_spectral_nonneg_of_binet
    (hBinet : BennettGammaBinetDigammaFormula) :
    ∃ epsilon > 0, ∃ A : Real, 0 <= A ∧
      ∀ g : SchwartzLineTestFunction,
        Function.support g ⊆
            Set.Icc (-(epsilon / (8 * Real.pi))) (epsilon / (8 * Real.pi)) →
        0 <= burnolLocalSpectralQuadraticForm g := by
  obtain ⟨epsilon, hepsilon, A, hA, hpointwise⟩ :=
    exists_burnolLocalCoefficient_cosineCorrection_of_binet hBinet
  refine ⟨epsilon, hepsilon, A, hA, ?_⟩
  intro g hsupport
  exact integral_burnolLocalCoefficient_mul_fourierEnergyDensity_nonneg
    hpointwise hsupport hepsilon
      (integrable_burnolLocalCoefficient_mul_fourierEnergyDensity_of_binet hBinet g)

/-- The same fixed-support theorem in Burnol's multiplicative coordinates.
The class is one interval `[1/c,c]`, with
`c = exp (epsilon / (8*pi))`; it is not a dense union over support radii. -/
theorem exists_burnolFixedSupport_multiplicative_nonneg_of_binet
    (hBinet : BennettGammaBinetDigammaFormula) :
    ∃ epsilon > 0, ∃ A : Real, 0 <= A ∧
      ∀ g : SchwartzLineTestFunction,
        Function.support (multiplicativeLogPushforward g) ⊆
            Set.Icc
              (Real.exp (-(epsilon / (8 * Real.pi))))
              (Real.exp (epsilon / (8 * Real.pi))) →
        0 <= burnolLocalSpectralQuadraticForm g := by
  obtain ⟨epsilon, hepsilon, A, hA, hnonneg⟩ :=
    exists_burnolFixedSupport_spectral_nonneg_of_binet hBinet
  refine ⟨epsilon, hepsilon, A, hA, ?_⟩
  intro g hsupport
  apply hnonneg g
  · exact
      (support_multiplicativeLogPushforward_subset_iff
        (g := g) (r := epsilon / (8 * Real.pi))).mp hsupport

end

end SchwartzLineTestFunction

end RiemannHypothesisProject
