import RiemannHypothesisProject.WeilPositivity.BurnolFormulaBridge

/-!
# Burnol residual formula identification

This module proves the normalization chain from the direct completed-zeta
pole evaluations and Gamma logarithmic derivative to Burnol's local spectral
quadratic form. The fixed-support prime cutoff is supplied by
`BurnolFormulaBridge`.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open ComplexCompactExhaustion
open scoped ComplexConjugate FourierTransform

namespace SchwartzLineTestFunction

noncomputable section

/-- The positive completed-zeta pole evaluation is the exponentially
weighted physical autocorrelation. -/
theorem burnolFourierLaplaceSource_I_div_two
    (g : SchwartzLineTestFunction) :
    burnolFourierLaplaceSource g (Complex.I / 2) =
      ∫ x : Real,
        Complex.exp ((Real.pi * x : Real) : Complex) * autocorrelation g x := by
  unfold burnolFourierLaplaceSource
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg (fun z : Complex => Complex.exp z * autocorrelation g x)
  calc
    (((-2 * Real.pi * x : Real) : Complex) * Complex.I *
        (Complex.I / 2)) =
        (((-2 * Real.pi * x : Real) : Complex) *
          (Complex.I * Complex.I)) / 2 := by ring
    _ = ((Real.pi * x : Real) : Complex) := by
      rw [← pow_two Complex.I, Complex.I_sq]
      push_cast
      ring

/-- The negative completed-zeta pole evaluation is the oppositely weighted
physical autocorrelation. -/
theorem burnolFourierLaplaceSource_neg_I_div_two
    (g : SchwartzLineTestFunction) :
    burnolFourierLaplaceSource g (-Complex.I / 2) =
      ∫ x : Real,
        Complex.exp ((-Real.pi * x : Real) : Complex) * autocorrelation g x := by
  unfold burnolFourierLaplaceSource
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg (fun z : Complex => Complex.exp z * autocorrelation g x)
  calc
    (((-2 * Real.pi * x : Real) : Complex) * Complex.I *
        (-Complex.I / 2)) =
        -((((-2 * Real.pi * x : Real) : Complex) *
          (Complex.I * Complex.I)) / 2) := by ring
    _ = ((-Real.pi * x : Real) : Complex) := by
      rw [← pow_two Complex.I, Complex.I_sq]
      push_cast
      ring

private theorem integrable_exp_mul_autocorrelation_of_fixedSupport
    {g : SchwartzLineTestFunction} {r a : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (ha : |a| = Real.pi) :
    Integrable (fun x : Real =>
      Complex.exp ((a * x : Real) : Complex) * autocorrelation g x) := by
  let C : Real := Real.exp (Real.pi * (2 * |r|))
  have hmajorant : Integrable (fun x : Real =>
      C * norm (autocorrelation g x)) :=
    (autocorrelation g).integrable.norm.const_mul C
  refine Integrable.mono' hmajorant ?_ ?_
  · fun_prop
  · filter_upwards with x
    by_cases hxzero : autocorrelation g x = 0
    · simp [hxzero]
    · have hxle : |x| ≤ 2 * r := by
        by_contra hnot
        have hxlt : 2 * r < |x| := lt_of_not_ge hnot
        exact hxzero
          (autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
            hsupport hxlt)
      have hrnonneg : 0 ≤ r := by
        by_contra hr
        have : |x| < 0 := lt_of_le_of_lt hxle (by linarith)
        exact (not_lt_of_ge (abs_nonneg x)) this
      have hax : a * x ≤ Real.pi * (2 * |r|) := by
        calc
          a * x ≤ |a * x| := le_abs_self _
          _ = |a| * |x| := abs_mul a x
          _ ≤ Real.pi * (2 * |r|) := by
            rw [ha, abs_of_nonneg hrnonneg]
            exact mul_le_mul_of_nonneg_left hxle Real.pi_pos.le
      rw [norm_mul, Complex.norm_exp]
      change Real.exp (a * x) * norm (autocorrelation g x) ≤
        C * norm (autocorrelation g x)
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hax)
        (norm_nonneg _)

/-- Both direct pole-evaluation integrands are integrable on the fixed-support
Burnol class. -/
theorem integrable_burnolPoleEvaluation_pair_of_fixedSupport
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r) :
    Integrable (fun x : Real =>
        Complex.exp ((Real.pi * x : Real) : Complex) * autocorrelation g x) ∧
      Integrable (fun x : Real =>
        Complex.exp ((-Real.pi * x : Real) : Complex) * autocorrelation g x) := by
  constructor
  · exact integrable_exp_mul_autocorrelation_of_fixedSupport hsupport
      (by simp [abs_of_pos Real.pi_pos])
  · exact integrable_exp_mul_autocorrelation_of_fixedSupport hsupport
      (by simp [abs_of_pos Real.pi_pos])

/-- On the fixed-support window, the spatial pole-kernel pairing is exactly
`2*pi` times the sum of the two direct completed-zeta pole evaluations. -/
theorem integral_burnolPoleSpatialKernel_mul_autocorrelation
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement) :
    (∫ x : Real, burnolPoleSpatialKernel x * autocorrelation g x) =
      ((2 * Real.pi : Real) : Complex) *
        (burnolFourierLaplaceSource g (Complex.I / 2) +
          burnolFourierLaplaceSource g (-Complex.I / 2)) := by
  obtain ⟨hpos, hneg⟩ :=
    integrable_burnolPoleEvaluation_pair_of_fixedSupport hsupport
  rw [burnolFourierLaplaceSource_I_div_two,
    burnolFourierLaplaceSource_neg_I_div_two,
    ← integral_add hpos hneg, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : |x| ≤ burnolPoleDisplacement
  · rw [burnolPoleSpatialKernel_eq_poleExponentials hx]
    ring
  · have hxoutside : 2 * r < |x| := hcutoff.trans (lt_of_not_ge hx)
    rw [autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
      hsupport hxoutside]
    simp

/-- Reflection in the second Fourier transform does not change the spatial
pole pairing because the pole kernel is even. -/
theorem integral_burnolPoleSpatialKernel_mul_autocorrelation_neg
    (g : SchwartzLineTestFunction) :
    (∫ x : Real, burnolPoleSpatialKernel x * autocorrelation g (-x)) =
      ∫ x : Real, burnolPoleSpatialKernel x * autocorrelation g x := by
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      burnolPoleSpatialKernel x * autocorrelation g x) volume
  simpa only [burnolPoleSpatialKernel_neg, neg_neg] using hreflect

/-- Fourier self-adjointness identifies Burnol's rational spectral pole
kernel with its translated-Cauchy spatial pairing. -/
theorem integral_burnolPoleSpectralKernel_mul_fourierAutocorrelation
    (g : SchwartzLineTestFunction) :
    (∫ t : Real,
        (burnolPoleSpectralKernel t : Complex) * fourierAutocorrelation g t) =
      ∫ x : Real, burnolPoleSpatialKernel x * autocorrelation g x := by
  have hself :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ Real)
        Real.continuous_fourierChar continuous_inner
        integrable_burnolPoleSpatialKernel (fourierAutocorrelation g).integrable
  rw [flip_innerₗ] at hself
  change
    (∫ t : Real,
        (𝓕 (burnolPoleSpatialKernel : Real → Complex)) t •
          fourierAutocorrelation g t) =
      ∫ x : Real,
        burnolPoleSpatialKernel x •
          (𝓕 (fourierAutocorrelation g : Real → Complex)) x at hself
  have hfunctionFourier (x : Real) :
      (𝓕 (fourierAutocorrelation g : Real → Complex)) x =
        autocorrelation g (-x) := by
    rw [← SchwartzMap.fourier_coe]
    exact fourier_fourierAutocorrelation_apply g x
  have hraw :
      (∫ t : Real,
          (burnolPoleSpectralKernel t : Complex) * fourierAutocorrelation g t) =
        ∫ x : Real, burnolPoleSpatialKernel x * autocorrelation g (-x) := by
    simpa only [smul_eq_mul, fourier_burnolPoleSpatialKernel,
      hfunctionFourier] using hself
  exact hraw.trans
    (integral_burnolPoleSpatialKernel_mul_autocorrelation_neg g)

/-- The formula-facing Fourier autocorrelation is the complex coercion of
Burnol's real Fourier energy density. -/
theorem fourierAutocorrelation_eq_fourierEnergyDensity
    (g : SchwartzLineTestFunction) (t : Real) :
    fourierAutocorrelation g t = (fourierEnergyDensity g t : Complex) := by
  rw [fourierAutocorrelation_apply, Complex.mul_conj]
  simp [fourierEnergyDensity]

/-- The rational pole integral is exactly `2*pi` times the direct pole side
on the fixed-support Burnol class. -/
theorem integral_burnolPoleSpectralKernel_mul_fourierEnergyDensity_eq_poleSide
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement) :
    (∫ t : Real,
        burnolPoleSpectralKernel t * fourierEnergyDensity g t) =
      2 * Real.pi * guinandWeilBurnolLiteraturePoleSide g := by
  have hspectral :=
    integral_burnolPoleSpectralKernel_mul_fourierAutocorrelation g
  have hspatial :=
    integral_burnolPoleSpatialKernel_mul_autocorrelation hsupport hcutoff
  have hcast :
      (((∫ t : Real,
          burnolPoleSpectralKernel t * fourierEnergyDensity g t) : Real) :
            Complex) =
        ∫ t : Real,
          (burnolPoleSpectralKernel t : Complex) *
            fourierAutocorrelation g t := by
    calc
      (((∫ t : Real,
          burnolPoleSpectralKernel t * fourierEnergyDensity g t) : Real) :
            Complex) =
          ∫ t : Real,
            ((burnolPoleSpectralKernel t * fourierEnergyDensity g t : Real) :
              Complex) := integral_ofReal.symm
      _ = ∫ t : Real,
          (burnolPoleSpectralKernel t : Complex) *
            fourierAutocorrelation g t := by
        apply integral_congr_ae
        filter_upwards with t
        rw [fourierAutocorrelation_eq_fourierEnergyDensity]
        push_cast
        rfl
  have hcomplex := hcast.trans (hspectral.trans hspatial)
  have hre := congrArg Complex.re hcomplex
  unfold guinandWeilBurnolLiteraturePoleSide
  simpa [Complex.mul_re] using hre

/-- The existing literature Gamma side is exactly the Archimedean part of
Burnol's coefficient, with the same `2*pi` formula normalization. -/
theorem two_pi_mul_guinandWeilLiteratureGammaSide_eq_burnolArchimedeanIntegral
    (g : SchwartzLineTestFunction) :
    2 * Real.pi * guinandWeilLiteratureGammaSide (fourierAutocorrelation g) =
      ∫ t : Real,
        (-Real.log Real.pi +
            (Complex.digamma (bellottiWongGammaLine t)).re) *
          fourierEnergyDensity g t := by
  rw [guinandWeilLiteratureGammaSide_eq_digammaIntegral]
  rw [← mul_assoc, show 2 * Real.pi * (1 / Real.pi) = 2 by
    field_simp [Real.pi_ne_zero]]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [fourierAutocorrelation_eq_fourierEnergyDensity]
  change
    2 * (((fourierEnergyDensity g t : Complex) *
      (-(Real.log Real.pi : Complex) / 2 +
        Complex.digamma (bellottiWongGammaLine t) / 2)).re) = _
  norm_num [Complex.mul_re, Complex.div_re]
  ring

/-- Burnol's rational pole kernel is uniformly bounded. -/
theorem abs_burnolPoleSpectralKernel_le (t : Real) :
    |burnolPoleSpectralKernel t| ≤ 8 * Real.sqrt 2 := by
  have hden : 1 ≤ 1 + 4 * t ^ 2 := by nlinarith [sq_nonneg t]
  have hnumNonneg :
      0 ≤ 8 * Real.sqrt 2 * |Real.cos (Real.log 2 * t)| := by positivity
  have hcoeffNonneg : 0 ≤ 8 * Real.sqrt 2 := by positivity
  calc
    |burnolPoleSpectralKernel t| =
        (8 * Real.sqrt 2 * |Real.cos (Real.log 2 * t)|) /
          (1 + 4 * t ^ 2) := by
      unfold burnolPoleSpectralKernel
      rw [abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 8),
        abs_of_nonneg (Real.sqrt_nonneg 2),
        abs_of_nonneg (zero_le_one.trans hden)]
    _ ≤ 8 * Real.sqrt 2 * |Real.cos (Real.log 2 * t)| :=
      div_le_self hnumNonneg hden
    _ ≤ 8 * Real.sqrt 2 := by
      simpa using mul_le_mul_of_nonneg_left
        (abs_le.mpr (Real.cos_mem_Icc (Real.log 2 * t))) hcoeffNonneg

/-- The rational pole term times Fourier energy is integrable for every
Schwartz base test. -/
theorem integrable_burnolPoleSpectralKernel_mul_fourierEnergyDensity
    (g : SchwartzLineTestFunction) :
    Integrable (fun t : Real =>
      burnolPoleSpectralKernel t * fourierEnergyDensity g t) := by
  apply (integrable_fourierEnergyDensity g).bdd_mul
      (c := 8 * Real.sqrt 2)
  · apply Continuous.aestronglyMeasurable
    unfold burnolPoleSpectralKernel
    exact (by fun_prop : Continuous (fun t : Real =>
      8 * Real.sqrt 2 * Real.cos (Real.log 2 * t))).div
        (by fun_prop) (fun t => by nlinarith [sq_nonneg t])
  · filter_upwards with t
    simpa only [Real.norm_eq_abs] using abs_burnolPoleSpectralKernel_le t

/-- Burnol's local coefficient is the sum of the rational pole and
Archimedean Gamma kernels appearing in the explicit formula. -/
theorem burnolLocalCoefficient_eq_pole_add_archimedean (t : Real) :
    burnolLocalCoefficient t =
      burnolPoleSpectralKernel t +
        (-Real.log Real.pi +
          (Complex.digamma (bellottiWongGammaLine t)).re) := by
  unfold burnolLocalCoefficient burnolPoleSpectralKernel
  ring

/-- The decisive project-normalized fixed-support bridge: on Burnol's exact fixed
support class, the existing local spectral quadratic form is `2*pi` times
the actual Guinand-Weil prime/pole/Gamma residual. The only finiteness input
retained is integrability of the exact local term. -/
theorem burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureResidualSide
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement)
    (hintegrable : Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t)) :
    burnolLocalSpectralQuadraticForm g =
      2 * Real.pi * guinandWeilBurnolLiteratureResidualSide g := by
  have hpoleIntegrable :=
    integrable_burnolPoleSpectralKernel_mul_fourierEnergyDensity g
  have harchIntegrable : Integrable (fun t : Real =>
      (-Real.log Real.pi +
          (Complex.digamma (bellottiWongGammaLine t)).re) *
        fourierEnergyDensity g t) := by
    have hsub := hintegrable.sub hpoleIntegrable
    convert hsub using 1
    ext t
    change
      (-Real.log Real.pi +
          (Complex.digamma (bellottiWongGammaLine t)).re) *
        fourierEnergyDensity g t =
      burnolLocalCoefficient t * fourierEnergyDensity g t -
        burnolPoleSpectralKernel t * fourierEnergyDensity g t
    rw [burnolLocalCoefficient_eq_pole_add_archimedean]
    ring
  unfold burnolLocalSpectralQuadraticForm
  calc
    (∫ t : Real,
        burnolLocalCoefficient t * fourierEnergyDensity g t) =
        ∫ t : Real,
          burnolPoleSpectralKernel t * fourierEnergyDensity g t +
            (-Real.log Real.pi +
                (Complex.digamma (bellottiWongGammaLine t)).re) *
              fourierEnergyDensity g t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [burnolLocalCoefficient_eq_pole_add_archimedean]
      ring
    _ = (∫ t : Real,
          burnolPoleSpectralKernel t * fourierEnergyDensity g t) +
        ∫ t : Real,
          (-Real.log Real.pi +
              (Complex.digamma (bellottiWongGammaLine t)).re) *
            fourierEnergyDensity g t :=
      integral_add hpoleIntegrable harchIntegrable
    _ = 2 * Real.pi * guinandWeilBurnolLiteraturePoleSide g +
        2 * Real.pi *
          guinandWeilLiteratureGammaSide (fourierAutocorrelation g) := by
      rw [integral_burnolPoleSpectralKernel_mul_fourierEnergyDensity_eq_poleSide
        hsupport hcutoff,
        ← two_pi_mul_guinandWeilLiteratureGammaSide_eq_burnolArchimedeanIntegral]
    _ = 2 * Real.pi * guinandWeilBurnolLiteratureResidualSide g := by
      rw [guinandWeilBurnolLiteratureResidualSide,
        guinandWeilLiteraturePrimeSide_fourierAutocorrelation_eq_zero
          hsupport hcutoff]
      ring

/-- When the borrowed Guinand-Weil source theorem is supplied, the same
quadratic form is the multiplicity-aware completed-zeta zero pairing. -/
theorem burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureZeroSide
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement)
    (hintegrable : Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t))
    (hsource : BurnolGuinandWeilSourceAssumptions g) :
    burnolLocalSpectralQuadraticForm g =
      2 * Real.pi * guinandWeilBurnolLiteratureZeroSide g := by
  rw [hsource.formula]
  exact
    burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureResidualSide
      hsupport hcutoff hintegrable

/-- Positivity of Burnol's local form transfers to the actual residual after
the normalization bridge, without invoking the source formula identity. -/
theorem guinandWeilBurnolLiteratureResidualSide_nonneg_of_burnolLocal
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement)
    (hintegrable : Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t))
    (hnonneg : 0 ≤ burnolLocalSpectralQuadraticForm g) :
    0 ≤ guinandWeilBurnolLiteratureResidualSide g := by
  have hbridge :=
    burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureResidualSide
      hsupport hcutoff hintegrable
  rw [hbridge] at hnonneg
  exact (mul_nonneg_iff_of_pos_left
    (by positivity : 0 < 2 * Real.pi)).mp hnonneg

/-- Under the borrowed source theorem, the same fixed-support positivity is
positivity of the multiplicity-aware completed-zeta pairing. -/
theorem guinandWeilBurnolLiteratureZeroSide_nonneg_of_burnolLocal
    {g : SchwartzLineTestFunction} {r : Real}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r)
    (hcutoff : 2 * r < burnolPoleDisplacement)
    (hintegrable : Integrable (fun t : Real =>
      burnolLocalCoefficient t * fourierEnergyDensity g t))
    (hsource : BurnolGuinandWeilSourceAssumptions g)
    (hnonneg : 0 ≤ burnolLocalSpectralQuadraticForm g) :
    0 ≤ guinandWeilBurnolLiteratureZeroSide g := by
  rw [hsource.formula]
  exact guinandWeilBurnolLiteratureResidualSide_nonneg_of_burnolLocal
    hsupport hcutoff hintegrable hnonneg

end

end SchwartzLineTestFunction

end RiemannHypothesisProject
