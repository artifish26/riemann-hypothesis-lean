import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Burnol formula pole kernel

Burnol's fixed-support formula replaces the two completed-zeta pole
evaluations by a rational spectral coefficient. This module freezes that
coefficient in Mathlib's `exp (-2 * pi * I * x * t)` Fourier convention.

The proof starts from the exact Fourier transform of `exp (-pi * |x|)`.
After two translations by `log 2 / (2*pi)`, the resulting spatial kernel is
the pair of pole exponentials on the support window used by Burnol.
-/

namespace RiemannHypothesisProject

open MeasureTheory Set
open scoped FourierTransform

noncomputable section

/-- The elementary spatial Cauchy kernel whose Fourier transform has
denominator `1 + 4*t^2`. -/
def burnolCauchySpatialKernel (x : Real) : Complex :=
  Real.exp (-Real.pi * |x|)

/-- Burnol's displacement in additive coordinates under Mathlib's Fourier
character. -/
def burnolPoleDisplacement : Real :=
  Real.log 2 / (2 * Real.pi)

/-- The rational part of Burnol's local coefficient. -/
def burnolPoleSpectralKernel (t : Real) : Real :=
  8 * Real.sqrt 2 * Real.cos (Real.log 2 * t) / (1 + 4 * t ^ 2)

/-- The translated spatial kernel corresponding to
`burnolPoleSpectralKernel`. -/
def burnolPoleSpatialKernel (x : Real) : Complex :=
  (2 * Real.pi * Real.sqrt 2 : Real) *
    (burnolCauchySpatialKernel (x - burnolPoleDisplacement) +
      burnolCauchySpatialKernel (x + burnolPoleDisplacement))

@[simp]
theorem burnolCauchySpatialKernel_neg (x : Real) :
    burnolCauchySpatialKernel (-x) = burnolCauchySpatialKernel x := by
  simp [burnolCauchySpatialKernel]

/-- The translated pole kernel is even. -/
theorem burnolPoleSpatialKernel_neg (x : Real) :
    burnolPoleSpatialKernel (-x) = burnolPoleSpatialKernel x := by
  unfold burnolPoleSpatialKernel
  rw [show -x - burnolPoleDisplacement =
      -(x + burnolPoleDisplacement) by ring,
    show -x + burnolPoleDisplacement =
      -(x - burnolPoleDisplacement) by ring]
  rw [burnolCauchySpatialKernel_neg, burnolCauchySpatialKernel_neg]
  ring

private def burnolCauchyFourierIntegrand (t x : Real) : Complex :=
  Complex.exp (((-2 * Real.pi * x * t : Real) : Complex) * Complex.I) *
    burnolCauchySpatialKernel x

private def burnolCauchyRightExponent (t : Real) : Complex :=
  -(Real.pi : Complex) -
    ((2 * Real.pi * t : Real) : Complex) * Complex.I

private def burnolCauchyLeftExponent (t : Real) : Complex :=
  (Real.pi : Complex) -
    ((2 * Real.pi * t : Real) : Complex) * Complex.I

private theorem burnolCauchyFourierIntegrand_eq_right
    (t x : Real) (hx : x ∈ Set.Ioi 0) :
    burnolCauchyFourierIntegrand t x =
      Complex.exp (burnolCauchyRightExponent t * x) := by
  rw [burnolCauchyFourierIntegrand, burnolCauchySpatialKernel,
    abs_of_pos hx]
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  simp only [burnolCauchyRightExponent]
  push_cast
  ring_nf

private theorem burnolCauchyFourierIntegrand_eq_left
    (t x : Real) (hx : x ∈ Set.Iic 0) :
    burnolCauchyFourierIntegrand t x =
      Complex.exp (burnolCauchyLeftExponent t * x) := by
  rw [burnolCauchyFourierIntegrand, burnolCauchySpatialKernel,
    abs_of_nonpos hx]
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  simp only [burnolCauchyLeftExponent]
  push_cast
  ring_nf

private theorem burnolCauchyRightExponent_re_neg (t : Real) :
    (burnolCauchyRightExponent t).re < 0 := by
  simp [burnolCauchyRightExponent, Real.pi_pos]

private theorem burnolCauchyLeftExponent_re_pos (t : Real) :
    0 < (burnolCauchyLeftExponent t).re := by
  simp [burnolCauchyLeftExponent, Real.pi_pos]

/-- The elementary Cauchy spatial kernel is integrable. -/
theorem integrable_burnolCauchySpatialKernel :
    Integrable burnolCauchySpatialKernel := by
  have hright : IntegrableOn burnolCauchySpatialKernel (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Ioi
        (a := -(Real.pi : Complex)) (by simp [Real.pi_pos]) 0) ?_
        measurableSet_Ioi
    intro x hx
    rw [burnolCauchySpatialKernel, abs_of_pos hx,
      Complex.ofReal_exp]
    push_cast
    ring_nf
  have hleft : IntegrableOn burnolCauchySpatialKernel (Set.Iic 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Iic
        (a := (Real.pi : Complex)) (by simp [Real.pi_pos]) 0) ?_
        measurableSet_Iic
    intro x hx
    rw [burnolCauchySpatialKernel, abs_of_nonpos hx,
      Complex.ofReal_exp]
    push_cast
    ring_nf
  have hunion := hleft.union hright
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hunion

/-- The two translated Cauchy kernels forming the pole kernel are integrable. -/
theorem integrable_burnolPoleSpatialKernel :
    Integrable burnolPoleSpatialKernel := by
  have hminus : Integrable (fun x : Real =>
      burnolCauchySpatialKernel (x - burnolPoleDisplacement)) := by
    simpa only [sub_eq_add_neg, Function.comp_def] using
      (MeasurePreserving.integrable_comp_of_integrable
        (measurePreserving_add_right
          (MeasureSpace.volume : Measure Real) (-burnolPoleDisplacement))
        integrable_burnolCauchySpatialKernel)
  have hplus : Integrable (fun x : Real =>
      burnolCauchySpatialKernel (x + burnolPoleDisplacement)) := by
    simpa only [Function.comp_def] using
      (MeasurePreserving.integrable_comp_of_integrable
        (measurePreserving_add_right
          (MeasureSpace.volume : Measure Real) burnolPoleDisplacement)
        integrable_burnolCauchySpatialKernel)
  unfold burnolPoleSpatialKernel
  exact (hminus.add hplus).const_mul _

/-- Exact Fourier transform of `exp (-pi * |x|)` in Mathlib's convention. -/
theorem fourier_burnolCauchySpatialKernel (t : Real) :
    (𝓕 burnolCauchySpatialKernel) t =
      ((2 / (Real.pi * (1 + 4 * t ^ 2)) : Real) : Complex) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ x : Real, burnolCauchyFourierIntegrand t x) = _
  have hright : IntegrableOn (burnolCauchyFourierIntegrand t) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Ioi
        (burnolCauchyRightExponent_re_neg t) 0) ?_ measurableSet_Ioi
    intro x hx
    exact (burnolCauchyFourierIntegrand_eq_right t x hx).symm
  have hleft : IntegrableOn (burnolCauchyFourierIntegrand t) (Set.Iic 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Iic
        (burnolCauchyLeftExponent_re_pos t) 0) ?_ measurableSet_Iic
    intro x hx
    exact (burnolCauchyFourierIntegrand_eq_left t x hx).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright]
  have hleftIntegral :
      (∫ x : Real in Set.Iic 0, burnolCauchyFourierIntegrand t x) =
        1 / burnolCauchyLeftExponent t := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (burnolCauchyFourierIntegrand_eq_left t)]
    simpa using integral_exp_mul_complex_Iic
      (burnolCauchyLeftExponent_re_pos t) 0
  have hrightIntegral :
      (∫ x : Real in Set.Ioi 0, burnolCauchyFourierIntegrand t x) =
        -1 / burnolCauchyRightExponent t := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (burnolCauchyFourierIntegrand_eq_right t)]
    simpa using integral_exp_mul_complex_Ioi
      (burnolCauchyRightExponent_re_neg t) 0
  rw [hleftIntegral, hrightIntegral]
  have hleft_ne : burnolCauchyLeftExponent t ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp [burnolCauchyLeftExponent, Real.pi_ne_zero] at this
  have hright_ne : burnolCauchyRightExponent t ≠ 0 := by
    intro hzero
    have := congrArg Complex.re hzero
    simp [burnolCauchyRightExponent, Real.pi_ne_zero] at this
  have hden_ne : (1 + 4 * t ^ 2 : Real) ≠ 0 := by
    nlinarith [sq_nonneg t]
  have hdenComplex_ne : (1 + 4 * (t : Complex) ^ 2) ≠ 0 := by
    exact_mod_cast hden_ne
  have hleftDen_ne :
      ((Real.pi : Complex) -
          ((2 * Real.pi * t : Real) : Complex) * Complex.I) ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp [Real.pi_ne_zero] at hreal
  have hrightDen_ne :
      (-(Real.pi : Complex) -
          ((2 * Real.pi * t : Real) : Complex) * Complex.I) ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp [Real.pi_ne_zero] at hreal
  push_cast
  simp only [burnolCauchyLeftExponent, burnolCauchyRightExponent]
  field_simp [hleftDen_ne, hrightDen_ne, Real.pi_ne_zero, hdenComplex_ne]
  ring_nf
  rw [Complex.I_sq]
  push_cast
  ring

/-- Exact Fourier transform of the translated pole kernel. -/
theorem fourier_burnolPoleSpatialKernel (t : Real) :
    (𝓕 burnolPoleSpatialKernel) t =
      (burnolPoleSpectralKernel t : Complex) := by
  let shiftedMinus : Real → Complex := fun x =>
    burnolCauchySpatialKernel (x - burnolPoleDisplacement)
  let shiftedPlus : Real → Complex := fun x =>
    burnolCauchySpatialKernel (x + burnolPoleDisplacement)
  have hminus :
      (𝓕 shiftedMinus) t =
        Real.fourierChar (-(t * burnolPoleDisplacement)) •
          (𝓕 burnolCauchySpatialKernel) t := by
    change
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
          ((burnolCauchySpatialKernel : Real → Complex) ∘
            fun x => x + (-burnolPoleDisplacement)) t =
        Real.fourierChar (-(t * burnolPoleDisplacement)) •
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
            burnolCauchySpatialKernel t
    simpa using congrFun
      (VectorFourier.fourierIntegral_comp_add_right
        Real.fourierChar volume (innerₗ Real) burnolCauchySpatialKernel
          (-burnolPoleDisplacement)) t
  have hplus :
      (𝓕 shiftedPlus) t =
        Real.fourierChar (t * burnolPoleDisplacement) •
          (𝓕 burnolCauchySpatialKernel) t := by
    change
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
          ((burnolCauchySpatialKernel : Real → Complex) ∘
            fun x => x + burnolPoleDisplacement) t =
        Real.fourierChar (t * burnolPoleDisplacement) •
          VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
            burnolCauchySpatialKernel t
    simpa using congrFun
      (VectorFourier.fourierIntegral_comp_add_right
        Real.fourierChar volume (innerₗ Real) burnolCauchySpatialKernel
          burnolPoleDisplacement) t
  have hkernel :
      burnolPoleSpatialKernel =
        ((2 * Real.pi * Real.sqrt 2 : Real) : Complex) •
          (shiftedMinus + shiftedPlus) := by
    funext x
    simp [burnolPoleSpatialKernel, shiftedMinus, shiftedPlus, smul_eq_mul]
  have hminusIntegrable : Integrable shiftedMinus := by
    simpa only [shiftedMinus, sub_eq_add_neg, Function.comp_def] using
      (MeasurePreserving.integrable_comp_of_integrable
        (measurePreserving_add_right
          (MeasureSpace.volume : Measure Real) (-burnolPoleDisplacement))
        integrable_burnolCauchySpatialKernel)
  have hplusIntegrable : Integrable shiftedPlus := by
    simpa only [shiftedPlus, Function.comp_def] using
      (MeasurePreserving.integrable_comp_of_integrable
        (measurePreserving_add_right
          (MeasureSpace.volume : Measure Real) burnolPoleDisplacement)
        integrable_burnolCauchySpatialKernel)
  let phase : Real → Complex := fun x =>
    Complex.exp (((-2 * Real.pi * x * t : Real) : Complex) * Complex.I)
  have hphase_norm (x : Real) : norm (phase x) ≤ 1 := by
    simp [phase, Complex.norm_exp]
  have hminusPhase : Integrable (fun x => phase x * shiftedMinus x) := by
    apply hminusIntegrable.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with x
      exact hphase_norm x
  have hplusPhase : Integrable (fun x => phase x * shiftedPlus x) := by
    apply hplusIntegrable.bdd_mul (c := 1)
    · fun_prop
    · filter_upwards with x
      exact hphase_norm x
  have hminusFourier :
      (∫ x : Real, phase x * shiftedMinus x) = (𝓕 shiftedMinus) t := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    rfl
  have hplusFourier :
      (∫ x : Real, phase x * shiftedPlus x) = (𝓕 shiftedPlus) t := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    rfl
  rw [hkernel, Real.fourier_real_eq_integral_exp_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  change
    (∫ x : Real,
      phase x *
        (((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
          (shiftedMinus x + shiftedPlus x))) = _
  calc
    (∫ x : Real,
        phase x *
          (((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
            (shiftedMinus x + shiftedPlus x))) =
      ((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
        ((∫ x : Real, phase x * shiftedMinus x) +
          ∫ x : Real, phase x * shiftedPlus x) := by
        rw [← integral_add hminusPhase hplusPhase, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring
    _ = ((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
        ((𝓕 shiftedMinus) t + (𝓕 shiftedPlus) t) := by
      rw [hminusFourier, hplusFourier]
  rw [hminus, hplus, fourier_burnolCauchySpatialKernel]
  simp only [smul_eq_mul, Real.fourierChar_apply, Circle.smul_def]
  rw [show
      (2 * Real.pi : Real) * (-(t * burnolPoleDisplacement)) =
        -(Real.log 2 * t) by
        unfold burnolPoleDisplacement
        field_simp [Real.pi_ne_zero],
    show
      (2 * Real.pi : Real) * (t * burnolPoleDisplacement) =
        Real.log 2 * t by
        unfold burnolPoleDisplacement
        field_simp [Real.pi_ne_zero]]
  rw [← add_mul]
  rw [show
      Complex.exp (((-(Real.log 2 * t) : Real) : Complex) * Complex.I) +
          Complex.exp (((Real.log 2 * t : Real) : Complex) * Complex.I) =
        ((2 * Real.cos (Real.log 2 * t) : Real) : Complex) by
        rw [add_comm]
        push_cast
        rw [← Complex.two_cos]]
  unfold burnolPoleSpectralKernel
  push_cast
  have hpi : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : (1 + 4 * (t : Complex) ^ 2) ≠ 0 := by
    norm_cast
    nlinarith [sq_nonneg t]
  field_simp [hpi, hden]
  ring

/-- The Burnol displacement is positive. -/
theorem burnolPoleDisplacement_pos : 0 < burnolPoleDisplacement := by
  unfold burnolPoleDisplacement
  positivity

/-- On the fixed-support window, the translated Cauchy kernels are exactly
the two completed-zeta pole exponentials. -/
theorem burnolPoleSpatialKernel_eq_poleExponentials
    {x : Real} (hx : |x| ≤ burnolPoleDisplacement) :
    burnolPoleSpatialKernel x =
      ((2 * Real.pi : Real) : Complex) *
        (Complex.exp ((Real.pi * x : Real) : Complex) +
          Complex.exp ((-Real.pi * x : Real) : Complex)) := by
  have hxUpper : x ≤ burnolPoleDisplacement :=
    (le_abs_self x).trans hx
  have hxLower : -burnolPoleDisplacement ≤ x :=
    (neg_le_of_abs_le hx)
  have hminus : x - burnolPoleDisplacement ≤ 0 := sub_nonpos.mpr hxUpper
  have hplus : 0 ≤ x + burnolPoleDisplacement := by linarith
  rw [burnolPoleSpatialKernel, burnolCauchySpatialKernel,
    burnolCauchySpatialKernel, abs_of_nonpos hminus, abs_of_nonneg hplus]
  have hlog : Real.exp (-Real.pi * burnolPoleDisplacement) =
      (Real.sqrt 2)⁻¹ := by
    rw [burnolPoleDisplacement]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [show -Real.pi * (Real.log 2 / (2 * Real.pi)) =
        -(Real.log 2) / 2 by
          field_simp [hpi]]
    rw [show -(Real.log 2) / 2 = -(Real.log 2 / 2) by ring,
      Real.exp_neg, Real.exp_half,
      Real.exp_log (by norm_num : (0 : Real) < 2)]
  have hlogComplex :
      Complex.exp ((-Real.pi * burnolPoleDisplacement : Real) : Complex) =
        (((Real.sqrt 2)⁻¹ : Real) : Complex) := by
    rw [← Complex.ofReal_exp]
    exact_mod_cast hlog
  simp only [Complex.ofReal_exp]
  rw [show
      Complex.exp ((-Real.pi * -(x - burnolPoleDisplacement) : Real) : Complex) =
        Complex.exp ((Real.pi * x : Real) : Complex) *
          Complex.exp ((-Real.pi * burnolPoleDisplacement : Real) : Complex) by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring]
  rw [show
      Complex.exp ((-Real.pi * (x + burnolPoleDisplacement) : Real) : Complex) =
        Complex.exp ((-Real.pi * x : Real) : Complex) *
          Complex.exp ((-Real.pi * burnolPoleDisplacement : Real) : Complex) by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring]
  rw [hlogComplex]
  have hsqrtReal_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hcoefficient :
      (2 * Real.pi * Real.sqrt 2) * (Real.sqrt 2)⁻¹ = 2 * Real.pi := by
    field_simp [hsqrtReal_ne]
  have hcoefficientComplex :
      ((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
          (((Real.sqrt 2)⁻¹ : Real) : Complex) =
        ((2 * Real.pi : Real) : Complex) := by
    exact_mod_cast hcoefficient
  calc
    ((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
        (Complex.exp ((Real.pi * x : Real) : Complex) *
            (((Real.sqrt 2)⁻¹ : Real) : Complex) +
          Complex.exp ((-Real.pi * x : Real) : Complex) *
            (((Real.sqrt 2)⁻¹ : Real) : Complex)) =
      (((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
          (((Real.sqrt 2)⁻¹ : Real) : Complex)) *
            Complex.exp ((Real.pi * x : Real) : Complex) +
        (((2 * Real.pi * Real.sqrt 2 : Real) : Complex) *
          (((Real.sqrt 2)⁻¹ : Real) : Complex)) *
            Complex.exp ((-Real.pi * x : Real) : Complex) := by ring
    _ = _ := by rw [hcoefficientComplex]; ring

end

end RiemannHypothesisProject
