import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointComparisonFormAssembly

/-!
# Endpoint source-variable normalization

This module changes the ordinary endpoint Fourier pairing from Mathlib's
frequency `xi` to Suzuki's source variable `z = -2*pi*xi`.  It keeps the
finitely many removable resonances out of pointwise statements and removes
them only almost everywhere in the integral.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory
open scoped ComplexConjugate

/-- Suzuki's source-variable logarithmic multiplier. -/
def suzukiYoshidaEndpointSourceVariableWeight (z : Real) : Real :=
  Real.log |z| + Real.eulerMascheroniConstant

/-- The source-variable sine quotient for one normalized endpoint
exponential.  Its value at the removable resonance is immaterial to the
integrals below. -/
def suzukiYoshidaEndpointSourceVariableProfile
    (r : Real) (n : Int) (z : Real) : Complex :=
  ((Real.sqrt (2 * r))⁻¹ : Complex) *
    ((2 * Real.sin (r * z + (n : Real) * Real.pi) /
      (z + (n : Real) * Real.pi / r) : Real) : Complex)

/-- Source-variable profile of the normalized even Yoshida mode. -/
def suzukiYoshidaEndpointEvenSourceVariableProfile
    (r : Real) (n : Nat) (z : Real) : Complex :=
  if n = 0 then
    suzukiYoshidaEndpointSourceVariableProfile r 0 z
  else
    ((Real.sqrt 2)⁻¹ : Complex) *
      (suzukiYoshidaEndpointSourceVariableProfile r (n : Int) z +
        suzukiYoshidaEndpointSourceVariableProfile r (-(n : Int)) z)

/-- Source-variable profile of the normalized odd Yoshida mode. -/
def suzukiYoshidaEndpointOddSourceVariableProfile
    (r : Real) (n : Nat) (z : Real) : Complex :=
  ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) *
    (suzukiYoshidaEndpointSourceVariableProfile r (n : Int) z -
      suzukiYoshidaEndpointSourceVariableProfile r (-(n : Int)) z)

/-- Positive even profiles have the exact sum of the two rational source
denominators. -/
theorem suzukiYoshidaEndpointEvenSourceVariableProfile_of_pos
    {r : Real} (n : Nat) (hn : 0 < n) (z : Real) :
    suzukiYoshidaEndpointEvenSourceVariableProfile r n z =
      ((Real.sqrt 2)⁻¹ : Complex) *
        (((Real.sqrt (2 * r))⁻¹ : Complex) *
          ((2 * ((-1 : Real) ^ n) * Real.sin (r * z) /
            (z + (n : Real) * Real.pi / r) : Real) : Complex) +
        ((Real.sqrt (2 * r))⁻¹ : Complex) *
          ((2 * ((-1 : Real) ^ n) * Real.sin (r * z) /
            (z - (n : Real) * Real.pi / r) : Real) : Complex)) := by
  rw [suzukiYoshidaEndpointEvenSourceVariableProfile, if_neg hn.ne']
  unfold suzukiYoshidaEndpointSourceVariableProfile
  have hplus :
      Real.sin (r * z + (n : Real) * Real.pi) =
        (-1 : Real) ^ n * Real.sin (r * z) := by
    exact Real.sin_add_nat_mul_pi (r * z) n
  have hminus :
      Real.sin (r * z + -(n : Real) * Real.pi) =
        (-1 : Real) ^ n * Real.sin (r * z) := by
    convert Real.sin_sub_nat_mul_pi (r * z) n using 1 <;> ring
  simp only [Int.cast_natCast, Int.cast_neg]
  rw [hplus, hminus]
  push_cast
  congr 2 <;> field_simp <;> ring

/-- Odd profiles have the exact difference of the two rational source
denominators. -/
theorem suzukiYoshidaEndpointOddSourceVariableProfile_eq
    {r : Real} (n : Nat) (z : Real) :
    suzukiYoshidaEndpointOddSourceVariableProfile r n z =
      ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) *
        (((Real.sqrt (2 * r))⁻¹ : Complex) *
          ((2 * ((-1 : Real) ^ n) * Real.sin (r * z) /
            (z + (n : Real) * Real.pi / r) : Real) : Complex) -
        ((Real.sqrt (2 * r))⁻¹ : Complex) *
          ((2 * ((-1 : Real) ^ n) * Real.sin (r * z) /
            (z - (n : Real) * Real.pi / r) : Real) : Complex)) := by
  unfold suzukiYoshidaEndpointOddSourceVariableProfile
    suzukiYoshidaEndpointSourceVariableProfile
  have hplus :
      Real.sin (r * z + (n : Real) * Real.pi) =
        (-1 : Real) ^ n * Real.sin (r * z) := by
    exact Real.sin_add_nat_mul_pi (r * z) n
  have hminus :
      Real.sin (r * z + -(n : Real) * Real.pi) =
        (-1 : Real) ^ n * Real.sin (r * z) := by
    convert Real.sin_sub_nat_mul_pi (r * z) n using 1 <;> ring
  simp only [Int.cast_natCast, Int.cast_neg]
  rw [hplus, hminus]
  push_cast
  congr 2 <;> field_simp <;> ring

/-- Away from zero, the project multiplier becomes Suzuki's literal
`log |z| + EulerGamma` multiplier under `xi = -z/(2*pi)`. -/
theorem suzukiSourceLogFourierWeight_neg_div_two_pi
    {z : Real} (hz : z ≠ 0) :
    suzukiSourceLogFourierWeight (-z / (2 * Real.pi)) =
      suzukiYoshidaEndpointSourceVariableWeight z := by
  unfold suzukiSourceLogFourierWeight
    suzukiYoshidaEndpointSourceVariableWeight
  have htwoPi : 0 < (2 * Real.pi : Real) := by positivity
  have habs : |(-z / (2 * Real.pi) : Real)| = |z| / (2 * Real.pi) := by
    rw [abs_div, abs_neg, abs_of_pos htwoPi]
  rw [habs]
  have hzabs : |z| ≠ 0 := abs_ne_zero.mpr hz
  have hscale : (2 * Real.pi : Real) ≠ 0 := htwoPi.ne'
  rw [show 2 * Real.pi * (|z| / (2 * Real.pi)) = |z| by
    field_simp]

/-- The ordinary endpoint transform is represented almost everywhere by its
source-variable sine quotient after `xi = -z/(2*pi)`. -/
theorem fourier_suzukiYoshidaExponentialFunction_neg_div_two_pi_ae
    {r : Real} (hr : 0 < r) (n : Int) :
    (fun z : Real =>
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n)
        (-z / (2 * Real.pi))) =ᵐ[volume]
      suzukiYoshidaEndpointSourceVariableProfile r n := by
  filter_upwards
      [volume.ae_ne (-((n : Real) * Real.pi / r))] with z hz
  exact fourier_suzukiYoshidaExponentialFunction_eq_sourceFormula
    hr n z hz

/-- The endpoint source integrand in Suzuki's variable. -/
def suzukiYoshidaEndpointSourceVariableIntegrand
    (r : Real) (m n : Int) (z : Real) : Complex :=
  ((suzukiYoshidaEndpointSourceVariableWeight z : Real) : Complex) *
    (suzukiYoshidaEndpointSourceVariableProfile r m z *
      conj (suzukiYoshidaEndpointSourceVariableProfile r n z))

/-- After the exact source substitution, the project endpoint integrand is
almost everywhere the source-variable integrand. -/
theorem suzukiYoshidaEndpointSourceFourierIntegrand_neg_div_two_pi_ae
    {r : Real} (hr : 0 < r) (m n : Int) :
    (fun z : Real =>
      suzukiYoshidaEndpointSourceFourierIntegrand r m n
        (-z / (2 * Real.pi))) =ᵐ[volume]
      suzukiYoshidaEndpointSourceVariableIntegrand r m n := by
  filter_upwards
      [volume.ae_ne (0 : Real),
        fourier_suzukiYoshidaExponentialFunction_neg_div_two_pi_ae hr m,
        fourier_suzukiYoshidaExponentialFunction_neg_div_two_pi_ae hr n]
      with z hz hm hn
  unfold suzukiYoshidaEndpointSourceFourierIntegrand
    suzukiYoshidaEndpointSourceVariableIntegrand
  rw [suzukiSourceLogFourierWeight_neg_div_two_pi hz, hm, hn]

/-- The source-variable endpoint integrand is genuinely integrable for every
integer-mode pair. -/
theorem integrable_suzukiYoshidaEndpointSourceVariableIntegrand
    {r : Real} (hr : 0 < r) (m n : Int) :
    Integrable (suzukiYoshidaEndpointSourceVariableIntegrand r m n) := by
  have hscaled :=
    (integrable_suzukiYoshidaEndpointSourceFourierIntegrand hr m n).comp_mul_left'
      (show (-1 / (2 * Real.pi) : Real) ≠ 0 by positivity)
  apply hscaled.congr
  filter_upwards
      [suzukiYoshidaEndpointSourceFourierIntegrand_neg_div_two_pi_ae
        hr m n] with z hz
  have harg : -1 / (2 * Real.pi) * z = -z / (2 * Real.pi) := by ring
  rw [harg, hz]

/-- Whole-line source-variable normalization of the endpoint pairing.  The
Jacobian is the exact positive factor `2*pi`. -/
theorem two_pi_mul_suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
    {r : Real} (hr : 0 < r) (m n : Int) :
    ((2 * Real.pi : Real) : Complex) *
        suzukiYoshidaEndpointSourceFourierPairing r m n =
      ∫ z : Real,
        suzukiYoshidaEndpointSourceVariableIntegrand r m n z := by
  let f : Real → Complex :=
    suzukiYoshidaEndpointSourceFourierIntegrand r m n
  have hscale := Measure.integral_comp_mul_left
    (g := f) (-1 / (2 * Real.pi) : Real)
  have hscaleAbs : |(-1 / (2 * Real.pi) : Real)⁻¹| = 2 * Real.pi := by
    have htwoPi : 0 < (2 * Real.pi : Real) := by positivity
    have hinv : (-1 / (2 * Real.pi) : Real)⁻¹ = -(2 * Real.pi) := by
      field_simp [Real.pi_ne_zero]
    rw [hinv, abs_neg, abs_of_pos htwoPi]
  have hscaled :
      (∫ z : Real, f (-1 / (2 * Real.pi) * z)) =
        (2 * Real.pi : Real) • ∫ xi : Real, f xi := by
    simpa only [hscaleAbs] using hscale
  unfold suzukiYoshidaEndpointSourceFourierPairing
  rw [← integral_congr_ae
    (suzukiYoshidaEndpointSourceFourierIntegrand_neg_div_two_pi_ae
      hr m n)]
  rw [show (fun z : Real =>
      suzukiYoshidaEndpointSourceFourierIntegrand r m n
        (-z / (2 * Real.pi))) =
      fun z : Real => f (-1 / (2 * Real.pi) * z) by
    funext z
    dsimp only [f]
    congr 2
    ring]
  rw [hscaled]
  rfl

/-- Division by the nonzero Jacobian gives the directly usable normalized
source-variable formula. -/
theorem suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
    {r : Real} (hr : 0 < r) (m n : Int) :
    suzukiYoshidaEndpointSourceFourierPairing r m n =
      (((2 * Real.pi : Real) : Complex)⁻¹) *
        ∫ z : Real,
          suzukiYoshidaEndpointSourceVariableIntegrand r m n z := by
  have htwoPi : ((2 * Real.pi : Real) : Complex) ≠ 0 := by
    exact_mod_cast (show (2 * Real.pi : Real) ≠ 0 by positivity)
  rw [← two_pi_mul_suzukiYoshidaEndpointSourceFourierPairing_eq_sourceVariable
    hr m n]
  field_simp [htwoPi]

end

end RiemannHypothesisProject.Experiments.M100
