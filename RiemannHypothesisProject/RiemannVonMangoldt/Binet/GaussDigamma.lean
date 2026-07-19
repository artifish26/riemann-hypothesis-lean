import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Gauss's integral formula for the complex digamma function

This module freezes the exact source statement used by the Binet closure.  It
uses Mathlib's `Complex.digamma`, principal `Complex.log`, and set-integral
conventions directly.  The source theorem itself remains the next analytic
proof target; the normalization checks below prevent later changes of branch,
sign, or Euler-constant convention.
-/

open MeasureTheory

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The convergent combined integrand in Gauss's digamma formula. -/
def gaussDigammaIntegrand (z : Complex) (x : Real) : Complex :=
  (1 - (x : Complex) ^ (z - 1)) / (1 - (x : Complex))

/-- The removable-singularity extension of Gauss's integrand at `w = 1`.
The complex-variable form lets us use Mathlib's slope-extension theorem
directly. -/
def gaussDigammaIntegrandExtension (z w : Complex) : Complex :=
  Function.update
    (fun w : Complex =>
      (w ^ (z - 1) - (1 : Complex) ^ (z - 1)) / (w - 1))
    1 (z - 1) w

/-- The extended quotient agrees with Gauss's original quotient away from its
removable endpoint. -/
theorem gaussDigammaIntegrandExtension_of_ne_one
    (z : Complex) {x : Real} (hx : x ≠ 1) :
    gaussDigammaIntegrandExtension z x = gaussDigammaIntegrand z x := by
  have hxc : (x : Complex) ≠ 1 := by
    exact_mod_cast hx
  simp only [gaussDigammaIntegrandExtension, Function.update_of_ne hxc,
    Complex.one_cpow, gaussDigammaIntegrand]
  rw [show (x : Complex) ^ (z - 1) - 1 =
      -(1 - (x : Complex) ^ (z - 1)) by ring,
    show (x : Complex) - 1 = -(1 - (x : Complex)) by ring, neg_div_neg_eq]

/-- The value `z - 1` assigned at the removable endpoint is the derivative of
`w ↦ w ^ (z - 1)` at `w = 1`. -/
theorem hasDerivAt_cpow_sub_one_at_one (z : Complex) :
    HasDerivAt (fun w : Complex => w ^ (z - 1)) (z - 1) 1 := by
  simpa using
    (HasDerivAt.cpow_const (c := z - 1) (hasDerivAt_id (1 : Complex))
      (Or.inl (by norm_num)))

/-- The extended Gauss quotient is continuous at its removable endpoint. -/
theorem continuousAt_gaussDigammaIntegrandExtension_one (z : Complex) :
    ContinuousAt (gaussDigammaIntegrandExtension z) 1 := by
  exact (hasDerivAt_cpow_sub_one_at_one z).continuousAt_div

/-- The extended Gauss quotient is continuous throughout the open right half
plane.  Only its restriction to the positive real interval is needed below. -/
theorem continuousAt_gaussDigammaIntegrandExtension_of_re_pos
    (z : Complex) {w : Complex} (hw : 0 < w.re) :
    ContinuousAt (gaussDigammaIntegrandExtension z) w := by
  by_cases h1 : w = 1
  · subst w
    exact continuousAt_gaussDigammaIntegrandExtension_one z
  · unfold gaussDigammaIntegrandExtension
    rw [continuousAt_update_of_ne h1]
    exact ((continuousAt_cpow_const (Or.inl hw)).sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr h1)

/-- The removable extension is continuous on the compact interval used for
the `x = 1` endpoint estimate. -/
theorem continuousOn_gaussDigammaIntegrandExtension_half_one (z : Complex) :
    ContinuousOn (fun x : Real => gaussDigammaIntegrandExtension z x)
      (Set.Icc (1 / 2 : Real) 1) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply (continuousAt_gaussDigammaIntegrandExtension_of_re_pos z
    (w := (x : Complex)) ?_).comp Complex.continuous_ofReal.continuousAt
  simpa using (lt_of_lt_of_le (by norm_num : (0 : Real) < 1 / 2) hx.1)

/-- Gauss's combined quotient is integrable on the full source interval for
every point of the right half-plane.  Near zero this is the standard
`Re (z - 1) > -1` power estimate; near one it uses the removable extension. -/
theorem integrableOn_gaussDigammaIntegrand {z : Complex} (hz : 0 < z.re) :
    IntegrableOn (gaussDigammaIntegrand z) (Set.Ioo (0 : Real) 1) := by
  have hpow :
      IntegrableOn (fun x : Real => (x : Complex) ^ (z - 1))
        (Set.Ioo (0 : Real) (3 / 4)) := by
    rw [intervalIntegral.integrableOn_Ioo_cpow_iff
      (by norm_num : (0 : Real) < 3 / 4)]
    simpa using hz
  have hone :
      IntegrableOn (fun _ : Real => (1 : Complex))
        (Set.Ioo (0 : Real) (3 / 4)) := by
    exact integrableOn_const measure_Ioo_lt_top.ne
  have hnumerator :
      IntegrableOn (fun x : Real => 1 - (x : Complex) ^ (z - 1))
        (Set.Ioo (0 : Real) (3 / 4)) :=
    hone.sub hpow
  have hreciprocal :
      ContinuousOn (fun x : Real => (1 - (x : Complex))⁻¹)
        (Set.Icc (0 : Real) (3 / 4)) := by
    refine (continuousOn_const.sub Complex.continuous_ofReal.continuousOn).inv₀ ?_
    intro x hx
    exact sub_ne_zero.mpr (by
      exact_mod_cast ne_of_gt (lt_of_le_of_lt hx.2 (by norm_num : (3 / 4 : Real) < 1)))
  have hzero :
      IntegrableOn (gaussDigammaIntegrand z)
        (Set.Ioo (0 : Real) (3 / 4)) := by
    have hproduct := hnumerator.mul_continuousOn_of_subset hreciprocal
      measurableSet_Ioo isCompact_Icc (by
        intro x hx
        exact ⟨hx.1.le, hx.2.le⟩)
    refine IntegrableOn.congr_fun hproduct ?_ measurableSet_Ioo
    intro x _
    rw [gaussDigammaIntegrand, div_eq_mul_inv]
  have hnearOneExtension :
      IntegrableOn (fun x : Real => gaussDigammaIntegrandExtension z x)
        (Set.Ioo (1 / 2 : Real) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (1 / 2 : Real) ≤ 1)]
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : Real) ≤ 1)]
    exact continuousOn_gaussDigammaIntegrandExtension_half_one z
  have hnearOne :
      IntegrableOn (gaussDigammaIntegrand z) (Set.Ioo (1 / 2 : Real) 1) := by
    refine IntegrableOn.congr_fun hnearOneExtension ?_ measurableSet_Ioo
    intro x hx
    exact gaussDigammaIntegrandExtension_of_ne_one z hx.2.ne
  have hcover :
      Set.Ioo (0 : Real) 1 =
        Set.Ioo 0 (3 / 4) ∪ Set.Ioo (1 / 2) 1 := by
    ext x
    simp only [Set.mem_Ioo, Set.mem_union]
    constructor
    · intro hx
      by_cases h : x < 3 / 4
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨by linarith, hx.2⟩
    · rintro (hx | hx)
      · exact ⟨hx.1, by linarith⟩
      · exact ⟨by linarith, hx.2⟩
  rw [hcover]
  exact hzero.union hnearOne

/-- Gauss's integral formula in the exact right-half-plane normalization needed
for the Binet source closure. -/
def GaussDigammaIntegralFormula : Prop :=
  ∀ z : Complex, 0 < z.re →
    Complex.digamma z + Real.eulerMascheroniConstant =
      ∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand z x

@[simp]
theorem gaussDigammaIntegrand_one (x : Real) :
    gaussDigammaIntegrand 1 x = 0 := by
  simp [gaussDigammaIntegrand]

/-- The source convention agrees unconditionally with Mathlib at `z = 1`. -/
theorem gaussDigamma_formula_at_one :
    Complex.digamma 1 + Real.eulerMascheroniConstant =
      ∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand 1 x := by
  rw [Complex.digamma_one]
  simp

/-- The source convention specializes at `z = 1/2` to the standard
`-2 * log 2` integral value.  This is a normalization consequence, not a proof
of the general source theorem. -/
theorem GaussDigammaIntegralFormula.integral_at_one_half
    (hGauss : GaussDigammaIntegralFormula) :
    (∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand (1 / 2) x) =
      -2 * Complex.log 2 := by
  have h := hGauss (1 / 2) (by norm_num)
  rw [Complex.digamma_one_half] at h
  linear_combination -h

/-- The elementary Mellin integral used by the Gauss-formula recurrence. -/
theorem integral_Ioo_cpow_sub_one {z : Complex} (hz : 0 < z.re) :
    (∫ x : Real in Set.Ioo 0 1, (x : Complex) ^ (z - 1)) = 1 / z := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : Real) ≤ 1 by norm_num),
    integral_cpow]
  · have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hz
      norm_num at hz
    simp [hz0]
  · left
    simpa using hz

/-- Gauss's combined integrand has the same unit-shift difference as the
digamma function.  Keeping the two terms combined avoids any endpoint split. -/
theorem gaussDigammaIntegrand_add_one_sub
    (z : Complex) {x : Real} (hx : x ∈ Set.Ioo (0 : Real) 1) :
    gaussDigammaIntegrand (z + 1) x - gaussDigammaIntegrand z x =
      (x : Complex) ^ (z - 1) := by
  have hx0 : (x : Complex) ≠ 0 := by
    exact_mod_cast hx.1.ne'
  have hx1 : (1 - (x : Complex)) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hx.2.ne')
  rw [gaussDigammaIntegrand, gaussDigammaIntegrand]
  have hpow : (x : Complex) ^ z = (x : Complex) ^ (z - 1) * x := by
    conv_lhs => rw [show z = z - 1 + 1 by ring, Complex.cpow_add _ _ hx0]
    simp
  rw [show z + 1 - 1 = z by ring, hpow]
  field_simp [hx1]
  ring

/-- The integrated Gauss kernel satisfies the digamma recurrence on the right
half-plane. -/
theorem integral_gaussDigammaIntegrand_add_one_sub
    {z : Complex} (hz : 0 < z.re) :
    (∫ x : Real in Set.Ioo 0 1,
      (gaussDigammaIntegrand (z + 1) x - gaussDigammaIntegrand z x)) =
        1 / z := by
  rw [← integral_Ioo_cpow_sub_one hz]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact gaussDigammaIntegrand_add_one_sub z hx

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
