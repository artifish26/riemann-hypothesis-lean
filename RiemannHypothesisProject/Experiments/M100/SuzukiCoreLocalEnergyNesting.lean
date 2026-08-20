import RiemannHypothesisProject.SchwartzLineTestFunction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# M100-DF6B Suzuki smooth-core local-energy nesting

This experimental module formalizes the elementary radius-change calculation
for Suzuki's local energy on `C_c^infinity(-a,a)`.  Core functions are global
Schwartz functions with support in the open interval, so zero extension to a
larger concentric interval is literal subtype inclusion.

The module evaluates both outer-annulus kernel integrals and proves that their
polarized cross contribution cancels the change in the logarithmic boundary
potential.  It does not construct closed form domains or identify the complete
project-normalized Weil form.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

/-- The smooth compactly supported core, represented by the global zero
extension used in Suzuki's finite-interval convention. -/
def SuzukiSmoothCore (a : Real) :=
  {v : SchwartzLineTestFunction //
    Function.support v ⊆ Set.Ioo (-a) a}

/-- Zero extension from a smaller concentric core to a larger one.  Because
core functions are already global and vanish off the smaller interval, the
underlying Schwartz function is unchanged. -/
def suzukiSmoothCoreZeroExtension
  {a b : Real} (hab : a <= b) : SuzukiSmoothCore a -> SuzukiSmoothCore b :=
  fun v =>
    ⟨v.1, fun _x hx =>
      let hsmall := v.2 hx
      ⟨lt_of_le_of_lt (neg_le_neg hab) hsmall.1,
        lt_of_lt_of_le hsmall.2 hab⟩⟩

@[simp]
theorem suzukiSmoothCoreZeroExtension_apply
    {a b : Real} (hab : a <= b) (v : SuzukiSmoothCore a) (x : Real) :
    (suzukiSmoothCoreZeroExtension hab v).1 x = v.1 x := rfl

/-- The larger-radius representative vanishes off the smaller open interval. -/
theorem suzukiSmoothCoreZeroExtension_eq_zero_of_not_mem
    {a b : Real} (hab : a <= b) (v : SuzukiSmoothCore a) {x : Real}
    (hx : x ∉ Set.Ioo (-a) a) :
    (suzukiSmoothCoreZeroExtension hab v).1 x = 0 := by
  change v.1 x = 0
  by_contra hne
  exact hx (v.2 hne)

/-- In particular, zero extension vanishes on both open outer annuli. -/
theorem suzukiSmoothCoreZeroExtension_eq_zero_on_outerAnnulus
    {a b : Real} (hab : a <= b) (v : SuzukiSmoothCore a) {x : Real}
    (hx : x ∈ Set.Ioo (-b) (-a) ∪ Set.Ioo a b) :
    (suzukiSmoothCoreZeroExtension hab v).1 x = 0 := by
  apply suzukiSmoothCoreZeroExtension_eq_zero_of_not_mem hab v
  rintro ⟨hleft, hright⟩
  rcases hx with hx | hx
  · exact (not_lt_of_ge hx.2.le) hleft
  · exact (not_lt_of_ge hx.1.le) hright

/-- The two simplified kernel integrals over the outer annuli.  For a point in
the smaller open interval, the absolute values in `1 / |x-y|` reduce to these
positive denominators. -/
def suzukiOuterAnnulusKernelIntegral
    (a b x : Real) : Real :=
  (∫ y in a..b, 1 / (y - x)) +
    ∫ y in (-b)..(-a), 1 / (x - y)

/-- On the right annulus, the absolute-value kernel has denominator `y-x`. -/
theorem one_div_abs_sub_eq_one_div_sub_right
    {a x y : Real} (hxa : x < a) (hay : a <= y) :
    1 / |x - y| = 1 / (y - x) := by
  rw [abs_of_neg (sub_neg.mpr (lt_of_lt_of_le hxa hay))]
  congr 2
  ring

/-- On the left annulus, the absolute-value kernel has denominator `x-y`. -/
theorem one_div_abs_sub_eq_one_div_sub_left
    {a x y : Real} (hya : y <= -a) (hax : -a < x) :
    1 / |x - y| = 1 / (x - y) := by
  rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt hya hax))]

/-- The right-annulus kernel integral. -/
theorem integral_one_div_sub_right
    {a b x : Real} (hxa : x < a) (hab : a <= b) :
    (∫ y in a..b, 1 / (y - x)) =
      Real.log ((b - x) / (a - x)) := by
  calc
    (∫ y in a..b, 1 / (y - x)) =
        ∫ t in (a - x)..(b - x), 1 / t := by
      simpa only using
        (intervalIntegral.integral_comp_sub_right
          (f := fun t : Real => 1 / t) (a := a) (b := b) x)
    _ = Real.log ((b - x) / (a - x)) :=
      integral_one_div_of_pos
        (sub_pos.mpr hxa) (sub_pos.mpr (lt_of_lt_of_le hxa hab))

/-- The left-annulus kernel integral. -/
theorem integral_one_div_sub_left
    {a b x : Real} (hax : -a < x) (hab : a <= b) :
    (∫ y in (-b)..(-a), 1 / (x - y)) =
      Real.log ((b + x) / (a + x)) := by
  have hbx : -b < x := lt_of_le_of_lt (neg_le_neg hab) hax
  calc
    (∫ y in (-b)..(-a), 1 / (x - y)) =
        ∫ t in (x + a)..(x + b), 1 / t := by
      simpa only [sub_neg_eq_add, add_comm] using
        (intervalIntegral.integral_comp_sub_left
          (f := fun t : Real => 1 / t) (a := -b) (b := -a) x)
    _ = Real.log ((x + b) / (x + a)) :=
      integral_one_div_of_pos
        (by linarith) (by linarith)
    _ = Real.log ((b + x) / (a + x)) := by
      congr 2 <;> ring

/-- Exact logarithmic evaluation of the two outer-annulus integrals. -/
theorem suzukiOuterAnnulusKernelIntegral_eq_boundaryLogIncrement
    {a b x : Real} (hab : a <= b)
    (hleft : -a < x) (hright : x < a) :
    suzukiOuterAnnulusKernelIntegral a b x =
      Real.log (b ^ 2 - x ^ 2) - Real.log (a ^ 2 - x ^ 2) := by
  have haminus : 0 < a - x := sub_pos.mpr hright
  have haplus : 0 < a + x := by linarith
  have hbminus : 0 < b - x := by linarith
  have hbplus : 0 < b + x := by linarith
  rw [suzukiOuterAnnulusKernelIntegral,
    integral_one_div_sub_right hright hab,
    integral_one_div_sub_left hleft hab,
    Real.log_div hbminus.ne' haminus.ne',
    Real.log_div hbplus.ne' haplus.ne']
  calc
    Real.log (b - x) - Real.log (a - x) +
          (Real.log (b + x) - Real.log (a + x)) =
        (Real.log (b - x) + Real.log (b + x)) -
          (Real.log (a - x) + Real.log (a + x)) := by ring
    _ = Real.log ((b - x) * (b + x)) -
          Real.log ((a - x) * (a + x)) := by
      rw [Real.log_mul hbminus.ne' hbplus.ne',
        Real.log_mul haminus.ne' haplus.ne']
    _ = Real.log (b ^ 2 - x ^ 2) -
          Real.log (a ^ 2 - x ^ 2) := by
      congr 1 <;> ring_nf

/-- The polarized cross-region increment in the `1/4`-normalized double
integral.  The two equal cross rectangles account for the coefficient `1/2`. -/
def suzukiCoreCrossRegionIncrement
    (a b : Real) (weight : Real -> Complex) : Complex :=
  (1 / 2 : Complex) *
    ∫ x in Set.Ioo (-a) a,
      (suzukiOuterAnnulusKernelIntegral a b x : Complex) * weight x

/-- The change in the `-1/2` logarithmic boundary potential. -/
def suzukiCoreBoundaryPotentialIncrement
    (a b : Real) (weight : Real -> Complex) : Complex :=
  -(1 / 2 : Complex) *
    ∫ x in Set.Ioo (-a) a,
      ((Real.log (b ^ 2 - x ^ 2) -
        Real.log (a ^ 2 - x ^ 2) : Real) : Complex) * weight x

/-- The complete radius increment in the smooth-core local-energy formula. -/
def suzukiCoreLocalEnergyRadiusIncrement
    (a b : Real) (weight : Real -> Complex) : Complex :=
  suzukiCoreCrossRegionIncrement a b weight +
    suzukiCoreBoundaryPotentialIncrement a b weight

/-- The outer-annulus cross contribution and boundary-potential change cancel
exactly for every polarized core weight. -/
theorem suzukiCoreLocalEnergyRadiusIncrement_eq_zero
    {a b : Real} (hab : a <= b)
    (weight : Real -> Complex) :
    suzukiCoreLocalEnergyRadiusIncrement a b weight = 0 := by
  have hintegral :
      (∫ x in Set.Ioo (-a) a,
          (suzukiOuterAnnulusKernelIntegral a b x : Complex) * weight x) =
        ∫ x in Set.Ioo (-a) a,
          ((Real.log (b ^ 2 - x ^ 2) -
            Real.log (a ^ 2 - x ^ 2) : Real) : Complex) * weight x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [suzukiOuterAnnulusKernelIntegral_eq_boundaryLogIncrement
      hab hx.1 hx.2]
  unfold suzukiCoreLocalEnergyRadiusIncrement
    suzukiCoreCrossRegionIncrement
    suzukiCoreBoundaryPotentialIncrement
  rw [hintegral]
  ring

/-- The complex-polarized weight for two smooth core functions. -/
def suzukiSmoothCorePolarizedWeight
    {a : Real} (u v : SuzukiSmoothCore a) (x : Real) : Complex :=
  u.1 x * conj (v.1 x)

/-- DF6B endpoint: zero extension of two smooth core functions has exact
polarized local-energy radius increment zero. -/
theorem suzukiSmoothCore_polarizedLocalEnergyRadiusIncrement_eq_zero
    {a b : Real} (hab : a <= b)
    (u v : SuzukiSmoothCore a) :
    suzukiCoreLocalEnergyRadiusIncrement a b
      (suzukiSmoothCorePolarizedWeight u v) = 0 :=
  suzukiCoreLocalEnergyRadiusIncrement_eq_zero hab _

/-- Diagonal specialization of the smooth-core cancellation theorem. -/
theorem suzukiSmoothCore_localEnergyRadiusIncrement_eq_zero
    {a b : Real} (hab : a <= b)
    (v : SuzukiSmoothCore a) :
    suzukiCoreLocalEnergyRadiusIncrement a b
      (suzukiSmoothCorePolarizedWeight v v) = 0 :=
  suzukiSmoothCore_polarizedLocalEnergyRadiusIncrement_eq_zero hab v v

end


end M100
end Experiments
end RiemannHypothesisProject
