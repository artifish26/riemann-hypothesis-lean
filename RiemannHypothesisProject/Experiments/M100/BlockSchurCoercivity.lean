import Mathlib.Analysis.Real.Sqrt

/-!
# M100-DF6A abstract block-Schur coercivity

This experimental module isolates the scalar algebra behind the DF5A block
assembly.  A squared Schur bound controls the negative cross term and yields a
lower bound for the complete two-block energy.

The statements are independent of the project source form, its domains, and
the endpoint certificates.  Later DF6 modules must supply those identifications
before applying these lemmas.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

/-- The scalar value of a symmetric two-block quadratic form. -/
def blockSchurFormValue (low far cross : Real) : Real :=
  low + 2 * cross + far

/-- A squared Schur bound controls the most negative possible cross term. -/
theorem two_mul_cross_ge_neg_sqrt_mul_add
    {rho low far cross : Real}
    (hrho : 0 <= rho)
    (hlow : 0 <= low)
    (hfar : 0 <= far)
    (hschur : cross ^ 2 <= rho * low * far) :
    -(Real.sqrt rho) * (low + far) <= 2 * cross := by
  have hsqrt_nonneg : 0 <= Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrt_sq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho
  by_cases hsqrt_zero : Real.sqrt rho = 0
  · have hrho_zero : rho = 0 := by
      nlinarith
    have hcross_sq : cross ^ 2 <= 0 := by
      simpa [hrho_zero] using hschur
    have hcross_zero : cross = 0 := by
      nlinarith [sq_nonneg cross]
    simp [hsqrt_zero, hcross_zero]
  by_cases hlow_zero : low = 0
  · have hcross_sq : cross ^ 2 <= 0 := by
      simpa [hlow_zero] using hschur
    have hcross_zero : cross = 0 := by
      nlinarith [sq_nonneg cross]
    nlinarith [mul_nonneg hsqrt_nonneg hfar]
  have hsqrt_pos : 0 < Real.sqrt rho :=
    lt_of_le_of_ne hsqrt_nonneg (Ne.symm hsqrt_zero)
  have hlow_pos : 0 < low := lt_of_le_of_ne hlow (Ne.symm hlow_zero)
  have hcoefficient_pos : 0 < Real.sqrt rho * low :=
    mul_pos hsqrt_pos hlow_pos
  have hschur' :
      cross ^ 2 <= (Real.sqrt rho) ^ 2 * low * far := by
    rwa [hsqrt_sq]
  have hidentity :
      (Real.sqrt rho * low) *
          (Real.sqrt rho * (low + far) + 2 * cross) =
        (Real.sqrt rho * low + cross) ^ 2 +
          ((Real.sqrt rho) ^ 2 * low * far - cross ^ 2) := by
    ring
  have hproduct :
      0 <= (Real.sqrt rho * low) *
        (Real.sqrt rho * (low + far) + 2 * cross) := by
    rw [hidentity]
    exact add_nonneg (sq_nonneg _) (sub_nonneg.mpr hschur')
  have hbracket :
      0 <= Real.sqrt rho * (low + far) + 2 * cross :=
    nonneg_of_mul_nonneg_left
      (by simpa [mul_comm] using hproduct) hcoefficient_pos
  nlinarith

/-- Abstract block-Schur-to-full-energy lower bound. -/
theorem blockSchurFormValue_ge_one_sub_sqrt_mul
    {rho low far cross : Real}
    (hrho : 0 <= rho)
    (hlow : 0 <= low)
    (hfar : 0 <= far)
    (hschur : cross ^ 2 <= rho * low * far) :
    (1 - Real.sqrt rho) * (low + far) <=
      blockSchurFormValue low far cross := by
  have hcross :=
    two_mul_cross_ge_neg_sqrt_mul_add hrho hlow hfar hschur
  unfold blockSchurFormValue
  nlinarith

/-- Any checked reserve below `1 - sqrt rho` inherits the full-energy bound. -/
theorem blockSchurFormValue_ge_reserve_mul
    {rho reserve low far cross : Real}
    (hrho : 0 <= rho)
    (hlow : 0 <= low)
    (hfar : 0 <= far)
    (hschur : cross ^ 2 <= rho * low * far)
    (hreserve : reserve <= 1 - Real.sqrt rho) :
    reserve * (low + far) <= blockSchurFormValue low far cross := by
  calc
    reserve * (low + far) <=
        (1 - Real.sqrt rho) * (low + far) :=
      mul_le_mul_of_nonneg_right hreserve (add_nonneg hlow hfar)
    _ <= blockSchurFormValue low far cross :=
      blockSchurFormValue_ge_one_sub_sqrt_mul hrho hlow hfar hschur

/-- A nonnegative reserve transports any lower bound for the diagonal energy
to the complete two-block form. -/
theorem blockSchurFormValue_ge_coercive
    {rho reserve low far cross diagonalLower : Real}
    (hrho : 0 <= rho)
    (hlow : 0 <= low)
    (hfar : 0 <= far)
    (hschur : cross ^ 2 <= rho * low * far)
    (hreserve_nonneg : 0 <= reserve)
    (hreserve : reserve <= 1 - Real.sqrt rho)
    {target : Real}
    (hdiagonal : diagonalLower * target <= low + far) :
    reserve * diagonalLower * target <=
      blockSchurFormValue low far cross := by
  calc
    reserve * diagonalLower * target =
        reserve * (diagonalLower * target) := by ring
    _ <= reserve * (low + far) :=
      mul_le_mul_of_nonneg_left hdiagonal hreserve_nonneg
    _ <= blockSchurFormValue low far cross :=
      blockSchurFormValue_ge_reserve_mul
        hrho hlow hfar hschur hreserve

/-- Exact even-parity reserve used by the closed DF5A endpoint package. -/
theorem three_quarters_lt_one_sub_sqrt_one_twentieth :
    (3 / 4 : Real) < 1 - Real.sqrt (1 / 20 : Real) := by
  have hsqrt_nonneg : 0 <= Real.sqrt (1 / 20 : Real) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (1 / 20 : Real)) ^ 2 = (1 / 20 : Real) :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- Exact odd-parity reserve used by the closed DF5A endpoint package. -/
theorem one_div_two_thousand_lt_one_sub_sqrt_nine_nine_nine_thousandths :
    (1 / 2000 : Real) < 1 - Real.sqrt (999 / 1000 : Real) := by
  have hsqrt_nonneg : 0 <= Real.sqrt (999 / 1000 : Real) :=
    Real.sqrt_nonneg _
  have hsqrt_sq :
      (Real.sqrt (999 / 1000 : Real)) ^ 2 = (999 / 1000 : Real) :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- The abstract theorem specialized to DF5A's even-parity reserve. -/
theorem blockSchurFormValue_ge_even_reserve
    {low far cross : Real}
    (hlow : 0 <= low)
    (hfar : 0 <= far)
    (hschur : cross ^ 2 <= (1 / 20 : Real) * low * far) :
    (3 / 4 : Real) * (low + far) <=
      blockSchurFormValue low far cross :=
  blockSchurFormValue_ge_reserve_mul
    (by norm_num) hlow hfar hschur
    three_quarters_lt_one_sub_sqrt_one_twentieth.le

/-- The abstract theorem specialized to DF5A's odd-parity reserve. -/
theorem blockSchurFormValue_ge_odd_reserve
    {low far cross : Real}
    (hlow : 0 <= low)
    (hfar : 0 <= far)
    (hschur : cross ^ 2 <= (999 / 1000 : Real) * low * far) :
    (1 / 2000 : Real) * (low + far) <=
      blockSchurFormValue low far cross :=
  blockSchurFormValue_ge_reserve_mul
    (by norm_num) hlow hfar hschur
    one_div_two_thousand_lt_one_sub_sqrt_nine_nine_nine_thousandths.le

end

end M100
end Experiments
end RiemannHypothesisProject
