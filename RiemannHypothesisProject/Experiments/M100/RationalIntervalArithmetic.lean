import RiemannHypothesisProject.Experiments.M100.RationalMatrixCertificate
import Mathlib.Data.Rat.Floor

/-!
# Rational interval arithmetic for M100-DF6D4

This module adds the elementary compositional operations used by the analytic
enclosure layer.  The interval endpoints remain exact rationals; each theorem
proves soundness after casting to the real analytic quantity.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

namespace RationalInterval

/-- The degenerate interval at an exact rational value. -/
def point (q : Rat) : RationalInterval := ⟨q, q⟩

/-- Minkowski addition of rational intervals. -/
def add (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower + J.lower, I.upper + J.upper⟩

/-- Minkowski sum of a finite family of rational intervals. -/
def sum {ι : Type*} (s : Finset ι) (f : ι → RationalInterval) :
    RationalInterval :=
  ⟨∑ i ∈ s, (f i).lower, ∑ i ∈ s, (f i).upper⟩

/-- Midpoint of an interval, used by the signed-product evaluator. -/
def center (I : RationalInterval) : Rat := (I.lower + I.upper) / 2

/-- Half-width of an ordered interval. -/
def radius (I : RationalInterval) : Rat := (I.upper - I.lower) / 2

/-- Signed product enclosure in midpoint-radius form.  Unlike `mulNonneg`,
this works for intervals crossing zero and remains sharp when both inputs are
narrow. -/
def mulCentered (I J : RationalInterval) : RationalInterval :=
  let c := I.center * J.center
  let r := |I.center| * J.radius + |J.center| * I.radius + I.radius * J.radius
  ⟨c - r, c + r⟩

/-- Reflection of a rational interval through the origin. -/
def neg (I : RationalInterval) : RationalInterval :=
  ⟨-I.upper, -I.lower⟩

/-- Minkowski subtraction of rational intervals. -/
def sub (I J : RationalInterval) : RationalInterval :=
  I.add J.neg

/-- Symmetric interval with exact rational radius. -/
def symmetric (radius : Rat) : RationalInterval :=
  ⟨-radius, radius⟩

/-- Multiplication by an exact rational scalar, with endpoint order handled
uniformly for positive and negative scalars. -/
def scale (q : Rat) (I : RationalInterval) : RationalInterval :=
  ⟨min (q * I.lower) (q * I.upper), max (q * I.lower) (q * I.upper)⟩

/-- Product enclosure specialized to nonnegative intervals.  This is the
high-throughput operation used by the frozen endpoint evaluators, where all
reciprocal-series numerators and denominators are nonnegative. -/
def mulNonneg (I J : RationalInterval) : RationalInterval :=
  ⟨I.lower * J.lower, I.upper * J.upper⟩

/-- Product enclosure where the left interval is nonnegative and the right
interval may have either sign. -/
def mulLeftNonneg (I J : RationalInterval) : RationalInterval :=
  ⟨min (I.lower * J.lower) (I.upper * J.lower),
    max (I.lower * J.upper) (I.upper * J.upper)⟩

/-- Natural power enclosure specialized to a nonnegative interval. -/
def powNonneg (I : RationalInterval) (n : Nat) : RationalInterval :=
  ⟨I.lower ^ n, I.upper ^ n⟩

/-- Reciprocal enclosure for an interval with a strictly positive lower
endpoint. -/
def invPos (I : RationalInterval) : RationalInterval :=
  ⟨I.upper⁻¹, I.lower⁻¹⟩

/-- Quotient enclosure for a nonnegative numerator interval and a strictly
positive denominator interval. -/
def divNonneg (I J : RationalInterval) : RationalInterval :=
  I.mulNonneg J.invPos

/-- Round a rational down to the grid with denominator `D`. -/
def roundDown (D : Nat) (q : Rat) : Rat :=
  (⌊q * D⌋ : Int) / D

/-- Round a rational up to the grid with denominator `D`. -/
def roundUp (D : Nat) (q : Rat) : Rat :=
  (⌈q * D⌉ : Int) / D

/-- Outward rounding of both endpoints to a common rational grid. -/
def roundOut (D : Nat) (I : RationalInterval) : RationalInterval :=
  ⟨roundDown D I.lower, roundUp D I.upper⟩

theorem contains_point (q : Rat) : (point q).Contains (q : Real) := by
  simp [point, Contains]

theorem contains_add
    {I J : RationalInterval} {x y : Real}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.add J).Contains (x + y) := by
  unfold Contains add at *
  norm_num at *
  exact ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem contains_sum
    {ι : Type*} {s : Finset ι} {f : ι → RationalInterval}
    {x : ι → Real}
    (hx : ∀ i ∈ s, (f i).Contains (x i)) :
    (sum s f).Contains (∑ i ∈ s, x i) := by
  unfold Contains sum
  simp only [Rat.cast_sum]
  constructor
  · exact Finset.sum_le_sum fun i hi => (hx i hi).1
  · exact Finset.sum_le_sum fun i hi => (hx i hi).2

private theorem abs_sub_center_le_radius
    {I : RationalInterval} {x : Real} (hx : I.Contains x) :
    |x - (I.center : Real)| ≤ (I.radius : Real) := by
  unfold Contains at hx
  unfold center radius
  norm_num at hx ⊢
  rw [abs_le]
  constructor <;> linarith

theorem contains_mulCentered
    {I J : RationalInterval} {x y : Real}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.mulCentered J).Contains (x * y) := by
  have hxError := abs_sub_center_le_radius hx
  have hyError := abs_sub_center_le_radius hy
  have hIRadius : (0 : Real) ≤ (I.radius : Real) := by
    unfold radius
    norm_num
    linarith [hx.1, hx.2]
  have hJRadius : (0 : Real) ≤ (J.radius : Real) := by
    unfold radius
    norm_num
    linarith [hy.1, hy.2]
  have hError :
      |x * y - (I.center : Real) * (J.center : Real)| ≤
        |(I.center : Real)| * (J.radius : Real) +
          |(J.center : Real)| * (I.radius : Real) +
            (I.radius : Real) * (J.radius : Real) := by
    rw [show x * y - (I.center : Real) * (J.center : Real) =
        (I.center : Real) * (y - (J.center : Real)) +
          (J.center : Real) * (x - (I.center : Real)) +
            (x - (I.center : Real)) * (y - (J.center : Real)) by ring]
    calc
      |(I.center : Real) * (y - (J.center : Real)) +
          (J.center : Real) * (x - (I.center : Real)) +
            (x - (I.center : Real)) * (y - (J.center : Real))| ≤
          |(I.center : Real) * (y - (J.center : Real))| +
            |(J.center : Real) * (x - (I.center : Real))| +
              |(x - (I.center : Real)) * (y - (J.center : Real))| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      _ = |(I.center : Real)| * |y - (J.center : Real)| +
            |(J.center : Real)| * |x - (I.center : Real)| +
              |x - (I.center : Real)| * |y - (J.center : Real)| := by
        rw [abs_mul, abs_mul, abs_mul]
      _ ≤ |(I.center : Real)| * (J.radius : Real) +
            |(J.center : Real)| * (I.radius : Real) +
              (I.radius : Real) * (J.radius : Real) := by
        gcongr
  unfold mulCentered Contains
  dsimp only
  norm_num
  rw [abs_le] at hError
  exact ⟨by linarith [hError.1], by linarith [hError.2]⟩

theorem contains_neg
    {I : RationalInterval} {x : Real} (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  unfold Contains neg at *
  norm_num at *
  exact ⟨hx.2, hx.1⟩

theorem contains_sub
    {I J : RationalInterval} {x y : Real}
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.sub J).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using contains_add hx (contains_neg hy)

theorem contains_symmetric_of_abs_le
    {radius : Rat} {x : Real}
    (hx : abs x ≤ (radius : Real)) :
    (symmetric radius).Contains x := by
  unfold symmetric Contains
  rw [abs_le] at hx
  simpa using hx

theorem contains_scale
    {I : RationalInterval} {x : Real} (q : Rat) (hx : I.Contains x) :
    (scale q I).Contains ((q : Real) * x) := by
  unfold Contains scale at *
  rw [Rat.cast_min, Rat.cast_max, Rat.cast_mul, Rat.cast_mul]
  rcases le_total (0 : Rat) q with hq | hq
  · have hqReal : (0 : Real) ≤ (q : Real) := by exact_mod_cast hq
    exact
      ⟨min_le_of_left_le (mul_le_mul_of_nonneg_left hx.1 hqReal),
        le_max_of_le_right (mul_le_mul_of_nonneg_left hx.2 hqReal)⟩
  · have hqReal : (q : Real) ≤ 0 := by exact_mod_cast hq
    exact
      ⟨min_le_of_right_le (mul_le_mul_of_nonpos_left hx.2 hqReal),
        le_max_of_le_left (mul_le_mul_of_nonpos_left hx.1 hqReal)⟩

theorem contains_mulNonneg
    {I J : RationalInterval} {x y : Real}
    (hI0 : 0 ≤ I.lower) (hJ0 : 0 ≤ J.lower)
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.mulNonneg J).Contains (x * y) := by
  unfold Contains mulNonneg at *
  norm_num at *
  have hI0Real : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hJ0Real : (0 : Real) ≤ (J.lower : Real) := by exact_mod_cast hJ0
  have hx0 : 0 ≤ x := hI0Real.trans hx.1
  have hy0 : 0 ≤ y := hJ0Real.trans hy.1
  have hIUpper0 : 0 ≤ (I.upper : Real) := hx0.trans hx.2
  constructor
  · exact mul_le_mul hx.1 hy.1 hJ0Real hx0
  · exact mul_le_mul hx.2 hy.2 hy0 hIUpper0

theorem contains_mulLeftNonneg
    {I J : RationalInterval} {x y : Real}
    (hI0 : 0 ≤ I.lower) (hx : I.Contains x) (hy : J.Contains y) :
    (I.mulLeftNonneg J).Contains (x * y) := by
  have hLowerScale := contains_scale J.lower hx
  have hUpperScale := contains_scale J.upper hx
  have hLower0 : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hLower0.trans hx.1
  unfold Contains scale at hLowerScale hUpperScale
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_mul] at hLowerScale hUpperScale
  unfold Contains mulLeftNonneg
  simp only [Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  constructor
  · calc
      min ((I.lower : Real) * (J.lower : Real))
            ((I.upper : Real) * (J.lower : Real)) ≤
          (J.lower : Real) * x := by
        simpa only [mul_comm] using hLowerScale.1
      _ = x * (J.lower : Real) := by ring
      _ ≤ x * y := mul_le_mul_of_nonneg_left hy.1 hx0
  · calc
      x * y ≤ x * (J.upper : Real) :=
        mul_le_mul_of_nonneg_left hy.2 hx0
      _ = (J.upper : Real) * x := by ring
      _ ≤ max ((I.lower : Real) * (J.upper : Real))
            ((I.upper : Real) * (J.upper : Real)) := by
        simpa only [mul_comm] using hUpperScale.2

theorem contains_powNonneg
    {I : RationalInterval} {x : Real} (n : Nat)
    (hI0 : 0 ≤ I.lower) (hx : I.Contains x) :
    (I.powNonneg n).Contains (x ^ n) := by
  unfold Contains powNonneg at *
  norm_num at *
  have hLower0 : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hx0 : 0 ≤ x := hLower0.trans hx.1
  constructor
  · exact pow_le_pow_left₀ hLower0 hx.1 n
  · exact pow_le_pow_left₀ hx0 hx.2 n

theorem contains_invPos
    {I : RationalInterval} {x : Real}
    (hIpos : 0 < I.lower) (hx : I.Contains x) :
    I.invPos.Contains x⁻¹ := by
  unfold Contains invPos at *
  norm_num at *
  have hLowerPos : (0 : Real) < (I.lower : Real) := by exact_mod_cast hIpos
  have hxPos : 0 < x := hLowerPos.trans_le hx.1
  have hUpperPos : (0 : Real) < (I.upper : Real) := hxPos.trans_le hx.2
  constructor
  · exact (inv_le_inv₀ hUpperPos hxPos).2 hx.2
  · exact (inv_le_inv₀ hxPos hLowerPos).2 hx.1

theorem contains_divNonneg
    {I J : RationalInterval} {x y : Real}
    (hI0 : 0 ≤ I.lower) (hJpos : 0 < J.lower)
    (hx : I.Contains x) (hy : J.Contains y) :
    (I.divNonneg J).Contains (x / y) := by
  have hJOrdered : J.lower ≤ J.upper := by
    exact_mod_cast hy.1.trans hy.2
  have hJUpperPos : 0 < J.upper := hJpos.trans_le hJOrdered
  have hInv0 : 0 ≤ J.invPos.lower := by
    unfold invPos
    exact inv_nonneg.mpr hJUpperPos.le
  simpa only [div_eq_mul_inv, divNonneg] using
    contains_mulNonneg hI0 hInv0 hx (contains_invPos hJpos hy)

theorem roundDown_le {D : Nat} (hD : 0 < D) (q : Rat) :
    roundDown D q ≤ q := by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).2
  simpa only [Int.cast_ofNat, Rat.cast_natCast] using
    (Int.floor_le (q * D))

theorem le_roundUp {D : Nat} (hD : 0 < D) (q : Rat) :
    q ≤ roundUp D q := by
  unfold roundUp
  apply (le_div_iff₀ (by exact_mod_cast hD)).2
  simpa only [Int.cast_ofNat, Rat.cast_natCast] using
    (Int.le_ceil (q * D))

theorem contains_roundOut
    {D : Nat} (hD : 0 < D) {I : RationalInterval} {x : Real}
    (hx : I.Contains x) :
    (roundOut D I).Contains x := by
  have hlower : (roundDown D I.lower : Real) ≤ (I.lower : Real) := by
    exact_mod_cast roundDown_le hD I.lower
  have hupper : (I.upper : Real) ≤ (roundUp D I.upper : Real) := by
    exact_mod_cast le_roundUp hD I.upper
  unfold Contains roundOut
  exact ⟨hlower.trans hx.1, hx.2.trans hupper⟩

/-- Widening an interval preserves every enclosure it already proves. -/
theorem contains_of_widen
    {I J : RationalInterval} {x : Real}
    (hlower : J.lower ≤ I.lower) (hupper : I.upper ≤ J.upper)
    (hx : I.Contains x) : J.Contains x := by
  unfold Contains at *
  have hlowerReal : (J.lower : Real) ≤ (I.lower : Real) := by
    exact_mod_cast hlower
  have hupperReal : (I.upper : Real) ≤ (J.upper : Real) := by
    exact_mod_cast hupper
  constructor
  · exact hlowerReal.trans hx.1
  · exact hx.2.trans hupperReal

end RationalInterval

end M100
end Experiments
end RiemannHypothesisProject
