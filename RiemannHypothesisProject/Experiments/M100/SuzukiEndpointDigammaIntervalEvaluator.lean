import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDigammaEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFineConstantEnclosures
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Exact interval evaluator for DF6D4 quarter-line digamma values

The evaluator in this module instantiates the common digamma-series and tail
theorems with exact rational interval arithmetic.  It is designed for the 44
frozen wave numbers used by the endpoint sine-transform certificates.
-/

namespace RiemannHypothesisProject.Experiments.M100

open Filter

set_option maxHeartbeats 1000000

private theorem arctan_small_bounds {x : Real} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x ∧
      Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  let f : Nat → Real := fun n => x ^ (2 * n + 1) / (2 * n + 1 : Nat)
  have hanti : Antitone f := by
    intro n m hnm
    dsimp only [f]
    apply div_le_div₀
    · positivity
    · exact pow_le_pow_of_le_one hx0 hx1.le (by omega)
    · positivity
    · exact_mod_cast (show 2 * n + 1 ≤ 2 * m + 1 by omega)
  have htend := (Real.hasSum_arctan hnorm).tendsto_sum_nat
  have htend' : Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i)
      atTop (nhds (Real.arctan x)) := by
    simpa only [f, mul_div_assoc] using htend
  have hlower := hanti.alternating_series_le_tendsto htend' 1
  have hupper := hanti.tendsto_le_alternating_series htend' 1
  norm_num [f, Finset.sum_range_succ] at hlower hupper
  constructor <;> nlinarith

namespace RationalInterval

/-- A five-term alternating-series enclosure for `arctan` on a nonnegative
interval below one.  Dependency-safe endpoint choices make the result valid
even when the input interval is not degenerate. -/
def arctanSmall (I : RationalInterval) : RationalInterval :=
  ⟨I.lower - I.upper ^ 3 / 3,
    I.upper - I.lower ^ 3 / 3 + I.upper ^ 5 / 5⟩

theorem contains_arctanSmall
    {I : RationalInterval} {x : Real}
    (hI0 : 0 ≤ I.lower) (hI1 : I.upper < 1)
    (hx : I.Contains x) :
    I.arctanSmall.Contains (Real.arctan x) := by
  have hLower0 : (0 : Real) ≤ (I.lower : Real) := by exact_mod_cast hI0
  have hUpper1 : (I.upper : Real) < 1 := by exact_mod_cast hI1
  have hx0 : 0 ≤ x := hLower0.trans hx.1
  have hx1 : x < 1 := hx.2.trans_lt hUpper1
  have hxLower : (I.lower : Real) ≤ x := hx.1
  have hxUpper : x ≤ (I.upper : Real) := hx.2
  have harctan := arctan_small_bounds hx0 hx1
  have hLowerCube : (I.lower : Real) ^ 3 ≤ x ^ 3 := by
    gcongr
  have hUpperCube : x ^ 3 ≤ (I.upper : Real) ^ 3 := by
    gcongr
  have hUpperFifth : x ^ 5 ≤ (I.upper : Real) ^ 5 := by
    gcongr
  unfold Contains arctanSmall
  norm_num
  constructor <;> nlinarith

end RationalInterval

/-- Exact rational quarter-line denominator offset `n + 1/4`. -/
def suzukiDF6D4DigammaOffset (n : Nat) : Rat :=
  n + 1 / 4

private theorem suzukiDF6D4DigammaSummand_increasing
    {d a b : Real}
    (hd : 0 < d) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ d) :
    a / (d ^ 2 + a ^ 2) ≤ b / (d ^ 2 + b ^ 2) := by
  have hda : 0 < d ^ 2 + a ^ 2 := by positivity
  have hdb : 0 < d ^ 2 + b ^ 2 := by positivity
  have hprod : a * b ≤ d * d :=
    mul_le_mul (hab.trans hb) hb (ha.trans hab) hd.le
  rw [div_le_div_iff₀ hda hdb]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (sub_nonneg.mpr hprod)]

private theorem suzukiDF6D4DigammaSummand_decreasing
    {d a b : Real}
    (hd : 0 < d) (hda : d ≤ a) (hab : a ≤ b) :
    b / (d ^ 2 + b ^ 2) ≤ a / (d ^ 2 + a ^ 2) := by
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hdena : 0 < d ^ 2 + a ^ 2 := by positivity
  have hdenb : 0 < d ^ 2 + b ^ 2 := by positivity
  have hprod : d * d ≤ a * b :=
    mul_le_mul hda (hda.trans hab) hd.le ha.le
  rw [div_le_div_iff₀ hdenb hdena]
  nlinarith [mul_nonneg (sub_nonneg.mpr hab)
    (sub_nonneg.mpr hprod)]

private theorem suzukiDF6D4DigammaSummand_global_upper
    {d y : Real} (hd : 0 < d) :
    y / (d ^ 2 + y ^ 2) ≤ 1 / (2 * d) := by
  have hden : 0 < d ^ 2 + y ^ 2 := by positivity
  have htwo : 0 < 2 * d := by positivity
  rw [div_le_div_iff₀ hden htwo]
  nlinarith [sq_nonneg (y - d)]

/-- Exact rational evaluation of one reciprocal-series summand. -/
def suzukiDF6D4DigammaSummandRat (d y : Rat) : Rat :=
  y / (d ^ 2 + y ^ 2)

/-- Dependency-aware interval evaluation of one positive reciprocal-series
summand.  The summand increases up to `y = d` and decreases afterwards; when
the input straddles the maximum, `1 / (2*d)` is its exact global upper bound. -/
def suzukiDF6D4DigammaSummandInterval
    (n : Nat) (Y : RationalInterval) : RationalInterval :=
  let d := suzukiDF6D4DigammaOffset n
  let lowerValue := suzukiDF6D4DigammaSummandRat d Y.lower
  let upperValue := suzukiDF6D4DigammaSummandRat d Y.upper
  if Y.upper ≤ d then
    ⟨lowerValue, upperValue⟩
  else if d ≤ Y.lower then
    ⟨upperValue, lowerValue⟩
  else
    ⟨min lowerValue upperValue, 1 / (2 * d)⟩

theorem suzukiDF6D4DigammaSummandInterval_contains
    (n : Nat) {Y : RationalInterval} {y : Real}
    (hY0 : 0 ≤ Y.lower) (hy : Y.Contains y) :
    (suzukiDF6D4DigammaSummandInterval n Y).Contains
      (y / (((n : Real) + 1 / 4) ^ 2 + y ^ 2)) := by
  let d := suzukiDF6D4DigammaOffset n
  have hd : 0 < d := by
    unfold d suzukiDF6D4DigammaOffset
    positivity
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have hdEq : (d : Real) = (n : Real) + 1 / 4 := by
    unfold d suzukiDF6D4DigammaOffset
    norm_num
  have hLower0 : (0 : Real) ≤ (Y.lower : Real) := by exact_mod_cast hY0
  have hy0 : 0 ≤ y := hLower0.trans hy.1
  have hUpper0 : (0 : Real) ≤ (Y.upper : Real) := hy0.trans hy.2
  have hLowerValue :
      (suzukiDF6D4DigammaSummandRat d Y.lower : Real) =
        (Y.lower : Real) / ((d : Real) ^ 2 + (Y.lower : Real) ^ 2) := by
    norm_num [suzukiDF6D4DigammaSummandRat]
  have hUpperValue :
      (suzukiDF6D4DigammaSummandRat d Y.upper : Real) =
        (Y.upper : Real) / ((d : Real) ^ 2 + (Y.upper : Real) ^ 2) := by
    norm_num [suzukiDF6D4DigammaSummandRat]
  unfold suzukiDF6D4DigammaSummandInterval
  dsimp only
  split_ifs with hIncreasing hDecreasing
  · have hIncreasingR : (Y.upper : Real) ≤ (d : Real) := by
      exact_mod_cast hIncreasing
    unfold RationalInterval.Contains
    norm_num
    rw [hLowerValue, hUpperValue, ← hdEq]
    constructor
    · exact suzukiDF6D4DigammaSummand_increasing
        hdR hLower0 hy.1 (hy.2.trans hIncreasingR)
    · exact suzukiDF6D4DigammaSummand_increasing hdR hy0 hy.2 hIncreasingR
  · have hDecreasingR : (d : Real) ≤ (Y.lower : Real) := by
      exact_mod_cast hDecreasing
    unfold RationalInterval.Contains
    norm_num
    rw [hLowerValue, hUpperValue, ← hdEq]
    constructor
    · exact suzukiDF6D4DigammaSummand_decreasing
        hdR (hDecreasingR.trans hy.1) hy.2
    · exact suzukiDF6D4DigammaSummand_decreasing hdR hDecreasingR hy.1
  · have hUpperGt : (d : Real) < (Y.upper : Real) := by
      exact_mod_cast (lt_of_not_ge hIncreasing)
    have hLowerLt : (Y.lower : Real) < (d : Real) := by
      exact_mod_cast (lt_of_not_ge hDecreasing)
    unfold RationalInterval.Contains
    norm_num
    rw [hLowerValue, hUpperValue, ← hdEq]
    constructor
    · rcases le_total y (d : Real) with hyd | hdy
      · exact Or.inl
          (suzukiDF6D4DigammaSummand_increasing hdR hLower0 hy.1 hyd)
      · exact Or.inr
          (suzukiDF6D4DigammaSummand_decreasing hdR hdy hy.2)
    · rw [show (suzukiDF6D4DigammaOffset n : Real) = (d : Real) by rfl]
      convert suzukiDF6D4DigammaSummand_global_upper hdR using 1
      field_simp [ne_of_gt hdR]

/-- Outward-rounded interval fold for the first `N` positive reciprocal-series
terms.  Rounding after every addition prevents denominator explosion while
preserving the enclosure theorem. -/
def suzukiDF6D4DigammaPartialInterval (D : Nat) :
    Nat → RationalInterval → RationalInterval
  | 0, _ => RationalInterval.point 0
  | N + 1, Y =>
      RationalInterval.roundOut D
        ((suzukiDF6D4DigammaPartialInterval D N Y).add
          (suzukiDF6D4DigammaSummandInterval N Y))

theorem suzukiDF6D4DigammaPartialInterval_contains
    (D N : Nat) (hD : 0 < D) {Y : RationalInterval} {y : Real}
    (hY0 : 0 ≤ Y.lower) (hy : Y.Contains y) :
    (suzukiDF6D4DigammaPartialInterval D N Y).Contains
      (∑ n ∈ Finset.range N,
        y / (((n : Real) + 1 / 4) ^ 2 + y ^ 2)) := by
  induction N with
  | zero =>
      simpa [suzukiDF6D4DigammaPartialInterval] using
        RationalInterval.contains_point 0
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact RationalInterval.contains_roundOut hD
        (RationalInterval.contains_add ih
          (suzukiDF6D4DigammaSummandInterval_contains N hY0 hy))

/-- Small arctangent argument at the reciprocal-series cutoff. -/
def suzukiDF6D4DigammaTailArgumentInterval
    (N : Nat) (Y : RationalInterval) : RationalInterval :=
  Y.divNonneg (RationalInterval.point (suzukiDF6D4DigammaOffset N))

/-- Rational enclosure of the telescoping second-order tail correction. -/
def suzukiDF6D4DigammaTailCorrectionInterval
    (N : Nat) (Y : RationalInterval) : RationalInterval :=
  Y.divNonneg (RationalInterval.point
    (3 * suzukiDF6D4DigammaOffset N ^ 3))

/-- Accelerated second-order interval for the complete reciprocal-series
tail.  Its center is the arctangent integral plus half the first omitted term;
the uncertainty is the proved `N⁻³` telescoping correction. -/
def suzukiDF6D4DigammaTailInterval
    (N : Nat) (Y : RationalInterval) : RationalInterval :=
  let A := (suzukiDF6D4DigammaTailArgumentInterval N Y).arctanSmall
  let T := suzukiDF6D4DigammaSummandInterval N Y
  let C := suzukiDF6D4DigammaTailCorrectionInterval N Y
  let B := A.add (RationalInterval.scale (1 / 2) T)
  ⟨B.lower, B.upper + C.upper⟩

theorem suzukiDF6D4DigammaTailInterval_contains
    (N : Nat) {Y : RationalInterval} {t : Real}
    (ht : 0 ≤ t) (hY0 : 0 ≤ Y.lower) (hy : Y.Contains (t / 2))
    (hArg0 : 0 ≤ (suzukiDF6D4DigammaTailArgumentInterval N Y).lower)
    (hArg1 : (suzukiDF6D4DigammaTailArgumentInterval N Y).upper < 1)
    (hsmall : t / 2 ≤ (N : Real) + 1 / 4) :
    (suzukiDF6D4DigammaTailInterval N Y).Contains
      (∑' k : Nat, suzukiDF6D4DigammaSummand (N + k) t) := by
  let X := suzukiDF6D4DigammaTailArgumentInterval N Y
  let A := X.arctanSmall
  let T := suzukiDF6D4DigammaSummandInterval N Y
  let C := suzukiDF6D4DigammaTailCorrectionInterval N Y
  let B := A.add (RationalInterval.scale (1 / 2) T)
  have hOffsetPos : 0 < suzukiDF6D4DigammaOffset N := by
    unfold suzukiDF6D4DigammaOffset
    positivity
  have hXRaw := RationalInterval.contains_divNonneg hY0 hOffsetPos hy
    (RationalInterval.contains_point (suzukiDF6D4DigammaOffset N))
  have hX : X.Contains
      ((t / 2) / ((N : Real) + 1 / 4)) := by
    dsimp only [X, suzukiDF6D4DigammaTailArgumentInterval]
    convert hXRaw using 1
    unfold suzukiDF6D4DigammaOffset
    norm_num
  have hA : A.Contains
      (Real.arctan ((t / 2) / ((N : Real) + 1 / 4))) := by
    apply RationalInterval.contains_arctanSmall hArg0 hArg1 hX
  have hTRaw := suzukiDF6D4DigammaSummandInterval_contains N hY0 hy
  have hT : T.Contains (suzukiDF6D4DigammaSummand N t) := by
    dsimp only [T]
    convert! hTRaw using 1
  have hCorrectionDenPos : 0 < 3 * suzukiDF6D4DigammaOffset N ^ 3 := by
    have : 0 < suzukiDF6D4DigammaOffset N := by
      unfold suzukiDF6D4DigammaOffset
      positivity
    positivity
  have hCRaw := RationalInterval.contains_divNonneg hY0 hCorrectionDenPos hy
    (RationalInterval.contains_point
      (3 * suzukiDF6D4DigammaOffset N ^ 3))
  have hC : C.Contains (suzukiDF6D4DigammaTailCorrection N t) := by
    dsimp only [C, suzukiDF6D4DigammaTailCorrectionInterval]
    convert! hCRaw using 1
    unfold suzukiDF6D4DigammaTailCorrection suzukiDF6D4DigammaOffset
    push_cast
    field_simp
  have hB : B.Contains (suzukiDF6D4DigammaTailCenter N t) := by
    have hHalf := RationalInterval.contains_scale (1 / 2) hT
    have hAdd := RationalInterval.contains_add hA hHalf
    dsimp only [B]
    unfold suzukiDF6D4DigammaTailCenter suzukiDF6D4DigammaArctanTail
    convert! hAdd using 1
    norm_num
    ring
  have htail := suzukiDF6D4DigammaTail_secondOrder_bounds N ht hsmall
  unfold suzukiDF6D4DigammaTailInterval RationalInterval.Contains
  dsimp only
  norm_num
  constructor
  · linarith [hB.1, htail.1]
  · linarith [hB.2, hC.2, htail.2]

/-- Complete interval evaluator: exact finite prefix plus accelerated complete
tail. -/
def suzukiDF6D4DigammaInterval
    (D N : Nat) (Y : RationalInterval) : RationalInterval :=
  (suzukiDF6D4DigammaPartialInterval D N Y).add
    (suzukiDF6D4DigammaTailInterval N Y)

theorem suzukiDF6D4DigammaInterval_contains
    (D N : Nat) (hD : 0 < D) {Y : RationalInterval} {t : Real}
    (ht : 0 ≤ t) (hY0 : 0 ≤ Y.lower) (hy : Y.Contains (t / 2))
    (hArg0 : 0 ≤ (suzukiDF6D4DigammaTailArgumentInterval N Y).lower)
    (hArg1 : (suzukiDF6D4DigammaTailArgumentInterval N Y).upper < 1)
    (hsmall : t / 2 ≤ (N : Real) + 1 / 4) :
    (suzukiDF6D4DigammaInterval D N Y).Contains
      (Complex.digamma
        ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I)).im := by
  have hPartialRaw :=
    suzukiDF6D4DigammaPartialInterval_contains D N hD hY0 hy
  have hPartial : (suzukiDF6D4DigammaPartialInterval D N Y).Contains
      (∑ n ∈ Finset.range N, suzukiDF6D4DigammaSummand n t) := by
    convert! hPartialRaw using 1
  have hTail :=
    suzukiDF6D4DigammaTailInterval_contains N ht hY0 hy hArg0 hArg1 hsmall
  have hCombined := RationalInterval.contains_add hPartial hTail
  have hsum := summable_suzukiDF6D4DigammaSummand t
  have hsplit :
      (∑ n ∈ Finset.range N, suzukiDF6D4DigammaSummand n t) +
          (∑' k : Nat, suzukiDF6D4DigammaSummand (N + k) t) =
        ∑' n : Nat, suzukiDF6D4DigammaSummand n t := by
    convert hsum.sum_add_tsum_nat_add N using 1
    congr 1
    · apply tsum_congr
      intro k
      congr 1
      omega
  unfold suzukiDF6D4DigammaInterval
  rw [suzukiDF6D4_digamma_im_eq_tsum, ← hsplit]
  exact hCombined

/-- Rational enclosure of the frozen wave number `mode * pi / a_star`. -/
def suzukiDF6D4WaveNumberInterval (mode : Nat) : RationalInterval :=
  (RationalInterval.scale (mode : Rat) suzukiDF6D4PiInterval).divNonneg
    fineAStarInterval

private theorem suzukiDF6D4WaveNumeratorInterval_lower_nonneg (mode : Nat) :
    0 ≤ (RationalInterval.scale (mode : Rat)
      suzukiDF6D4PiInterval).lower := by
  unfold RationalInterval.scale suzukiDF6D4PiInterval
  norm_num

private theorem suzukiDF6D4WaveNumeratorInterval_upper_nonneg (mode : Nat) :
    0 ≤ (RationalInterval.scale (mode : Rat)
      suzukiDF6D4PiInterval).upper := by
  unfold RationalInterval.scale suzukiDF6D4PiInterval
  norm_num

theorem suzukiDF6D4WaveNumberInterval_lower_nonneg (mode : Nat) :
    0 ≤ (suzukiDF6D4WaveNumberInterval mode).lower := by
  unfold suzukiDF6D4WaveNumberInterval RationalInterval.divNonneg
    RationalInterval.mulNonneg RationalInterval.invPos
  dsimp only
  exact mul_nonneg (suzukiDF6D4WaveNumeratorInterval_lower_nonneg mode)
    (inv_nonneg.mpr (by norm_num [fineAStarInterval]))

private theorem suzukiDF6D4WaveNumberInterval_upper_nonneg (mode : Nat) :
    0 ≤ (suzukiDF6D4WaveNumberInterval mode).upper := by
  unfold suzukiDF6D4WaveNumberInterval RationalInterval.divNonneg
    RationalInterval.mulNonneg RationalInterval.invPos
  dsimp only
  exact mul_nonneg (suzukiDF6D4WaveNumeratorInterval_upper_nonneg mode)
    (inv_nonneg.mpr (by norm_num [fineAStarInterval]))

theorem suzukiDF6D4WaveNumberInterval_contains (mode : Nat) :
    (suzukiDF6D4WaveNumberInterval mode).Contains
      ((mode : Real) * Real.pi / suzukiProjectAStar) := by
  have hNumerator := RationalInterval.contains_scale (mode : Rat)
    suzukiDF6D4PiInterval_contains
  have hAStarPos : 0 < fineAStarInterval.lower := by
    norm_num [fineAStarInterval]
  have hquot := RationalInterval.contains_divNonneg
    (suzukiDF6D4WaveNumeratorInterval_lower_nonneg mode) hAStarPos
    hNumerator fineAStarInterval_contains
  unfold suzukiDF6D4WaveNumberInterval
  convert! hquot using 1

/-- Rational enclosure of half the frozen wave number, the variable used by
the positive reciprocal series. -/
def suzukiDF6D4HalfWaveNumberInterval (mode : Nat) : RationalInterval :=
  RationalInterval.scale (1 / 2) (suzukiDF6D4WaveNumberInterval mode)

theorem suzukiDF6D4HalfWaveNumberInterval_lower_nonneg (mode : Nat) :
    0 ≤ (suzukiDF6D4HalfWaveNumberInterval mode).lower := by
  unfold suzukiDF6D4HalfWaveNumberInterval RationalInterval.scale
  norm_num
  exact ⟨suzukiDF6D4WaveNumberInterval_lower_nonneg mode,
    suzukiDF6D4WaveNumberInterval_upper_nonneg mode⟩

theorem suzukiDF6D4HalfWaveNumberInterval_contains (mode : Nat) :
    (suzukiDF6D4HalfWaveNumberInterval mode).Contains
      (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) := by
  have h := RationalInterval.contains_scale (1 / 2)
    (suzukiDF6D4WaveNumberInterval_contains mode)
  unfold suzukiDF6D4HalfWaveNumberInterval
  convert! h using 1
  norm_num
  ring

/-- Frozen `N = 16384` complete digamma enclosure for one endpoint mode. -/
def suzukiDF6D4FrozenDigammaInterval (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4DigammaInterval 1000000000000000000 16384
      (suzukiDF6D4HalfWaveNumberInterval mode))

theorem suzukiDF6D4FrozenDigammaInterval_contains
    (mode : Nat) (hmode : mode ≤ 602) :
    (suzukiDF6D4FrozenDigammaInterval mode).Contains
      (Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im := by
  let t : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have ht : 0 ≤ t := by
    dsimp only [t]
    positivity [suzukiProjectAStar_pos]
  have hArg0 : 0 ≤
      (suzukiDF6D4DigammaTailArgumentInterval 16384
        (suzukiDF6D4HalfWaveNumberInterval mode)).lower := by
    interval_cases mode <;> native_decide
  have hArg1 :
      (suzukiDF6D4DigammaTailArgumentInterval 16384
        (suzukiDF6D4HalfWaveNumberInterval mode)).upper < 1 := by
    interval_cases mode <;> native_decide
  unfold suzukiDF6D4FrozenDigammaInterval
  have hy : (suzukiDF6D4HalfWaveNumberInterval mode).Contains (t / 2) := by
    dsimp only [t]
    exact suzukiDF6D4HalfWaveNumberInterval_contains mode
  have hSmallUpper :
      (suzukiDF6D4HalfWaveNumberInterval mode).upper ≤
        suzukiDF6D4DigammaOffset 16384 := by
    interval_cases mode <;> native_decide
  have hsmall : t / 2 ≤ (16384 : Real) + 1 / 4 := by
    have hUpperReal :
        ((suzukiDF6D4HalfWaveNumberInterval mode).upper : Real) ≤
          (suzukiDF6D4DigammaOffset 16384 : Real) := by
      exact_mod_cast hSmallUpper
    calc
      t / 2 ≤ ((suzukiDF6D4HalfWaveNumberInterval mode).upper : Real) := hy.2
      _ ≤ (suzukiDF6D4DigammaOffset 16384 : Real) := hUpperReal
      _ = (16384 : Real) + 1 / 4 := by
        unfold suzukiDF6D4DigammaOffset
        norm_num
  have h := suzukiDF6D4DigammaInterval_contains
    1000000000000000000 16384 (by norm_num) ht
    (suzukiDF6D4HalfWaveNumberInterval_lower_nonneg mode) hy hArg0 hArg1 hsmall
  have hRounded := RationalInterval.contains_roundOut
    (D := 10000000000000000) (by norm_num) h
  dsimp only [t] at hRounded
  convert hRounded using 1
  congr 3
  push_cast
  ring

end RiemannHypothesisProject.Experiments.M100
