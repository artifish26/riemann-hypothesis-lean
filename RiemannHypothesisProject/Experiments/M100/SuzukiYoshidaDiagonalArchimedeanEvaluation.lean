import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaGammaOperatorBridge

/-!
# Diagonal Archimedean evaluation for the Yoshida endpoint basis

This module evaluates the two diagonal component families left by B3Q-G.  It
keeps the calculation separated into the three literal source pieces:

* the renormalized logarithmic comparison pairing;
* the two elementary pole exponentials; and
* the regular Gamma kernel, whose exponential series is matched term by term
  with the independent DF6D4 diagonal series.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Topology

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Diagonal correlation profiles -/

/-- Half of the symmetric translation energy on a positive even diagonal. -/
def suzukiYoshidaEvenPositiveDiagonalCorrelation
    (mode : Nat) (t : Real) : Real :=
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  ((2 * a - t) * Real.cos (w * t) - Real.sin (w * t) / w) /
    (2 * a)

/-- Half of the symmetric translation energy on the constant even diagonal. -/
def suzukiYoshidaEvenZeroDiagonalCorrelation (t : Real) : Real :=
  1 - t / (2 * suzukiProjectAStar)

/-- Half of the symmetric translation energy on a positive odd diagonal. -/
def suzukiYoshidaOddDiagonalCorrelation
    (mode : Nat) (t : Real) : Real :=
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  ((2 * a - t) * Real.cos (w * t) + Real.sin (w * t) / w) /
    (2 * a)

theorem continuous_suzukiYoshidaEvenPositiveDiagonalCorrelation
    (mode : Nat) :
    Continuous (suzukiYoshidaEvenPositiveDiagonalCorrelation mode) := by
  unfold suzukiYoshidaEvenPositiveDiagonalCorrelation
  dsimp only
  fun_prop

theorem continuous_suzukiYoshidaEvenZeroDiagonalCorrelation :
    Continuous suzukiYoshidaEvenZeroDiagonalCorrelation := by
  unfold suzukiYoshidaEvenZeroDiagonalCorrelation
  fun_prop

theorem continuous_suzukiYoshidaOddDiagonalCorrelation (mode : Nat) :
    Continuous (suzukiYoshidaOddDiagonalCorrelation mode) := by
  unfold suzukiYoshidaOddDiagonalCorrelation
  dsimp only
  fun_prop

@[simp]
theorem suzukiYoshidaEvenPositiveDiagonalCorrelation_zero
    (mode : Nat) :
    suzukiYoshidaEvenPositiveDiagonalCorrelation mode 0 = 1 := by
  simp [suzukiYoshidaEvenPositiveDiagonalCorrelation,
    suzukiProjectAStar_pos.ne']

@[simp]
theorem suzukiYoshidaEvenZeroDiagonalCorrelation_zero :
    suzukiYoshidaEvenZeroDiagonalCorrelation 0 = 1 := by
  simp [suzukiYoshidaEvenZeroDiagonalCorrelation]

@[simp]
theorem suzukiYoshidaOddDiagonalCorrelation_zero (mode : Nat) :
    suzukiYoshidaOddDiagonalCorrelation mode 0 = 1 := by
  simp [suzukiYoshidaOddDiagonalCorrelation,
    suzukiProjectAStar_pos.ne']

/-! ## Elementary exponential primitives -/

def suzukiExpCosPrimitive (d w t : Real) : Real :=
  Real.exp (-d * t) *
      (-d * Real.cos (w * t) + w * Real.sin (w * t)) /
    (d ^ 2 + w ^ 2)

def suzukiExpTCosPrimitive (d w t : Real) : Real :=
  Real.exp (-d * t) *
      (t * (d ^ 2 + w ^ 2) *
          (-d * Real.cos (w * t) + w * Real.sin (w * t)) -
        (d ^ 2 - w ^ 2) * Real.cos (w * t) +
        2 * d * w * Real.sin (w * t)) /
    (d ^ 2 + w ^ 2) ^ 2

private theorem hasDerivAt_exp_neg_mul' (d t : Real) :
    HasDerivAt (fun x : Real => Real.exp (-d * x))
      (-d * Real.exp (-d * t)) t := by
  have h := (Real.hasDerivAt_exp (-d * t)).comp t
    ((hasDerivAt_id t).const_mul (-d))
  have heq :
      (Real.exp ∘ fun x : Real => -d * id x) =ᶠ[nhds t]
        fun x : Real => Real.exp (-d * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_sin_mul' (w t : Real) :
    HasDerivAt (fun x : Real => Real.sin (w * x))
      (w * Real.cos (w * t)) t := by
  have h := (Real.hasDerivAt_sin (w * t)).comp t
    ((hasDerivAt_id t).const_mul w)
  have heq :
      (Real.sin ∘ fun x : Real => w * id x) =ᶠ[nhds t]
        fun x : Real => Real.sin (w * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

private theorem hasDerivAt_cos_mul' (w t : Real) :
    HasDerivAt (fun x : Real => Real.cos (w * x))
      (-w * Real.sin (w * t)) t := by
  have h := (Real.hasDerivAt_cos (w * t)).comp t
    ((hasDerivAt_id t).const_mul w)
  have heq :
      (Real.cos ∘ fun x : Real => w * id x) =ᶠ[nhds t]
        fun x : Real => Real.cos (w * x) := by
    filter_upwards with x
    rfl
  exact (h.congr_of_eventuallyEq heq).congr_deriv (by ring)

theorem hasDerivAt_suzukiExpCosPrimitive
    {d w t : Real} (hden : d ^ 2 + w ^ 2 ≠ 0) :
    HasDerivAt (suzukiExpCosPrimitive d w)
      (Real.exp (-d * t) * Real.cos (w * t)) t := by
  have hbracket :=
    (hasDerivAt_cos_mul' w t).const_mul (-d) |>.add
      ((hasDerivAt_sin_mul' w t).const_mul w)
  have h := ((hasDerivAt_exp_neg_mul' d t).mul hbracket).div_const
    (d ^ 2 + w ^ 2)
  unfold suzukiExpCosPrimitive
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    simp only [Pi.mul_apply, Pi.add_apply]
  · field_simp [hden]
    simp only [Pi.add_apply]
    ring

theorem hasDerivAt_suzukiExpTCosPrimitive
    {d w t : Real} (hden : d ^ 2 + w ^ 2 ≠ 0) :
    HasDerivAt (suzukiExpTCosPrimitive d w)
      (t * Real.exp (-d * t) * Real.cos (w * t)) t := by
  have hsin := hasDerivAt_sin_mul' w t
  have hcos := hasDerivAt_cos_mul' w t
  have hbracket : HasDerivAt
      (fun x : Real => -d * Real.cos (w * x) + w * Real.sin (w * x))
      (d * w * Real.sin (w * t) + w ^ 2 * Real.cos (w * t)) t := by
    have hraw := (hcos.const_mul (-d)).add (hsin.const_mul w)
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with x
      simp only [Pi.add_apply]
    · ring
  have hfirst :=
    (((hasDerivAt_id t).mul_const (d ^ 2 + w ^ 2)).mul hbracket)
  have hsecond := hcos.const_mul (-(d ^ 2 - w ^ 2))
  have hthird := hsin.const_mul (2 * d * w)
  have hlinear : HasDerivAt
      (fun x : Real =>
        x * (d ^ 2 + w ^ 2) *
            (-d * Real.cos (w * x) + w * Real.sin (w * x)) -
          (d ^ 2 - w ^ 2) * Real.cos (w * x) +
          2 * d * w * Real.sin (w * x))
      ((d ^ 2 + w ^ 2) *
            (-d * Real.cos (w * t) + w * Real.sin (w * t)) +
        t * (d ^ 2 + w ^ 2) *
            (d * w * Real.sin (w * t) + w ^ 2 * Real.cos (w * t)) +
        (d ^ 2 - w ^ 2) * w * Real.sin (w * t) +
        2 * d * w ^ 2 * Real.cos (w * t)) t := by
    have hraw := (hfirst.add hsecond).add hthird
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with x
      simp only [Pi.mul_apply, Pi.add_apply, id_eq]
      ring
    · simp only [id_eq, one_mul]
      ring
  have h := ((hasDerivAt_exp_neg_mul' d t).mul hlinear).div_const
    ((d ^ 2 + w ^ 2) ^ 2)
  unfold suzukiExpTCosPrimitive
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with x
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  · field_simp [hden]
    ring

theorem integral_exp_neg_mul_cos_eq_primitive_sub
    {d w L : Real} (hden : d ^ 2 + w ^ 2 ≠ 0) :
    (∫ t in (0 : Real)..L,
        Real.exp (-d * t) * Real.cos (w * t)) =
      suzukiExpCosPrimitive d w L - suzukiExpCosPrimitive d w 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact hasDerivAt_suzukiExpCosPrimitive hden
  · exact (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _

theorem integral_mul_exp_neg_mul_cos_eq_primitive_sub
    {d w L : Real} (hden : d ^ 2 + w ^ 2 ≠ 0) :
    (∫ t in (0 : Real)..L,
        t * Real.exp (-d * t) * Real.cos (w * t)) =
      suzukiExpTCosPrimitive d w L - suzukiExpTCosPrimitive d w 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t _
    exact hasDerivAt_suzukiExpTCosPrimitive hden
  · exact (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _

private theorem suzukiEvenPrimitiveCombination_eq_closed
    {a d w e : Real} (ha : 0 < a) (hw : 0 < w)
    (hsin : Real.sin (w * (2 * a)) = 0)
    (hcos : Real.cos (w * (2 * a)) = 1)
    (hexp : Real.exp (-d * (2 * a)) = e) :
    (suzukiExpCosPrimitive d w (2 * a) - suzukiExpCosPrimitive d w 0) -
          (1 / (2 * a)) *
            (suzukiExpTCosPrimitive d w (2 * a) -
              suzukiExpTCosPrimitive d w 0) -
        (1 / (2 * a * w)) *
          (suzukiDF6D4ArchimedeanPrimitive d w (2 * a) -
            suzukiDF6D4ArchimedeanPrimitive d w 0) =
      d * (1 - e) / (d ^ 2 + w ^ 2) -
          (e * (-(2 * a * d * (d ^ 2 + w ^ 2)) -
              (d ^ 2 - w ^ 2)) + (d ^ 2 - w ^ 2)) /
            (2 * a * (d ^ 2 + w ^ 2) ^ 2) -
        (1 - e) / (2 * a * (d ^ 2 + w ^ 2)) := by
  have hD : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  unfold suzukiExpCosPrimitive suzukiExpTCosPrimitive
    suzukiDF6D4ArchimedeanPrimitive
  rw [hsin, hcos, hexp]
  simp only [Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_zero,
    zero_mul, add_zero, sub_zero]
  field_simp [ha.ne', hw.ne', hD]
  ring

private theorem suzukiOddPrimitiveCombination_eq_closed
    {a d w e : Real} (ha : 0 < a) (hw : 0 < w)
    (hsin : Real.sin (w * (2 * a)) = 0)
    (hcos : Real.cos (w * (2 * a)) = 1)
    (hexp : Real.exp (-d * (2 * a)) = e) :
    (suzukiExpCosPrimitive d w (2 * a) - suzukiExpCosPrimitive d w 0) -
          (1 / (2 * a)) *
            (suzukiExpTCosPrimitive d w (2 * a) -
              suzukiExpTCosPrimitive d w 0) +
        (1 / (2 * a * w)) *
          (suzukiDF6D4ArchimedeanPrimitive d w (2 * a) -
            suzukiDF6D4ArchimedeanPrimitive d w 0) =
      d * (1 - e) / (d ^ 2 + w ^ 2) -
          (e * (-(2 * a * d * (d ^ 2 + w ^ 2)) -
              (d ^ 2 - w ^ 2)) + (d ^ 2 - w ^ 2)) /
            (2 * a * (d ^ 2 + w ^ 2) ^ 2) +
        (1 - e) / (2 * a * (d ^ 2 + w ^ 2)) := by
  have hD : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  unfold suzukiExpCosPrimitive suzukiExpTCosPrimitive
    suzukiDF6D4ArchimedeanPrimitive
  rw [hsin, hcos, hexp]
  simp only [Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_zero,
    zero_mul, add_zero, sub_zero]
  field_simp [ha.ne', hw.ne', hD]
  ring

private theorem suzukiEvenZeroPrimitiveCombination_eq_closed
    {a d e : Real} (ha : 0 < a) (hd : d ≠ 0)
    (hexp : Real.exp (-d * (2 * a)) = e) :
    (suzukiExpCosPrimitive d 0 (2 * a) - suzukiExpCosPrimitive d 0 0) -
        (1 / (2 * a)) *
          (suzukiExpTCosPrimitive d 0 (2 * a) -
            suzukiExpTCosPrimitive d 0 0) =
      d * (1 - e) / d ^ 2 -
        (e * (-(2 * a * d * d ^ 2) - d ^ 2) + d ^ 2) /
          (2 * a * (d ^ 2) ^ 2) := by
  unfold suzukiExpCosPrimitive suzukiExpTCosPrimitive
  rw [hexp]
  simp only [Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_zero,
    zero_mul, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true,
    add_zero, sub_zero]
  field_simp [ha.ne', hd]
  ring

/-! ## Generic exponential evaluations for the two pole decays -/

private theorem integral_exp_neg_mul_evenPositiveDiagonalCorrelation_generic
    (mode : Nat) (hmode : 0 < mode) {d : Real} :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-d * t) *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
      let a := suzukiProjectAStar
      let w := (mode : Real) * Real.pi / a
      let e := Real.exp (-d * (2 * a))
      d * (1 - e) / (d ^ 2 + w ^ 2) -
          (e * (-(2 * a * d * (d ^ 2 + w ^ 2)) -
              (d ^ 2 - w ^ 2)) + (d ^ 2 - w ^ 2)) /
            (2 * a * (d ^ 2 + w ^ 2) ^ 2) -
        (1 - e) / (2 * a * (d ^ 2 + w ^ 2)) := by
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  have ha : 0 < a := suzukiProjectAStar_pos
  have hw : 0 < w := by
    dsimp only [w]
    positivity
  have hden : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  have hcos := integral_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have htcos := integral_mul_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have hsin := integral_exp_neg_mul_mul_sin_eq_archimedeanPrimitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have harg : w * (2 * a) = (mode : Real) * (2 * Real.pi) := by
    dsimp only [w, a]
    field_simp [suzukiProjectAStar_pos.ne']
  have hsinEnd : Real.sin (w * (2 * a)) = 0 := by
    rw [harg, ← sub_zero ((mode : Real) * (2 * Real.pi)),
      Real.sin_nat_mul_two_pi_sub]
    simp
  have hcosEnd : Real.cos (w * (2 * a)) = 1 := by
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hCosInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hTCosInt : IntervalIntegrable
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hSinInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) *
            suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.cos (w * t)) -
        (1 / (2 * a)) * (∫ t in (0 : Real)..2 * a,
          t * Real.exp (-d * t) * Real.cos (w * t)) -
        (1 / (2 * a * w)) * (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.sin (w * t)) := by
    calc
      _ = ∫ t in (0 : Real)..2 * a,
          (Real.exp (-d * t) * Real.cos (w * t) -
            (1 / (2 * a)) *
              (t * Real.exp (-d * t) * Real.cos (w * t)) -
            (1 / (2 * a * w)) *
              (Real.exp (-d * t) * Real.sin (w * t))) := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiYoshidaEvenPositiveDiagonalCorrelation
            dsimp only [a, w]
            field_simp [ha.ne', hw.ne', suzukiProjectAStar_pos.ne']
      _ = _ := by
        rw [intervalIntegral.integral_sub
              (hCosInt.sub (hTCosInt.const_mul _)) (hSinInt.const_mul _),
          intervalIntegral.integral_sub hCosInt (hTCosInt.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hsplit, hcos, htcos, hsin]
  exact suzukiEvenPrimitiveCombination_eq_closed
    ha hw hsinEnd hcosEnd rfl

private theorem integral_exp_neg_mul_oddDiagonalCorrelation_generic
    (mode : Nat) (hmode : 0 < mode) {d : Real} :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-d * t) * suzukiYoshidaOddDiagonalCorrelation mode t) =
      let a := suzukiProjectAStar
      let w := (mode : Real) * Real.pi / a
      let e := Real.exp (-d * (2 * a))
      d * (1 - e) / (d ^ 2 + w ^ 2) -
          (e * (-(2 * a * d * (d ^ 2 + w ^ 2)) -
              (d ^ 2 - w ^ 2)) + (d ^ 2 - w ^ 2)) /
            (2 * a * (d ^ 2 + w ^ 2) ^ 2) +
        (1 - e) / (2 * a * (d ^ 2 + w ^ 2)) := by
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  have ha : 0 < a := suzukiProjectAStar_pos
  have hw : 0 < w := by
    dsimp only [w]
    positivity
  have hden : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  have hcos := integral_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have htcos := integral_mul_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have hsin := integral_exp_neg_mul_mul_sin_eq_archimedeanPrimitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have harg : w * (2 * a) = (mode : Real) * (2 * Real.pi) := by
    dsimp only [w, a]
    field_simp [suzukiProjectAStar_pos.ne']
  have hsinEnd : Real.sin (w * (2 * a)) = 0 := by
    rw [harg, ← sub_zero ((mode : Real) * (2 * Real.pi)),
      Real.sin_nat_mul_two_pi_sub]
    simp
  have hcosEnd : Real.cos (w * (2 * a)) = 1 := by
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hCosInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hTCosInt : IntervalIntegrable
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hSinInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * suzukiYoshidaOddDiagonalCorrelation mode t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.cos (w * t)) -
        (1 / (2 * a)) * (∫ t in (0 : Real)..2 * a,
          t * Real.exp (-d * t) * Real.cos (w * t)) +
        (1 / (2 * a * w)) * (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.sin (w * t)) := by
    calc
      _ = ∫ t in (0 : Real)..2 * a,
          (Real.exp (-d * t) * Real.cos (w * t) -
            (1 / (2 * a)) *
              (t * Real.exp (-d * t) * Real.cos (w * t)) +
            (1 / (2 * a * w)) *
              (Real.exp (-d * t) * Real.sin (w * t))) := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiYoshidaOddDiagonalCorrelation
            dsimp only [a, w]
            field_simp [ha.ne', hw.ne', suzukiProjectAStar_pos.ne']
      _ = _ := by
        rw [intervalIntegral.integral_add
              (hCosInt.sub (hTCosInt.const_mul _)) (hSinInt.const_mul _),
          intervalIntegral.integral_sub hCosInt (hTCosInt.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hsplit, hcos, htcos, hsin]
  exact suzukiOddPrimitiveCombination_eq_closed
    ha hw hsinEnd hcosEnd rfl

private theorem integral_exp_neg_mul_evenZeroDiagonalCorrelation_generic
    {d : Real} (hd : d ≠ 0) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-d * t) * suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      let a := suzukiProjectAStar
      let e := Real.exp (-d * (2 * a))
      d * (1 - e) / d ^ 2 -
        (e * (-(2 * a * d * d ^ 2) - d ^ 2) + d ^ 2) /
          (2 * a * (d ^ 2) ^ 2) := by
  let a := suzukiProjectAStar
  have ha : 0 < a := suzukiProjectAStar_pos
  have hden : d ^ 2 + (0 : Real) ^ 2 ≠ 0 := by
    simp [hd]
  have hcos := integral_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := 0) (L := 2 * a) hden
  have htcos := integral_mul_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := 0) (L := 2 * a) hden
  have hCosInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.cos (0 * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (0 * t))).intervalIntegrable _ _
  have hTCosInt : IntervalIntegrable
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (0 * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (0 * t))).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * suzukiYoshidaEvenZeroDiagonalCorrelation t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.cos (0 * t)) -
        (1 / (2 * a)) * (∫ t in (0 : Real)..2 * a,
          t * Real.exp (-d * t) * Real.cos (0 * t)) := by
    calc
      _ = ∫ t in (0 : Real)..2 * a,
          (Real.exp (-d * t) * Real.cos (0 * t) -
            (1 / (2 * a)) *
              (t * Real.exp (-d * t) * Real.cos (0 * t))) := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiYoshidaEvenZeroDiagonalCorrelation
            dsimp only [a]
            simp
            ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hCosInt (hTCosInt.const_mul _),
          intervalIntegral.integral_const_mul]
  rw [hsplit, hcos, htcos]
  exact suzukiEvenZeroPrimitiveCombination_eq_closed ha hd rfl

theorem two_mul_integral_pole_evenPositiveDiagonalCorrelation
    (mode : Nat) (hmode : 0 < mode) :
    2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (Real.exp (t / 2) + Real.exp (-t / 2)) *
        suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
      suzukiDF6D4EvenDiagonalPoleTerm mode := by
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  have ha : 0 < a := suzukiProjectAStar_pos
  have hw : 0 < w := by
    dsimp only [w]
    positivity
  have hplus :=
    integral_exp_neg_mul_evenPositiveDiagonalCorrelation_generic
      mode hmode (d := -(1 / 2 : Real))
  have hminus :=
    integral_exp_neg_mul_evenPositiveDiagonalCorrelation_generic
      mode hmode (d := (1 / 2 : Real))
  have hPlusInt : IntervalIntegrable
      (fun t : Real => Real.exp (t / 2) *
        suzukiYoshidaEvenPositiveDiagonalCorrelation mode t)
      volume 0 (2 * a) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      (continuous_suzukiYoshidaEvenPositiveDiagonalCorrelation mode)
        ).intervalIntegrable _ _
  have hMinusInt : IntervalIntegrable
      (fun t : Real => Real.exp (-t / 2) *
        suzukiYoshidaEvenPositiveDiagonalCorrelation mode t)
      volume 0 (2 * a) :=
    ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      (continuous_suzukiYoshidaEvenPositiveDiagonalCorrelation mode)
        ).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
        (Real.exp (t / 2) + Real.exp (-t / 2)) *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (t / 2) *
            suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) +
        ∫ t in (0 : Real)..2 * a,
          Real.exp (-t / 2) *
            suzukiYoshidaEvenPositiveDiagonalCorrelation mode t := by
    rw [← intervalIntegral.integral_add hPlusInt hMinusInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hsplit]
  rw [show (∫ t in (0 : Real)..2 * a,
      Real.exp (t / 2) *
        suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-(-(1 / 2 : Real)) * t) *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t by
    dsimp only [a]
    apply intervalIntegral.integral_congr
    intro t _
    congr 2 <;> ring,
    show (∫ t in (0 : Real)..2 * a,
      Real.exp (-t / 2) *
        suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-(1 / 2 : Real) * t) *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t by
    dsimp only [a]
    apply intervalIntegral.integral_congr
    intro t _
    congr 2 <;> ring,
    hplus, hminus]
  dsimp only
  norm_num
  unfold suzukiDF6D4EvenDiagonalPoleTerm
    suzukiDF6D4DiagonalPoleFactor suzukiDF6D4DiagonalFrequency
  simp only [if_neg hmode.ne']
  rw [← Real.exp_neg]
  field_simp [suzukiProjectAStar_pos.ne', Real.pi_ne_zero,
    Real.exp_ne_zero]
  ring

theorem two_mul_integral_pole_oddDiagonalCorrelation
    (mode : Nat) (hmode : 0 < mode) :
    2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (Real.exp (t / 2) + Real.exp (-t / 2)) *
        suzukiYoshidaOddDiagonalCorrelation mode t) =
      suzukiDF6D4OddDiagonalPoleTerm mode := by
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  have ha : 0 < a := suzukiProjectAStar_pos
  have hw : 0 < w := by
    dsimp only [w]
    positivity
  have hplus := integral_exp_neg_mul_oddDiagonalCorrelation_generic
    mode hmode (d := -(1 / 2 : Real))
  have hminus := integral_exp_neg_mul_oddDiagonalCorrelation_generic
    mode hmode (d := (1 / 2 : Real))
  have hPlusInt : IntervalIntegrable
      (fun t : Real => Real.exp (t / 2) *
        suzukiYoshidaOddDiagonalCorrelation mode t)
      volume 0 (2 * a) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      (continuous_suzukiYoshidaOddDiagonalCorrelation mode)
        ).intervalIntegrable _ _
  have hMinusInt : IntervalIntegrable
      (fun t : Real => Real.exp (-t / 2) *
        suzukiYoshidaOddDiagonalCorrelation mode t)
      volume 0 (2 * a) :=
    ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      (continuous_suzukiYoshidaOddDiagonalCorrelation mode)
        ).intervalIntegrable _ _
  rw [show (∫ t in (0 : Real)..2 * a,
      (Real.exp (t / 2) + Real.exp (-t / 2)) *
        suzukiYoshidaOddDiagonalCorrelation mode t) =
      (∫ t in (0 : Real)..2 * a,
        Real.exp (t / 2) * suzukiYoshidaOddDiagonalCorrelation mode t) +
      ∫ t in (0 : Real)..2 * a,
        Real.exp (-t / 2) * suzukiYoshidaOddDiagonalCorrelation mode t by
    rw [← intervalIntegral.integral_add hPlusInt hMinusInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring]
  rw [show (∫ t in (0 : Real)..2 * a,
      Real.exp (t / 2) * suzukiYoshidaOddDiagonalCorrelation mode t) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-(-(1 / 2 : Real)) * t) *
          suzukiYoshidaOddDiagonalCorrelation mode t by
    dsimp only [a]
    apply intervalIntegral.integral_congr
    intro t _
    congr 2 <;> ring,
    show (∫ t in (0 : Real)..2 * a,
      Real.exp (-t / 2) * suzukiYoshidaOddDiagonalCorrelation mode t) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-(1 / 2 : Real) * t) *
          suzukiYoshidaOddDiagonalCorrelation mode t by
    dsimp only [a]
    apply intervalIntegral.integral_congr
    intro t _
    congr 2 <;> ring,
    hplus, hminus]
  dsimp only
  norm_num
  unfold suzukiDF6D4OddDiagonalPoleTerm
    suzukiDF6D4DiagonalPoleFactor suzukiDF6D4DiagonalFrequency
  dsimp only [a, w]
  rw [← Real.exp_neg]
  field_simp [suzukiProjectAStar_pos.ne', Real.pi_ne_zero,
    Real.exp_ne_zero]
  ring

theorem two_mul_integral_pole_evenZeroDiagonalCorrelation :
    2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (Real.exp (t / 2) + Real.exp (-t / 2)) *
        suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      suzukiDF6D4EvenDiagonalPoleTerm 0 := by
  have hplus := integral_exp_neg_mul_evenZeroDiagonalCorrelation_generic
    (d := -(1 / 2 : Real)) (by norm_num)
  have hminus := integral_exp_neg_mul_evenZeroDiagonalCorrelation_generic
    (d := (1 / 2 : Real)) (by norm_num)
  have hPlusInt : IntervalIntegrable
      (fun t : Real => Real.exp (t / 2) *
        suzukiYoshidaEvenZeroDiagonalCorrelation t)
      volume 0 (2 * suzukiProjectAStar) :=
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul
      continuous_suzukiYoshidaEvenZeroDiagonalCorrelation
        ).intervalIntegrable _ _
  have hMinusInt : IntervalIntegrable
      (fun t : Real => Real.exp (-t / 2) *
        suzukiYoshidaEvenZeroDiagonalCorrelation t)
      volume 0 (2 * suzukiProjectAStar) :=
    ((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
      continuous_suzukiYoshidaEvenZeroDiagonalCorrelation
        ).intervalIntegrable _ _
  rw [show (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      (Real.exp (t / 2) + Real.exp (-t / 2)) *
        suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (t / 2) * suzukiYoshidaEvenZeroDiagonalCorrelation t) +
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-t / 2) * suzukiYoshidaEvenZeroDiagonalCorrelation t by
    rw [← intervalIntegral.integral_add hPlusInt hMinusInt]
    apply intervalIntegral.integral_congr
    intro t _
    ring]
  rw [show (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      Real.exp (t / 2) * suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-(-(1 / 2 : Real)) * t) *
          suzukiYoshidaEvenZeroDiagonalCorrelation t by
    apply intervalIntegral.integral_congr
    intro t _
    congr 2 <;> ring,
    show (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      Real.exp (-t / 2) * suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-(1 / 2 : Real) * t) *
          suzukiYoshidaEvenZeroDiagonalCorrelation t by
    apply intervalIntegral.integral_congr
    intro t _
    congr 2 <;> ring,
    hplus, hminus]
  dsimp only
  norm_num
  unfold suzukiDF6D4EvenDiagonalPoleTerm
    suzukiDF6D4DiagonalPoleFactor
  simp [suzukiDF6D4DiagonalFrequency]
  rw [← Real.exp_neg]
  field_simp [suzukiProjectAStar_pos.ne', Real.exp_ne_zero]
  ring

/-! ## Finite-cutoff diagonal source normalization -/

/-- Half of the renormalized cutoff integral, with the integer-mode arguments
reversed to match the sesquilinear orientation of the comparison kernel. -/
noncomputable def suzukiYoshidaDiagonalRenormalizedCutoffKernel
    (ε R : Real) (m n : Int) : Complex :=
  (2 : Complex)⁻¹ *
    ∫ ξ : Real,
      suzukiYoshidaEndpointRenormalizedCutoffIntegrand
        suzukiProjectAStar n m ε R ξ

/-- The finite diagonal cutoff kernels converge pointwise to the already
identified comparison-limit kernel. -/
theorem tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) :
    Tendsto
      (fun p : Real × Real =>
        suzukiYoshidaDiagonalRenormalizedCutoffKernel p.1 p.2 m n)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (suzukiYoshidaComparisonLimitKernel hsource m n)) := by
  have hlimit :=
    (tendsto_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      suzukiProjectAStar_pos n m).const_mul ((2 : Complex)⁻¹)
  rw [suzukiYoshidaComparisonLimitKernel_eq_endpointSourceFourierPairing]
  unfold suzukiYoshidaDiagonalRenormalizedCutoffKernel
  convert hlimit using 1
  ring

theorem integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R) (m n : Int) :
    (∫ ξ : Real,
        suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r m n ε R ξ) =
      (((-2 * Real.log ε * (if m = n then 1 else 0) : Real) : Complex)) -
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
          (suzukiYoshidaExponentialL2 r hr m)
          (suzukiYoshidaExponentialL2 r hr n) := by
  let P : Real → Complex := fun ξ =>
    FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r m) ξ *
      conj (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) ξ)
  have hprod : Integrable P := by
    simpa only [P] using
      (integrable_suzukiYoshidaEndpointFourierPairing
        hsource hr n m)
  have hconst : Integrable (fun ξ : Real =>
      (((-2 * Real.log ε : Real) : Complex)) * P ξ) :=
    hprod.const_mul _
  have hcos : Integrable (fun ξ : Real =>
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) * P ξ) := by
    exact hprod.bdd_mul
      (c := suzukiReciprocalCutoffMultiplierBound ε R)
      ((Complex.continuous_ofReal.comp
        (continuous_suzukiReciprocalCutoffCosineMultiplier hε hεR)
          ).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ =>
        norm_suzukiReciprocalCutoffCosineMultiplier_le hε hεR ξ)
  have horth := (orthonormal_iff_ite.mp
    (orthonormal_suzukiYoshidaExponentialL2 hr)) n m
  have hunweighted :
      (∫ ξ : Real, P ξ) = if m = n then 1 else 0 := by
    rw [← inner_suzukiYoshidaExponentialL2_eq_fourierIntegral
      hsource hr n m]
    simpa [eq_comm] using horth
  have hrenormalized :
      (∫ ξ : Real,
        suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r m n ε R ξ) =
        (((-2 * Real.log ε : Real) : Complex) *
            ((if m = n then 1 else 0 : Real) : Complex)) -
          suzukiYoshidaEndpointReciprocalCutoffFourierPairing
            r ε R m n := by
    unfold suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      suzukiYoshidaEndpointReciprocalCutoffFourierPairing
      suzukiRenormalizedCutoffMultiplier
    change (∫ ξ : Real,
        (((-2 * Real.log ε -
          suzukiReciprocalCutoffCosineMultiplier ε R ξ : Real) : Complex) *
            P ξ)) = _
    calc
      _ = ∫ ξ : Real,
          (((-2 * Real.log ε : Real) : Complex) * P ξ -
            (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
              P ξ) := by
            apply integral_congr_ae
            filter_upwards with ξ
            push_cast
            ring
      _ = (∫ ξ : Real,
            (((-2 * Real.log ε : Real) : Complex) * P ξ)) -
          ∫ ξ : Real,
            (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
              P ξ := integral_sub hconst hcos
      _ = (((-2 * Real.log ε : Real) : Complex) *
            (∫ ξ : Real, P ξ)) -
          ∫ ξ : Real,
            (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
              P ξ := by rw [integral_const_mul]
      _ = _ := by
        rw [hunweighted]
        by_cases hmn : m = n <;> simp [hmn, P]
  rw [suzukiYoshidaEndpointReciprocalCutoffPairing_eq_fourier
    hsource hr hε hεR]
  by_cases hmn : m = n <;> simp [hmn] at hrenormalized ⊢
  all_goals exact hrenormalized

theorem re_integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R) (m n : Int) :
    (∫ ξ : Real,
        suzukiYoshidaEndpointRenormalizedCutoffIntegrand
          r m n ε R ξ).re =
      -2 * Real.log ε * (if m = n then 1 else 0) -
        (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
          (suzukiYoshidaExponentialL2 r hr m)
          (suzukiYoshidaExponentialL2 r hr n)).re := by
  have h := congrArg Complex.re
    (integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      hsource hr hε hεR m n)
  push_cast at h
  by_cases hmn : m = n <;> simp [hmn] at h ⊢
  all_goals exact h

theorem suzukiReciprocalCutoffL2CrossCorrelationPairing_add_left
    {ε R : Real} (hε : 0 < ε) (u v w : SuzukiL2) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R (u + v) w =
      suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u w +
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R v w := by
  have hu := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε u w
  have hv := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε v w
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  rw [← integral_add hu hv]
  apply integral_congr_ae
  filter_upwards with t
  have ht : suzukiL2Translate t (u + v) =
      suzukiL2Translate t u + suzukiL2Translate t v := by
    rw [← suzukiL2TranslateCLM_apply, ← suzukiL2TranslateCLM_apply,
      ← suzukiL2TranslateCLM_apply]
    exact map_add _ _ _
  rw [ht, inner_add_left, map_add]
  ring

theorem suzukiReciprocalCutoffL2CrossCorrelationPairing_add_right
    {ε R : Real} (hε : 0 < ε) (u v w : SuzukiL2) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u (v + w) =
      suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v +
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u w := by
  have hv := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε u v
  have hw := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε u w
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  rw [← integral_add hv hw]
  apply integral_congr_ae
  filter_upwards with t
  simp only [inner_add_right, map_add]
  ring

theorem suzukiReciprocalCutoffL2CrossCorrelationPairing_sub_left
    {ε R : Real} (hε : 0 < ε) (u v w : SuzukiL2) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R (u - v) w =
      suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u w -
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R v w := by
  have hu := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε u w
  have hv := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε v w
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  rw [← integral_sub hu hv]
  apply integral_congr_ae
  filter_upwards with t
  have ht : suzukiL2Translate t (u - v) =
      suzukiL2Translate t u - suzukiL2Translate t v := by
    rw [← suzukiL2TranslateCLM_apply, ← suzukiL2TranslateCLM_apply,
      ← suzukiL2TranslateCLM_apply]
    exact map_sub _ _ _
  rw [ht, inner_sub_left, map_sub]
  ring

theorem suzukiReciprocalCutoffL2CrossCorrelationPairing_sub_right
    {ε R : Real} (hε : 0 < ε) (u v w : SuzukiL2) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u (v - w) =
      suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v -
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u w := by
  have hv := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε u v
  have hw := integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    (R := R) hε u w
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  rw [← integral_sub hv hw]
  apply integral_congr_ae
  filter_upwards with t
  simp only [inner_sub_right, map_sub]
  ring

theorem suzukiReciprocalCutoffL2CrossCorrelationPairing_smul_left
    {ε R : Real} (hε : 0 < ε) (c : Complex) (u v : SuzukiL2) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R (c • u) v =
      c * suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v := by
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  have ht : suzukiL2Translate t (c • u) =
      c • suzukiL2Translate t u := by
    rw [← suzukiL2TranslateCLM_apply, ← suzukiL2TranslateCLM_apply]
    exact map_smul _ _ _
  simp only [ht, inner_smul_left, map_mul, map_star, starRingEnd_apply, star_star]
  ring

theorem suzukiReciprocalCutoffL2CrossCorrelationPairing_smul_right
    {ε R : Real} (hε : 0 < ε) (c : Complex) (u v : SuzukiL2) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u (c • v) =
      conj c * suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v := by
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [inner_smul_right, map_mul, starRingEnd_apply]
  ring

private theorem suzukiYoshida_even_cutoff_scalar_normalization :
    conj (((Real.sqrt 2)⁻¹ : Complex)) *
        (((Real.sqrt 2)⁻¹ : Complex) * 2) = 1 := by
  rw [map_inv₀, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquareC : (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]

private theorem suzukiYoshida_odd_cutoff_scalar_normalization :
    conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
        (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) * 2) = 1 := by
  rw [map_inv₀, map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsquareC : (((Real.sqrt 2 : Real) : Complex) ^ 2) = (2 : Complex) := by
    exact_mod_cast hsquare
  rw [← hsquareC]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity, Complex.I_ne_zero]
  rw [Complex.I_sq]

/-- At a finite cutoff the even parity diagonal is exactly the logarithmic
counterterm minus one half of the physical reciprocal-correlation energy. -/
theorem suzukiYoshidaEvenSourceKernelPairing_cutoff_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (mode : Nat) :
    suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R) mode mode =
      ((-Real.log ε : Real) : Complex) - (2 : Complex)⁻¹ *
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
          (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos mode)
          (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos mode) := by
  by_cases hmode : mode = 0
  · subst mode
    unfold suzukiYoshidaEvenSourceKernelPairing
      suzukiYoshidaDiagonalRenormalizedCutoffKernel
      suzukiYoshidaEvenL2
    rw [integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      hsource suzukiProjectAStar_pos hε hεR]
    simp
    ring
  · have hcross : (mode : Int) ≠ -(mode : Int) := by omega
    have hcross' : -(mode : Int) ≠ (mode : Int) := by omega
    let s : Complex := ((Real.sqrt 2)⁻¹ : Complex)
    let ep := suzukiYoshidaExponentialL2
      suzukiProjectAStar suzukiProjectAStar_pos (mode : Int)
    let em := suzukiYoshidaExponentialL2
      suzukiProjectAStar suzukiProjectAStar_pos (-(mode : Int))
    rw [show suzukiYoshidaEvenSourceKernelPairing
          (suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R) mode mode =
        conj s * s *
          (suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
              (mode : Int) (mode : Int) +
            suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
              (mode : Int) (-(mode : Int)) +
            suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
              (-(mode : Int)) (mode : Int) +
            suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
              (-(mode : Int)) (-(mode : Int))) by
        simp [suzukiYoshidaEvenSourceKernelPairing, hmode, s]]
    rw [show suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos mode = s • (ep + em) by
        simp [suzukiYoshidaEvenL2, hmode, s, ep, em]]
    rw [suzukiReciprocalCutoffL2CrossCorrelationPairing_smul_right hε,
      suzukiReciprocalCutoffL2CrossCorrelationPairing_smul_left hε,
      suzukiReciprocalCutoffL2CrossCorrelationPairing_add_left hε,
      suzukiReciprocalCutoffL2CrossCorrelationPairing_add_right hε,
      suzukiReciprocalCutoffL2CrossCorrelationPairing_add_right hε]
    rw [← mul_assoc (conj s) s]
    unfold suzukiYoshidaDiagonalRenormalizedCutoffKernel
    simp_rw [integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
      hsource suzukiProjectAStar_pos hε hεR]
    dsimp only [s, ep, em]
    simp only [if_pos, if_neg hcross, if_neg hcross']
    have hcoef :
        conj (((Real.sqrt 2)⁻¹ : Complex)) *
            (((Real.sqrt 2)⁻¹ : Complex)) = (2 : Complex)⁻¹ := by
      calc
        _ = (conj (((Real.sqrt 2)⁻¹ : Complex)) *
              (((Real.sqrt 2)⁻¹ : Complex) * 2)) * (2 : Complex)⁻¹ := by ring
        _ = (2 : Complex)⁻¹ := by
          rw [suzukiYoshida_even_cutoff_scalar_normalization]
          ring
    rw [hcoef]
    push_cast
    ring

/-- At a finite cutoff the positive odd parity diagonal has the same scalar
normalization and the odd reciprocal-correlation energy. -/
theorem suzukiYoshidaOddSourceKernelPairing_cutoff_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R) mode mode =
      ((-Real.log ε : Real) : Complex) - (2 : Complex)⁻¹ *
        suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
          (suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos mode)
          (suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos mode) := by
  have hcross : (mode : Int) ≠ -(mode : Int) := by omega
  have hcross' : -(mode : Int) ≠ (mode : Int) := by omega
  let s : Complex := ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)
  let ep := suzukiYoshidaExponentialL2
    suzukiProjectAStar suzukiProjectAStar_pos (mode : Int)
  let em := suzukiYoshidaExponentialL2
    suzukiProjectAStar suzukiProjectAStar_pos (-(mode : Int))
  rw [show suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R) mode mode =
      conj s * s *
        (suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
            (mode : Int) (mode : Int) -
          suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
            (mode : Int) (-(mode : Int)) -
          suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
            (-(mode : Int)) (mode : Int) +
          suzukiYoshidaDiagonalRenormalizedCutoffKernel ε R
            (-(mode : Int)) (-(mode : Int))) by
      simp [suzukiYoshidaOddSourceKernelPairing, s]]
  rw [show suzukiYoshidaOddL2
        suzukiProjectAStar suzukiProjectAStar_pos mode = s • (ep - em) by
      simp [suzukiYoshidaOddL2, s, ep, em]]
  rw [suzukiReciprocalCutoffL2CrossCorrelationPairing_smul_right hε,
    suzukiReciprocalCutoffL2CrossCorrelationPairing_smul_left hε,
    suzukiReciprocalCutoffL2CrossCorrelationPairing_sub_left hε,
    suzukiReciprocalCutoffL2CrossCorrelationPairing_sub_right hε,
    suzukiReciprocalCutoffL2CrossCorrelationPairing_sub_right hε]
  rw [← mul_assoc (conj s) s]
  unfold suzukiYoshidaDiagonalRenormalizedCutoffKernel
  simp_rw [integral_suzukiYoshidaEndpointRenormalizedCutoffIntegrand
    hsource suzukiProjectAStar_pos hε hεR]
  dsimp only [s, ep, em]
  simp only [if_pos, if_neg hcross, if_neg hcross']
  have hcoef :
      conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
          (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) =
        (2 : Complex)⁻¹ := by
    calc
      _ = (conj (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) *
            (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex) * 2)) *
          (2 : Complex)⁻¹ := by ring
      _ = (2 : Complex)⁻¹ := by
        rw [suzukiYoshida_odd_cutoff_scalar_normalization]
        ring
  rw [hcoef]
  push_cast
  ring

/-- Finite even parity cutoffs converge to the even comparison entry. -/
theorem tendsto_suzukiYoshidaEvenSourceKernelPairing_cutoff_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) :
    Tendsto
      (fun p : Real × Real =>
        suzukiYoshidaEvenSourceKernelPairing
          (suzukiYoshidaDiagonalRenormalizedCutoffKernel p.1 p.2) mode mode)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) mode mode)) := by
  by_cases hmode : mode = 0
  · subst mode
    simpa [suzukiYoshidaEvenSourceKernelPairing] using
      (tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel hsource 0 0)
  · let s : Complex := ((Real.sqrt 2)⁻¹ : Complex)
    have hpp := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
      hsource (mode : Int) (mode : Int)
    have hpn := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
      hsource (mode : Int) (-(mode : Int))
    have hnp := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
      hsource (-(mode : Int)) (mode : Int)
    have hnn := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
      hsource (-(mode : Int)) (-(mode : Int))
    have hsum := (((hpp.add hpn).add hnp).add hnn).const_mul (conj s * s)
    simpa [suzukiYoshidaEvenSourceKernelPairing, hmode, s] using hsum

/-- Finite positive odd parity cutoffs converge to the odd comparison entry. -/
theorem tendsto_suzukiYoshidaOddSourceKernelPairing_cutoff_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) :
    Tendsto
      (fun p : Real × Real =>
        suzukiYoshidaOddSourceKernelPairing
          (suzukiYoshidaDiagonalRenormalizedCutoffKernel p.1 p.2) mode mode)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) mode mode)) := by
  let s : Complex := ((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)
  have hpp := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
    hsource (mode : Int) (mode : Int)
  have hpn := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
    hsource (mode : Int) (-(mode : Int))
  have hnp := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
    hsource (-(mode : Int)) (mode : Int)
  have hnn := tendsto_suzukiYoshidaDiagonalRenormalizedCutoffKernel
    hsource (-(mode : Int)) (-(mode : Int))
  have hsum := (((hpp.sub hpn).sub hnp).add hnn).const_mul (conj s * s)
  simpa [suzukiYoshidaOddSourceKernelPairing, s] using hsum

/-- A physical reciprocal pairing may be truncated at any radius beyond
which its symmetric translation energy vanishes. -/
theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval_of_zero
    {ε L R : Real} (hε : 0 < ε) (hεL : ε ≤ L) (hLR : L ≤ R)
    (u v : SuzukiL2)
    (hzero : ∀ t : Real, L < t →
      suzukiL2SymmetricTranslationEnergy t u v = 0) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v).re =
      ∫ t in ε..L, (suzukiL2SymmetricTranslationEnergy t u v).re / t := by
  let g : Real → Real := fun t =>
    (suzukiL2SymmetricTranslationEnergy t u v).re / t
  have hεR : ε ≤ R := hεL.trans hLR
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval
    hε hεR]
  change (∫ t in ε..R, g t) = ∫ t in ε..L, g t
  have hcontEnergy : Continuous (fun t : Real =>
      (suzukiL2SymmetricTranslationEnergy t u v).re) :=
    Complex.continuous_re.comp
      (continuous_suzukiL2SymmetricTranslationEnergy_orbit _ _)
  have hleft : IntervalIntegrable g volume ε L := by
    apply ContinuousOn.intervalIntegrable
    apply hcontEnergy.continuousOn.div continuous_id.continuousOn
    intro t ht
    have htε : ε ≤ t := by
      rw [uIcc_of_le hεL] at ht
      exact ht.1
    exact ne_of_gt (hε.trans_le htε)
  have hright : IntervalIntegrable g volume L R := by
    apply ContinuousOn.intervalIntegrable
    apply hcontEnergy.continuousOn.div continuous_id.continuousOn
    intro t ht
    have htL : L ≤ t := by
      rw [uIcc_of_le hLR] at ht
      exact ht.1
    exact ne_of_gt (hε.trans_le (hεL.trans htL))
  have htail : (∫ t in L..R, g t) = 0 := by
    calc
      (∫ t in L..R, g t) = ∫ _t in L..R, (0 : Real) := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le hLR] at ht
        unfold g
        rw [hzero t ht.1]
        simp
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  rw [← hadd, htail, add_zero]

theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_evenPositive
    {ε R : Real} (hε : 0 < ε)
    (hεL : ε ≤ 2 * suzukiProjectAStar)
    (hLR : 2 * suzukiProjectAStar ≤ R)
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
      (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos mode)
      (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos mode)).re =
      2 * ∫ t in ε..2 * suzukiProjectAStar,
        suzukiYoshidaEvenPositiveDiagonalCorrelation mode t / t := by
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval_of_zero
    hε hεL hLR]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hεL] at ht
    have henergy :
        (suzukiL2SymmetricTranslationEnergy t
          (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos mode)
          (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos mode)).re =
            2 * suzukiYoshidaEvenPositiveDiagonalCorrelation mode t := by
      have hre := congrArg Complex.re
        (suzukiL2SymmetricTranslationEnergy_yoshidaEvenPositive_diagonal
          suzukiProjectAStar_pos (hε.trans_le ht.1).le ht.2 mode hmode)
      simpa only [Complex.ofReal_re,
        suzukiYoshidaEvenPositiveDiagonalCorrelation] using hre
    rw [henergy]
    ring
  · intro t ht
    exact suzukiL2SymmetricTranslationEnergy_yoshidaEven_eq_zero_of_two_mul_lt
      suzukiProjectAStar_pos ht mode

theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_evenZero
    {ε R : Real} (hε : 0 < ε)
    (hεL : ε ≤ 2 * suzukiProjectAStar)
    (hLR : 2 * suzukiProjectAStar ≤ R) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
      (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos 0)
      (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos 0)).re =
      2 * ∫ t in ε..2 * suzukiProjectAStar,
        suzukiYoshidaEvenZeroDiagonalCorrelation t / t := by
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval_of_zero
    hε hεL hLR]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hεL] at ht
    have henergy :
        (suzukiL2SymmetricTranslationEnergy t
          (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos 0)
          (suzukiYoshidaEvenL2 suzukiProjectAStar suzukiProjectAStar_pos 0)).re =
            2 * suzukiYoshidaEvenZeroDiagonalCorrelation t := by
      have hre := congrArg Complex.re
        (suzukiL2SymmetricTranslationEnergy_yoshidaEvenZero_diagonal
          suzukiProjectAStar_pos (hε.trans_le ht.1).le ht.2)
      simpa only [Complex.ofReal_re,
        suzukiYoshidaEvenZeroDiagonalCorrelation] using hre
    rw [henergy]
    ring
  · intro t ht
    exact suzukiL2SymmetricTranslationEnergy_yoshidaEven_eq_zero_of_two_mul_lt
      suzukiProjectAStar_pos ht 0

theorem re_suzukiReciprocalCutoffL2CrossCorrelationPairing_odd
    {ε R : Real} (hε : 0 < ε)
    (hεL : ε ≤ 2 * suzukiProjectAStar)
    (hLR : 2 * suzukiProjectAStar ≤ R)
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
      (suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos mode)
      (suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos mode)).re =
      2 * ∫ t in ε..2 * suzukiProjectAStar,
        suzukiYoshidaOddDiagonalCorrelation mode t / t := by
  rw [re_suzukiReciprocalCutoffL2CrossCorrelationPairing_eq_interval_of_zero
    hε hεL hLR]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hεL] at ht
    have henergy :
        (suzukiL2SymmetricTranslationEnergy t
          (suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos mode)
          (suzukiYoshidaOddL2 suzukiProjectAStar suzukiProjectAStar_pos mode)).re =
            2 * suzukiYoshidaOddDiagonalCorrelation mode t := by
      have hre := congrArg Complex.re
        (suzukiL2SymmetricTranslationEnergy_yoshidaOdd_diagonal
          suzukiProjectAStar_pos (hε.trans_le ht.1).le ht.2 mode hmode)
      simpa only [Complex.ofReal_re,
        suzukiYoshidaOddDiagonalCorrelation] using hre
    rw [henergy]
    ring
  · intro t ht
    exact suzukiL2SymmetricTranslationEnergy_yoshidaOdd_eq_zero_of_two_mul_lt
      suzukiProjectAStar_pos ht mode

/-! ## Removal of the logarithmic diagonal singularity -/

/-- Continuous extension of `(c(t)-1)/t` for a positive even diagonal. -/
def suzukiYoshidaEvenPositiveDiagonalRegularPart
    (mode : Nat) (t : Real) : Real :=
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  w * suzukiCosineRegularPart (w * t) -
    Real.cos (w * t) / (2 * a) - Real.sinc (w * t) / (2 * a)

/-- Continuous extension of `(c(t)-1)/t` for a positive odd diagonal. -/
def suzukiYoshidaOddDiagonalRegularPart
    (mode : Nat) (t : Real) : Real :=
  let a := suzukiProjectAStar
  let w := (mode : Real) * Real.pi / a
  w * suzukiCosineRegularPart (w * t) -
    Real.cos (w * t) / (2 * a) + Real.sinc (w * t) / (2 * a)

theorem continuous_suzukiYoshidaEvenPositiveDiagonalRegularPart
    (mode : Nat) :
    Continuous (suzukiYoshidaEvenPositiveDiagonalRegularPart mode) := by
  unfold suzukiYoshidaEvenPositiveDiagonalRegularPart
  dsimp only
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hw : Continuous (fun t : Real => w * t) := continuous_const.mul continuous_id
  exact ((continuous_const.mul (continuous_suzukiCosineRegularPart.comp hw)).sub
    ((Real.continuous_cos.comp hw).div_const _)).sub
      ((Real.continuous_sinc.comp hw).div_const _)

theorem continuous_suzukiYoshidaOddDiagonalRegularPart (mode : Nat) :
    Continuous (suzukiYoshidaOddDiagonalRegularPart mode) := by
  unfold suzukiYoshidaOddDiagonalRegularPart
  dsimp only
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hw : Continuous (fun t : Real => w * t) := continuous_const.mul continuous_id
  exact ((continuous_const.mul (continuous_suzukiCosineRegularPart.comp hw)).sub
    ((Real.continuous_cos.comp hw).div_const _)).add
      ((Real.continuous_sinc.comp hw).div_const _)

theorem suzukiYoshidaEvenPositiveDiagonalCorrelation_sub_one_div
    (mode : Nat) (hmode : 0 < mode) {t : Real} (ht : t ≠ 0) :
    (suzukiYoshidaEvenPositiveDiagonalCorrelation mode t - 1) / t =
      suzukiYoshidaEvenPositiveDiagonalRegularPart mode t := by
  have hw : (mode : Real) * Real.pi / suzukiProjectAStar ≠ 0 := by
    have hm : 0 < (mode : Real) := by exact_mod_cast hmode
    exact (div_pos (mul_pos hm Real.pi_pos) suzukiProjectAStar_pos).ne'
  unfold suzukiYoshidaEvenPositiveDiagonalCorrelation
    suzukiYoshidaEvenPositiveDiagonalRegularPart
    suzukiCosineRegularPart
  dsimp only
  rw [Real.sinc_of_ne_zero (mul_ne_zero hw ht)]
  field_simp [suzukiProjectAStar_pos.ne', hw, ht]
  ring

theorem suzukiYoshidaOddDiagonalCorrelation_sub_one_div
    (mode : Nat) (hmode : 0 < mode) {t : Real} (ht : t ≠ 0) :
    (suzukiYoshidaOddDiagonalCorrelation mode t - 1) / t =
      suzukiYoshidaOddDiagonalRegularPart mode t := by
  have hw : (mode : Real) * Real.pi / suzukiProjectAStar ≠ 0 := by
    have hm : 0 < (mode : Real) := by exact_mod_cast hmode
    exact (div_pos (mul_pos hm Real.pi_pos) suzukiProjectAStar_pos).ne'
  unfold suzukiYoshidaOddDiagonalCorrelation
    suzukiYoshidaOddDiagonalRegularPart
    suzukiCosineRegularPart
  dsimp only
  rw [Real.sinc_of_ne_zero (mul_ne_zero hw ht)]
  field_simp [suzukiProjectAStar_pos.ne', hw, ht]
  ring

theorem suzukiYoshidaEvenZeroDiagonalCorrelation_sub_one_div
    {t : Real} (ht : t ≠ 0) :
    (suzukiYoshidaEvenZeroDiagonalCorrelation t - 1) / t =
      -(2 * suzukiProjectAStar)⁻¹ := by
  unfold suzukiYoshidaEvenZeroDiagonalCorrelation
  field_simp [suzukiProjectAStar_pos.ne', ht]
  ring

/-- Lower cutoffs recover an integrable regular part on any positive finite
interval. -/
theorem tendsto_intervalIntegral_zero_right_of_integrableOn_Ioc
    {f : Real → Real} {L : Real} (hL : 0 < L)
    (hf : IntegrableOn f (Ioc 0 L)) :
    Tendsto (fun ε : Real => ∫ t in ε..L, f t) (𝓝[>] (0 : Real))
      (nhds (∫ t in (0 : Real)..L, f t)) := by
  have hcont : ContinuousOn (fun ε : Real => ∫ t in ε..L, f t)
      (uIcc (0 : Real) L) :=
    intervalIntegral.continuousOn_primitive_interval_left
      (by
        rw [uIcc_of_le hL.le]
        exact hf.congr_set_ae Ioc_ae_eq_Icc.symm)
  have hzero : (0 : Real) ∈ uIcc (0 : Real) L := by
    rw [uIcc_of_le hL.le]
    exact ⟨le_rfl, hL.le⟩
  have htend := (hcont 0 hzero).tendsto
  apply htend.mono_left
  rw [uIcc_of_le hL.le, nhdsWithin, nhdsWithin, le_inf_iff]
  constructor
  · exact inf_le_left
  · rw [le_principal_iff]
    refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
      ⟨Iio L, Iio_mem_nhds hL, ?_⟩
    intro ε hε
    exact ⟨hε.2.le, hε.1.le⟩

/-- Exact finite-cutoff removal of the logarithmic singularity. -/
theorem diagonal_log_cutoff_eq_regularPart
    {c f : Real → Real} {ε L : Real}
    (hε : 0 < ε) (hεL : ε ≤ L)
    (hccont : Continuous c)
    (hcf : ∀ t : Real, t ∈ Icc ε L → (c t - 1) / t = f t) :
    -Real.log ε - (∫ t in ε..L, c t / t) =
      -Real.log L - ∫ t in ε..L, f t := by
  have hL : 0 < L := hε.trans_le hεL
  have hone : IntervalIntegrable (fun t : Real => 1 / t) volume ε L := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div continuous_id.continuousOn
    intro t ht
    rw [uIcc_of_le hεL] at ht
    exact ne_of_gt (hε.trans_le ht.1)
  have hc : IntervalIntegrable (fun t : Real => c t / t) volume ε L := by
    apply ContinuousOn.intervalIntegrable
    apply hccont.continuousOn.div continuous_id.continuousOn
    intro t ht
    rw [uIcc_of_le hεL] at ht
    exact ne_of_gt (hε.trans_le ht.1)
  have hdiff :
      (∫ t in ε..L, c t / t) - (∫ t in ε..L, 1 / t) =
        ∫ t in ε..L, f t := by
    rw [← intervalIntegral.integral_sub hc hone]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hεL] at ht
    rw [← hcf t ht]
    ring
  have honeval := integral_one_div_of_pos hε hL
  rw [Real.log_div hL.ne' hε.ne'] at honeval
  linarith [hdiff, honeval]

theorem re_suzukiYoshidaEvenSourceKernelPairing_diagonal_of_pos
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiYoshidaEvenSourceKernelPairing
      (suzukiYoshidaComparisonLimitKernel hsource) mode mode).re =
      -Real.log (2 * suzukiProjectAStar) -
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiYoshidaEvenPositiveDiagonalRegularPart mode t := by
  let L : Real := 2 * suzukiProjectAStar
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  let cutoff : Real × Real → Real := fun p =>
    (suzukiYoshidaEvenSourceKernelPairing
      (suzukiYoshidaDiagonalRenormalizedCutoffKernel p.1 p.2) mode mode).re
  let scalar : Real → Real := fun ε =>
    -Real.log ε - ∫ t in ε..L,
      suzukiYoshidaEvenPositiveDiagonalCorrelation mode t / t
  let target : Real :=
    -Real.log L - ∫ t in (0 : Real)..L,
      suzukiYoshidaEvenPositiveDiagonalRegularPart mode t
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos (by norm_num) suzukiProjectAStar_pos
  have hregularInt : IntegrableOn
      (suzukiYoshidaEvenPositiveDiagonalRegularPart mode) (Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      ((continuous_suzukiYoshidaEvenPositiveDiagonalRegularPart mode).intervalIntegrable
        0 L)
  have hregular := tendsto_intervalIntegral_zero_right_of_integrableOn_Ioc
    hL hregularInt
  have hscalar : Tendsto scalar (𝓝[>] (0 : Real)) (nhds target) := by
    have hconst : Tendsto (fun _ : Real => -Real.log L) (𝓝[>] (0 : Real))
        (nhds (-Real.log L)) := tendsto_const_nhds
    have hbase := hconst.sub hregular
    apply hbase.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iio_mem_nhds hL)] with ε hε hεL
    dsimp only [scalar, target, L]
    symm
    exact diagonal_log_cutoff_eq_regularPart hε hεL.le
      (continuous_suzukiYoshidaEvenPositiveDiagonalCorrelation mode)
      (fun t ht =>
        suzukiYoshidaEvenPositiveDiagonalCorrelation_sub_one_div
          mode hmode (ne_of_gt (hε.trans_le ht.1)))
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεLscalar : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ L := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < L :=
      mem_inf_of_left (Iio_mem_nhds hL)
    exact hlt.mono fun _ h => h.le
  have hεL : ∀ᶠ p in l, p.1 ≤ L :=
    tendsto_fst.eventually hεLscalar
  have hLR : ∀ᶠ p in l, L ≤ p.2 :=
    tendsto_snd.eventually (eventually_ge_atTop L)
  have heq : ∀ᶠ p in l, cutoff p = scalar p.1 := by
    filter_upwards [hεpos, hεL, hLR] with p hp hpl hpR
    have hcut := congrArg Complex.re
      (suzukiYoshidaEvenSourceKernelPairing_cutoff_diagonal
        hsource hp (hpl.trans hpR) mode)
    have hphysical :=
      re_suzukiReciprocalCutoffL2CrossCorrelationPairing_evenPositive
        hp hpl hpR mode hmode
    dsimp only [cutoff, scalar]
    norm_num [Complex.sub_re, Complex.mul_re, Complex.inv_re,
      Complex.normSq] at hcut
    rw [hphysical] at hcut
    dsimp only [L]
    linarith
  have hcutLimit : Tendsto cutoff l
      (nhds (suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) mode mode).re) :=
    (Complex.continuous_re.tendsto _).comp
      (tendsto_suzukiYoshidaEvenSourceKernelPairing_cutoff_diagonal
        hsource mode)
  have hcutTarget : Tendsto cutoff l (nhds target) :=
    (hscalar.comp tendsto_fst).congr'
      (heq.mono fun _ h => h.symm)
  dsimp only [target, L] at hcutTarget ⊢
  exact tendsto_nhds_unique hcutLimit hcutTarget

theorem re_suzukiYoshidaEvenSourceKernelPairing_diagonal_zero
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    (suzukiYoshidaEvenSourceKernelPairing
      (suzukiYoshidaComparisonLimitKernel hsource) 0 0).re =
      -Real.log (2 * suzukiProjectAStar) -
        ∫ _t in (0 : Real)..2 * suzukiProjectAStar,
          -(2 * suzukiProjectAStar)⁻¹ := by
  let L : Real := 2 * suzukiProjectAStar
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  let cutoff : Real × Real → Real := fun p =>
    (suzukiYoshidaEvenSourceKernelPairing
      (suzukiYoshidaDiagonalRenormalizedCutoffKernel p.1 p.2) 0 0).re
  let scalar : Real → Real := fun ε =>
    -Real.log ε - ∫ t in ε..L,
      suzukiYoshidaEvenZeroDiagonalCorrelation t / t
  let target : Real :=
    -Real.log L - ∫ _t in (0 : Real)..L, -(2 * suzukiProjectAStar)⁻¹
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos (by norm_num) suzukiProjectAStar_pos
  have hregularInt : IntegrableOn
      (fun _t : Real => -(2 * suzukiProjectAStar)⁻¹) (Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      (continuous_const.intervalIntegrable 0 L)
  have hregular := tendsto_intervalIntegral_zero_right_of_integrableOn_Ioc
    hL hregularInt
  have hscalar : Tendsto scalar (𝓝[>] (0 : Real)) (nhds target) := by
    have hconst : Tendsto (fun _ : Real => -Real.log L) (𝓝[>] (0 : Real))
        (nhds (-Real.log L)) := tendsto_const_nhds
    have hbase := hconst.sub hregular
    apply hbase.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iio_mem_nhds hL)] with ε hε hεL
    dsimp only [scalar, target, L]
    symm
    exact diagonal_log_cutoff_eq_regularPart hε hεL.le
      continuous_suzukiYoshidaEvenZeroDiagonalCorrelation
      (fun t ht =>
        suzukiYoshidaEvenZeroDiagonalCorrelation_sub_one_div
          (ne_of_gt (hε.trans_le ht.1)))
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεLscalar : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ L := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < L :=
      mem_inf_of_left (Iio_mem_nhds hL)
    exact hlt.mono fun _ h => h.le
  have hεL : ∀ᶠ p in l, p.1 ≤ L :=
    tendsto_fst.eventually hεLscalar
  have hLR : ∀ᶠ p in l, L ≤ p.2 :=
    tendsto_snd.eventually (eventually_ge_atTop L)
  have heq : ∀ᶠ p in l, cutoff p = scalar p.1 := by
    filter_upwards [hεpos, hεL, hLR] with p hp hpl hpR
    have hcut := congrArg Complex.re
      (suzukiYoshidaEvenSourceKernelPairing_cutoff_diagonal
        hsource hp (hpl.trans hpR) 0)
    have hphysical :=
      re_suzukiReciprocalCutoffL2CrossCorrelationPairing_evenZero
        hp hpl hpR
    dsimp only [cutoff, scalar]
    norm_num [Complex.sub_re, Complex.mul_re, Complex.inv_re,
      Complex.normSq] at hcut
    rw [hphysical] at hcut
    dsimp only [L]
    linarith
  have hcutLimit : Tendsto cutoff l
      (nhds (suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) 0 0).re) :=
    (Complex.continuous_re.tendsto _).comp
      (tendsto_suzukiYoshidaEvenSourceKernelPairing_cutoff_diagonal
        hsource 0)
  have hcutTarget : Tendsto cutoff l (nhds target) :=
    (hscalar.comp tendsto_fst).congr'
      (heq.mono fun _ h => h.symm)
  dsimp only [target, L] at hcutTarget ⊢
  exact tendsto_nhds_unique hcutLimit hcutTarget

theorem re_suzukiYoshidaOddSourceKernelPairing_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiYoshidaOddSourceKernelPairing
      (suzukiYoshidaComparisonLimitKernel hsource) mode mode).re =
      -Real.log (2 * suzukiProjectAStar) -
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiYoshidaOddDiagonalRegularPart mode t := by
  let L : Real := 2 * suzukiProjectAStar
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  let cutoff : Real × Real → Real := fun p =>
    (suzukiYoshidaOddSourceKernelPairing
      (suzukiYoshidaDiagonalRenormalizedCutoffKernel p.1 p.2) mode mode).re
  let scalar : Real → Real := fun ε =>
    -Real.log ε - ∫ t in ε..L,
      suzukiYoshidaOddDiagonalCorrelation mode t / t
  let target : Real :=
    -Real.log L - ∫ t in (0 : Real)..L,
      suzukiYoshidaOddDiagonalRegularPart mode t
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos (by norm_num) suzukiProjectAStar_pos
  have hregularInt : IntegrableOn
      (suzukiYoshidaOddDiagonalRegularPart mode) (Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      ((continuous_suzukiYoshidaOddDiagonalRegularPart mode).intervalIntegrable
        0 L)
  have hregular := tendsto_intervalIntegral_zero_right_of_integrableOn_Ioc
    hL hregularInt
  have hscalar : Tendsto scalar (𝓝[>] (0 : Real)) (nhds target) := by
    have hconst : Tendsto (fun _ : Real => -Real.log L) (𝓝[>] (0 : Real))
        (nhds (-Real.log L)) := tendsto_const_nhds
    have hbase := hconst.sub hregular
    apply hbase.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iio_mem_nhds hL)] with ε hε hεL
    dsimp only [scalar, target, L]
    symm
    exact diagonal_log_cutoff_eq_regularPart hε hεL.le
      (continuous_suzukiYoshidaOddDiagonalCorrelation mode)
      (fun t ht =>
        suzukiYoshidaOddDiagonalCorrelation_sub_one_div
          mode hmode (ne_of_gt (hε.trans_le ht.1)))
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεLscalar : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ L := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < L :=
      mem_inf_of_left (Iio_mem_nhds hL)
    exact hlt.mono fun _ h => h.le
  have hεL : ∀ᶠ p in l, p.1 ≤ L :=
    tendsto_fst.eventually hεLscalar
  have hLR : ∀ᶠ p in l, L ≤ p.2 :=
    tendsto_snd.eventually (eventually_ge_atTop L)
  have heq : ∀ᶠ p in l, cutoff p = scalar p.1 := by
    filter_upwards [hεpos, hεL, hLR] with p hp hpl hpR
    have hcut := congrArg Complex.re
      (suzukiYoshidaOddSourceKernelPairing_cutoff_diagonal
        hsource hp (hpl.trans hpR) mode hmode)
    have hphysical :=
      re_suzukiReciprocalCutoffL2CrossCorrelationPairing_odd
        hp hpl hpR mode hmode
    dsimp only [cutoff, scalar]
    norm_num [Complex.sub_re, Complex.mul_re, Complex.inv_re,
      Complex.normSq] at hcut
    rw [hphysical] at hcut
    dsimp only [L]
    linarith
  have hcutLimit : Tendsto cutoff l
      (nhds (suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaComparisonLimitKernel hsource) mode mode).re) :=
    (Complex.continuous_re.tendsto _).comp
      (tendsto_suzukiYoshidaOddSourceKernelPairing_cutoff_diagonal
        hsource mode)
  have hcutTarget : Tendsto cutoff l (nhds target) :=
    (hscalar.comp tendsto_fst).congr'
      (heq.mono fun _ h => h.symm)
  dsimp only [target, L] at hcutTarget ⊢
  exact tendsto_nhds_unique hcutLimit hcutTarget

theorem suzukiYoshidaComparisonForm_evenPositive_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      ((-Real.log (2 * suzukiProjectAStar) -
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiYoshidaEvenPositiveDiagonalRegularPart mode t : Real) : Complex) := by
  apply Complex.ext
  · rw [suzukiYoshidaComparisonForm_evenSource]
    exact re_suzukiYoshidaEvenSourceKernelPairing_diagonal_of_pos
      hsource mode hmode
  · have hsym := suzukiYoshidaComparisonForm_conj_symm
      (suzukiYoshidaEvenLinearCompletionOfSource
        hsource suzukiProjectAStar_pos mode)
      (suzukiYoshidaEvenLinearCompletionOfSource
        hsource suzukiProjectAStar_pos mode)
    have him := congrArg Complex.im hsym
    rw [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

theorem suzukiYoshidaComparisonForm_evenZero_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0) =
      ((-Real.log (2 * suzukiProjectAStar) -
        ∫ _t in (0 : Real)..2 * suzukiProjectAStar,
          -(2 * suzukiProjectAStar)⁻¹ : Real) : Complex) := by
  apply Complex.ext
  · rw [suzukiYoshidaComparisonForm_evenSource]
    exact re_suzukiYoshidaEvenSourceKernelPairing_diagonal_zero hsource
  · have hsym := suzukiYoshidaComparisonForm_conj_symm
      (suzukiYoshidaEvenLinearCompletionOfSource
        hsource suzukiProjectAStar_pos 0)
      (suzukiYoshidaEvenLinearCompletionOfSource
        hsource suzukiProjectAStar_pos 0)
    have him := congrArg Complex.im hsym
    rw [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

theorem suzukiYoshidaComparisonForm_odd_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      ((-Real.log (2 * suzukiProjectAStar) -
        ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiYoshidaOddDiagonalRegularPart mode t : Real) : Complex) := by
  apply Complex.ext
  · rw [suzukiYoshidaComparisonForm_oddSource]
    exact re_suzukiYoshidaOddSourceKernelPairing_diagonal hsource mode hmode
  · have hsym := suzukiYoshidaComparisonForm_conj_symm
      (suzukiYoshidaOddLinearCompletionOfSource
        hsource suzukiProjectAStar_pos mode)
      (suzukiYoshidaOddLinearCompletionOfSource
        hsource suzukiProjectAStar_pos mode)
    have him := congrArg Complex.im hsym
    rw [Complex.conj_im] at him
    simp only [Complex.ofReal_im]
    linarith

/-! ## Algebraic normalization of one-decay terms -/

private theorem suzukiEvenPositiveDecayAlgebra
    {a d f e : Real} (ha : 0 < a) (hd : 0 < d) (hf : 0 < f) :
    let w := f / a
    let D := d ^ 2 + w ^ 2
    d * (1 - e) / D -
          (e * (-(2 * a * d * D) - (d ^ 2 - w ^ 2)) +
            (d ^ 2 - w ^ 2)) / (2 * a * D ^ 2) -
        (1 - e) / (2 * a * D) =
      1 / d +
        a * f ^ 2 *
            (2 * (a * d) ^ 3 + (a * d) ^ 2 * f ^ 2 +
              (a * d) * f ^ 2 + f ^ 4) /
          ((a * d) ^ 3 * ((a * d) ^ 2 + f ^ 2) ^ 2) +
        a * (a * d) ^ 2 * e / ((a * d) ^ 2 + f ^ 2) ^ 2 -
        (1 / a) / d ^ 2 -
        (f ^ 2 / a ^ 2) / d ^ 3 := by
  dsimp only
  have hD : d ^ 2 + (f / a) ^ 2 ≠ 0 := by positivity
  have hScaled : (a * d) ^ 2 + f ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', hd.ne', hf.ne', hD, hScaled]
  ring

private theorem suzukiOddPositiveDecayAlgebra
    {a d f e : Real} (ha : 0 < a) (hd : 0 < d) (hf : 0 < f) :
    let w := f / a
    let D := d ^ 2 + w ^ 2
    d * (1 - e) / D -
          (e * (-(2 * a * d * D) - (d ^ 2 - w ^ 2)) +
            (d ^ 2 - w ^ 2)) / (2 * a * D ^ 2) +
        (1 - e) / (2 * a * D) =
      1 / d +
        a * f ^ 2 *
            ((a * d) ^ 3 + (a * d) ^ 2 * f ^ 2 + f ^ 4) /
          ((a * d) ^ 3 * ((a * d) ^ 2 + f ^ 2) ^ 2) -
        a * f ^ 2 * e / ((a * d) ^ 2 + f ^ 2) ^ 2 -
        (f ^ 2 / a ^ 2) / d ^ 3 := by
  dsimp only
  have hD : d ^ 2 + (f / a) ^ 2 ≠ 0 := by positivity
  have hScaled : (a * d) ^ 2 + f ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', hd.ne', hf.ne', hD, hScaled]
  ring

private theorem suzukiEvenZeroDecayAlgebra
    {a d e : Real} (ha : 0 < a) (hd : 0 < d) :
    d * (1 - e) / d ^ 2 -
        (e * (-(2 * a * d * d ^ 2) - d ^ 2) + d ^ 2) /
          (2 * a * (d ^ 2) ^ 2) =
      1 / d + e / (2 * a * d ^ 2) - (1 / (2 * a)) / d ^ 2 := by
  field_simp [ha.ne', hd.ne']
  ring

private theorem suzukiEvenPositiveDecayAlgebra_frozen
    (mode n : Nat) (hmode : 0 < mode) :
    let a := suzukiProjectAStar
    let d := suzukiDF6D4DiagonalDecay n
    let f := suzukiDF6D4DiagonalFrequency mode
    let e := Real.exp (-a) ^ (4 * n + 1)
    let D := d ^ 2 + (f / a) ^ 2
    d * (1 - e) / D -
          (e * (-(2 * a * d * D) - (d ^ 2 - (f / a) ^ 2)) +
            (d ^ 2 - (f / a) ^ 2)) / (2 * a * D ^ 2) -
        (1 - e) / (2 * a * D) =
      1 / d + suzukiDF6D4EvenDiagonalBaseTerm mode n +
        suzukiDF6D4EvenDiagonalExpTerm mode n +
        suzukiDF6D4EvenDiagonalOriginSlope mode / d ^ 2 +
        suzukiDF6D4DiagonalOriginSecond mode / d ^ 3 := by
  dsimp only
  have hd : 0 < suzukiDF6D4DiagonalDecay n := by
    unfold suzukiDF6D4DiagonalDecay
    positivity
  have hf : 0 < suzukiDF6D4DiagonalFrequency mode := by
    unfold suzukiDF6D4DiagonalFrequency
    positivity
  have h := suzukiEvenPositiveDecayAlgebra
    (a := suzukiProjectAStar) (d := suzukiDF6D4DiagonalDecay n)
    (f := suzukiDF6D4DiagonalFrequency mode)
    (e := Real.exp (-suzukiProjectAStar) ^ (4 * n + 1))
    suzukiProjectAStar_pos hd hf
  unfold suzukiDF6D4EvenDiagonalBaseTerm
    suzukiDF6D4EvenDiagonalExpTerm
    suzukiDF6D4EvenDiagonalOriginSlope
    suzukiDF6D4DiagonalOriginSecond
  simp only [if_neg hmode.ne']
  convert h using 1 <;>
    field_simp [suzukiProjectAStar_pos.ne', hd.ne', hf.ne'] <;> ring

private theorem suzukiOddPositiveDecayAlgebra_frozen
    (mode n : Nat) (hmode : 0 < mode) :
    let a := suzukiProjectAStar
    let d := suzukiDF6D4DiagonalDecay n
    let f := suzukiDF6D4DiagonalFrequency mode
    let e := Real.exp (-a) ^ (4 * n + 1)
    let D := d ^ 2 + (f / a) ^ 2
    d * (1 - e) / D -
          (e * (-(2 * a * d * D) - (d ^ 2 - (f / a) ^ 2)) +
            (d ^ 2 - (f / a) ^ 2)) / (2 * a * D ^ 2) +
        (1 - e) / (2 * a * D) =
      1 / d + suzukiDF6D4OddDiagonalBaseTerm mode n -
        suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n +
        suzukiDF6D4DiagonalOriginSecond mode / d ^ 3 := by
  dsimp only
  have hd : 0 < suzukiDF6D4DiagonalDecay n := by
    unfold suzukiDF6D4DiagonalDecay
    positivity
  have hf : 0 < suzukiDF6D4DiagonalFrequency mode := by
    unfold suzukiDF6D4DiagonalFrequency
    positivity
  have h := suzukiOddPositiveDecayAlgebra
    (a := suzukiProjectAStar) (d := suzukiDF6D4DiagonalDecay n)
    (f := suzukiDF6D4DiagonalFrequency mode)
    (e := Real.exp (-suzukiProjectAStar) ^ (4 * n + 1))
    suzukiProjectAStar_pos hd hf
  unfold suzukiDF6D4OddDiagonalBaseTerm
    suzukiDF6D4OddDiagonalExpMagnitudeTerm
    suzukiDF6D4DiagonalOriginSecond
  convert h using 1 <;>
    field_simp [suzukiProjectAStar_pos.ne', hd.ne', hf.ne'] <;> ring

private theorem suzukiEvenZeroDecayAlgebra_frozen (n : Nat) :
    let a := suzukiProjectAStar
    let d := suzukiDF6D4DiagonalDecay n
    let e := Real.exp (-a) ^ (4 * n + 1)
    d * (1 - e) / d ^ 2 -
        (e * (-(2 * a * d * d ^ 2) - d ^ 2) + d ^ 2) /
          (2 * a * (d ^ 2) ^ 2) =
      1 / d + suzukiDF6D4EvenDiagonalBaseTerm 0 n +
        suzukiDF6D4EvenDiagonalExpTerm 0 n +
        suzukiDF6D4EvenDiagonalOriginSlope 0 / d ^ 2 +
        suzukiDF6D4DiagonalOriginSecond 0 / d ^ 3 := by
  dsimp only
  have hd : 0 < suzukiDF6D4DiagonalDecay n := by
    unfold suzukiDF6D4DiagonalDecay
    positivity
  have h := suzukiEvenZeroDecayAlgebra
    (a := suzukiProjectAStar) (d := suzukiDF6D4DiagonalDecay n)
    (e := Real.exp (-suzukiProjectAStar) ^ (4 * n + 1))
    suzukiProjectAStar_pos hd
  unfold suzukiDF6D4EvenDiagonalBaseTerm
    suzukiDF6D4EvenDiagonalExpTerm
    suzukiDF6D4EvenDiagonalOriginSlope
    suzukiDF6D4DiagonalOriginSecond
    suzukiDF6D4DiagonalFrequency
  simp only [if_pos rfl]
  convert h using 1 <;>
    norm_num <;> field_simp [suzukiProjectAStar_pos.ne', hd.ne'] <;> ring

/-! ## One-decay correlation evaluations -/

theorem integral_exp_neg_mul_evenPositiveDiagonalCorrelation
    (mode n : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
      1 / suzukiDF6D4DiagonalDecay n +
        suzukiDF6D4EvenDiagonalBaseTerm mode n +
        suzukiDF6D4EvenDiagonalExpTerm mode n +
        suzukiDF6D4EvenDiagonalOriginSlope mode /
          suzukiDF6D4DiagonalDecay n ^ 2 +
        suzukiDF6D4DiagonalOriginSecond mode /
          suzukiDF6D4DiagonalDecay n ^ 3 := by
  let a := suzukiProjectAStar
  let d := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let w := f / a
  have ha : 0 < a := suzukiProjectAStar_pos
  have hd : 0 < d := by
    dsimp only [d]
    unfold suzukiDF6D4DiagonalDecay
    positivity
  have hf : 0 < f := by
    dsimp only [f]
    unfold suzukiDF6D4DiagonalFrequency
    positivity
  have hw : 0 < w := div_pos hf ha
  have hden : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  have hscaledDen : (a * d) ^ 2 + f ^ 2 ≠ 0 := by positivity
  have hexpandedDen :
      d ^ 2 * f ^ 2 * a⁻¹ ^ 2 * 2 + d ^ 4 + f ^ 4 * a⁻¹ ^ 4 ≠ 0 := by
    positivity
  have hfrozenDen :
      d ^ 2 * f ^ 2 * a ^ 4 * 2 + d ^ 4 * a ^ 6 + f ^ 4 * a ^ 2 ≠ 0 := by
    positivity
  have hendpointDen :
      d ^ 2 * f ^ 2 * a ^ 2 * 2 + d ^ 4 * a ^ 4 + f ^ 4 ≠ 0 := by
    positivity
  have hcos := integral_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have htcos := integral_mul_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have hsin := integral_exp_neg_mul_mul_sin_eq_archimedeanPrimitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have harg : w * (2 * a) = (mode : Real) * (2 * Real.pi) := by
    dsimp only [w, f, a]
    unfold suzukiDF6D4DiagonalFrequency
    field_simp [ha.ne']
    simp [suzukiProjectAStar_pos.ne']
  have hsinEnd : Real.sin (w * (2 * a)) = 0 := by
    rw [harg, ← sub_zero ((mode : Real) * (2 * Real.pi)),
      Real.sin_nat_mul_two_pi_sub]
    simp
  have hcosEnd : Real.cos (w * (2 * a)) = 1 := by
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hexpEnd : Real.exp (-d * (2 * a)) =
      Real.exp (-a) ^ (4 * n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [d, a]
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    ring
  have hCosInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hTCosInt : IntervalIntegrable
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hSinInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) *
            suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.cos (w * t)) -
        (1 / (2 * a)) * (∫ t in (0 : Real)..2 * a,
          t * Real.exp (-d * t) * Real.cos (w * t)) -
        (1 / (2 * a * w)) * (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.sin (w * t)) := by
    calc
      _ = ∫ t in (0 : Real)..2 * a,
          (Real.exp (-d * t) * Real.cos (w * t) -
            (1 / (2 * a)) *
              (t * Real.exp (-d * t) * Real.cos (w * t)) -
            (1 / (2 * a * w)) *
              (Real.exp (-d * t) * Real.sin (w * t))) := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiYoshidaEvenPositiveDiagonalCorrelation
            dsimp only [a, w, f]
            unfold suzukiDF6D4DiagonalFrequency
            field_simp [ha.ne', hw.ne', hf.ne']
            field_simp [suzukiProjectAStar_pos.ne']
      _ = _ := by
        rw [intervalIntegral.integral_sub
              (hCosInt.sub (hTCosInt.const_mul _)) (hSinInt.const_mul _),
          intervalIntegral.integral_sub hCosInt (hTCosInt.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hsplit, hcos, htcos, hsin]
  have hprimitive := suzukiEvenPrimitiveCombination_eq_closed
    ha hw hsinEnd hcosEnd hexpEnd
  have halgebra := suzukiEvenPositiveDecayAlgebra_frozen mode n hmode
  dsimp only at halgebra
  rw [hprimitive]
  simpa only [a, d, f, w] using halgebra

theorem integral_exp_neg_mul_oddDiagonalCorrelation
    (mode n : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
          suzukiYoshidaOddDiagonalCorrelation mode t) =
      1 / suzukiDF6D4DiagonalDecay n +
        suzukiDF6D4OddDiagonalBaseTerm mode n -
        suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n +
        suzukiDF6D4DiagonalOriginSecond mode /
          suzukiDF6D4DiagonalDecay n ^ 3 := by
  let a := suzukiProjectAStar
  let d := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let w := f / a
  have ha : 0 < a := suzukiProjectAStar_pos
  have hd : 0 < d := by
    dsimp only [d]
    unfold suzukiDF6D4DiagonalDecay
    positivity
  have hf : 0 < f := by
    dsimp only [f]
    unfold suzukiDF6D4DiagonalFrequency
    positivity
  have hw : 0 < w := div_pos hf ha
  have hden : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  have hscaledDen : (a * d) ^ 2 + f ^ 2 ≠ 0 := by positivity
  have hexpandedDen :
      d ^ 2 * f ^ 2 * a⁻¹ ^ 2 * 2 + d ^ 4 + f ^ 4 * a⁻¹ ^ 4 ≠ 0 := by
    positivity
  have hfrozenDen :
      d ^ 2 * f ^ 2 * a ^ 4 * 2 + d ^ 4 * a ^ 6 + f ^ 4 * a ^ 2 ≠ 0 := by
    positivity
  have hendpointDen :
      d ^ 2 * f ^ 2 * a ^ 2 * 2 + d ^ 4 * a ^ 4 + f ^ 4 ≠ 0 := by
    positivity
  have hcos := integral_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have htcos := integral_mul_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have hsin := integral_exp_neg_mul_mul_sin_eq_archimedeanPrimitive_sub
    (d := d) (w := w) (L := 2 * a) hden
  have harg : w * (2 * a) = (mode : Real) * (2 * Real.pi) := by
    dsimp only [w, f, a]
    unfold suzukiDF6D4DiagonalFrequency
    field_simp [ha.ne']
    simp [suzukiProjectAStar_pos.ne']
  have hsinEnd : Real.sin (w * (2 * a)) = 0 := by
    rw [harg, ← sub_zero ((mode : Real) * (2 * Real.pi)),
      Real.sin_nat_mul_two_pi_sub]
    simp
  have hcosEnd : Real.cos (w * (2 * a)) = 1 := by
    rw [harg]
    exact Real.cos_nat_mul_two_pi mode
  have hexpEnd : Real.exp (-d * (2 * a)) =
      Real.exp (-a) ^ (4 * n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [d, a]
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    ring
  have hCosInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hTCosInt : IntervalIntegrable
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (w * t))).intervalIntegrable _ _
  have hSinInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.sin (w * t))).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * suzukiYoshidaOddDiagonalCorrelation mode t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.cos (w * t)) -
        (1 / (2 * a)) * (∫ t in (0 : Real)..2 * a,
          t * Real.exp (-d * t) * Real.cos (w * t)) +
        (1 / (2 * a * w)) * (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.sin (w * t)) := by
    calc
      _ = ∫ t in (0 : Real)..2 * a,
          (Real.exp (-d * t) * Real.cos (w * t) -
            (1 / (2 * a)) *
              (t * Real.exp (-d * t) * Real.cos (w * t)) +
            (1 / (2 * a * w)) *
              (Real.exp (-d * t) * Real.sin (w * t))) := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiYoshidaOddDiagonalCorrelation
            dsimp only [a, w, f]
            unfold suzukiDF6D4DiagonalFrequency
            field_simp [ha.ne', hw.ne', hf.ne']
            field_simp [suzukiProjectAStar_pos.ne']
      _ = _ := by
        rw [intervalIntegral.integral_add
              (hCosInt.sub (hTCosInt.const_mul _)) (hSinInt.const_mul _),
          intervalIntegral.integral_sub hCosInt (hTCosInt.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hsplit, hcos, htcos, hsin]
  have hprimitive := suzukiOddPrimitiveCombination_eq_closed
    ha hw hsinEnd hcosEnd hexpEnd
  have halgebra := suzukiOddPositiveDecayAlgebra_frozen mode n hmode
  dsimp only at halgebra
  rw [hprimitive]
  simpa only [a, d, f, w] using halgebra

theorem integral_exp_neg_mul_evenZeroDiagonalCorrelation (n : Nat) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
          suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      1 / suzukiDF6D4DiagonalDecay n +
        suzukiDF6D4EvenDiagonalBaseTerm 0 n +
        suzukiDF6D4EvenDiagonalExpTerm 0 n +
        suzukiDF6D4EvenDiagonalOriginSlope 0 /
          suzukiDF6D4DiagonalDecay n ^ 2 +
        suzukiDF6D4DiagonalOriginSecond 0 /
          suzukiDF6D4DiagonalDecay n ^ 3 := by
  let a := suzukiProjectAStar
  let d := suzukiDF6D4DiagonalDecay n
  have ha : 0 < a := suzukiProjectAStar_pos
  have hd : 0 < d := by
    dsimp only [d]
    unfold suzukiDF6D4DiagonalDecay
    positivity
  have hden : d ^ 2 + (0 : Real) ^ 2 ≠ 0 := by positivity
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd.ne'
  have hd3 : d ^ 3 ≠ 0 := pow_ne_zero 3 hd.ne'
  have hd4 : d ^ 4 ≠ 0 := pow_ne_zero 4 hd.ne'
  have hcos := integral_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := 0) (L := 2 * a) hden
  have htcos := integral_mul_exp_neg_mul_cos_eq_primitive_sub
    (d := d) (w := 0) (L := 2 * a) hden
  have hexpEnd : Real.exp (-d * (2 * a)) =
      Real.exp (-a) ^ (4 * n + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [d, a]
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    ring
  have hCosInt : IntervalIntegrable
      (fun t : Real => Real.exp (-d * t) * Real.cos (0 * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => Real.exp (-d * t) * Real.cos (0 * t))).intervalIntegrable _ _
  have hTCosInt : IntervalIntegrable
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (0 * t))
      volume 0 (2 * a) :=
    (by fun_prop : Continuous
      (fun t : Real => t * Real.exp (-d * t) * Real.cos (0 * t))).intervalIntegrable _ _
  have hsplit :
      (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * suzukiYoshidaEvenZeroDiagonalCorrelation t) =
        (∫ t in (0 : Real)..2 * a,
          Real.exp (-d * t) * Real.cos (0 * t)) -
        (1 / (2 * a)) * (∫ t in (0 : Real)..2 * a,
          t * Real.exp (-d * t) * Real.cos (0 * t)) := by
    calc
      _ = ∫ t in (0 : Real)..2 * a,
          (Real.exp (-d * t) * Real.cos (0 * t) -
            (1 / (2 * a)) *
              (t * Real.exp (-d * t) * Real.cos (0 * t))) := by
            apply intervalIntegral.integral_congr
            intro t _
            unfold suzukiYoshidaEvenZeroDiagonalCorrelation
            simp
            ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hCosInt (hTCosInt.const_mul _),
          intervalIntegral.integral_const_mul]
  rw [hsplit, hcos, htcos]
  have hprimitive := suzukiEvenZeroPrimitiveCombination_eq_closed
    ha hd.ne' hexpEnd
  have halgebra := suzukiEvenZeroDecayAlgebra_frozen n
  dsimp only at halgebra
  rw [hprimitive]
  simpa only [a, d] using halgebra

/-! ## The diagonal restoration constant -/

/-- The summable correction between Suzuki's half-integer Gamma decays and
the odd reciprocal kernel used to renormalize the source cutoff. -/
def suzukiDF6D4DiagonalRestorationSummand (n : Nat) : Real :=
  1 / suzukiDF6D4DiagonalDecay n - 1 / (2 * (n : Real) + 1)

theorem suzukiDF6D4DiagonalRestorationSummand_eq (n : Nat) :
    suzukiDF6D4DiagonalRestorationSummand n =
      1 / ((4 * (n : Real) + 1) * (2 * (n : Real) + 1)) := by
  unfold suzukiDF6D4DiagonalRestorationSummand
    suzukiDF6D4DiagonalDecay
  field_simp
  ring

theorem suzukiDF6D4DiagonalRestorationSummand_nonneg (n : Nat) :
    0 ≤ suzukiDF6D4DiagonalRestorationSummand n := by
  rw [suzukiDF6D4DiagonalRestorationSummand_eq]
  positivity

theorem suzukiDF6D4DiagonalRestorationSummand_le (n : Nat) :
    suzukiDF6D4DiagonalRestorationSummand n ≤
      1 / ((n : Real) + 1) ^ 2 := by
  rw [suzukiDF6D4DiagonalRestorationSummand_eq]
  have hleft : 0 < ((n : Real) + 1) ^ 2 := by positivity
  have hright : 0 <
      (4 * (n : Real) + 1) * (2 * (n : Real) + 1) := by positivity
  apply (div_le_div_iff₀ hright hleft).2
  norm_num
  nlinarith [sq_nonneg (n : Real)]

theorem summable_suzukiDF6D4DiagonalRestorationSummand :
    Summable suzukiDF6D4DiagonalRestorationSummand := by
  have hp : Summable (fun n : Nat => 1 / ((n : Real) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow).2 (by norm_num : 1 < 2)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).2 h
  exact Summable.of_nonneg_of_le
    suzukiDF6D4DiagonalRestorationSummand_nonneg
    suzukiDF6D4DiagonalRestorationSummand_le hp

/-- A finite restoration prefix splits into a Leibniz prefix and a harmonic
combination whose logarithmic limit is `log 2 / 2`. -/
theorem sum_suzukiDF6D4DiagonalRestorationSummand (N : Nat) :
    (∑ n ∈ Finset.range N, suzukiDF6D4DiagonalRestorationSummand n) =
      (∑ i ∈ Finset.range (2 * N),
        (-1 : Real) ^ i / (2 * (i : Real) + 1)) +
      ((harmonic (4 * N) : Real) -
        (3 / 2 : Real) * (harmonic (2 * N) : Real) +
        (1 / 2 : Real) * (harmonic N : Real)) := by
  induction N with
  | zero => simp [suzukiDF6D4DiagonalRestorationSummand]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
        Finset.sum_range_succ,
        show 2 * N + 1 = 2 * N + 1 by rfl,
        Finset.sum_range_succ]
      have hH4 :
          (harmonic (4 * (N + 1)) : Real) =
            (harmonic (4 * N) : Real) +
              1 / (4 * (N : Real) + 1) +
              1 / (4 * (N : Real) + 2) +
              1 / (4 * (N : Real) + 3) +
              1 / (4 * (N : Real) + 4) := by
        rw [show 4 * (N + 1) = (((4 * N + 1) + 1) + 1) + 1 by omega,
          harmonic_succ, harmonic_succ, harmonic_succ, harmonic_succ]
        push_cast
        ring
      have hH2 :
          (harmonic (2 * (N + 1)) : Real) =
            (harmonic (2 * N) : Real) +
              1 / (2 * (N : Real) + 1) +
              1 / (2 * (N : Real) + 2) := by
        rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
          harmonic_succ, harmonic_succ]
        push_cast
        ring
      have hH1 :
          (harmonic (N + 1) : Real) =
            (harmonic N : Real) + 1 / ((N : Real) + 1) := by
        rw [harmonic_succ]
        push_cast
        simp only [one_div]
      rw [hH4,
        show 2 * N + 1 + 1 = 2 * (N + 1) by omega,
        hH2, hH1]
      have heven : (-1 : Real) ^ (2 * N) = 1 := by
        rw [pow_mul]
        norm_num
      have hodd : (-1 : Real) ^ (2 * N + 1) = -1 := by
        rw [pow_add, heven]
        norm_num
      rw [heven, hodd]
      unfold suzukiDF6D4DiagonalRestorationSummand
        suzukiDF6D4DiagonalDecay
      push_cast
      field_simp
      ring

private theorem tendsto_suzukiDiagonalHarmonicCombination :
    Tendsto
      (fun N : Nat =>
        (harmonic (4 * N) : Real) -
          (3 / 2 : Real) * (harmonic (2 * N) : Real) +
          (1 / 2 : Real) * (harmonic N : Real))
      atTop (nhds (Real.log 2 / 2)) := by
  let err : Nat → Real := fun N =>
    (harmonic N : Real) - Real.log (N : Real)
  have htwo : Tendsto (fun N : Nat => 2 * N) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b, fun N hN => by omega⟩
  have hfour : Tendsto (fun N : Nat => 4 * N) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b, fun N hN => by omega⟩
  have herr : Tendsto err atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa only [err] using Real.tendsto_harmonic_sub_log
  have herrTwo : Tendsto (fun N => err (2 * N)) atTop
      (nhds Real.eulerMascheroniConstant) := herr.comp htwo
  have herrFour : Tendsto (fun N => err (4 * N)) atTop
      (nhds Real.eulerMascheroniConstant) := herr.comp hfour
  have herrCombination : Tendsto
      (fun N => err (4 * N) - (3 / 2 : Real) * err (2 * N) +
        (1 / 2 : Real) * err N)
      atTop (nhds 0) := by
    have h := (herrFour.sub (herrTwo.const_mul (3 / 2 : Real))).add
      (herr.const_mul (1 / 2 : Real))
    convert h using 1 <;> ring
  have heventually : ∀ᶠ N in atTop,
      (harmonic (4 * N) : Real) -
          (3 / 2 : Real) * (harmonic (2 * N) : Real) +
          (1 / 2 : Real) * (harmonic N : Real) =
        (err (4 * N) - (3 / 2 : Real) * err (2 * N) +
          (1 / 2 : Real) * err N) + Real.log 2 / 2 := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
    have hlogTwo :
        Real.log ((2 * N : Nat) : Real) =
          Real.log 2 + Real.log (N : Real) := by
      rw [Nat.cast_mul]
      norm_num only [Nat.cast_ofNat]
      rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hN0]
    have hlogFour :
        Real.log ((4 * N : Nat) : Real) =
          2 * Real.log 2 + Real.log (N : Real) := by
      rw [Nat.cast_mul]
      norm_num only [Nat.cast_ofNat]
      rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0) hN0]
      have hfourLog : Real.log (4 : Real) = 2 * Real.log 2 := by
        rw [show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [hfourLog]
    dsimp only [err]
    rw [hlogFour, hlogTwo]
    ring
  have hlimit := herrCombination.add
    (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2 / 2)
      atTop (nhds (Real.log 2 / 2)))
  convert hlimit.congr' (heventually.mono fun _ h => h.symm) using 1 <;> ring

/-- The exact restoration series used in both diagonal Gamma components. -/
theorem tsum_suzukiDF6D4DiagonalRestorationSummand :
    (∑' n : Nat, suzukiDF6D4DiagonalRestorationSummand n) =
      Real.pi / 4 + Real.log 2 / 2 := by
  have htwo : Tendsto (fun N : Nat => 2 * N) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    exact eventually_atTop.2 ⟨b, fun N hN => by omega⟩
  have hLeibniz := Real.tendsto_sum_pi_div_four.comp htwo
  have hHarmonic := tendsto_suzukiDiagonalHarmonicCombination
  have hcombined := hLeibniz.add hHarmonic
  have hprefix : Tendsto
      (fun N => ∑ n ∈ Finset.range N,
        suzukiDF6D4DiagonalRestorationSummand n)
      atTop (nhds (Real.pi / 4 + Real.log 2 / 2)) := by
    apply hcombined.congr'
    filter_upwards with N
    simpa only [Function.comp_apply] using
      (sum_suzukiDF6D4DiagonalRestorationSummand N).symm
  exact tendsto_nhds_unique
    summable_suzukiDF6D4DiagonalRestorationSummand.hasSum.tendsto_sum_nat
    hprefix

/-! ## Assembly of the frozen diagonal Gamma cores -/

private theorem summable_suzukiDF6D4DiagonalDecay_inv_pow_local
    (p : Nat) (hp : 1 < p) :
    Summable (fun n : Nat => 1 / suzukiDF6D4DiagonalDecay n ^ p) := by
  have hNat : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ p)) := by
    have h := (Real.summable_nat_pow_inv (p := p)).2 hp
    simpa only [one_div] using (summable_nat_add_iff 1).2 h
  apply (summable_nat_add_iff 1).1
  apply Summable.of_nonneg_of_le
    (fun n => one_div_nonneg.mpr (pow_nonneg (by
      unfold suzukiDF6D4DiagonalDecay
      positivity : 0 ≤ suzukiDF6D4DiagonalDecay (n + 1)) p))
    (fun n => ?_) hNat
  have hbase : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hle : ((n + 1 : Nat) : Real) ≤
      suzukiDF6D4DiagonalDecay (n + 1) := by
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    linarith
  exact one_div_le_one_div_of_le (pow_pos hbase p)
    (pow_le_pow_left₀ hbase.le hle p)

/-- The renormalized even summand obtained after removing `1/λₙ` from the
literal exponential-correlation integral. -/
def suzukiYoshidaEvenDiagonalGammaCoreSummand
    (mode n : Nat) : Real :=
  suzukiDF6D4EvenDiagonalBaseTerm mode n +
    suzukiDF6D4EvenDiagonalExpTerm mode n +
    suzukiDF6D4EvenDiagonalOriginSlope mode /
      suzukiDF6D4DiagonalDecay n ^ 2 +
    suzukiDF6D4DiagonalOriginSecond mode /
      suzukiDF6D4DiagonalDecay n ^ 3

/-- The renormalized odd summand obtained after removing `1/λₙ`. -/
def suzukiYoshidaOddDiagonalGammaCoreSummand
    (mode n : Nat) : Real :=
  suzukiDF6D4OddDiagonalBaseTerm mode n -
    suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n +
    suzukiDF6D4DiagonalOriginSecond mode /
      suzukiDF6D4DiagonalDecay n ^ 3

theorem summable_suzukiYoshidaEvenDiagonalGammaCoreSummand (mode : Nat) :
    Summable (suzukiYoshidaEvenDiagonalGammaCoreSummand mode) := by
  have hbase := summable_suzukiDF6D4EvenDiagonalBaseTerm mode
  have hexp := summable_suzukiDF6D4EvenDiagonalExpTerm mode
  have hinv2 := summable_suzukiDF6D4DiagonalDecay_inv_pow_local 2 (by norm_num)
  have hinv3 := summable_suzukiDF6D4DiagonalDecay_inv_pow_local 3 (by norm_num)
  have hslope : Summable (fun n : Nat =>
      suzukiDF6D4EvenDiagonalOriginSlope mode /
        suzukiDF6D4DiagonalDecay n ^ 2) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      hinv2.mul_left (suzukiDF6D4EvenDiagonalOriginSlope mode)
  have hsecond : Summable (fun n : Nat =>
      suzukiDF6D4DiagonalOriginSecond mode /
        suzukiDF6D4DiagonalDecay n ^ 3) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      hinv3.mul_left (suzukiDF6D4DiagonalOriginSecond mode)
  exact ((hbase.add hexp).add hslope).add hsecond

theorem summable_suzukiYoshidaOddDiagonalGammaCoreSummand
    (mode : Nat) (hmode : 0 < mode) :
    Summable (suzukiYoshidaOddDiagonalGammaCoreSummand mode) := by
  have hbase := summable_suzukiDF6D4OddDiagonalBaseTerm mode hmode
  have hexp := summable_suzukiDF6D4OddDiagonalExpMagnitudeTerm mode
  have hinv3 := summable_suzukiDF6D4DiagonalDecay_inv_pow_local 3 (by norm_num)
  have hsecond : Summable (fun n : Nat =>
      suzukiDF6D4DiagonalOriginSecond mode /
        suzukiDF6D4DiagonalDecay n ^ 3) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      hinv3.mul_left (suzukiDF6D4DiagonalOriginSecond mode)
  exact (hbase.sub hexp).add hsecond

theorem tsum_suzukiYoshidaEvenDiagonalGammaCoreSummand (mode : Nat) :
    (∑' n : Nat, suzukiYoshidaEvenDiagonalGammaCoreSummand mode n) =
      suzukiDF6D4EvenDiagonalGammaCore mode := by
  have hbase := summable_suzukiDF6D4EvenDiagonalBaseTerm mode
  have hexp := summable_suzukiDF6D4EvenDiagonalExpTerm mode
  have hinv2 := summable_suzukiDF6D4DiagonalDecay_inv_pow_local 2 (by norm_num)
  have hinv3 := summable_suzukiDF6D4DiagonalDecay_inv_pow_local 3 (by norm_num)
  have hslope : Summable (fun n : Nat =>
      suzukiDF6D4EvenDiagonalOriginSlope mode /
        suzukiDF6D4DiagonalDecay n ^ 2) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      hinv2.mul_left (suzukiDF6D4EvenDiagonalOriginSlope mode)
  have hsecond : Summable (fun n : Nat =>
      suzukiDF6D4DiagonalOriginSecond mode /
        suzukiDF6D4DiagonalDecay n ^ 3) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      hinv3.mul_left (suzukiDF6D4DiagonalOriginSecond mode)
  unfold suzukiYoshidaEvenDiagonalGammaCoreSummand
    suzukiDF6D4EvenDiagonalGammaCore
    suzukiDF6D4DiagonalReciprocalSquareSum
    suzukiDF6D4DiagonalReciprocalCubeSum
  rw [((hbase.add hexp).add hslope).tsum_add hsecond,
    (hbase.add hexp).tsum_add hslope,
    hbase.tsum_add hexp]
  simp only [div_eq_mul_inv, one_div, one_mul, tsum_mul_left]

theorem tsum_suzukiYoshidaOddDiagonalGammaCoreSummand
    (mode : Nat) (hmode : 0 < mode) :
    (∑' n : Nat, suzukiYoshidaOddDiagonalGammaCoreSummand mode n) =
      suzukiDF6D4OddDiagonalGammaCore mode := by
  have hbase := summable_suzukiDF6D4OddDiagonalBaseTerm mode hmode
  have hexp := summable_suzukiDF6D4OddDiagonalExpMagnitudeTerm mode
  have hinv3 := summable_suzukiDF6D4DiagonalDecay_inv_pow_local 3 (by norm_num)
  have hsecond : Summable (fun n : Nat =>
      suzukiDF6D4DiagonalOriginSecond mode /
        suzukiDF6D4DiagonalDecay n ^ 3) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      hinv3.mul_left (suzukiDF6D4DiagonalOriginSecond mode)
  unfold suzukiYoshidaOddDiagonalGammaCoreSummand
    suzukiDF6D4OddDiagonalGammaCore
    suzukiDF6D4DiagonalReciprocalCubeSum
  rw [(hbase.sub hexp).tsum_add hsecond,
    hbase.tsum_sub hexp]
  simp only [div_eq_mul_inv, one_div, one_mul, tsum_mul_left]

theorem integral_exp_neg_mul_evenPositiveDiagonalCorrelation_sub_reciprocal
    (mode n : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) -
        1 / suzukiDF6D4DiagonalDecay n =
      suzukiYoshidaEvenDiagonalGammaCoreSummand mode n := by
  rw [integral_exp_neg_mul_evenPositiveDiagonalCorrelation mode n hmode]
  unfold suzukiYoshidaEvenDiagonalGammaCoreSummand
  ring

theorem integral_exp_neg_mul_evenZeroDiagonalCorrelation_sub_reciprocal
    (n : Nat) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
          suzukiYoshidaEvenZeroDiagonalCorrelation t) -
        1 / suzukiDF6D4DiagonalDecay n =
      suzukiYoshidaEvenDiagonalGammaCoreSummand 0 n := by
  rw [integral_exp_neg_mul_evenZeroDiagonalCorrelation n]
  unfold suzukiYoshidaEvenDiagonalGammaCoreSummand
  ring

theorem integral_exp_neg_mul_oddDiagonalCorrelation_sub_reciprocal
    (mode n : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
          suzukiYoshidaOddDiagonalCorrelation mode t) -
        1 / suzukiDF6D4DiagonalDecay n =
      suzukiYoshidaOddDiagonalGammaCoreSummand mode n := by
  rw [integral_exp_neg_mul_oddDiagonalCorrelation mode n hmode]
  unfold suzukiYoshidaOddDiagonalGammaCoreSummand
  ring

theorem tsum_integral_evenPositiveDiagonalCorrelation_sub_reciprocal
    (mode : Nat) (hmode : 0 < mode) :
    (∑' n : Nat,
      ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
            suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) -
        1 / suzukiDF6D4DiagonalDecay n)) =
      suzukiDF6D4EvenDiagonalGammaCore mode := by
  rw [tsum_congr (fun n =>
    integral_exp_neg_mul_evenPositiveDiagonalCorrelation_sub_reciprocal
      mode n hmode)]
  exact tsum_suzukiYoshidaEvenDiagonalGammaCoreSummand mode

theorem tsum_integral_evenZeroDiagonalCorrelation_sub_reciprocal :
    (∑' n : Nat,
      ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
            suzukiYoshidaEvenZeroDiagonalCorrelation t) -
        1 / suzukiDF6D4DiagonalDecay n)) =
      suzukiDF6D4EvenDiagonalGammaCore 0 := by
  rw [tsum_congr (fun n =>
    integral_exp_neg_mul_evenZeroDiagonalCorrelation_sub_reciprocal n)]
  exact tsum_suzukiYoshidaEvenDiagonalGammaCoreSummand 0

theorem tsum_integral_oddDiagonalCorrelation_sub_reciprocal
    (mode : Nat) (hmode : 0 < mode) :
    (∑' n : Nat,
      ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
            suzukiYoshidaOddDiagonalCorrelation mode t) -
        1 / suzukiDF6D4DiagonalDecay n)) =
      suzukiDF6D4OddDiagonalGammaCore mode := by
  rw [tsum_congr (fun n =>
    integral_exp_neg_mul_oddDiagonalCorrelation_sub_reciprocal
      mode n hmode)]
  exact tsum_suzukiYoshidaOddDiagonalGammaCoreSummand mode hmode

/-! ## Odd-reference series and its logarithmic normalization -/

/-- The odd-integer decay used to cancel the universal diagonal singularity. -/
def suzukiYoshidaDiagonalReferenceDecay (n : Nat) : Real :=
  2 * (n : Real) + 1

theorem suzukiYoshidaDiagonalReferenceDecay_pos (n : Nat) :
    0 < suzukiYoshidaDiagonalReferenceDecay n := by
  unfold suzukiYoshidaDiagonalReferenceDecay
  positivity

theorem suzukiYoshidaDiagonalReferenceDecay_eq_restoration_add_half
    (n : Nat) :
    suzukiYoshidaDiagonalReferenceDecay n =
      suzukiDF6D4DiagonalDecay n + 1 / 2 := by
  unfold suzukiYoshidaDiagonalReferenceDecay suzukiDF6D4DiagonalDecay
  ring

theorem summable_exp_neg_referenceDecay_mul {t : Real} (ht : 0 < t) :
    Summable (fun n : Nat =>
      Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)) := by
  let q : Real := Real.exp (-2 * t)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (Real.exp_lt_one_iff).2 (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom := (hasSum_geometric_of_norm_lt_one hqnorm).summable.mul_left
    (Real.exp (-t))
  exact hgeom.congr fun n => by
    dsimp only [q]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    unfold suzukiYoshidaDiagonalReferenceDecay
    congr 1
    ring

theorem tsum_exp_neg_referenceDecay_mul {t : Real} (ht : 0 < t) :
    (∑' n : Nat,
      Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)) =
      Real.exp (-t) / (1 - Real.exp (-2 * t)) := by
  let q : Real := Real.exp (-2 * t)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact (Real.exp_lt_one_iff).2 (by linarith)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hgeom := (hasSum_geometric_of_norm_lt_one hqnorm).mul_left
    (Real.exp (-t))
  calc
    (∑' n : Nat,
        Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)) =
        ∑' n : Nat, Real.exp (-t) * q ^ n := by
          apply tsum_congr
          intro n
          dsimp only [q]
          rw [← Real.exp_nat_mul, ← Real.exp_add]
          unfold suzukiYoshidaDiagonalReferenceDecay
          congr 1
          ring
    _ = Real.exp (-t) * (1 - q)⁻¹ := hgeom.tsum_eq
    _ = Real.exp (-t) / (1 - Real.exp (-2 * t)) := by
      simp only [q, div_eq_mul_inv]

theorem hasSum_exp_neg_referenceDecay_div
    {t : Real} (ht : 0 < t) :
    HasSum
      (fun n : Nat =>
        Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t) /
          suzukiYoshidaDiagonalReferenceDecay n)
      (1 / 2 *
        (Real.log (1 + Real.exp (-t)) -
          Real.log (1 - Real.exp (-t)))) := by
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 :=
    (Real.exp_lt_one_iff).2 (by linarith)
  have hqabs : |Real.exp (-t)| < 1 := by
    rwa [abs_of_nonneg hq0]
  have hseries :=
    (Real.hasSum_log_sub_log_of_abs_lt_one hqabs).mul_left (1 / 2)
  apply HasSum.congr_fun hseries
  intro n
  rw [← Real.exp_nat_mul]
  unfold suzukiYoshidaDiagonalReferenceDecay
  push_cast
  ring_nf

theorem tsum_exp_neg_referenceDecay_div
    {t : Real} (ht : 0 < t) :
    (∑' n : Nat,
      Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t) /
        suzukiYoshidaDiagonalReferenceDecay n) =
      1 / 2 *
        (Real.log (1 + Real.exp (-t)) -
          Real.log (1 - Real.exp (-t))) :=
  (hasSum_exp_neg_referenceDecay_div ht).tsum_eq

/-- Closed logarithmic form of the odd-reference reciprocal tail. -/
def suzukiYoshidaDiagonalReferenceTail (t : Real) : Real :=
  1 / 2 *
    (Real.log (1 + Real.exp (-t)) -
      Real.log (1 - Real.exp (-t)))

/-- Closed geometric form of the odd-reference exponential sum. -/
def suzukiYoshidaDiagonalReferenceSum (t : Real) : Real :=
  Real.exp (-t) / (1 - Real.exp (-2 * t))

theorem hasDerivAt_suzukiYoshidaDiagonalReferenceTail
    {t : Real} (ht : 0 < t) :
    HasDerivAt suzukiYoshidaDiagonalReferenceTail
      (-suzukiYoshidaDiagonalReferenceSum t) t := by
  have hq_lt : Real.exp (-t) < 1 :=
    (Real.exp_lt_one_iff).2 (by linarith)
  have hq : HasDerivAt (fun x : Real => Real.exp (-x))
      (-Real.exp (-t)) t := by
    have hbase := hasDerivAt_exp_neg_mul' 1 t
    have heq :
        (fun x : Real => Real.exp (-(1 : Real) * x)) =ᶠ[nhds t]
          fun x : Real => Real.exp (-x) := by
      filter_upwards with x
      congr 1
      ring
    exact (hbase.congr_of_eventuallyEq heq.symm).congr_deriv (by ring)
  have hplus : HasDerivAt (fun x : Real => 1 + Real.exp (-x))
      (-Real.exp (-t)) t := hq.const_add 1
  have hminus : HasDerivAt (fun x : Real => 1 - Real.exp (-x))
      (Real.exp (-t)) t := by
    exact (hq.const_sub 1).congr_deriv (neg_neg _)
  have hraw : HasDerivAt suzukiYoshidaDiagonalReferenceTail
      (1 / 2 *
        (-Real.exp (-t) / (1 + Real.exp (-t)) -
          Real.exp (-t) / (1 - Real.exp (-t)))) t := by
    have hlogs :=
      (hplus.log (by positivity)).sub (hminus.log (by linarith))
    have hscaled := hlogs.const_mul (1 / 2)
    have heq :
        (fun x : Real =>
          1 / 2 *
            (Real.log (1 + Real.exp (-x)) -
              Real.log (1 - Real.exp (-x)))) =ᶠ[nhds t]
          suzukiYoshidaDiagonalReferenceTail := by
      filter_upwards with x
      rfl
    exact (hscaled.congr_of_eventuallyEq heq).congr_deriv (by ring)
  have hvalue :
      1 / 2 *
          (-Real.exp (-t) / (1 + Real.exp (-t)) -
            Real.exp (-t) / (1 - Real.exp (-t))) =
        -suzukiYoshidaDiagonalReferenceSum t := by
    unfold suzukiYoshidaDiagonalReferenceSum
    have hden1 : 1 - Real.exp (-t) ≠ 0 := (sub_pos.mpr hq_lt).ne'
    have hden2 : 1 + Real.exp (-t) ≠ 0 := by positivity
    have hexp2 : Real.exp (-2 * t) = Real.exp (-t) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [hexp2]
    have hden3 : 1 - Real.exp (-t) ^ 2 ≠ 0 := by
      have hq0 : 0 < Real.exp (-t) := Real.exp_pos _
      apply sub_ne_zero.mpr
      nlinarith
    field_simp [hden1, hden2, hden3]
    ring
  rw [hvalue] at hraw
  exact hraw

theorem integral_suzukiYoshidaDiagonalReferenceSum
    {ε L : Real} (hε : 0 < ε) (hεL : ε ≤ L) :
    (∫ t in ε..L, suzukiYoshidaDiagonalReferenceSum t) =
      suzukiYoshidaDiagonalReferenceTail ε -
        suzukiYoshidaDiagonalReferenceTail L := by
  have hL : 0 < L := hε.trans_le hεL
  have hderiv : ∀ t ∈ Set.uIcc ε L,
      HasDerivAt (fun x => -suzukiYoshidaDiagonalReferenceTail x)
        (suzukiYoshidaDiagonalReferenceSum t) t := by
    intro t ht
    rw [Set.uIcc_of_le hεL] at ht
    have hbase := (hasDerivAt_suzukiYoshidaDiagonalReferenceTail
      (hε.trans_le ht.1)).neg
    have heq :
        (fun x : Real => -suzukiYoshidaDiagonalReferenceTail x) =ᶠ[nhds t]
          fun x => -suzukiYoshidaDiagonalReferenceTail x := by
      filter_upwards with x
      rfl
    exact (hbase.congr_of_eventuallyEq heq).congr_deriv (neg_neg _)
  have hint : IntervalIntegrable suzukiYoshidaDiagonalReferenceSum
      volume ε L := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hεL] at ht
    have htpos : 0 < t := hε.trans_le ht.1
    have hden : 1 - Real.exp (-2 * t) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact ne_of_gt ((Real.exp_lt_one_iff).2 (by linarith))
    unfold suzukiYoshidaDiagonalReferenceSum
    have hnum : ContinuousAt (fun x : Real => Real.exp (-x)) t := by
      fun_prop
    have hdencont : ContinuousAt
        (fun x : Real => 1 - Real.exp (-2 * x)) t := by
      fun_prop
    exact (hnum.div hdencont hden).continuousWithinAt
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [sub_eq_add_neg, add_comm] using hfund

theorem tendsto_one_sub_exp_neg_div_zero_right :
    Tendsto (fun t : Real => (1 - Real.exp (-t)) / t)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hslope := (hasDerivAt_exp_neg_mul' 1 0).tendsto_slope_zero_right
  have hneg := hslope.neg
  have hneg' : Tendsto
      (fun t : Real =>
        -(t⁻¹ • (Real.exp (-(1 : Real) * (0 + t)) -
          Real.exp (-(1 : Real) * 0))))
      (𝓝[>] (0 : Real)) (𝓝 1) := by
    simpa using hneg
  apply hneg'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht.ne'
  simp only [zero_add, one_mul, neg_zero, Real.exp_zero, smul_eq_mul]
  field_simp [ht0]
  norm_num

theorem tendsto_diagonalReference_logArgument_zero_right :
    Tendsto
      (fun t : Real =>
        t * (1 + Real.exp (-t)) / (1 - Real.exp (-t)))
      (𝓝[>] (0 : Real)) (𝓝 2) := by
  have hbase := tendsto_one_sub_exp_neg_div_zero_right
  have hinv := hbase.inv₀ one_ne_zero
  have hratio : Tendsto
      (fun t : Real => t / (1 - Real.exp (-t)))
      (𝓝[>] (0 : Real)) (𝓝 1) := by
    have hinv' : Tendsto
        (fun t : Real => ((1 - Real.exp (-t)) / t)⁻¹)
        (𝓝[>] (0 : Real)) (𝓝 1) := by
      simpa using hinv
    apply hinv'.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    have ht0 : t ≠ 0 := ht.ne'
    have hden : 1 - Real.exp (-t) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact ne_of_gt ((Real.exp_lt_one_iff).2 (neg_lt_zero.mpr htpos))
    field_simp [ht0, hden]
  have hexp : Tendsto (fun t : Real => Real.exp (-t))
      (𝓝[>] (0 : Real)) (𝓝 1) := by
    have hcont : ContinuousAt (fun t : Real => Real.exp (-t)) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hone : Tendsto (fun _ : Real => (1 : Real))
      (𝓝[>] (0 : Real)) (𝓝 1) := tendsto_const_nhds
  have honeAdd := hone.add hexp
  have hprod := hratio.mul honeAdd
  have hprod' : Tendsto
      (fun t : Real =>
        (t / (1 - Real.exp (-t))) * (1 + Real.exp (-t)))
      (𝓝[>] (0 : Real)) (𝓝 2) := by
    norm_num at hprod ⊢
    exact hprod
  apply hprod'.congr'
  filter_upwards with t
  simp only [div_eq_mul_inv]
  ring

theorem tendsto_neg_log_sub_two_mul_referenceTail_zero_right :
    Tendsto
      (fun t : Real =>
        -Real.log t - 2 * suzukiYoshidaDiagonalReferenceTail t)
      (𝓝[>] (0 : Real)) (𝓝 (-Real.log 2)) := by
  have harg := tendsto_diagonalReference_logArgument_zero_right
  have hlog := (Real.continuousAt_log (by norm_num : (2 : Real) ≠ 0)).tendsto.comp harg
  have hneg := hlog.neg
  apply hneg.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have ht0 : t ≠ 0 := ht.ne'
  have hq_lt : Real.exp (-t) < 1 :=
    (Real.exp_lt_one_iff).2 (neg_lt_zero.mpr htpos)
  have hplus : 1 + Real.exp (-t) ≠ 0 := by positivity
  have hminus : 1 - Real.exp (-t) ≠ 0 := (sub_pos.mpr hq_lt).ne'
  simp only [Function.comp_apply]
  rw [Real.log_div (mul_ne_zero ht0 hplus) hminus,
    Real.log_mul ht0 hplus]
  unfold suzukiYoshidaDiagonalReferenceTail
  ring

theorem diagonalReference_cutoff_normalization
    {ε L : Real} (hε : 0 < ε) (hεL : ε ≤ L) :
    -Real.log ε -
        2 * (∫ t in ε..L, suzukiYoshidaDiagonalReferenceSum t) =
      (-Real.log ε -
          2 * suzukiYoshidaDiagonalReferenceTail ε) +
        2 * suzukiYoshidaDiagonalReferenceTail L := by
  rw [integral_suzukiYoshidaDiagonalReferenceSum hε hεL]
  ring

/-! ## Cancellation-aware diagonal sum/integral exchange -/

theorem suzukiYoshidaDiagonalCancellation_integral_tsum
    {L : Real} (hL : 0 < L) (c f : Real → Real)
    (hc : Continuous c) (hf : Continuous f)
    (hrelation : ∀ t ≠ 0, (c t - 1) / t = f t) :
    IntervalIntegrable
        (fun t => ∑' n : Nat,
          (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
            Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)))
        volume 0 L ∧
      (∫ t in (0 : Real)..L,
        ∑' n : Nat,
          (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
            Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t))) =
        ∑' n : Nat,
          ∫ t in (0 : Real)..L,
            (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
              Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)) := by
  let F : Nat → Real → Real := fun n t =>
    Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
      Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hf.norm.continuousOn
  let M : Real := max 0 C
  let bound : Nat → Real → Real := fun n t =>
    (M + 1) * t * Real.exp (-suzukiDF6D4DiagonalDecay n * t)
  have hM0 : 0 ≤ M := le_max_left _ _
  have hfM : ∀ t ∈ Set.Icc (0 : Real) L, |f t| ≤ M := by
    intro t ht
    have hle : ‖f t‖ ≤ C := hC ⟨t, ht, rfl⟩
    exact hle.trans (le_max_right _ _)
  have hFMeasurable : ∀ n,
      AEStronglyMeasurable (F n)
        (volume.restrict (Set.uIoc (0 : Real) L)) := by
    intro n
    exact (((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).mul hc).sub
        (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hBound : ∀ n, ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Set.uIoc (0 : Real) L → ‖F n t‖ ≤ bound n t := by
    intro n
    filter_upwards with t
    intro ht
    rw [Set.uIoc_of_le hL.le] at ht
    have htpos : 0 < t := ht.1
    have ht0 : t ≠ 0 := htpos.ne'
    have hft := hfM t ⟨htpos.le, ht.2⟩
    have hcsub : |c t - 1| ≤ M * t := by
      have hrel := hrelation t ht0
      rw [div_eq_iff ht0] at hrel
      rw [hrel, abs_mul, abs_of_pos htpos]
      exact mul_le_mul_of_nonneg_right hft htpos.le
    have hDecayPos : 0 < suzukiDF6D4DiagonalDecay n := by
      unfold suzukiDF6D4DiagonalDecay
      positivity
    have hExpDecayPos : 0 < Real.exp (-suzukiDF6D4DiagonalDecay n * t) :=
      Real.exp_pos _
    have hhalf : 0 ≤ 1 - Real.exp (-t / 2) := by
      apply sub_nonneg.mpr
      exact (Real.exp_le_one_iff).2 (by linarith)
    have hhalf_le : 1 - Real.exp (-t / 2) ≤ t / 2 := by
      have h := Real.one_sub_le_exp_neg (t / 2)
      rw [show -(t / 2) = -t / 2 by ring] at h
      linarith
    have hrefexp :
        Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t) =
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
            Real.exp (-t / 2) := by
      rw [← Real.exp_add]
      rw [suzukiYoshidaDiagonalReferenceDecay_eq_restoration_add_half]
      congr 1
      ring
    have hdecomp : F n t =
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) * (c t - 1) +
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
            (1 - Real.exp (-t / 2)) := by
      dsimp only [F]
      rw [hrefexp]
      ring
    rw [hdecomp, Real.norm_eq_abs]
    calc
      |Real.exp (-suzukiDF6D4DiagonalDecay n * t) * (c t - 1) +
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
            (1 - Real.exp (-t / 2))| ≤
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) * |c t - 1| +
            Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
              |1 - Real.exp (-t / 2)| := by
        calc
          |Real.exp (-suzukiDF6D4DiagonalDecay n * t) * (c t - 1) +
              Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
                (1 - Real.exp (-t / 2))| ≤
              |Real.exp (-suzukiDF6D4DiagonalDecay n * t) * (c t - 1)| +
                |Real.exp (-suzukiDF6D4DiagonalDecay n * t) *
                  (1 - Real.exp (-t / 2))| := abs_add_le _ _
          _ = _ := by
            simp only [abs_mul, abs_of_pos hExpDecayPos]
      _ ≤ Real.exp (-suzukiDF6D4DiagonalDecay n * t) * (M * t) +
            Real.exp (-suzukiDF6D4DiagonalDecay n * t) * (t / 2) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hcsub hExpDecayPos.le
        · apply mul_le_mul_of_nonneg_left _ hExpDecayPos.le
          rw [abs_of_nonneg hhalf]
          exact hhalf_le
      _ ≤ bound n t := by
        dsimp only [bound]
        nlinarith
  have hBoundSummable : ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Set.uIoc (0 : Real) L → Summable (fun n => bound n t) := by
    filter_upwards with t
    intro ht
    rw [Set.uIoc_of_le hL.le] at ht
    have hsum : Summable (fun n : Nat =>
        Real.exp (-suzukiDF6D4DiagonalDecay n * t)) := by
      simpa only [suzukiDF6D4DiagonalDecay,
        suzukiDF6D4RestorationDecay] using
          summable_exp_neg_restorationDecay_mul ht.1
    exact (hsum.mul_left ((M + 1) * t)).congr fun n => by
      dsimp only [bound]
  have hBoundIntegrable : IntervalIntegrable
      (fun t => ∑' n : Nat, bound n t) volume 0 L := by
    let g : Real → Real := fun t =>
      (M + 1) * (t * suzukiR1SecondKernel t + 1 / 2)
    have hg : Continuous g := continuous_const.mul
      ((continuous_id.mul continuous_suzukiR1SecondKernel).add continuous_const)
    apply (hg.intervalIntegrable 0 L).congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le hL.le] at ht
    have htpos : 0 < t := ht.1
    have hfactor : (∑' n : Nat, bound n t) =
        ((M + 1) * t) *
          ∑' n : Nat,
            Real.exp (-suzukiDF6D4DiagonalDecay n * t) := by
      rw [← tsum_mul_left]
    change g t = ∑' n : Nat, bound n t
    rw [hfactor]
    dsimp only [g]
    rw [suzukiR1SecondKernel_eq_tsum_sub_of_pos htpos]
    simp only [suzukiDF6D4DiagonalDecay,
      suzukiDF6D4RestorationDecay]
    field_simp [htpos.ne']
    ring
  have hLimit : ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Set.uIoc (0 : Real) L →
        HasSum (fun n => F n t) (∑' n : Nat, F n t) := by
    filter_upwards with t
    intro ht
    rw [Set.uIoc_of_le hL.le] at ht
    have hDecay : Summable (fun n : Nat =>
        Real.exp (-suzukiDF6D4DiagonalDecay n * t)) := by
      simpa only [suzukiDF6D4DiagonalDecay,
        suzukiDF6D4RestorationDecay] using
          summable_exp_neg_restorationDecay_mul ht.1
    have hReference := summable_exp_neg_referenceDecay_mul ht.1
    exact ((hDecay.mul_right (c t)).sub hReference).hasSum
  have hinterchange :=
    intervalIntegral.hasSum_integral_of_dominated_convergence
      (a := (0 : Real)) (b := L) (μ := volume)
      bound hFMeasurable hBound hBoundSummable hBoundIntegrable hLimit
  have hFMeasurableRestrict : ∀ n,
      AEStronglyMeasurable (F n)
        (volume.restrict (Set.Ioc (0 : Real) L)) := by
    intro n
    simpa only [Set.uIoc_of_le hL.le] using hFMeasurable n
  have hSeriesMeasurable : AEStronglyMeasurable
      (fun t => ∑' n : Nat, F n t)
        (volume.restrict (Set.Ioc (0 : Real) L)) :=
    (AEMeasurable.tsum (fun n =>
      (hFMeasurableRestrict n).aemeasurable)).aestronglyMeasurable
  have hBoundRestrict : ∀ n, ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) L)),
      ‖F n t‖ ≤ bound n t := by
    intro n
    rw [ae_restrict_iff' measurableSet_Ioc]
    simpa only [Set.uIoc_of_le hL.le] using hBound n
  have hBoundSummableRestrict :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) L)),
        Summable (fun n => bound n t) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    simpa only [Set.uIoc_of_le hL.le] using hBoundSummable
  have hLimitRestrict :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) L)),
        HasSum (fun n => F n t) (∑' n : Nat, F n t) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    simpa only [Set.uIoc_of_le hL.le] using hLimit
  have hNormBound :
      ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : Real) L)),
        ‖∑' n : Nat, F n t‖ ≤ ∑' n : Nat, bound n t := by
    filter_upwards [ae_all_iff.2 hBoundRestrict,
      hBoundSummableRestrict, hLimitRestrict] with t htBound htSum htLimit
    have htNorm : Summable (fun n : Nat => ‖F n t‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htBound htSum
    exact (norm_tsum_le_tsum_norm htNorm).trans
      (htNorm.tsum_le_tsum htBound htSum)
  have hBoundIntegrableOn : IntegrableOn
      (fun t => ∑' n : Nat, bound n t) (Set.Ioc (0 : Real) L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      hBoundIntegrable
  have hSeriesIntegrableOn : IntegrableOn
      (fun t => ∑' n : Nat, F n t) (Set.Ioc (0 : Real) L) :=
    hBoundIntegrableOn.mono' hSeriesMeasurable hNormBound
  have hSeriesIntegrable : IntervalIntegrable
      (fun t => ∑' n : Nat, F n t) volume 0 L :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).2
      hSeriesIntegrableOn
  constructor
  · simpa only [F] using hSeriesIntegrable
  · simpa only [F] using hinterchange.tsum_eq.symm

theorem integral_exp_neg_referenceDecay
    (n : Nat) (L : Real) :
    (∫ t in (0 : Real)..L,
      Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)) =
      (1 - Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * L)) /
        suzukiYoshidaDiagonalReferenceDecay n := by
  let d := suzukiYoshidaDiagonalReferenceDecay n
  have hd : 0 < d := suzukiYoshidaDiagonalReferenceDecay_pos n
  let primitive : Real → Real := fun t => -Real.exp (-d * t) / d
  have hderiv : ∀ t ∈ Set.uIcc (0 : Real) L,
      HasDerivAt primitive (Real.exp (-d * t)) t := by
    intro t _
    have hbase := hasDerivAt_exp_neg_mul' d t
    have hscaled := hbase.const_mul (-1 / d)
    have heq :
        (fun x : Real => (-1 / d) * Real.exp (-d * x)) =ᶠ[nhds t]
          primitive := by
      filter_upwards with x
      dsimp only [primitive]
      ring
    have hvalue : (-1 / d) * (-d * Real.exp (-d * t)) =
        Real.exp (-d * t) := by
      field_simp [hd.ne']
    exact (hscaled.congr_of_eventuallyEq heq.symm).congr_deriv hvalue
  have hint : IntervalIntegrable (fun t : Real => Real.exp (-d * t))
      volume 0 L :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp only [primitive] at hfund
  simp only [mul_zero, neg_zero, Real.exp_zero] at hfund
  dsimp only [d] at hfund ⊢
  rw [hfund]
  ring

theorem tsum_integral_diagonalCancellation_of_core
    {L : Real} (hL : 0 < L) (c : Real → Real) (G : Real)
    (hc : Continuous c)
    (hcoreSummable : Summable (fun n : Nat =>
      (∫ t in (0 : Real)..L,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t) -
          1 / suzukiDF6D4DiagonalDecay n))
    (hcore :
      (∑' n : Nat,
        ((∫ t in (0 : Real)..L,
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t) -
            1 / suzukiDF6D4DiagonalDecay n)) = G) :
    (∑' n : Nat,
      ∫ t in (0 : Real)..L,
        (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
          Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t))) =
      G + (Real.pi / 4 + Real.log 2 / 2) +
        suzukiYoshidaDiagonalReferenceTail L := by
  let core : Nat → Real := fun n =>
    (∫ t in (0 : Real)..L,
      Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t) -
        1 / suzukiDF6D4DiagonalDecay n
  let restore : Nat → Real := suzukiDF6D4DiagonalRestorationSummand
  let tail : Nat → Real := fun n =>
    Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * L) /
      suzukiYoshidaDiagonalReferenceDecay n
  have hrestore : Summable restore :=
    summable_suzukiDF6D4DiagonalRestorationSummand
  have htailHas : HasSum tail (suzukiYoshidaDiagonalReferenceTail L) := by
    simpa only [tail, suzukiYoshidaDiagonalReferenceTail] using
      hasSum_exp_neg_referenceDecay_div hL
  have htail : Summable tail := htailHas.summable
  have hpoint : ∀ n : Nat,
      (∫ t in (0 : Real)..L,
        (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
          Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t))) =
        core n + restore n + tail n := by
    intro n
    have hfirst : IntervalIntegrable
        (fun t : Real =>
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t)
        volume 0 L :=
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).mul hc).intervalIntegrable _ _
    have hsecond : IntervalIntegrable
        (fun t : Real =>
          Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t))
        volume 0 L :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub
      hfirst hsecond,
      integral_exp_neg_referenceDecay]
    dsimp only [core, restore, tail]
    unfold suzukiDF6D4DiagonalRestorationSummand
      suzukiYoshidaDiagonalReferenceDecay
    ring
  rw [tsum_congr hpoint]
  rw [(hcoreSummable.add hrestore).tsum_add htail,
    hcoreSummable.tsum_add hrestore]
  have hcoreTsum : (∑' n : Nat, core n) = G := by
    simpa only [core] using hcore
  rw [hcoreTsum, tsum_suzukiDF6D4DiagonalRestorationSummand,
    htailHas.tsum_eq]

theorem tsum_diagonalCancellation_eq_regular
    (c f : Real → Real) (hrelation : ∀ t ≠ 0, (c t - 1) / t = f t)
    {t : Real} (ht : 0 < t) :
    (∑' n : Nat,
      (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
        Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t))) =
      suzukiR1SecondKernel t * c t + f t / 2 -
        (suzukiYoshidaDiagonalReferenceSum t - 1 / (2 * t)) := by
  have hDecay : Summable (fun n : Nat =>
      Real.exp (-suzukiDF6D4DiagonalDecay n * t)) := by
    simpa only [suzukiDF6D4DiagonalDecay,
      suzukiDF6D4RestorationDecay] using
        summable_exp_neg_restorationDecay_mul ht
  have hReference := summable_exp_neg_referenceDecay_mul ht
  rw [(hDecay.mul_right (c t)).tsum_sub hReference]
  rw [tsum_mul_right]
  rw [suzukiR1SecondKernel_eq_tsum_sub_of_pos ht]
  rw [tsum_exp_neg_referenceDecay_mul ht]
  unfold suzukiYoshidaDiagonalReferenceSum
  have hrel := hrelation t ht.ne'
  rw [div_eq_iff ht.ne'] at hrel
  have hDecayTsumEq :
      (∑' n : Nat, Real.exp (-suzukiDF6D4DiagonalDecay n * t)) =
        ∑' n : Nat, Real.exp (-suzukiDF6D4RestorationDecay n * t) := by
    apply tsum_congr
    intro n
    unfold suzukiDF6D4DiagonalDecay suzukiDF6D4RestorationDecay
    rfl
  rw [hDecayTsumEq]
  field_simp [ht.ne']
  rw [show t * f t = f t * t by ring]
  rw [← hrel]
  ring

/-- The universal diagonal Archimedean identity after the half-integer Gamma
series is paired with the odd-reference cutoff. -/
theorem suzukiYoshidaDiagonalArchimedeanScalarIdentity_of_core
    {L : Real} (hL : 0 < L) (c f : Real → Real) (G : Real)
    (hc : Continuous c) (hf : Continuous f)
    (hrelation : ∀ t ≠ 0, (c t - 1) / t = f t)
    (hcoreSummable : Summable (fun n : Nat =>
      (∫ t in (0 : Real)..L,
        Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t) -
          1 / suzukiDF6D4DiagonalDecay n))
    (hcore :
      (∑' n : Nat,
        ((∫ t in (0 : Real)..L,
          Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t) -
            1 / suzukiDF6D4DiagonalDecay n)) = G) :
    -Real.log L - (∫ t in (0 : Real)..L, f t) -
        2 * (∫ t in (0 : Real)..L, suzukiR1SecondKernel t * c t) =
      -Real.log 2 -
        2 * (G + (Real.pi / 4 + Real.log 2 / 2)) := by
  let series : Real → Real := fun t =>
    ∑' n : Nat,
      (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
        Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t))
  let combined : Real → Real := fun t =>
    suzukiR1SecondKernel t * c t + f t / 2
  have hcombinedContinuous : Continuous combined := by
    dsimp only [combined]
    exact (continuous_suzukiR1SecondKernel.mul hc).add (hf.div_const 2)
  have hcancel := suzukiYoshidaDiagonalCancellation_integral_tsum
    hL c f hc hf hrelation
  have hseriesInt : IntervalIntegrable series volume 0 L := by
    simpa only [series] using hcancel.1
  have hseriesValue :
      (∫ t in (0 : Real)..L, series t) =
        G + (Real.pi / 4 + Real.log 2 / 2) +
          suzukiYoshidaDiagonalReferenceTail L := by
    rw [show (∫ t in (0 : Real)..L, series t) =
        ∑' n : Nat,
          ∫ t in (0 : Real)..L,
            (Real.exp (-suzukiDF6D4DiagonalDecay n * t) * c t -
              Real.exp (-suzukiYoshidaDiagonalReferenceDecay n * t)) by
      simpa only [series] using hcancel.2]
    exact tsum_integral_diagonalCancellation_of_core
      hL c G hc hcoreSummable hcore
  have hcombinedIntegrableOn : IntegrableOn combined (Set.Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
      (hcombinedContinuous.intervalIntegrable 0 L)
  have hseriesIntegrableOn : IntegrableOn series (Set.Ioc 0 L) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1 hseriesInt
  have hcombinedLimit : Tendsto
      (fun ε : Real => ∫ t in ε..L, combined t)
      (𝓝[>] (0 : Real)) (𝓝 (∫ t in (0 : Real)..L, combined t)) :=
    tendsto_intervalIntegral_zero_right_of_integrableOn_Ioc
      hL hcombinedIntegrableOn
  have hseriesLimit : Tendsto
      (fun ε : Real => ∫ t in ε..L, series t)
      (𝓝[>] (0 : Real)) (𝓝 (∫ t in (0 : Real)..L, series t)) :=
    tendsto_intervalIntegral_zero_right_of_integrableOn_Ioc
      hL hseriesIntegrableOn
  have hrefCutoffLimit : Tendsto
      (fun ε : Real =>
        -Real.log ε -
          2 * (∫ t in ε..L, suzukiYoshidaDiagonalReferenceSum t))
      (𝓝[>] (0 : Real))
      (𝓝 (-Real.log 2 + 2 * suzukiYoshidaDiagonalReferenceTail L)) := by
    have hbase :=
      tendsto_neg_log_sub_two_mul_referenceTail_zero_right.add
        (tendsto_const_nhds : Tendsto
          (fun _ : Real => 2 * suzukiYoshidaDiagonalReferenceTail L)
          (𝓝[>] (0 : Real))
          (𝓝 (2 * suzukiYoshidaDiagonalReferenceTail L)))
    apply hbase.congr'
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iic_mem_nhds hL)] with ε hε hεL
    exact (diagonalReference_cutoff_normalization hε hεL).symm
  have hcutoffEquality : ∀ᶠ ε in (𝓝[>] (0 : Real)),
      -Real.log L - 2 * (∫ t in ε..L, combined t) =
        -2 * (∫ t in ε..L, series t) +
          (-Real.log ε -
            2 * (∫ t in ε..L, suzukiYoshidaDiagonalReferenceSum t)) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_inf_of_left (Iic_mem_nhds hL)] with ε hε hεL
    have hseriesCut : IntervalIntegrable series volume ε L := by
      apply hseriesInt.mono_set
      rw [Set.uIcc_of_le hεL, Set.uIcc_of_le hL.le]
      intro t ht
      exact ⟨hε.le.trans ht.1, ht.2⟩
    have hrefCut : IntervalIntegrable suzukiYoshidaDiagonalReferenceSum
        volume ε L := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hεL] at ht
      have htpos : 0 < t := hε.trans_le ht.1
      have hden : 1 - Real.exp (-2 * t) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact ne_of_gt ((Real.exp_lt_one_iff).2 (by linarith))
      unfold suzukiYoshidaDiagonalReferenceSum
      have hnum : ContinuousAt (fun x : Real => Real.exp (-x)) t := by
        fun_prop
      have hdencont : ContinuousAt
          (fun x : Real => 1 - Real.exp (-2 * x)) t := by
        fun_prop
      exact (hnum.div hdencont hden).continuousWithinAt
    have hinvCut : IntervalIntegrable (fun t : Real => 1 / (2 * t))
        volume ε L := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hεL] at ht
      have ht0 : t ≠ 0 := (hε.trans_le ht.1).ne'
      exact (continuousAt_const.div
        (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero (by norm_num) ht0)).continuousWithinAt
    have hcombinedDecomp :
        (∫ t in ε..L, combined t) =
          (∫ t in ε..L, series t) +
            (∫ t in ε..L, suzukiYoshidaDiagonalReferenceSum t) -
              (∫ t in ε..L, 1 / (2 * t)) := by
      calc
        (∫ t in ε..L, combined t) =
            ∫ t in ε..L,
              (series t + suzukiYoshidaDiagonalReferenceSum t -
                1 / (2 * t)) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [Set.uIcc_of_le hεL] at ht
          have htpos : 0 < t := hε.trans_le ht.1
          have hpoint := tsum_diagonalCancellation_eq_regular
            c f hrelation htpos
          dsimp only [series, combined]
          rw [hpoint]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_sub
            (hseriesCut.add hrefCut) hinvCut,
            intervalIntegral.integral_add hseriesCut hrefCut]
    have hinvValue :
        (∫ t in ε..L, 1 / (2 * t)) =
          (Real.log L - Real.log ε) / 2 := by
      calc
        (∫ t in ε..L, 1 / (2 * t)) =
            (1 / 2 : Real) * (∫ t in ε..L, 1 / t) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = (1 / 2 : Real) * Real.log (L / ε) := by
          rw [show (∫ t in ε..L, 1 / t) = Real.log (L / ε) by
            simpa only [one_div] using integral_inv_of_pos hε (hε.trans_le hεL)]
        _ = (Real.log L - Real.log ε) / 2 := by
          rw [Real.log_div (hε.trans_le hεL).ne' hε.ne']
          ring
    rw [hcombinedDecomp, hinvValue]
    ring
  have hleftLimit : Tendsto
      (fun ε : Real => -Real.log L - 2 * (∫ t in ε..L, combined t))
      (𝓝[>] (0 : Real))
      (𝓝 (-Real.log L - 2 * (∫ t in (0 : Real)..L, combined t))) :=
    tendsto_const_nhds.sub (hcombinedLimit.const_mul 2)
  have hrightLimit : Tendsto
      (fun ε : Real =>
        -2 * (∫ t in ε..L, series t) +
          (-Real.log ε -
            2 * (∫ t in ε..L, suzukiYoshidaDiagonalReferenceSum t)))
      (𝓝[>] (0 : Real))
      (𝓝 (-Real.log 2 -
        2 * (G + (Real.pi / 4 + Real.log 2 / 2)))) := by
    have hbase := (hseriesLimit.const_mul (-2)).add hrefCutoffLimit
    rw [hseriesValue] at hbase
    convert hbase using 1 <;> ring
  have hscalar :
      -Real.log L - 2 * (∫ t in (0 : Real)..L, combined t) =
        -Real.log 2 -
          2 * (G + (Real.pi / 4 + Real.log 2 / 2)) :=
    tendsto_nhds_unique hleftLimit
      (hrightLimit.congr' (hcutoffEquality.mono fun _ h => h.symm))
  have hcombine :
      (∫ t in (0 : Real)..L, combined t) =
        (∫ t in (0 : Real)..L, suzukiR1SecondKernel t * c t) +
          (∫ t in (0 : Real)..L, f t) / 2 := by
    have hfirst : IntervalIntegrable
        (fun x : Real => suzukiR1SecondKernel x * c x) volume 0 L :=
      (continuous_suzukiR1SecondKernel.mul hc).intervalIntegrable
        (0 : Real) L
    have hsecond : IntervalIntegrable (fun x : Real => f x / 2)
        volume 0 L := (hf.div_const 2).intervalIntegrable (0 : Real) L
    dsimp only [combined]
    rw [intervalIntegral.integral_add
      (f := fun x => suzukiR1SecondKernel x * c x)
      (g := fun x => f x / 2) hfirst hsecond]
    rw [intervalIntegral.integral_div]
  rw [hcombine] at hscalar
  linarith

theorem suzukiYoshidaEvenPositiveDiagonalArchimedeanScalar
    (mode : Nat) (hmode : 0 < mode) :
    -Real.log (2 * suzukiProjectAStar) -
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiYoshidaEvenPositiveDiagonalRegularPart mode t) -
        2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiR1SecondKernel t *
            suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) =
      -Real.log 2 -
        2 * (suzukiDF6D4EvenDiagonalGammaCore mode +
          (Real.pi / 4 + Real.log 2 / 2)) := by
  apply suzukiYoshidaDiagonalArchimedeanScalarIdentity_of_core
    (mul_pos (by norm_num) suzukiProjectAStar_pos)
  · exact continuous_suzukiYoshidaEvenPositiveDiagonalCorrelation mode
  · exact continuous_suzukiYoshidaEvenPositiveDiagonalRegularPart mode
  · intro t ht
    exact suzukiYoshidaEvenPositiveDiagonalCorrelation_sub_one_div
      mode hmode ht
  · exact (summable_suzukiYoshidaEvenDiagonalGammaCoreSummand mode).congr
      (fun n =>
        (integral_exp_neg_mul_evenPositiveDiagonalCorrelation_sub_reciprocal
          mode n hmode).symm)
  · exact tsum_integral_evenPositiveDiagonalCorrelation_sub_reciprocal
      mode hmode

theorem suzukiYoshidaEvenZeroDiagonalArchimedeanScalar :
    -Real.log (2 * suzukiProjectAStar) -
        (∫ _t in (0 : Real)..2 * suzukiProjectAStar,
          -(2 * suzukiProjectAStar)⁻¹) -
        2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiR1SecondKernel t *
            suzukiYoshidaEvenZeroDiagonalCorrelation t) =
      -Real.log 2 -
        2 * (suzukiDF6D4EvenDiagonalGammaCore 0 +
          (Real.pi / 4 + Real.log 2 / 2)) := by
  apply suzukiYoshidaDiagonalArchimedeanScalarIdentity_of_core
    (mul_pos (by norm_num) suzukiProjectAStar_pos)
  · exact continuous_suzukiYoshidaEvenZeroDiagonalCorrelation
  · exact continuous_const
  · intro t ht
    exact suzukiYoshidaEvenZeroDiagonalCorrelation_sub_one_div ht
  · exact (summable_suzukiYoshidaEvenDiagonalGammaCoreSummand 0).congr
      (fun n =>
        (integral_exp_neg_mul_evenZeroDiagonalCorrelation_sub_reciprocal
          n).symm)
  · exact tsum_integral_evenZeroDiagonalCorrelation_sub_reciprocal

theorem suzukiYoshidaOddDiagonalArchimedeanScalar
    (mode : Nat) (hmode : 0 < mode) :
    -Real.log (2 * suzukiProjectAStar) -
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiYoshidaOddDiagonalRegularPart mode t) -
        2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiR1SecondKernel t *
            suzukiYoshidaOddDiagonalCorrelation mode t) =
      -Real.log 2 -
        2 * (suzukiDF6D4OddDiagonalGammaCore mode +
          (Real.pi / 4 + Real.log 2 / 2)) := by
  apply suzukiYoshidaDiagonalArchimedeanScalarIdentity_of_core
    (mul_pos (by norm_num) suzukiProjectAStar_pos)
  · exact continuous_suzukiYoshidaOddDiagonalCorrelation mode
  · exact continuous_suzukiYoshidaOddDiagonalRegularPart mode
  · intro t ht
    exact suzukiYoshidaOddDiagonalCorrelation_sub_one_div mode hmode ht
  · exact
      (summable_suzukiYoshidaOddDiagonalGammaCoreSummand mode hmode).congr
        (fun n =>
          (integral_exp_neg_mul_oddDiagonalCorrelation_sub_reciprocal
            mode n hmode).symm)
  · exact tsum_integral_oddDiagonalCorrelation_sub_reciprocal mode hmode

theorem integral_two_mul_suzukiRSecondKernel_mul
    {L : Real} (c : Real → Real) (hc : Continuous c) :
    (∫ t in (0 : Real)..L, 2 * suzukiRSecondKernel t * c t) =
      -(2 * (∫ t in (0 : Real)..L,
        (Real.exp (t / 2) + Real.exp (-t / 2)) * c t)) +
        2 * (∫ t in (0 : Real)..L, suzukiR1SecondKernel t * c t) := by
  have hpole : IntervalIntegrable
      (fun t : Real =>
        (Real.exp (t / 2) + Real.exp (-t / 2)) * c t)
      volume 0 L := by
    exact (((Real.continuous_exp.comp (continuous_id.div_const 2)).add
      (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).mul hc
        ).intervalIntegrable _ _
  have hgamma : IntervalIntegrable
      (fun t : Real => suzukiR1SecondKernel t * c t)
      volume 0 L :=
    (continuous_suzukiR1SecondKernel.mul hc).intervalIntegrable _ _
  calc
    (∫ t in (0 : Real)..L, 2 * suzukiRSecondKernel t * c t) =
        ∫ t in (0 : Real)..L,
          (-2) * ((Real.exp (t / 2) + Real.exp (-t / 2)) * c t) +
            2 * (suzukiR1SecondKernel t * c t) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [suzukiRSecondKernel_eq_pole_add_gamma]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hpole.const_mul (-2))
        (hgamma.const_mul 2), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring

/-! ## Diagonal Gamma-operator reduction to the scalar correlations -/

theorem suzukiYoshidaGammaRemainderForm_evenPositive_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      (((∫ t in (0 : Real)..2 * suzukiProjectAStar,
        2 * suzukiRSecondKernel t *
          suzukiYoshidaEvenPositiveDiagonalCorrelation mode t) : Real) :
        Complex) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_symmetricInterval,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le
    (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)] at ht
  rw [suzukiL2SymmetricTranslationEnergy_yoshidaEvenPositive_diagonal
    suzukiProjectAStar_pos ht.1 ht.2 mode hmode]
  unfold suzukiYoshidaEvenPositiveDiagonalCorrelation
  push_cast
  ring

theorem suzukiYoshidaGammaRemainderForm_evenZero_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0) =
      (((∫ t in (0 : Real)..2 * suzukiProjectAStar,
        2 * suzukiRSecondKernel t *
          suzukiYoshidaEvenZeroDiagonalCorrelation t) : Real) : Complex) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_symmetricInterval,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le
    (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)] at ht
  rw [suzukiL2SymmetricTranslationEnergy_yoshidaEvenZero_diagonal
    suzukiProjectAStar_pos ht.1 ht.2]
  unfold suzukiYoshidaEvenZeroDiagonalCorrelation
  push_cast
  ring

theorem suzukiYoshidaGammaRemainderForm_odd_diagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      (((∫ t in (0 : Real)..2 * suzukiProjectAStar,
        2 * suzukiRSecondKernel t *
          suzukiYoshidaOddDiagonalCorrelation mode t) : Real) : Complex) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_symmetricInterval,
    suzukiYoshidaOddLinearCompletionOfSource_toL2]
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Set.uIcc_of_le
    (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)] at ht
  rw [suzukiL2SymmetricTranslationEnergy_yoshidaOdd_diagonal
    suzukiProjectAStar_pos ht.1 ht.2 mode hmode]
  unfold suzukiYoshidaOddDiagonalCorrelation
  push_cast
  ring

/-! ## B3Q-G component evaluations -/

theorem suzukiDF6D4DiagonalConstant_add_sourceNormalization :
    suzukiDF6D4DiagonalConstantTerm +
        suzukiSourceLogNormalizationConstant =
      -Real.log 2 := by
  unfold suzukiDF6D4DiagonalConstantTerm
    suzukiSourceLogNormalizationConstant
  rw [Real.log_mul (by norm_num : (4 : Real) ≠ 0) Real.pi_ne_zero,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) Real.pi_ne_zero,
    show (4 : Real) = 2 ^ 2 by norm_num, Real.log_pow]
  ring

theorem suzukiEquation25EvenDiagonalArchimedeanEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25EvenDiagonalArchimedeanEvaluation hsource := by
  intro mode
  rcases mode.eq_zero_or_pos with rfl | hmode
  · rw [suzukiYoshidaComparisonForm_evenZero_diagonal hsource,
      suzukiYoshidaGammaRemainderForm_evenZero_diagonal hsource]
    have hkernel := integral_two_mul_suzukiRSecondKernel_mul
      suzukiYoshidaEvenZeroDiagonalCorrelation
      continuous_suzukiYoshidaEvenZeroDiagonalCorrelation
      (L := 2 * suzukiProjectAStar)
    rw [two_mul_integral_pole_evenZeroDiagonalCorrelation] at hkernel
    have hscalar := suzukiYoshidaEvenZeroDiagonalArchimedeanScalar
    have hconstant := suzukiDF6D4DiagonalConstant_add_sourceNormalization
    norm_cast
    unfold suzukiDF6D4EvenDiagonalGammaTerm
    linarith
  · rw [suzukiYoshidaComparisonForm_evenPositive_diagonal
        hsource mode hmode,
      suzukiYoshidaGammaRemainderForm_evenPositive_diagonal
        hsource mode hmode]
    have hkernel := integral_two_mul_suzukiRSecondKernel_mul
      (suzukiYoshidaEvenPositiveDiagonalCorrelation mode)
      (continuous_suzukiYoshidaEvenPositiveDiagonalCorrelation mode)
      (L := 2 * suzukiProjectAStar)
    rw [two_mul_integral_pole_evenPositiveDiagonalCorrelation
      mode hmode] at hkernel
    have hscalar :=
      suzukiYoshidaEvenPositiveDiagonalArchimedeanScalar mode hmode
    have hconstant := suzukiDF6D4DiagonalConstant_add_sourceNormalization
    norm_cast
    unfold suzukiDF6D4EvenDiagonalGammaTerm
    linarith

theorem suzukiEquation25OddDiagonalArchimedeanEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25OddDiagonalArchimedeanEvaluation hsource := by
  intro mode hmode
  rw [suzukiYoshidaComparisonForm_odd_diagonal hsource mode hmode,
    suzukiYoshidaGammaRemainderForm_odd_diagonal hsource mode hmode]
  have hkernel := integral_two_mul_suzukiRSecondKernel_mul
    (suzukiYoshidaOddDiagonalCorrelation mode)
    (continuous_suzukiYoshidaOddDiagonalCorrelation mode)
    (L := 2 * suzukiProjectAStar)
  rw [two_mul_integral_pole_oddDiagonalCorrelation mode hmode] at hkernel
  have hscalar := suzukiYoshidaOddDiagonalArchimedeanScalar mode hmode
  have hconstant := suzukiDF6D4DiagonalConstant_add_sourceNormalization
  norm_cast
  unfold suzukiDF6D4OddDiagonalGammaTerm
  linarith

/-! ## B3Q-E/F endpoint assembly -/

theorem suzukiYoshidaEquation25EndpointKernelEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiYoshidaEquation25EndpointKernelEvaluation hsource := by
  have hcomparison :=
    suzukiEquation25OffDiagonalComparisonEvaluations_of_source hsource
  have hevenCorrection :=
    suzukiEquation25EvenOffDiagonalCorrectionEvaluation_of_gamma hsource
      (suzukiEquation25EvenOffDiagonalGammaEvaluation hsource)
  have hoddCorrection :=
    suzukiEquation25OddOffDiagonalCorrectionEvaluation_of_gamma hsource
      (suzukiEquation25OddOffDiagonalGammaEvaluation hsource)
  have hparity := suzukiEquation25ParityEntries_of_componentEvaluations
    hsource hequation25 hcomparison.1 hevenCorrection hcomparison.2
      hoddCorrection
      (suzukiEquation25EvenDiagonalPrimeEvaluation hsource)
      (suzukiEquation25EvenDiagonalArchimedeanEvaluation hsource)
      (suzukiEquation25OddDiagonalPrimeEvaluation hsource)
      (suzukiEquation25OddDiagonalArchimedeanEvaluation hsource)
  exact suzukiYoshidaEquation25EndpointKernelEvaluation_of_parityEntries
    hsource hequation25 hparity.1 hparity.2

theorem suzukiYoshidaCorrectedCompleteForm_exponential_eq_explicitKernel_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaCorrectedExplicitKernel m n :=
  suzukiYoshidaCorrectedCompleteForm_exponential_eq_explicitKernel
    hsource hequation25
      (suzukiYoshidaEquation25EndpointKernelEvaluation hsource hequation25)
        m n

end

end RiemannHypothesisProject.Experiments.M100
