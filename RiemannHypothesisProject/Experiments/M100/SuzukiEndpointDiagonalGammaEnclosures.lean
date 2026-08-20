import Mathlib.Analysis.SpecificLimits.Normed
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointPrimeSineEnclosures

/-!
# Analytic diagonal Gamma-series enclosures for M100-DF6D4

On a Yoshida basis diagonal, every endpoint trigonometric value is an integer
multiple of `π`.  The weighted correlation integral therefore has a rational
closed form in the decay, the mode frequency, `a*`, and `exp (-a*)`.

This module separates that closed form into:

* a nonnegative fourth-order renormalized term;
* an exponentially decaying endpoint correction; and
* the two complete half-integer reciprocal sums carrying the origin slope and
  second derivative.

This is exactly the algebra used by the frozen 16,384-term Arb calculation,
but it avoids dependency loss from separately rounding Catalan's constant and
`ζ(3)` before their compensating series terms cancel.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Frozen half-integer Gamma decay `2n + 1/2`. -/
def suzukiDF6D4DiagonalDecay (n : Nat) : Real :=
  2 * (n : Real) + 1 / 2

/-- Yoshida frequency of physical mode `m`. -/
def suzukiDF6D4DiagonalFrequency (mode : Nat) : Real :=
  (mode : Real) * Real.pi

private theorem suzukiDF6D4DiagonalDecay_pos (n : Nat) :
    0 < suzukiDF6D4DiagonalDecay n := by
  unfold suzukiDF6D4DiagonalDecay
  positivity

private theorem suzukiDF6D4DiagonalFrequency_nonneg (mode : Nat) :
    0 ≤ suzukiDF6D4DiagonalFrequency mode := by
  unfold suzukiDF6D4DiagonalFrequency
  positivity

private theorem suzukiDF6D4DiagonalFrequency_pos
    {mode : Nat} (hmode : 0 < mode) :
    0 < suzukiDF6D4DiagonalFrequency mode := by
  unfold suzukiDF6D4DiagonalFrequency
  positivity

/-- Fourth-order renormalized part of one even diagonal Gamma summand.  The
formula is valid also at mode zero, where its numerator vanishes. -/
def suzukiDF6D4EvenDiagonalBaseTerm (mode n : Nat) : Real :=
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let y := f ^ 2
  let d := x ^ 2 + y
  a * y * (2 * x ^ 3 + x ^ 2 * y + x * y + y ^ 2) /
    (x ^ 3 * d ^ 2)

/-- Fourth-order renormalized part of one odd diagonal Gamma summand. -/
def suzukiDF6D4OddDiagonalBaseTerm (mode n : Nat) : Real :=
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let y := f ^ 2
  let d := x ^ 2 + y
  a * y * (x ^ 3 + x ^ 2 * y + y ^ 2) /
    (x ^ 3 * d ^ 2)

/-- Exponential endpoint correction in one even diagonal summand.  The
constant Yoshida mode carries its exact extra factor `1/2`. -/
def suzukiDF6D4EvenDiagonalExpTerm (mode n : Nat) : Real :=
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let d := x ^ 2 + f ^ 2
  let e := Real.exp (-a) ^ (4 * n + 1)
  if mode = 0 then e / (2 * a * r ^ 2)
  else a * x ^ 2 * e / d ^ 2

/-- Magnitude of the negative exponential endpoint correction in one odd
diagonal summand. -/
def suzukiDF6D4OddDiagonalExpMagnitudeTerm (mode n : Nat) : Real :=
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let d := x ^ 2 + f ^ 2
  a * f ^ 2 * Real.exp (-a) ^ (4 * n + 1) / d ^ 2

def suzukiDF6D4OddDiagonalExpTerm (mode n : Nat) : Real :=
  -suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n

/-- Right-origin slope of the physical even autocorrelation. -/
def suzukiDF6D4EvenDiagonalOriginSlope (mode : Nat) : Real :=
  if mode = 0 then -(1 / (2 * suzukiProjectAStar))
  else -(1 / suzukiProjectAStar)

/-- Right-origin second derivative of either parity autocorrelation. -/
def suzukiDF6D4DiagonalOriginSecond (mode : Nat) : Real :=
  -(suzukiDF6D4DiagonalFrequency mode ^ 2 / suzukiProjectAStar ^ 2)

/-- The derivative constant used by the fourth-order tail estimate in the
frozen script. -/
def suzukiDF6D4DiagonalThirdBound (mode : Nat) : Real :=
  let f := suzukiDF6D4DiagonalFrequency mode
  (2 * f ^ 3 + 3 * f ^ 2) / suzukiProjectAStar ^ 3

theorem suzukiDF6D4EvenDiagonalBaseTerm_nonneg (mode n : Nat) :
    0 ≤ suzukiDF6D4EvenDiagonalBaseTerm mode n := by
  unfold suzukiDF6D4EvenDiagonalBaseTerm
  dsimp only
  have hx : 0 < suzukiProjectAStar * suzukiDF6D4DiagonalDecay n :=
    mul_pos suzukiProjectAStar_pos (suzukiDF6D4DiagonalDecay_pos n)
  have hd : 0 <
      (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
        suzukiDF6D4DiagonalFrequency mode ^ 2 := by
    nlinarith [sq_pos_of_pos hx,
      sq_nonneg (suzukiDF6D4DiagonalFrequency mode)]
  apply div_nonneg
  · positivity [suzukiProjectAStar_pos,
      suzukiDF6D4DiagonalFrequency_nonneg]
  · positivity

theorem suzukiDF6D4OddDiagonalBaseTerm_nonneg (mode n : Nat) :
    0 ≤ suzukiDF6D4OddDiagonalBaseTerm mode n := by
  unfold suzukiDF6D4OddDiagonalBaseTerm
  dsimp only
  have hx : 0 < suzukiProjectAStar * suzukiDF6D4DiagonalDecay n :=
    mul_pos suzukiProjectAStar_pos (suzukiDF6D4DiagonalDecay_pos n)
  have hd : 0 <
      (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
        suzukiDF6D4DiagonalFrequency mode ^ 2 := by
    nlinarith [sq_pos_of_pos hx,
      sq_nonneg (suzukiDF6D4DiagonalFrequency mode)]
  apply div_nonneg
  · positivity [suzukiProjectAStar_pos,
      suzukiDF6D4DiagonalFrequency_nonneg]
  · positivity

private theorem suzukiDF6D4_poly_aux_one
    {x f : Real} (hx : 0 ≤ x) (hf : 0 ≤ f) :
    x ^ 3 * f ^ 2 ≤ f * (x ^ 2 + f ^ 2) ^ 2 := by
  have hfactor :
      f * (x ^ 2 + f ^ 2) ^ 2 - x ^ 3 * f ^ 2 =
        f * (x ^ 2 * (x - f / 2) ^ 2 +
          (7 / 4 : Real) * x ^ 2 * f ^ 2 + f ^ 4) := by
    ring
  rw [← sub_nonneg, hfactor]
  positivity

private theorem suzukiDF6D4_poly_aux_two
    {x f : Real} (hx : 0 ≤ x) (hf : 0 ≤ f) :
    x * f ^ 4 ≤ f * (x ^ 2 + f ^ 2) ^ 2 := by
  have hfactor :
      f * (x ^ 2 + f ^ 2) ^ 2 - x * f ^ 4 =
        f * (x ^ 4 + f ^ 2 * (x - f / 2) ^ 2 +
          x ^ 2 * f ^ 2 + (3 / 4 : Real) * f ^ 4) := by
    ring
  rw [← sub_nonneg, hfactor]
  positivity

private theorem suzukiDF6D4_odd_poly_bound
    {x f : Real} (hx : 0 ≤ x) (hf : 0 ≤ f) :
    x * (x ^ 3 + x ^ 2 * f ^ 2 + f ^ 4) ≤
      (2 * f + 3) * (x ^ 2 + f ^ 2) ^ 2 := by
  have hD : 0 ≤ (x ^ 2 + f ^ 2) ^ 2 := sq_nonneg _
  have h0 : x ^ 4 ≤ (x ^ 2 + f ^ 2) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg f,
      mul_nonneg (sq_nonneg x) (sq_nonneg f)]
  have h1 := suzukiDF6D4_poly_aux_one hx hf
  have h2 := suzukiDF6D4_poly_aux_two hx hf
  ring_nf at h0 h1 h2 ⊢
  nlinarith

private theorem suzukiDF6D4_even_poly_bound
    {x f : Real} (hx : 0 ≤ x) (hf : 0 ≤ f) :
    x * (2 * x ^ 3 + x ^ 2 * f ^ 2 + x * f ^ 2 + f ^ 4) ≤
      (2 * f + 3) * (x ^ 2 + f ^ 2) ^ 2 := by
  have hD : 0 ≤ (x ^ 2 + f ^ 2) ^ 2 := sq_nonneg _
  have h0 : x ^ 4 ≤ (x ^ 2 + f ^ 2) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg f,
      mul_nonneg (sq_nonneg x) (sq_nonneg f)]
  have hmid : x ^ 2 * f ^ 2 ≤ (x ^ 2 + f ^ 2) ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg f,
      mul_nonneg (sq_nonneg x) (sq_nonneg f)]
  have h1 := suzukiDF6D4_poly_aux_one hx hf
  have h2 := suzukiDF6D4_poly_aux_two hx hf
  ring_nf at h0 hmid h1 h2 ⊢
  nlinarith

private theorem suzukiDF6D4EvenDiagonalBaseTerm_le_bound_of_pos
    {mode n : Nat} (hmode : 0 < mode) :
    suzukiDF6D4EvenDiagonalBaseTerm mode n ≤
      suzukiDF6D4DiagonalThirdBound mode /
        suzukiDF6D4DiagonalDecay n ^ 4 := by
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let d := x ^ 2 + f ^ 2
  have ha : 0 < a := suzukiProjectAStar_pos
  have hr : 0 < r := suzukiDF6D4DiagonalDecay_pos n
  have hf : 0 < f := suzukiDF6D4DiagonalFrequency_pos hmode
  have hx : 0 < x := mul_pos ha hr
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [sq_pos_of_pos hx, sq_nonneg f]
  have hpoly := suzukiDF6D4_even_poly_bound hx.le hf.le
  have hcross := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg ha.le (sq_nonneg f)) (pow_nonneg hx.le 3))
  have hdiv :
      a * f ^ 2 *
            (2 * x ^ 3 + x ^ 2 * f ^ 2 + x * f ^ 2 + f ^ 4) /
          (x ^ 3 * d ^ 2) ≤
        a * f ^ 2 * (2 * f + 3) / x ^ 4 := by
    rw [div_le_div_iff₀ (mul_pos (pow_pos hx 3) (pow_pos hd 2))
      (pow_pos hx 4)]
    dsimp only [d] at hcross ⊢
    nlinarith
  unfold suzukiDF6D4EvenDiagonalBaseTerm suzukiDF6D4DiagonalThirdBound
  dsimp only [a, r, f, x, d] at hdiv ⊢
  rw [show (suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2 =
      suzukiDF6D4DiagonalFrequency mode ^ 4 by ring]
  calc
    suzukiProjectAStar * suzukiDF6D4DiagonalFrequency mode ^ 2 *
          (2 * (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 3 +
            (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 *
              suzukiDF6D4DiagonalFrequency mode ^ 2 +
            (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) *
              suzukiDF6D4DiagonalFrequency mode ^ 2 +
            suzukiDF6D4DiagonalFrequency mode ^ 4) /
        ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 3 *
          ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
            suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2) ≤
      suzukiProjectAStar * suzukiDF6D4DiagonalFrequency mode ^ 2 *
          (2 * suzukiDF6D4DiagonalFrequency mode + 3) /
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 4 := hdiv
    _ = (2 * suzukiDF6D4DiagonalFrequency mode ^ 3 +
            3 * suzukiDF6D4DiagonalFrequency mode ^ 2) /
          suzukiProjectAStar ^ 3 /
        suzukiDF6D4DiagonalDecay n ^ 4 := by
      field_simp [ha.ne', hr.ne']

private theorem suzukiDF6D4OddDiagonalBaseTerm_le_bound_of_pos
    {mode n : Nat} (hmode : 0 < mode) :
    suzukiDF6D4OddDiagonalBaseTerm mode n ≤
      suzukiDF6D4DiagonalThirdBound mode /
        suzukiDF6D4DiagonalDecay n ^ 4 := by
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let d := x ^ 2 + f ^ 2
  have ha : 0 < a := suzukiProjectAStar_pos
  have hr : 0 < r := suzukiDF6D4DiagonalDecay_pos n
  have hf : 0 < f := suzukiDF6D4DiagonalFrequency_pos hmode
  have hx : 0 < x := mul_pos ha hr
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [sq_pos_of_pos hx, sq_nonneg f]
  have hpoly := suzukiDF6D4_odd_poly_bound hx.le hf.le
  have hcross := mul_le_mul_of_nonneg_left hpoly
    (mul_nonneg (mul_nonneg ha.le (sq_nonneg f)) (pow_nonneg hx.le 3))
  have hdiv :
      a * f ^ 2 * (x ^ 3 + x ^ 2 * f ^ 2 + f ^ 4) /
          (x ^ 3 * d ^ 2) ≤
        a * f ^ 2 * (2 * f + 3) / x ^ 4 := by
    rw [div_le_div_iff₀ (mul_pos (pow_pos hx 3) (pow_pos hd 2))
      (pow_pos hx 4)]
    dsimp only [d] at hcross ⊢
    nlinarith
  unfold suzukiDF6D4OddDiagonalBaseTerm suzukiDF6D4DiagonalThirdBound
  dsimp only [a, r, f, x, d] at hdiv ⊢
  rw [show (suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2 =
      suzukiDF6D4DiagonalFrequency mode ^ 4 by ring]
  calc
    suzukiProjectAStar * suzukiDF6D4DiagonalFrequency mode ^ 2 *
          ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 3 +
            (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 *
              suzukiDF6D4DiagonalFrequency mode ^ 2 +
            suzukiDF6D4DiagonalFrequency mode ^ 4) /
        ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 3 *
          ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
            suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2) ≤
      suzukiProjectAStar * suzukiDF6D4DiagonalFrequency mode ^ 2 *
          (2 * suzukiDF6D4DiagonalFrequency mode + 3) /
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 4 := hdiv
    _ = (2 * suzukiDF6D4DiagonalFrequency mode ^ 3 +
            3 * suzukiDF6D4DiagonalFrequency mode ^ 2) /
          suzukiProjectAStar ^ 3 /
        suzukiDF6D4DiagonalDecay n ^ 4 := by
      field_simp [ha.ne', hr.ne']

theorem suzukiDF6D4EvenDiagonalBaseTerm_le_bound (mode n : Nat) :
    suzukiDF6D4EvenDiagonalBaseTerm mode n ≤
      suzukiDF6D4DiagonalThirdBound mode /
        suzukiDF6D4DiagonalDecay n ^ 4 := by
  rcases mode.eq_zero_or_pos with rfl | hmode
  · norm_num [suzukiDF6D4EvenDiagonalBaseTerm,
      suzukiDF6D4DiagonalThirdBound, suzukiDF6D4DiagonalFrequency]
  · exact suzukiDF6D4EvenDiagonalBaseTerm_le_bound_of_pos hmode

theorem suzukiDF6D4OddDiagonalBaseTerm_le_bound
    (mode n : Nat) (hmode : 0 < mode) :
    suzukiDF6D4OddDiagonalBaseTerm mode n ≤
      suzukiDF6D4DiagonalThirdBound mode /
        suzukiDF6D4DiagonalDecay n ^ 4 :=
  suzukiDF6D4OddDiagonalBaseTerm_le_bound_of_pos hmode

/-! ## Reciprocal fourth-power tail -/

private theorem summable_suzukiDF6D4DiagonalDecay_inv_pow
    (p : Nat) (hp : 1 < p) :
    Summable (fun n : Nat => 1 / suzukiDF6D4DiagonalDecay n ^ p) := by
  have hNat : Summable (fun n : Nat => 1 / (((n + 1 : Nat) : Real) ^ p)) := by
    have h := (Real.summable_nat_pow_inv (p := p)).2 hp
    simpa only [one_div] using (summable_nat_add_iff 1).2 h
  apply (summable_nat_add_iff 1).1
  apply Summable.of_nonneg_of_le
    (fun n => one_div_nonneg.mpr
      (pow_nonneg (suzukiDF6D4DiagonalDecay_pos (n + 1)).le p))
    (fun n => ?_) hNat
  have hbase : (0 : Real) < ((n + 1 : Nat) : Real) := by positivity
  have hle : ((n + 1 : Nat) : Real) ≤
      suzukiDF6D4DiagonalDecay (n + 1) := by
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    linarith
  exact one_div_le_one_div_of_le (pow_pos hbase p)
    (pow_le_pow_left₀ hbase.le hle p)

private theorem suzukiDF6D4_inv_four_succ_le_difference
    {x : Real} (hx : 0 < x) :
    1 / (x + 2) ^ 4 ≤
      (1 / 6 : Real) * (1 / x ^ 3 - 1 / (x + 2) ^ 3) := by
  field_simp
  nlinarith [sq_nonneg x]

theorem suzukiDF6D4DiagonalDecayFourthTail_le (N : Nat) :
    (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 4) ≤
      1 / suzukiDF6D4DiagonalDecay N ^ 4 +
        1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3) := by
  let f : Nat → Real := fun j =>
    1 / suzukiDF6D4DiagonalDecay (N + j) ^ 4
  have hf : Summable f := by
    dsimp only [f]
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2
      (summable_suzukiDF6D4DiagonalDecay_inv_pow 4 (by norm_num))
  have hrest :
      (∑' j : Nat,
          1 / suzukiDF6D4DiagonalDecay (N + 1 + j) ^ 4) ≤
        1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3) := by
    apply Real.tsum_le_of_sum_range_le
    · intro j
      positivity
    · intro k
      calc
        ∑ j ∈ Finset.range k,
              1 / suzukiDF6D4DiagonalDecay (N + 1 + j) ^ 4 ≤
            ∑ j ∈ Finset.range k,
              (1 / 6 : Real) *
                (1 / suzukiDF6D4DiagonalDecay (N + j) ^ 3 -
                  1 / suzukiDF6D4DiagonalDecay (N + 1 + j) ^ 3) := by
          apply Finset.sum_le_sum
          intro j hj
          have hdecay :
              suzukiDF6D4DiagonalDecay (N + 1 + j) =
                suzukiDF6D4DiagonalDecay (N + j) + 2 := by
            unfold suzukiDF6D4DiagonalDecay
            push_cast
            ring
          rw [hdecay]
          exact suzukiDF6D4_inv_four_succ_le_difference
            (suzukiDF6D4DiagonalDecay_pos (N + j))
        _ = (1 / 6 : Real) *
              (1 / suzukiDF6D4DiagonalDecay N ^ 3 -
                1 / suzukiDF6D4DiagonalDecay (N + k) ^ 3) := by
          induction k with
          | zero => simp
          | succ k ih =>
              rw [Finset.sum_range_succ, ih]
              have hindex : N + 1 + k = N + (k + 1) := by omega
              rw [hindex]
              ring
        _ ≤ 1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3) := by
          have htail :
              0 ≤ 1 / suzukiDF6D4DiagonalDecay (N + k) ^ 3 := by
            exact one_div_nonneg.mpr
              (pow_nonneg (suzukiDF6D4DiagonalDecay_pos (N + k)).le 3)
          field_simp
          nlinarith
  have hsplit := hf.sum_add_tsum_nat_add 1
  have hsplit' : f 0 + (∑' j : Nat, f (j + 1)) = ∑' j : Nat, f j := by
    simpa only [Finset.sum_range_one, Nat.zero_add] using hsplit
  rw [← hsplit']
  dsimp only [f]
  have hfun :
      (fun j : Nat => 1 / suzukiDF6D4DiagonalDecay (N + (j + 1)) ^ 4) =
        (fun j : Nat =>
          1 / suzukiDF6D4DiagonalDecay (N + 1 + j) ^ 4) := by
    funext j
    congr 3
    omega
  rw [hfun]
  simp only [Nat.add_zero]
  linarith

private theorem suzukiDF6D4DiagonalThirdBound_nonneg (mode : Nat) :
    0 ≤ suzukiDF6D4DiagonalThirdBound mode := by
  unfold suzukiDF6D4DiagonalThirdBound
  dsimp only
  apply div_nonneg
  · have hf := suzukiDF6D4DiagonalFrequency_nonneg mode
    positivity
  · positivity [suzukiProjectAStar_pos]

theorem summable_suzukiDF6D4EvenDiagonalBaseTerm (mode : Nat) :
    Summable (fun n : Nat => suzukiDF6D4EvenDiagonalBaseTerm mode n) := by
  have hmajor : Summable (fun n : Nat =>
      suzukiDF6D4DiagonalThirdBound mode /
        suzukiDF6D4DiagonalDecay n ^ 4) := by
    simpa [div_eq_mul_inv] using
      (summable_suzukiDF6D4DiagonalDecay_inv_pow 4 (by norm_num)).mul_left
        (suzukiDF6D4DiagonalThirdBound mode)
  exact Summable.of_nonneg_of_le
    (suzukiDF6D4EvenDiagonalBaseTerm_nonneg mode)
    (suzukiDF6D4EvenDiagonalBaseTerm_le_bound mode) hmajor

theorem summable_suzukiDF6D4OddDiagonalBaseTerm
    (mode : Nat) (hmode : 0 < mode) :
    Summable (fun n : Nat => suzukiDF6D4OddDiagonalBaseTerm mode n) := by
  have hmajor : Summable (fun n : Nat =>
      suzukiDF6D4DiagonalThirdBound mode /
        suzukiDF6D4DiagonalDecay n ^ 4) := by
    simpa [div_eq_mul_inv] using
      (summable_suzukiDF6D4DiagonalDecay_inv_pow 4 (by norm_num)).mul_left
        (suzukiDF6D4DiagonalThirdBound mode)
  exact Summable.of_nonneg_of_le
    (suzukiDF6D4OddDiagonalBaseTerm_nonneg mode)
    (fun n => suzukiDF6D4OddDiagonalBaseTerm_le_bound mode n hmode) hmajor

def suzukiDF6D4EvenDiagonalBaseTail (mode N : Nat) : Real :=
  ∑' j : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode (N + j)

def suzukiDF6D4OddDiagonalBaseTail (mode N : Nat) : Real :=
  ∑' j : Nat, suzukiDF6D4OddDiagonalBaseTerm mode (N + j)

theorem suzukiDF6D4EvenDiagonalBaseTail_bounds (mode N : Nat) :
    0 ≤ suzukiDF6D4EvenDiagonalBaseTail mode N ∧
      suzukiDF6D4EvenDiagonalBaseTail mode N ≤
        suzukiDF6D4DiagonalThirdBound mode *
          (1 / suzukiDF6D4DiagonalDecay N ^ 4 +
            1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3)) := by
  have hbase := summable_suzukiDF6D4EvenDiagonalBaseTerm mode
  have htail : Summable (fun j : Nat =>
      suzukiDF6D4EvenDiagonalBaseTerm mode (N + j)) :=
    by simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hbase
  have hrecip := summable_suzukiDF6D4DiagonalDecay_inv_pow 4 (by norm_num)
  have hrecipTail : Summable (fun j : Nat =>
      1 / suzukiDF6D4DiagonalDecay (N + j) ^ 4) :=
    by simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hrecip
  constructor
  · unfold suzukiDF6D4EvenDiagonalBaseTail
    exact tsum_nonneg fun j =>
      suzukiDF6D4EvenDiagonalBaseTerm_nonneg mode (N + j)
  · unfold suzukiDF6D4EvenDiagonalBaseTail
    have hmajorTail : Summable (fun j : Nat =>
        suzukiDF6D4DiagonalThirdBound mode /
          suzukiDF6D4DiagonalDecay (N + j) ^ 4) := by
      simpa [div_eq_mul_inv] using
        hrecipTail.mul_left (suzukiDF6D4DiagonalThirdBound mode)
    have hle := htail.tsum_le_tsum
      (fun j => suzukiDF6D4EvenDiagonalBaseTerm_le_bound mode (N + j))
      hmajorTail
    calc
      (∑' j : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode (N + j)) ≤
          ∑' j : Nat, suzukiDF6D4DiagonalThirdBound mode /
            suzukiDF6D4DiagonalDecay (N + j) ^ 4 := hle
      _ = suzukiDF6D4DiagonalThirdBound mode *
          (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 4) := by
        simp [div_eq_mul_inv, tsum_mul_left]
      _ ≤ suzukiDF6D4DiagonalThirdBound mode *
          (1 / suzukiDF6D4DiagonalDecay N ^ 4 +
            1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (suzukiDF6D4DiagonalDecayFourthTail_le N)
          (suzukiDF6D4DiagonalThirdBound_nonneg mode)

theorem suzukiDF6D4OddDiagonalBaseTail_bounds
    (mode N : Nat) (hmode : 0 < mode) :
    0 ≤ suzukiDF6D4OddDiagonalBaseTail mode N ∧
      suzukiDF6D4OddDiagonalBaseTail mode N ≤
        suzukiDF6D4DiagonalThirdBound mode *
          (1 / suzukiDF6D4DiagonalDecay N ^ 4 +
            1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3)) := by
  have hbase := summable_suzukiDF6D4OddDiagonalBaseTerm mode hmode
  have htail : Summable (fun j : Nat =>
      suzukiDF6D4OddDiagonalBaseTerm mode (N + j)) :=
    by simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hbase
  have hrecip := summable_suzukiDF6D4DiagonalDecay_inv_pow 4 (by norm_num)
  have hrecipTail : Summable (fun j : Nat =>
      1 / suzukiDF6D4DiagonalDecay (N + j) ^ 4) :=
    by simpa only [Nat.add_comm] using (summable_nat_add_iff N).2 hrecip
  constructor
  · unfold suzukiDF6D4OddDiagonalBaseTail
    exact tsum_nonneg fun j =>
      suzukiDF6D4OddDiagonalBaseTerm_nonneg mode (N + j)
  · unfold suzukiDF6D4OddDiagonalBaseTail
    have hmajorTail : Summable (fun j : Nat =>
        suzukiDF6D4DiagonalThirdBound mode /
          suzukiDF6D4DiagonalDecay (N + j) ^ 4) := by
      simpa [div_eq_mul_inv] using
        hrecipTail.mul_left (suzukiDF6D4DiagonalThirdBound mode)
    have hle := htail.tsum_le_tsum
      (fun j => suzukiDF6D4OddDiagonalBaseTerm_le_bound mode (N + j) hmode)
      hmajorTail
    calc
      (∑' j : Nat, suzukiDF6D4OddDiagonalBaseTerm mode (N + j)) ≤
          ∑' j : Nat, suzukiDF6D4DiagonalThirdBound mode /
            suzukiDF6D4DiagonalDecay (N + j) ^ 4 := hle
      _ = suzukiDF6D4DiagonalThirdBound mode *
          (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 4) := by
        simp [div_eq_mul_inv, tsum_mul_left]
      _ ≤ suzukiDF6D4DiagonalThirdBound mode *
          (1 / suzukiDF6D4DiagonalDecay N ^ 4 +
            1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (suzukiDF6D4DiagonalDecayFourthTail_le N)
          (suzukiDF6D4DiagonalThirdBound_nonneg mode)

/-! ## Exponential endpoint corrections -/

private theorem suzukiDF6D4ExpNegAStar_nonneg :
    0 ≤ Real.exp (-suzukiProjectAStar) :=
  (Real.exp_pos _).le

private theorem suzukiDF6D4ExpNegAStar_lt_one :
    Real.exp (-suzukiProjectAStar) < 1 := by
  rw [Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr suzukiProjectAStar_pos

theorem suzukiDF6D4EvenDiagonalExpTerm_nonneg (mode n : Nat) :
    0 ≤ suzukiDF6D4EvenDiagonalExpTerm mode n := by
  unfold suzukiDF6D4EvenDiagonalExpTerm
  dsimp only
  split_ifs
  · positivity [suzukiProjectAStar_pos,
      suzukiDF6D4DiagonalDecay_pos]
  · positivity [suzukiProjectAStar_pos,
      suzukiDF6D4DiagonalDecay_pos,
      suzukiDF6D4DiagonalFrequency_nonneg]

theorem suzukiDF6D4OddDiagonalExpMagnitudeTerm_nonneg (mode n : Nat) :
    0 ≤ suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n := by
  unfold suzukiDF6D4OddDiagonalExpMagnitudeTerm
  dsimp only
  positivity [suzukiProjectAStar_pos,
    suzukiDF6D4DiagonalDecay_pos,
    suzukiDF6D4DiagonalFrequency_nonneg]

private theorem suzukiDF6D4EvenDiagonalExpTerm_le_basic
    (mode n : Nat) :
    suzukiDF6D4EvenDiagonalExpTerm mode n ≤
      Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) /
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n ^ 2) := by
  by_cases hmode : mode = 0
  · subst mode
    unfold suzukiDF6D4EvenDiagonalExpTerm
    simp only [if_pos]
    have hnum : 0 ≤ Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) := by
      positivity
    have hden : 0 <
        suzukiProjectAStar * suzukiDF6D4DiagonalDecay n ^ 2 := by
      exact mul_pos suzukiProjectAStar_pos
        (pow_pos (suzukiDF6D4DiagonalDecay_pos n) 2)
    apply div_le_div_of_nonneg_left hnum hden
    nlinarith
  · let a := suzukiProjectAStar
    let r := suzukiDF6D4DiagonalDecay n
    let f := suzukiDF6D4DiagonalFrequency mode
    let x := a * r
    let d := x ^ 2 + f ^ 2
    let q := Real.exp (-a) ^ (4 * n + 1)
    have ha : 0 < a := suzukiProjectAStar_pos
    have hr : 0 < r := suzukiDF6D4DiagonalDecay_pos n
    have hf : 0 ≤ f := suzukiDF6D4DiagonalFrequency_nonneg mode
    have hx : 0 < x := mul_pos ha hr
    have hd : 0 < d := by
      dsimp only [d]
      nlinarith [sq_pos_of_pos hx, sq_nonneg f]
    have hq : 0 ≤ q := by dsimp only [q]; positivity
    have hden : x ^ 4 ≤ d ^ 2 := by
      dsimp only [d]
      nlinarith [sq_nonneg x, sq_nonneg f,
        mul_nonneg (sq_nonneg x) (sq_nonneg f)]
    have hcoeff : a * x ^ 2 / d ^ 2 ≤ 1 / (a * r ^ 2) := by
      rw [div_le_div_iff₀ (pow_pos hd 2)
        (mul_pos ha (pow_pos hr 2))]
      dsimp only [x] at hden ⊢
      nlinarith
    unfold suzukiDF6D4EvenDiagonalExpTerm
    simp only [hmode, if_false]
    dsimp only [a, r, f, x, d, q] at hcoeff hq ⊢
    calc
      suzukiProjectAStar *
            (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 *
            Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) /
          ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
            suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2 =
        (suzukiProjectAStar *
            (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 /
          ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
            suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2) *
          Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) := by ring
      _ ≤ (1 /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n ^ 2)) *
          Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) :=
        mul_le_mul_of_nonneg_right hcoeff hq
      _ = Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n ^ 2) := by ring

private theorem suzukiDF6D4OddDiagonalExpMagnitudeTerm_le_basic
    (mode n : Nat) :
    suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n ≤
      suzukiDF6D4DiagonalFrequency mode ^ 2 *
        Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) /
        (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay n ^ 4) := by
  let a := suzukiProjectAStar
  let r := suzukiDF6D4DiagonalDecay n
  let f := suzukiDF6D4DiagonalFrequency mode
  let x := a * r
  let d := x ^ 2 + f ^ 2
  let q := Real.exp (-a) ^ (4 * n + 1)
  have ha : 0 < a := suzukiProjectAStar_pos
  have hr : 0 < r := suzukiDF6D4DiagonalDecay_pos n
  have hf : 0 ≤ f := suzukiDF6D4DiagonalFrequency_nonneg mode
  have hx : 0 < x := mul_pos ha hr
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [sq_pos_of_pos hx, sq_nonneg f]
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hden : x ^ 4 ≤ d ^ 2 := by
    dsimp only [d]
    nlinarith [sq_nonneg x, sq_nonneg f,
      mul_nonneg (sq_nonneg x) (sq_nonneg f)]
  have hcoeff : a * f ^ 2 / d ^ 2 ≤
      f ^ 2 / (a ^ 3 * r ^ 4) := by
    rw [div_le_div_iff₀ (pow_pos hd 2)
      (mul_pos (pow_pos ha 3) (pow_pos hr 4))]
    dsimp only [x] at hden ⊢
    nlinarith
  unfold suzukiDF6D4OddDiagonalExpMagnitudeTerm
  dsimp only [a, r, f, x, d, q] at hcoeff hq ⊢
  calc
    suzukiProjectAStar * suzukiDF6D4DiagonalFrequency mode ^ 2 *
          Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) /
        ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
          suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2 =
      (suzukiProjectAStar * suzukiDF6D4DiagonalFrequency mode ^ 2 /
        ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
          suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2) *
        Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) := by ring
    _ ≤ (suzukiDF6D4DiagonalFrequency mode ^ 2 /
        (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay n ^ 4)) *
        Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) :=
      mul_le_mul_of_nonneg_right hcoeff hq
    _ = suzukiDF6D4DiagonalFrequency mode ^ 2 *
        Real.exp (-suzukiProjectAStar) ^ (4 * n + 1) /
        (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay n ^ 4) := by ring

private theorem suzukiDF6D4EvenDiagonalExpTerm_shift_le_geometric
    (mode N j : Nat) :
    suzukiDF6D4EvenDiagonalExpTerm mode (N + j) ≤
      (Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2)) *
        (Real.exp (-suzukiProjectAStar) ^ 4) ^ j := by
  let q := Real.exp (-suzukiProjectAStar)
  have hq : 0 ≤ q := suzukiDF6D4ExpNegAStar_nonneg
  have hrN : 0 < suzukiDF6D4DiagonalDecay N :=
    suzukiDF6D4DiagonalDecay_pos N
  have hrJ : 0 < suzukiDF6D4DiagonalDecay (N + j) :=
    suzukiDF6D4DiagonalDecay_pos (N + j)
  have hrle : suzukiDF6D4DiagonalDecay N ≤
      suzukiDF6D4DiagonalDecay (N + j) := by
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    gcongr
    exact_mod_cast Nat.le_add_right N j
  have hbasic := suzukiDF6D4EvenDiagonalExpTerm_le_basic mode (N + j)
  have hden :
      q ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay (N + j) ^ 2) ≤
        q ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2) := by
    apply div_le_div_of_nonneg_left (pow_nonneg hq _)
    · positivity [suzukiProjectAStar_pos]
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hrN.le hrle 2) suzukiProjectAStar_pos.le
  have hpow : q ^ (4 * (N + j) + 1) =
      q ^ (4 * N + 1) * (q ^ 4) ^ j := by
    rw [show 4 * (N + j) + 1 = (4 * N + 1) + 4 * j by omega,
      pow_add, ← pow_mul]
  dsimp only [q] at hbasic hden hpow ⊢
  calc
    suzukiDF6D4EvenDiagonalExpTerm mode (N + j) ≤
        Real.exp (-suzukiProjectAStar) ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar *
            suzukiDF6D4DiagonalDecay (N + j) ^ 2) := hbasic
    _ ≤ Real.exp (-suzukiProjectAStar) ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2) := hden
    _ = _ := by rw [hpow]; ring

private theorem suzukiDF6D4OddDiagonalExpMagnitudeTerm_shift_le_geometric
    (mode N j : Nat) :
    suzukiDF6D4OddDiagonalExpMagnitudeTerm mode (N + j) ≤
      (suzukiDF6D4DiagonalFrequency mode ^ 2 *
          Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4)) *
        (Real.exp (-suzukiProjectAStar) ^ 4) ^ j := by
  let q := Real.exp (-suzukiProjectAStar)
  have hq : 0 ≤ q := suzukiDF6D4ExpNegAStar_nonneg
  have hrN : 0 < suzukiDF6D4DiagonalDecay N :=
    suzukiDF6D4DiagonalDecay_pos N
  have hrJ : 0 < suzukiDF6D4DiagonalDecay (N + j) :=
    suzukiDF6D4DiagonalDecay_pos (N + j)
  have hrle : suzukiDF6D4DiagonalDecay N ≤
      suzukiDF6D4DiagonalDecay (N + j) := by
    unfold suzukiDF6D4DiagonalDecay
    push_cast
    gcongr
    exact_mod_cast Nat.le_add_right N j
  have hbasic :=
    suzukiDF6D4OddDiagonalExpMagnitudeTerm_le_basic mode (N + j)
  have hnum : 0 ≤ suzukiDF6D4DiagonalFrequency mode ^ 2 *
      q ^ (4 * (N + j) + 1) := by positivity
  have hden :
      suzukiDF6D4DiagonalFrequency mode ^ 2 * q ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar ^ 3 *
            suzukiDF6D4DiagonalDecay (N + j) ^ 4) ≤
        suzukiDF6D4DiagonalFrequency mode ^ 2 * q ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4) := by
    apply div_le_div_of_nonneg_left hnum
    · positivity [suzukiProjectAStar_pos]
    · exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hrN.le hrle 4)
        (pow_nonneg suzukiProjectAStar_pos.le 3)
  have hpow : q ^ (4 * (N + j) + 1) =
      q ^ (4 * N + 1) * (q ^ 4) ^ j := by
    rw [show 4 * (N + j) + 1 = (4 * N + 1) + 4 * j by omega,
      pow_add, ← pow_mul]
  dsimp only [q] at hbasic hden hpow ⊢
  calc
    suzukiDF6D4OddDiagonalExpMagnitudeTerm mode (N + j) ≤
        suzukiDF6D4DiagonalFrequency mode ^ 2 *
          Real.exp (-suzukiProjectAStar) ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar ^ 3 *
            suzukiDF6D4DiagonalDecay (N + j) ^ 4) := hbasic
    _ ≤ suzukiDF6D4DiagonalFrequency mode ^ 2 *
          Real.exp (-suzukiProjectAStar) ^ (4 * (N + j) + 1) /
          (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4) := hden
    _ = _ := by rw [hpow]; ring

theorem summable_suzukiDF6D4EvenDiagonalExpTerm (mode : Nat) :
    Summable (fun n : Nat => suzukiDF6D4EvenDiagonalExpTerm mode n) := by
  let C : Real := Real.exp (-suzukiProjectAStar) /
    (suzukiProjectAStar * suzukiDF6D4DiagonalDecay 0 ^ 2)
  let q : Real := Real.exp (-suzukiProjectAStar) ^ 4
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact pow_lt_one₀ suzukiDF6D4ExpNegAStar_nonneg
      suzukiDF6D4ExpNegAStar_lt_one (by omega)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hmajor : Summable (fun j : Nat => C * q ^ j) :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left C
  apply Summable.of_nonneg_of_le
    (suzukiDF6D4EvenDiagonalExpTerm_nonneg mode)
    (fun j => ?_) hmajor
  dsimp only [C, q]
  convert suzukiDF6D4EvenDiagonalExpTerm_shift_le_geometric mode 0 j using 1 <;>
    norm_num

theorem summable_suzukiDF6D4OddDiagonalExpMagnitudeTerm (mode : Nat) :
    Summable (fun n : Nat =>
      suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) := by
  let C : Real := suzukiDF6D4DiagonalFrequency mode ^ 2 *
      Real.exp (-suzukiProjectAStar) /
      (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay 0 ^ 4)
  let q : Real := Real.exp (-suzukiProjectAStar) ^ 4
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact pow_lt_one₀ suzukiDF6D4ExpNegAStar_nonneg
      suzukiDF6D4ExpNegAStar_lt_one (by omega)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hmajor : Summable (fun j : Nat => C * q ^ j) :=
    (summable_geometric_of_norm_lt_one hqnorm).mul_left C
  apply Summable.of_nonneg_of_le
    (suzukiDF6D4OddDiagonalExpMagnitudeTerm_nonneg mode)
    (fun j => ?_) hmajor
  dsimp only [C, q]
  convert suzukiDF6D4OddDiagonalExpMagnitudeTerm_shift_le_geometric mode 0 j using 1 <;>
    norm_num

def suzukiDF6D4EvenDiagonalExpTail (mode N : Nat) : Real :=
  ∑' j : Nat, suzukiDF6D4EvenDiagonalExpTerm mode (N + j)

def suzukiDF6D4OddDiagonalExpMagnitudeTail (mode N : Nat) : Real :=
  ∑' j : Nat, suzukiDF6D4OddDiagonalExpMagnitudeTerm mode (N + j)

theorem suzukiDF6D4EvenDiagonalExpTail_bounds (mode N : Nat) :
    0 ≤ suzukiDF6D4EvenDiagonalExpTail mode N ∧
      suzukiDF6D4EvenDiagonalExpTail mode N ≤
        Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2) /
          (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
  let C : Real := Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
    (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2)
  let q : Real := Real.exp (-suzukiProjectAStar) ^ 4
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact pow_lt_one₀ suzukiDF6D4ExpNegAStar_nonneg
      suzukiDF6D4ExpNegAStar_lt_one (by omega)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have htail : Summable (fun j : Nat =>
      suzukiDF6D4EvenDiagonalExpTerm mode (N + j)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2
      (summable_suzukiDF6D4EvenDiagonalExpTerm mode)
  have hgeom := (hasSum_geometric_of_norm_lt_one hqnorm).mul_left C
  constructor
  · unfold suzukiDF6D4EvenDiagonalExpTail
    exact tsum_nonneg fun j =>
      suzukiDF6D4EvenDiagonalExpTerm_nonneg mode (N + j)
  · unfold suzukiDF6D4EvenDiagonalExpTail
    have hle := htail.tsum_le_tsum
      (suzukiDF6D4EvenDiagonalExpTerm_shift_le_geometric mode N)
      hgeom.summable
    calc
      (∑' j : Nat, suzukiDF6D4EvenDiagonalExpTerm mode (N + j)) ≤
          ∑' j : Nat, C * q ^ j := hle
      _ = C * (1 - q)⁻¹ := hgeom.tsum_eq
      _ = Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2) /
          (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
        dsimp only [C, q]
        simp only [div_eq_mul_inv]

theorem suzukiDF6D4OddDiagonalExpMagnitudeTail_bounds (mode N : Nat) :
    0 ≤ suzukiDF6D4OddDiagonalExpMagnitudeTail mode N ∧
      suzukiDF6D4OddDiagonalExpMagnitudeTail mode N ≤
        suzukiDF6D4DiagonalFrequency mode ^ 2 *
          Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4) /
          (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
  let C : Real := suzukiDF6D4DiagonalFrequency mode ^ 2 *
      Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
      (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4)
  let q : Real := Real.exp (-suzukiProjectAStar) ^ 4
  have hq0 : 0 ≤ q := by dsimp only [q]; positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    exact pow_lt_one₀ suzukiDF6D4ExpNegAStar_nonneg
      suzukiDF6D4ExpNegAStar_lt_one (by omega)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have htail : Summable (fun j : Nat =>
      suzukiDF6D4OddDiagonalExpMagnitudeTerm mode (N + j)) := by
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2
      (summable_suzukiDF6D4OddDiagonalExpMagnitudeTerm mode)
  have hgeom := (hasSum_geometric_of_norm_lt_one hqnorm).mul_left C
  constructor
  · unfold suzukiDF6D4OddDiagonalExpMagnitudeTail
    exact tsum_nonneg fun j =>
      suzukiDF6D4OddDiagonalExpMagnitudeTerm_nonneg mode (N + j)
  · unfold suzukiDF6D4OddDiagonalExpMagnitudeTail
    have hle := htail.tsum_le_tsum
      (suzukiDF6D4OddDiagonalExpMagnitudeTerm_shift_le_geometric mode N)
      hgeom.summable
    calc
      (∑' j : Nat,
          suzukiDF6D4OddDiagonalExpMagnitudeTerm mode (N + j)) ≤
          ∑' j : Nat, C * q ^ j := hle
      _ = C * (1 - q)⁻¹ := hgeom.tsum_eq
      _ = suzukiDF6D4DiagonalFrequency mode ^ 2 *
          Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4) /
          (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
        dsimp only [C, q]
        simp only [div_eq_mul_inv]

/-! ## Complete half-integer reciprocal sums -/

private theorem suzukiDF6D4DiagonalDecay_mono_step (n : Nat) :
    suzukiDF6D4DiagonalDecay n ≤
      suzukiDF6D4DiagonalDecay (n + 1) := by
  unfold suzukiDF6D4DiagonalDecay
  push_cast
  linarith

private theorem suzukiDF6D4DiagonalDecay_tendsto_atTop (N : Nat) :
    Tendsto (fun k : Nat => suzukiDF6D4DiagonalDecay (N + k))
      atTop atTop := by
  have hbase : Tendsto (fun k : Nat => (k : Real) * 2) atTop atTop :=
    by
      simpa [mul_comm] using
        tendsto_natCast_atTop_atTop.const_mul_atTop
          (by norm_num : (0 : Real) < 2)
  have hadd : Tendsto
      (fun k : Nat => (k : Real) * 2 + (2 * (N : Real) + 1 / 2))
      atTop atTop := hbase.atTop_add tendsto_const_nhds
  convert hadd using 1
  funext k
  unfold suzukiDF6D4DiagonalDecay
  push_cast
  ring

private theorem suzukiDF6D4_hasSum_decay_inv_difference (N : Nat) :
    HasSum
      (fun j : Nat =>
        1 / suzukiDF6D4DiagonalDecay (N + j) -
          1 / suzukiDF6D4DiagonalDecay (N + 1 + j))
      (1 / suzukiDF6D4DiagonalDecay N) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hzero : Tendsto
        (fun k : Nat => 1 / suzukiDF6D4DiagonalDecay (N + k))
        atTop (nhds 0) :=
      (suzukiDF6D4DiagonalDecay_tendsto_atTop N).const_div_atTop 1
    have htend : Tendsto
        (fun k : Nat => 1 / suzukiDF6D4DiagonalDecay N -
          1 / suzukiDF6D4DiagonalDecay (N + k))
        atTop (nhds (1 / suzukiDF6D4DiagonalDecay N)) := by
      simpa using
        ((tendsto_const_nhds : Tendsto
          (fun _ : Nat => 1 / suzukiDF6D4DiagonalDecay N)
          atTop (nhds (1 / suzukiDF6D4DiagonalDecay N))).sub hzero)
    convert htend using 1
    funext k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hindex : N + 1 + k = N + (k + 1) := by omega
        rw [hindex]
        ring
  · intro j
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
      (suzukiDF6D4DiagonalDecay_pos (N + j))
    have h := suzukiDF6D4DiagonalDecay_mono_step (N + j)
    have hindex : N + 1 + j = (N + j) + 1 := by omega
    simpa only [hindex] using h

private theorem suzukiDF6D4_hasSum_decay_inv_sq_difference (N : Nat) :
    HasSum
      (fun j : Nat =>
        1 / suzukiDF6D4DiagonalDecay (N + j) ^ 2 -
          1 / suzukiDF6D4DiagonalDecay (N + 1 + j) ^ 2)
      (1 / suzukiDF6D4DiagonalDecay N ^ 2) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have hzeroOne : Tendsto
        (fun k : Nat => 1 / suzukiDF6D4DiagonalDecay (N + k))
        atTop (nhds 0) :=
      (suzukiDF6D4DiagonalDecay_tendsto_atTop N).const_div_atTop 1
    have hzero : Tendsto
        (fun k : Nat => 1 / suzukiDF6D4DiagonalDecay (N + k) ^ 2)
        atTop (nhds 0) := by
      simpa [one_div, inv_pow] using hzeroOne.pow 2
    have htend : Tendsto
        (fun k : Nat => 1 / suzukiDF6D4DiagonalDecay N ^ 2 -
          1 / suzukiDF6D4DiagonalDecay (N + k) ^ 2)
        atTop (nhds (1 / suzukiDF6D4DiagonalDecay N ^ 2)) := by
      simpa using
        ((tendsto_const_nhds : Tendsto
          (fun _ : Nat => 1 / suzukiDF6D4DiagonalDecay N ^ 2)
          atTop (nhds (1 / suzukiDF6D4DiagonalDecay N ^ 2))).sub hzero)
    convert htend using 1
    funext k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hindex : N + 1 + k = N + (k + 1) := by omega
        rw [hindex]
        ring
  · intro j
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le
      (pow_pos (suzukiDF6D4DiagonalDecay_pos (N + j)) 2)
    have h := suzukiDF6D4DiagonalDecay_mono_step (N + j)
    have hindex : N + 1 + j = (N + j) + 1 := by omega
    exact pow_le_pow_left₀ (suzukiDF6D4DiagonalDecay_pos (N + j)).le
      (by simpa only [hindex] using h) 2

private theorem suzukiDF6D4_inv_sq_lower_comparison
    {x : Real} (hx : 0 < x) :
    (1 / 2 : Real) * (1 / x - 1 / (x + 2)) ≤ 1 / x ^ 2 := by
  field_simp
  nlinarith [sq_nonneg x]

private theorem suzukiDF6D4_inv_sq_upper_comparison
    {x : Real} (hx : 0 < x) :
    1 / (x + 2) ^ 2 ≤
      (1 / 2 : Real) * (1 / x - 1 / (x + 2)) := by
  field_simp
  nlinarith [sq_nonneg x]

private theorem suzukiDF6D4_inv_cube_lower_comparison
    {x : Real} (hx : 0 < x) :
    (1 / 4 : Real) * (1 / x ^ 2 - 1 / (x + 2) ^ 2) ≤
      1 / x ^ 3 := by
  field_simp
  nlinarith [sq_nonneg x]

private theorem suzukiDF6D4_inv_cube_upper_comparison
    {x : Real} (hx : 0 < x) :
    1 / (x + 2) ^ 3 ≤
      (1 / 4 : Real) * (1 / x ^ 2 - 1 / (x + 2) ^ 2) := by
  field_simp
  nlinarith [sq_nonneg x]

/-- The complete reciprocal-square sum over the frozen half-integer Gamma
decays. -/
def suzukiDF6D4DiagonalReciprocalSquareSum : Real :=
  ∑' n : Nat, 1 / suzukiDF6D4DiagonalDecay n ^ 2

/-- The complete reciprocal-cube sum over the frozen half-integer Gamma
decays. -/
def suzukiDF6D4DiagonalReciprocalCubeSum : Real :=
  ∑' n : Nat, 1 / suzukiDF6D4DiagonalDecay n ^ 3

theorem suzukiDF6D4DiagonalReciprocalSquareTail_bounds (N : Nat) :
    1 / (2 * suzukiDF6D4DiagonalDecay N) ≤
        ∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 2 ∧
      (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 2) ≤
        1 / (2 * suzukiDF6D4DiagonalDecay N) +
          1 / suzukiDF6D4DiagonalDecay N ^ 2 := by
  let f : Nat → Real := fun j =>
    1 / suzukiDF6D4DiagonalDecay (N + j) ^ 2
  have hf : Summable f := by
    dsimp only [f]
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2
      (summable_suzukiDF6D4DiagonalDecay_inv_pow 2 (by norm_num))
  let lower : Nat → Real := fun j =>
    (1 / 2 : Real) *
      (1 / suzukiDF6D4DiagonalDecay (N + j) -
        1 / suzukiDF6D4DiagonalDecay (N + 1 + j))
  have hlowerSum : HasSum lower
      (1 / (2 * suzukiDF6D4DiagonalDecay N)) := by
    have h := (suzukiDF6D4_hasSum_decay_inv_difference N).mul_left (1 / 2)
    dsimp only [lower]
    rw [show 1 / (2 * suzukiDF6D4DiagonalDecay N) =
        (1 / 2 : Real) * (1 / suzukiDF6D4DiagonalDecay N) by ring]
    exact h
  constructor
  · have hle := hlowerSum.summable.tsum_le_tsum (fun j => ?_) hf
    · simpa only [hlowerSum.tsum_eq] using hle
    · dsimp only [lower, f]
      have hstep : suzukiDF6D4DiagonalDecay (N + 1 + j) =
          suzukiDF6D4DiagonalDecay (N + j) + 2 := by
        unfold suzukiDF6D4DiagonalDecay
        push_cast
        ring
      rw [hstep]
      exact suzukiDF6D4_inv_sq_lower_comparison
        (suzukiDF6D4DiagonalDecay_pos (N + j))
  · have hsplit := hf.sum_add_tsum_nat_add 1
    have hsplit' :
        f 0 + (∑' j : Nat, f (j + 1)) = ∑' j : Nat, f j := by
      simpa only [Finset.sum_range_one, Nat.zero_add] using hsplit
    rw [← hsplit']
    have hshift :
        (∑' j : Nat, f (j + 1)) ≤ ∑' j : Nat, lower j := by
      have hshiftSummable : Summable (fun j : Nat => f (j + 1)) :=
        (summable_nat_add_iff 1).2 hf
      apply hshiftSummable.tsum_le_tsum (fun j => ?_) hlowerSum.summable
      dsimp only [f, lower]
      have hleft : N + (j + 1) = N + 1 + j := by omega
      rw [hleft]
      have hstep : suzukiDF6D4DiagonalDecay (N + 1 + j) =
          suzukiDF6D4DiagonalDecay (N + j) + 2 := by
        unfold suzukiDF6D4DiagonalDecay
        push_cast
        ring
      rw [hstep]
      exact suzukiDF6D4_inv_sq_upper_comparison
        (suzukiDF6D4DiagonalDecay_pos (N + j))
    have hlowerEq := hlowerSum.tsum_eq
    dsimp only [f] at hshift ⊢
    simp only [Nat.add_zero] at hshift ⊢
    linarith

theorem suzukiDF6D4DiagonalReciprocalCubeTail_bounds (N : Nat) :
    1 / (4 * suzukiDF6D4DiagonalDecay N ^ 2) ≤
        ∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 3 ∧
      (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (N + j) ^ 3) ≤
        1 / (4 * suzukiDF6D4DiagonalDecay N ^ 2) +
          1 / suzukiDF6D4DiagonalDecay N ^ 3 := by
  let f : Nat → Real := fun j =>
    1 / suzukiDF6D4DiagonalDecay (N + j) ^ 3
  have hf : Summable f := by
    dsimp only [f]
    simpa only [Nat.add_comm] using (summable_nat_add_iff N).2
      (summable_suzukiDF6D4DiagonalDecay_inv_pow 3 (by norm_num))
  let lower : Nat → Real := fun j =>
    (1 / 4 : Real) *
      (1 / suzukiDF6D4DiagonalDecay (N + j) ^ 2 -
        1 / suzukiDF6D4DiagonalDecay (N + 1 + j) ^ 2)
  have hlowerSum : HasSum lower
      (1 / (4 * suzukiDF6D4DiagonalDecay N ^ 2)) := by
    have h :=
      (suzukiDF6D4_hasSum_decay_inv_sq_difference N).mul_left (1 / 4)
    dsimp only [lower]
    rw [show 1 / (4 * suzukiDF6D4DiagonalDecay N ^ 2) =
        (1 / 4 : Real) *
          (1 / suzukiDF6D4DiagonalDecay N ^ 2) by ring]
    exact h
  constructor
  · have hle := hlowerSum.summable.tsum_le_tsum (fun j => ?_) hf
    · simpa only [hlowerSum.tsum_eq] using hle
    · dsimp only [lower, f]
      have hstep : suzukiDF6D4DiagonalDecay (N + 1 + j) =
          suzukiDF6D4DiagonalDecay (N + j) + 2 := by
        unfold suzukiDF6D4DiagonalDecay
        push_cast
        ring
      rw [hstep]
      exact suzukiDF6D4_inv_cube_lower_comparison
        (suzukiDF6D4DiagonalDecay_pos (N + j))
  · have hsplit := hf.sum_add_tsum_nat_add 1
    have hsplit' :
        f 0 + (∑' j : Nat, f (j + 1)) = ∑' j : Nat, f j := by
      simpa only [Finset.sum_range_one, Nat.zero_add] using hsplit
    rw [← hsplit']
    have hshift :
        (∑' j : Nat, f (j + 1)) ≤ ∑' j : Nat, lower j := by
      have hshiftSummable : Summable (fun j : Nat => f (j + 1)) :=
        (summable_nat_add_iff 1).2 hf
      apply hshiftSummable.tsum_le_tsum (fun j => ?_) hlowerSum.summable
      dsimp only [f, lower]
      have hleft : N + (j + 1) = N + 1 + j := by omega
      rw [hleft]
      have hstep : suzukiDF6D4DiagonalDecay (N + 1 + j) =
          suzukiDF6D4DiagonalDecay (N + j) + 2 := by
        unfold suzukiDF6D4DiagonalDecay
        push_cast
        ring
      rw [hstep]
      exact suzukiDF6D4_inv_cube_upper_comparison
        (suzukiDF6D4DiagonalDecay_pos (N + j))
    have hlowerEq := hlowerSum.tsum_eq
    dsimp only [f] at hshift ⊢
    simp only [Nat.add_zero] at hshift ⊢
    linarith

private def suzukiDF6D4DiagonalDecayRat (n : Nat) : Rat :=
  2 * (n : Rat) + 1 / 2

private def suzukiDF6D4DiagonalReciprocalSquarePartialRat
    (N : Nat) : Rat :=
  ∑ n ∈ Finset.range N, 1 / suzukiDF6D4DiagonalDecayRat n ^ 2

private def suzukiDF6D4DiagonalReciprocalCubePartialRat
    (N : Nat) : Rat :=
  ∑ n ∈ Finset.range N, 1 / suzukiDF6D4DiagonalDecayRat n ^ 3

private theorem suzukiDF6D4DiagonalReciprocalSquarePartialRat_cast
    (N : Nat) :
    (suzukiDF6D4DiagonalReciprocalSquarePartialRat N : Real) =
      ∑ n ∈ Finset.range N, 1 / suzukiDF6D4DiagonalDecay n ^ 2 := by
  unfold suzukiDF6D4DiagonalReciprocalSquarePartialRat
    suzukiDF6D4DiagonalDecayRat suzukiDF6D4DiagonalDecay
  push_cast
  rfl

private theorem suzukiDF6D4DiagonalReciprocalCubePartialRat_cast
    (N : Nat) :
    (suzukiDF6D4DiagonalReciprocalCubePartialRat N : Real) =
      ∑ n ∈ Finset.range N, 1 / suzukiDF6D4DiagonalDecay n ^ 3 := by
  unfold suzukiDF6D4DiagonalReciprocalCubePartialRat
    suzukiDF6D4DiagonalDecayRat suzukiDF6D4DiagonalDecay
  push_cast
  rfl

def suzukiDF6D4DiagonalReciprocalSquareInterval : RationalInterval :=
  ⟨4299332288161 / 1000000000000,
    4299332289093 / 1000000000000⟩

def suzukiDF6D4DiagonalReciprocalCubeInterval : RationalInterval :=
  ⟨808298374609604 / 100000000000000,
    808298374609608 / 100000000000000⟩

private theorem suzukiDF6D4DiagonalReciprocalSquarePartialRat_bounds :
    (4299332288161 / 1000000000000 : Rat) ≤
        suzukiDF6D4DiagonalReciprocalSquarePartialRat 16384 +
          1 / (2 * suzukiDF6D4DiagonalDecayRat 16384) ∧
      suzukiDF6D4DiagonalReciprocalSquarePartialRat 16384 +
          1 / (2 * suzukiDF6D4DiagonalDecayRat 16384) +
          1 / suzukiDF6D4DiagonalDecayRat 16384 ^ 2 ≤
        (4299332289093 / 1000000000000 : Rat) := by
  native_decide

private theorem suzukiDF6D4DiagonalReciprocalCubePartialRat_bounds :
    (808298374609604 / 100000000000000 : Rat) ≤
        suzukiDF6D4DiagonalReciprocalCubePartialRat 16384 +
          1 / (4 * suzukiDF6D4DiagonalDecayRat 16384 ^ 2) ∧
      suzukiDF6D4DiagonalReciprocalCubePartialRat 16384 +
          1 / (4 * suzukiDF6D4DiagonalDecayRat 16384 ^ 2) +
          1 / suzukiDF6D4DiagonalDecayRat 16384 ^ 3 ≤
        (808298374609608 / 100000000000000 : Rat) := by
  native_decide

theorem suzukiDF6D4DiagonalReciprocalSquareInterval_contains :
    suzukiDF6D4DiagonalReciprocalSquareInterval.Contains
      suzukiDF6D4DiagonalReciprocalSquareSum := by
  have hsum :=
    (summable_suzukiDF6D4DiagonalDecay_inv_pow 2 (by norm_num)).sum_add_tsum_nat_add
      16384
  have htail := suzukiDF6D4DiagonalReciprocalSquareTail_bounds 16384
  have htail' :
      1 / (2 * suzukiDF6D4DiagonalDecay 16384) ≤
          ∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 2 ∧
        (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 2) ≤
          1 / (2 * suzukiDF6D4DiagonalDecay 16384) +
            1 / suzukiDF6D4DiagonalDecay 16384 ^ 2 := by
    simpa only [Nat.add_comm] using htail
  have htailLower : (1 / 65537 : Real) ≤
      ∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 2 := by
    convert htail'.1 using 1
    norm_num [suzukiDF6D4DiagonalDecay]
  have htailUpper :
      (∑' j : Nat,
          1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 2) ≤
        (1 / 65537 : Real) + 4 / 4295098369 := by
    convert htail'.2 using 1
    norm_num [suzukiDF6D4DiagonalDecay]
  have hcast :=
    suzukiDF6D4DiagonalReciprocalSquarePartialRat_cast 16384
  have hrat := suzukiDF6D4DiagonalReciprocalSquarePartialRat_bounds
  have hratLower := (Rat.cast_le (K := Real)).2 hrat.1
  have hratUpper := (Rat.cast_le (K := Real)).2 hrat.2
  unfold suzukiDF6D4DiagonalDecayRat at hratLower hratUpper
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] at hratLower hratUpper
  rw [hcast] at hratLower hratUpper
  unfold suzukiDF6D4DiagonalReciprocalSquareInterval
    RationalInterval.Contains suzukiDF6D4DiagonalReciprocalSquareSum
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  constructor
  · rw [← hsum]
    linarith
  · rw [← hsum]
    linarith

theorem suzukiDF6D4DiagonalReciprocalCubeInterval_contains :
    suzukiDF6D4DiagonalReciprocalCubeInterval.Contains
      suzukiDF6D4DiagonalReciprocalCubeSum := by
  have hsum :=
    (summable_suzukiDF6D4DiagonalDecay_inv_pow 3 (by norm_num)).sum_add_tsum_nat_add
      16384
  have htail := suzukiDF6D4DiagonalReciprocalCubeTail_bounds 16384
  have htail' :
      1 / (4 * suzukiDF6D4DiagonalDecay 16384 ^ 2) ≤
          ∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 3 ∧
        (∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 3) ≤
          1 / (4 * suzukiDF6D4DiagonalDecay 16384 ^ 2) +
            1 / suzukiDF6D4DiagonalDecay 16384 ^ 3 := by
    simpa only [Nat.add_comm] using htail
  have htailLower : (1 / 4295098369 : Real) ≤
      ∑' j : Nat, 1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 3 := by
    convert htail'.1 using 1
    norm_num [suzukiDF6D4DiagonalDecay]
  have htailUpper :
      (∑' j : Nat,
          1 / suzukiDF6D4DiagonalDecay (j + 16384) ^ 3) ≤
        (1 / 4295098369 : Real) + 8 / 281487861809153 := by
    convert htail'.2 using 1
    norm_num [suzukiDF6D4DiagonalDecay]
  have hcast :=
    suzukiDF6D4DiagonalReciprocalCubePartialRat_cast 16384
  have hrat := suzukiDF6D4DiagonalReciprocalCubePartialRat_bounds
  have hratLower := (Rat.cast_le (K := Real)).2 hrat.1
  have hratUpper := (Rat.cast_le (K := Real)).2 hrat.2
  unfold suzukiDF6D4DiagonalDecayRat at hratLower hratUpper
  norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat] at hratLower hratUpper
  rw [hcast] at hratLower hratUpper
  unfold suzukiDF6D4DiagonalReciprocalCubeInterval
    RationalInterval.Contains suzukiDF6D4DiagonalReciprocalCubeSum
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  constructor
  · rw [← hsum]
    linarith
  · rw [← hsum]
    linarith

/-! ## Exact complete diagonal components -/

/-- The fully restored even diagonal Gamma-series bracket, before the outer
factor `-2`. -/
def suzukiDF6D4EvenDiagonalGammaCore (mode : Nat) : Real :=
  (∑' n : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode n) +
    (∑' n : Nat, suzukiDF6D4EvenDiagonalExpTerm mode n) +
    suzukiDF6D4EvenDiagonalOriginSlope mode *
      suzukiDF6D4DiagonalReciprocalSquareSum +
    suzukiDF6D4DiagonalOriginSecond mode *
      suzukiDF6D4DiagonalReciprocalCubeSum

/-- The fully restored odd diagonal Gamma-series bracket, before the outer
factor `-2`.  The odd Yoshida basis has zero boundary slope. -/
def suzukiDF6D4OddDiagonalGammaCore (mode : Nat) : Real :=
  (∑' n : Nat, suzukiDF6D4OddDiagonalBaseTerm mode n) -
    (∑' n : Nat, suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) +
    suzukiDF6D4DiagonalOriginSecond mode *
      suzukiDF6D4DiagonalReciprocalCubeSum

/-- Complete even diagonal Gamma contribution, including the diagonal
`1/lambda - 1/(2n+1)` restoration. -/
def suzukiDF6D4EvenDiagonalGammaTerm (mode : Nat) : Real :=
  -2 * (Real.pi / 4 + Real.log 2 / 2 +
    suzukiDF6D4EvenDiagonalGammaCore mode)

/-- Complete odd diagonal Gamma contribution, including the diagonal
`1/lambda - 1/(2n+1)` restoration. -/
def suzukiDF6D4OddDiagonalGammaTerm (mode : Nat) : Real :=
  -2 * (Real.pi / 4 + Real.log 2 / 2 +
    suzukiDF6D4OddDiagonalGammaCore mode)

/-- Positive hyperbolic factor appearing after the two pole evaluations are
combined. -/
def suzukiDF6D4DiagonalPoleFactor : Real :=
  Real.exp (-suzukiProjectAStar) +
    (Real.exp (-suzukiProjectAStar))⁻¹ - 2

def suzukiDF6D4EvenDiagonalPoleTerm (mode : Nat) : Real :=
  let a := suzukiProjectAStar
  let f := suzukiDF6D4DiagonalFrequency mode
  let h := suzukiDF6D4DiagonalPoleFactor
  if mode = 0 then 4 * h / a
  else (a ^ 3 / 2) * h / (a ^ 2 / 4 + f ^ 2) ^ 2

def suzukiDF6D4OddDiagonalPoleTerm (mode : Nat) : Real :=
  let a := suzukiProjectAStar
  let f := suzukiDF6D4DiagonalFrequency mode
  let h := suzukiDF6D4DiagonalPoleFactor
  (-2 : Real) * a * f ^ 2 * h / (a ^ 2 / 4 + f ^ 2) ^ 2

/-- Prime-2 displacement in dimensionless Yoshida coordinates. -/
def suzukiDF6D4DiagonalPrimeDisplacement : Real :=
  Real.log 2 / suzukiProjectAStar

def suzukiDF6D4EvenDiagonalPrimeCorrelation (mode : Nat) : Real :=
  let d := suzukiDF6D4DiagonalPrimeDisplacement
  let f := suzukiDF6D4DiagonalFrequency mode
  if mode = 0 then 1 - d / 2
  else ((2 - d) * Real.cos (f * d) - Real.sin (f * d) / f) / 2

def suzukiDF6D4OddDiagonalPrimeCorrelation (mode : Nat) : Real :=
  let d := suzukiDF6D4DiagonalPrimeDisplacement
  let f := suzukiDF6D4DiagonalFrequency mode
  ((2 - d) * Real.cos (f * d) + Real.sin (f * d) / f) / 2

def suzukiDF6D4EvenDiagonalPrimeTerm (mode : Nat) : Real :=
  -(Real.sqrt 2 * Real.log 2 *
    suzukiDF6D4EvenDiagonalPrimeCorrelation mode)

def suzukiDF6D4OddDiagonalPrimeTerm (mode : Nat) : Real :=
  -(Real.sqrt 2 * Real.log 2 *
    suzukiDF6D4OddDiagonalPrimeCorrelation mode)

def suzukiDF6D4DiagonalConstantTerm : Real :=
  -(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)

/-- Exact complete even Yoshida diagonal entry at the frozen DF6D3 endpoint. -/
def suzukiDF6D4EvenDiagonalEntry (mode : Nat) : Real :=
  suzukiDF6D4EvenDiagonalPoleTerm mode +
    suzukiDF6D4EvenDiagonalPrimeTerm mode +
    suzukiDF6D4DiagonalConstantTerm +
    suzukiDF6D4EvenDiagonalGammaTerm mode

/-- Exact complete odd Yoshida diagonal entry; `mode` is the positive physical
frequency, so matrix row `i` uses `mode = i + 1`. -/
def suzukiDF6D4OddDiagonalEntry (mode : Nat) : Real :=
  suzukiDF6D4OddDiagonalPoleTerm mode +
    suzukiDF6D4OddDiagonalPrimeTerm mode +
    suzukiDF6D4DiagonalConstantTerm +
    suzukiDF6D4OddDiagonalGammaTerm mode

end

end RiemannHypothesisProject.Experiments.M100
