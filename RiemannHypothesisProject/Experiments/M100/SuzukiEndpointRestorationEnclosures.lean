import Mathlib.Analysis.SpecificLimits.Normed
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDigammaIntervalEvaluator

/-!
# Complete archimedean restoration enclosures for M100-DF6D4

The endpoint reconstruction restores the part of the archimedean sine
transform lying beyond `[-a*, a*]`.  This module proves the exact exponential
power reduction and the infinite geometric tail estimate used by the frozen
128-term evaluator.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The half-integer decay in the exponential restoration series. -/
def suzukiDF6D4RestorationDecay (k : Nat) : Real :=
  2 * (k : Real) + 1 / 2

/-- One positive term of the complete archimedean restoration series. -/
def suzukiDF6D4RestorationTerm (mode k : Nat) : Real :=
  let w := (mode : Real) * Real.pi / suzukiProjectAStar
  let d := suzukiDF6D4RestorationDecay k
  2 * w * Real.exp (-2 * suzukiProjectAStar * d) / (d ^ 2 + w ^ 2)

/-- The complete restoration tail beginning with term `N`. -/
def suzukiDF6D4RestorationTail (mode N : Nat) : Real :=
  ∑' j : Nat, suzukiDF6D4RestorationTerm mode (N + j)

theorem suzukiDF6D4Restoration_exp_eq_pow (k : Nat) :
    Real.exp
        (-2 * suzukiProjectAStar * suzukiDF6D4RestorationDecay k) =
      Real.exp (-suzukiProjectAStar) ^ (4 * k + 1) := by
  rw [← Real.exp_nat_mul]
  congr 1
  unfold suzukiDF6D4RestorationDecay
  push_cast
  ring

private theorem suzukiDF6D4ExpNegAStar_nonneg :
    0 ≤ Real.exp (-suzukiProjectAStar) :=
  (Real.exp_pos _).le

private theorem suzukiDF6D4ExpNegAStar_lt_one :
    Real.exp (-suzukiProjectAStar) < 1 := by
  rw [Real.exp_lt_one_iff]
  exact neg_lt_zero.mpr suzukiProjectAStar_pos

theorem suzukiDF6D4RestorationTerm_nonneg (mode k : Nat) :
    0 ≤ suzukiDF6D4RestorationTerm mode k := by
  unfold suzukiDF6D4RestorationTerm
  dsimp only
  positivity [suzukiProjectAStar_pos]

/-- Pointwise geometric majorant for the restoration tail.  The denominator
is frozen at the first omitted half-integer, exactly as in the certificate
script. -/
theorem suzukiDF6D4RestorationTerm_shift_le_geometric
    (mode N j : Nat) :
    suzukiDF6D4RestorationTerm mode (N + j) ≤
      (2 * ((mode : Real) * Real.pi / suzukiProjectAStar) *
          Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiDF6D4RestorationDecay N) ^ 2) *
        (Real.exp (-suzukiProjectAStar) ^ 4) ^ j := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let e : Real := Real.exp (-suzukiProjectAStar)
  let dN : Real := suzukiDF6D4RestorationDecay N
  let dJ : Real := suzukiDF6D4RestorationDecay (N + j)
  have hw : 0 ≤ w := by
    dsimp only [w]
    positivity [suzukiProjectAStar_pos]
  have he : 0 ≤ e := by
    dsimp only [e]
    exact suzukiDF6D4ExpNegAStar_nonneg
  have hdN : 0 < dN := by
    dsimp only [dN]
    unfold suzukiDF6D4RestorationDecay
    positivity
  have hdJ : 0 < dJ := by
    dsimp only [dJ]
    unfold suzukiDF6D4RestorationDecay
    positivity
  have hdle : dN ≤ dJ := by
    dsimp only [dN, dJ]
    unfold suzukiDF6D4RestorationDecay
    push_cast
    gcongr
    exact_mod_cast Nat.le_add_right N j
  have hden : dN ^ 2 ≤ dJ ^ 2 + w ^ 2 := by
    nlinarith [sq_nonneg w]
  have hnum : 0 ≤ 2 * w * e ^ (4 * (N + j) + 1) := by positivity
  have hdiv :
      2 * w * e ^ (4 * (N + j) + 1) / (dJ ^ 2 + w ^ 2) ≤
        2 * w * e ^ (4 * (N + j) + 1) / dN ^ 2 :=
    div_le_div_of_nonneg_left hnum (sq_pos_of_pos hdN) hden
  have hpow :
      e ^ (4 * (N + j) + 1) =
        e ^ (4 * N + 1) * (e ^ 4) ^ j := by
    rw [show 4 * (N + j) + 1 = (4 * N + 1) + 4 * j by omega,
      pow_add, ← pow_mul]
  unfold suzukiDF6D4RestorationTerm
  dsimp only
  rw [suzukiDF6D4Restoration_exp_eq_pow]
  change 2 * w * e ^ (4 * (N + j) + 1) / (dJ ^ 2 + w ^ 2) ≤ _
  rw [hpow] at hdiv
  rw [hpow]
  calc
    2 * w * (e ^ (4 * N + 1) * (e ^ 4) ^ j) /
          (dJ ^ 2 + w ^ 2) ≤
        2 * w * (e ^ (4 * N + 1) * (e ^ 4) ^ j) / dN ^ 2 := by
      simpa only [mul_assoc] using hdiv
    _ = (2 * w * e ^ (4 * N + 1) / dN ^ 2) * (e ^ 4) ^ j := by
      ring

theorem summable_suzukiDF6D4RestorationTail (mode N : Nat) :
    Summable (fun j : Nat => suzukiDF6D4RestorationTerm mode (N + j)) := by
  let C : Real :=
    2 * ((mode : Real) * Real.pi / suzukiProjectAStar) *
      Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
      (suzukiDF6D4RestorationDecay N) ^ 2
  let r : Real := Real.exp (-suzukiProjectAStar) ^ 4
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hr1 : r < 1 := by
    dsimp only [r]
    exact pow_lt_one₀ suzukiDF6D4ExpNegAStar_nonneg
      suzukiDF6D4ExpNegAStar_lt_one (by omega)
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hmajor : Summable (fun j : Nat => C * r ^ j) :=
    (summable_geometric_of_norm_lt_one hrnorm).mul_left C
  apply Summable.of_nonneg_of_le
    (fun j => suzukiDF6D4RestorationTerm_nonneg mode (N + j))
    (fun j => ?_) hmajor
  dsimp only [C, r]
  exact suzukiDF6D4RestorationTerm_shift_le_geometric mode N j

/-- Complete two-sided enclosure for the infinite restoration tail. -/
theorem suzukiDF6D4RestorationTail_bounds (mode N : Nat) :
    0 ≤ suzukiDF6D4RestorationTail mode N ∧
      suzukiDF6D4RestorationTail mode N ≤
        2 * ((mode : Real) * Real.pi / suzukiProjectAStar) *
          Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
          (suzukiDF6D4RestorationDecay N) ^ 2 /
          (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
  let C : Real :=
    2 * ((mode : Real) * Real.pi / suzukiProjectAStar) *
      Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
      (suzukiDF6D4RestorationDecay N) ^ 2
  let r : Real := Real.exp (-suzukiProjectAStar) ^ 4
  have hr0 : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hr1 : r < 1 := by
    dsimp only [r]
    exact pow_lt_one₀ suzukiDF6D4ExpNegAStar_nonneg
      suzukiDF6D4ExpNegAStar_lt_one (by omega)
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have htail := summable_suzukiDF6D4RestorationTail mode N
  have hgeom := (hasSum_geometric_of_norm_lt_one hrnorm).mul_left C
  constructor
  · unfold suzukiDF6D4RestorationTail
    exact tsum_nonneg fun j => suzukiDF6D4RestorationTerm_nonneg mode (N + j)
  · unfold suzukiDF6D4RestorationTail
    have hle := htail.tsum_le_tsum
      (fun j => suzukiDF6D4RestorationTerm_shift_le_geometric mode N j)
      hgeom.summable
    calc
      (∑' j : Nat, suzukiDF6D4RestorationTerm mode (N + j)) ≤
          ∑' j : Nat, C * r ^ j := hle
      _ = C * (1 - r)⁻¹ := hgeom.tsum_eq
      _ = 2 * ((mode : Real) * Real.pi / suzukiProjectAStar) *
            Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
            (suzukiDF6D4RestorationDecay N) ^ 2 /
            (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
        dsimp only [C, r]
        simp only [div_eq_mul_inv]

end

end RiemannHypothesisProject.Experiments.M100
