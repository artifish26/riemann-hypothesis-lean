import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointRestorationEnclosures

/-!
# Exact interval evaluator for the DF6D4 restoration series

This module instantiates the complete geometric-tail theorem with exact
rational interval arithmetic.  The frozen evaluator uses the unchanged 128
explicit restoration terms from the endpoint certificate script.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Exact rational version of the half-integer restoration decay. -/
def suzukiDF6D4RestorationDecayRat (k : Nat) : Rat :=
  2 * k + 1 / 2

/-- Dependency-safe interval for one positive restoration term. -/
def suzukiDF6D4RestorationTermInterval (mode k : Nat) : RationalInterval :=
  let W := suzukiDF6D4WaveNumberInterval mode
  let E := fineExpNegAStarInterval
  let EPow := E.powNonneg (4 * k + 1)
  let numerator := W.mulNonneg EPow
  let denominator :=
    (RationalInterval.point (suzukiDF6D4RestorationDecayRat k ^ 2)).add
      (W.powNonneg 2)
  RationalInterval.scale 2 (numerator.divNonneg denominator)

private theorem fineExpNegAStarInterval_lower_nonneg :
    0 ≤ fineExpNegAStarInterval.lower := by
  norm_num [fineExpNegAStarInterval]

private theorem suzukiDF6D4RestorationExpPower_lower_nonneg
    (k : Nat) :
    0 ≤ (fineExpNegAStarInterval.powNonneg
      (4 * k + 1)).lower := by
  unfold RationalInterval.powNonneg
  exact pow_nonneg fineExpNegAStarInterval_lower_nonneg _

private theorem suzukiDF6D4RestorationNumerator_lower_nonneg
    (mode k : Nat) :
    0 ≤ ((suzukiDF6D4WaveNumberInterval mode).mulNonneg
      (fineExpNegAStarInterval.powNonneg
        (4 * k + 1))).lower := by
  unfold RationalInterval.mulNonneg
  exact mul_nonneg (suzukiDF6D4WaveNumberInterval_lower_nonneg mode)
    (suzukiDF6D4RestorationExpPower_lower_nonneg k)

private theorem suzukiDF6D4RestorationDenominator_lower_pos
    (mode k : Nat) :
    0 < ((RationalInterval.point
          (suzukiDF6D4RestorationDecayRat k ^ 2)).add
        ((suzukiDF6D4WaveNumberInterval mode).powNonneg 2)).lower := by
  unfold RationalInterval.point RationalInterval.add RationalInterval.powNonneg
  dsimp only
  have hd : 0 < suzukiDF6D4RestorationDecayRat k := by
    unfold suzukiDF6D4RestorationDecayRat
    positivity
  nlinarith [sq_nonneg (suzukiDF6D4WaveNumberInterval mode).lower]

theorem suzukiDF6D4RestorationTermInterval_contains (mode k : Nat) :
    (suzukiDF6D4RestorationTermInterval mode k).Contains
      (suzukiDF6D4RestorationTerm mode k) := by
  let W := suzukiDF6D4WaveNumberInterval mode
  let E := fineExpNegAStarInterval
  let EPow := E.powNonneg (4 * k + 1)
  let numerator := W.mulNonneg EPow
  let denominator :=
    (RationalInterval.point (suzukiDF6D4RestorationDecayRat k ^ 2)).add
      (W.powNonneg 2)
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let e : Real := Real.exp (-suzukiProjectAStar)
  let d : Real := suzukiDF6D4RestorationDecay k
  have hW : W.Contains w := by
    dsimp only [W, w]
    exact suzukiDF6D4WaveNumberInterval_contains mode
  have hE : E.Contains e := by
    dsimp only [E, e]
    exact fineExpNegAStarInterval_contains
  have hEPow : EPow.Contains (e ^ (4 * k + 1)) := by
    dsimp only [EPow]
    exact RationalInterval.contains_powNonneg (4 * k + 1)
      fineExpNegAStarInterval_lower_nonneg hE
  have hNumerator : numerator.Contains (w * e ^ (4 * k + 1)) := by
    dsimp only [numerator]
    exact RationalInterval.contains_mulNonneg
      (suzukiDF6D4WaveNumberInterval_lower_nonneg mode)
      (suzukiDF6D4RestorationExpPower_lower_nonneg k) hW hEPow
  have hDecay :
      ((suzukiDF6D4RestorationDecayRat k : Rat) : Real) = d := by
    dsimp only [d]
    unfold suzukiDF6D4RestorationDecayRat suzukiDF6D4RestorationDecay
    norm_num
  have hDecaySq :
      ((suzukiDF6D4RestorationDecayRat k ^ 2 : Rat) : Real) = d ^ 2 := by
    norm_num
    rw [hDecay]
  have hDenominator : denominator.Contains (d ^ 2 + w ^ 2) := by
    dsimp only [denominator]
    have hPoint := RationalInterval.contains_point
      (suzukiDF6D4RestorationDecayRat k ^ 2)
    have hWSq := RationalInterval.contains_powNonneg 2
      (suzukiDF6D4WaveNumberInterval_lower_nonneg mode) hW
    have hAdd := RationalInterval.contains_add hPoint hWSq
    rw [hDecaySq] at hAdd
    exact hAdd
  have hBase := RationalInterval.contains_divNonneg
    (suzukiDF6D4RestorationNumerator_lower_nonneg mode k)
    (suzukiDF6D4RestorationDenominator_lower_pos mode k)
    hNumerator hDenominator
  have hScaled := RationalInterval.contains_scale 2 hBase
  unfold suzukiDF6D4RestorationTermInterval
  dsimp only [W, E, EPow, numerator, denominator] at hScaled ⊢
  unfold suzukiDF6D4RestorationTerm
  dsimp only
  rw [suzukiDF6D4Restoration_exp_eq_pow]
  convert hScaled using 1
  dsimp only [w, e, d]
  ring

/-- Outward-rounded fold of the first `N` restoration terms. -/
def suzukiDF6D4RestorationPartialInterval (D : Nat) :
    Nat → Nat → RationalInterval
  | _, 0 => RationalInterval.point 0
  | mode, N + 1 =>
      RationalInterval.roundOut D
        ((suzukiDF6D4RestorationPartialInterval D mode N).add
          (suzukiDF6D4RestorationTermInterval mode N))

theorem suzukiDF6D4RestorationPartialInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4RestorationPartialInterval D mode N).Contains
      (∑ k ∈ Finset.range N, suzukiDF6D4RestorationTerm mode k) := by
  induction N with
  | zero =>
      simpa [suzukiDF6D4RestorationPartialInterval] using
        RationalInterval.contains_point 0
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact RationalInterval.contains_roundOut hD
        (RationalInterval.contains_add ih
          (suzukiDF6D4RestorationTermInterval_contains mode N))

/-- Rational interval for the geometric bound on the tail beginning at `N`. -/
def suzukiDF6D4RestorationTailBoundInterval
    (mode N : Nat) : RationalInterval :=
  let W := suzukiDF6D4WaveNumberInterval mode
  let E := fineExpNegAStarInterval
  let numerator := W.mulNonneg (E.powNonneg (4 * N + 1))
  let first :=
    RationalInterval.scale 2
      (numerator.divNonneg
        (RationalInterval.point (suzukiDF6D4RestorationDecayRat N ^ 2)))
  let ratioDenominator :=
    (RationalInterval.point 1).sub (E.powNonneg 4)
  first.divNonneg ratioDenominator

private theorem suzukiDF6D4RestorationFirstBound_lower_nonneg
    (mode N : Nat) :
    0 ≤ (RationalInterval.scale 2
      (((suzukiDF6D4WaveNumberInterval mode).mulNonneg
        (fineExpNegAStarInterval.powNonneg (4 * N + 1))).divNonneg
          (RationalInterval.point
            (suzukiDF6D4RestorationDecayRat N ^ 2)))).lower := by
  unfold RationalInterval.scale RationalInterval.divNonneg
    RationalInterval.mulNonneg RationalInterval.invPos RationalInterval.point
  dsimp only
  have hW := suzukiDF6D4WaveNumberInterval_lower_nonneg mode
  have hE := suzukiDF6D4RestorationExpPower_lower_nonneg N
  have hWContains := suzukiDF6D4WaveNumberInterval_contains mode
  have hw0 : 0 ≤ (mode : Real) * Real.pi / suzukiProjectAStar := by
    positivity [suzukiProjectAStar_pos]
  have hWUpperReal :
      (0 : Real) ≤ ((suzukiDF6D4WaveNumberInterval mode).upper : Real) :=
    hw0.trans hWContains.2
  have hWUpper : 0 ≤ (suzukiDF6D4WaveNumberInterval mode).upper := by
    exact_mod_cast hWUpperReal
  have hEContains := fineExpNegAStarInterval_contains
  have hEUpperReal :
      (0 : Real) ≤ (fineExpNegAStarInterval.upper : Real) :=
    (Real.exp_pos _).le.trans hEContains.2
  have hEUpper : 0 ≤ fineExpNegAStarInterval.upper := by
    exact_mod_cast hEUpperReal
  have hEPowUpper :
      0 ≤ (fineExpNegAStarInterval.powNonneg
        (4 * N + 1)).upper := by
    unfold RationalInterval.powNonneg
    exact pow_nonneg hEUpper _
  have hd : 0 < suzukiDF6D4RestorationDecayRat N := by
    unfold suzukiDF6D4RestorationDecayRat
    positivity
  apply le_min
  · positivity
  · positivity

private theorem suzukiDF6D4RestorationRatioDenominator_lower_pos :
    0 < ((RationalInterval.point 1).sub
      (fineExpNegAStarInterval.powNonneg 4)).lower := by
  norm_num [RationalInterval.point, RationalInterval.sub,
    RationalInterval.add, RationalInterval.neg, RationalInterval.powNonneg,
    fineExpNegAStarInterval]

theorem suzukiDF6D4RestorationTailBoundInterval_contains (mode N : Nat) :
    (suzukiDF6D4RestorationTailBoundInterval mode N).Contains
      (2 * ((mode : Real) * Real.pi / suzukiProjectAStar) *
        Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
        (suzukiDF6D4RestorationDecay N) ^ 2 /
        (1 - Real.exp (-suzukiProjectAStar) ^ 4)) := by
  let W := suzukiDF6D4WaveNumberInterval mode
  let E := fineExpNegAStarInterval
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  let e : Real := Real.exp (-suzukiProjectAStar)
  let d : Real := suzukiDF6D4RestorationDecay N
  have hW : W.Contains w := by
    dsimp only [W, w]
    exact suzukiDF6D4WaveNumberInterval_contains mode
  have hE : E.Contains e := by
    dsimp only [E, e]
    exact fineExpNegAStarInterval_contains
  have hEPow : (E.powNonneg (4 * N + 1)).Contains (e ^ (4 * N + 1)) := by
    exact RationalInterval.contains_powNonneg (4 * N + 1)
      fineExpNegAStarInterval_lower_nonneg hE
  have hNumerator := RationalInterval.contains_mulNonneg
    (suzukiDF6D4WaveNumberInterval_lower_nonneg mode)
    (suzukiDF6D4RestorationExpPower_lower_nonneg N) hW hEPow
  have hDecay :
      ((suzukiDF6D4RestorationDecayRat N : Rat) : Real) = d := by
    dsimp only [d]
    unfold suzukiDF6D4RestorationDecayRat suzukiDF6D4RestorationDecay
    norm_num
  have hDecaySq :
      ((suzukiDF6D4RestorationDecayRat N ^ 2 : Rat) : Real) = d ^ 2 := by
    norm_num
    rw [hDecay]
  have hFirstBase := RationalInterval.contains_divNonneg
    (suzukiDF6D4RestorationNumerator_lower_nonneg mode N)
    (by
      unfold RationalInterval.point
      dsimp only
      have hd : 0 < suzukiDF6D4RestorationDecayRat N := by
        unfold suzukiDF6D4RestorationDecayRat
        positivity
      positivity)
    hNumerator (RationalInterval.contains_point
      (suzukiDF6D4RestorationDecayRat N ^ 2))
  rw [hDecaySq] at hFirstBase
  have hFirst := RationalInterval.contains_scale 2 hFirstBase
  have hRatioPower := RationalInterval.contains_powNonneg 4
    fineExpNegAStarInterval_lower_nonneg hE
  have hRatioDenominator := RationalInterval.contains_sub
    (RationalInterval.contains_point 1) hRatioPower
  have hBound := RationalInterval.contains_divNonneg
    (suzukiDF6D4RestorationFirstBound_lower_nonneg mode N)
    suzukiDF6D4RestorationRatioDenominator_lower_pos
    hFirst hRatioDenominator
  unfold suzukiDF6D4RestorationTailBoundInterval
  dsimp only [W, E] at hBound ⊢
  convert hBound using 1
  dsimp only [w, e, d]
  ring

/-- Tail enclosure using zero as the exact lower endpoint and the proved
geometric bound as the upper endpoint. -/
def suzukiDF6D4RestorationTailInterval
    (mode N : Nat) : RationalInterval :=
  ⟨0, (suzukiDF6D4RestorationTailBoundInterval mode N).upper⟩

theorem suzukiDF6D4RestorationTailInterval_contains (mode N : Nat) :
    (suzukiDF6D4RestorationTailInterval mode N).Contains
      (suzukiDF6D4RestorationTail mode N) := by
  have hTail := suzukiDF6D4RestorationTail_bounds mode N
  have hBound := suzukiDF6D4RestorationTailBoundInterval_contains mode N
  unfold suzukiDF6D4RestorationTailInterval RationalInterval.Contains
  norm_num
  exact ⟨hTail.1, hTail.2.trans hBound.2⟩

/-- Complete finite-prefix plus infinite-tail restoration evaluator. -/
def suzukiDF6D4RestorationInterval
    (D mode N : Nat) : RationalInterval :=
  (suzukiDF6D4RestorationPartialInterval D mode N).add
    (suzukiDF6D4RestorationTailInterval mode N)

theorem suzukiDF6D4RestorationInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4RestorationInterval D mode N).Contains
      (∑' k : Nat, suzukiDF6D4RestorationTerm mode k) := by
  have hPartial := suzukiDF6D4RestorationPartialInterval_contains D mode N hD
  have hTail := suzukiDF6D4RestorationTailInterval_contains mode N
  have hAdd := RationalInterval.contains_add hPartial hTail
  have hsum : Summable
      (fun k : Nat => suzukiDF6D4RestorationTerm mode k) := by
    simpa only [Nat.zero_add] using
      summable_suzukiDF6D4RestorationTail mode 0
  have hsplit :
      (∑ k ∈ Finset.range N, suzukiDF6D4RestorationTerm mode k) +
          suzukiDF6D4RestorationTail mode N =
        ∑' k : Nat, suzukiDF6D4RestorationTerm mode k := by
    unfold suzukiDF6D4RestorationTail
    convert hsum.sum_add_tsum_nat_add N using 1
    congr 1
    · apply tsum_congr
      intro k
      congr 1
      omega
  unfold suzukiDF6D4RestorationInterval
  rw [← hsplit]
  exact hAdd

/-- Frozen 128-term restoration evaluator on a `10^-16` output grid. -/
def suzukiDF6D4FrozenRestorationInterval (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4RestorationInterval 1000000000000000000 mode 128)

theorem suzukiDF6D4FrozenRestorationInterval_contains (mode : Nat) :
    (suzukiDF6D4FrozenRestorationInterval mode).Contains
    (∑' k : Nat, suzukiDF6D4RestorationTerm mode k) := by
  unfold suzukiDF6D4FrozenRestorationInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4RestorationInterval_contains
      1000000000000000000 mode 128 (by norm_num))

end

end RiemannHypothesisProject.Experiments.M100
