import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDiagonalGammaEnclosures

/-!
# Exact interval evaluator for the M100-DF6D4 diagonal entries

This module evaluates the nonnegative fourth-order Gamma terms and their
proved complete tails with exact rational interval arithmetic.  The frozen
prefix is the unchanged 16,384-term prefix used by the external Arb
reproduction.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

def suzukiDF6D4DiagonalDecayRatEval (n : Nat) : Rat :=
  2 * n + 1 / 2

def suzukiDF6D4DiagonalFrequencyInterval (mode : Nat) : RationalInterval :=
  RationalInterval.scale (mode : Rat) suzukiDF6D4PiInterval

private theorem suzukiDF6D4DiagonalDecayRatEval_pos (n : Nat) :
    0 < suzukiDF6D4DiagonalDecayRatEval n := by
  unfold suzukiDF6D4DiagonalDecayRatEval
  positivity

private theorem suzukiDF6D4DiagonalDecayRatEval_cast (n : Nat) :
    ((suzukiDF6D4DiagonalDecayRatEval n : Rat) : Real) =
      suzukiDF6D4DiagonalDecay n := by
  unfold suzukiDF6D4DiagonalDecayRatEval suzukiDF6D4DiagonalDecay
  norm_num

private theorem fineAStarInterval_lower_pos :
    0 < fineAStarInterval.lower := by
  norm_num [fineAStarInterval]

private theorem suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg
    (mode : Nat) :
    0 ≤ (suzukiDF6D4DiagonalFrequencyInterval mode).lower := by
  unfold suzukiDF6D4DiagonalFrequencyInterval RationalInterval.scale
    suzukiDF6D4PiInterval
  dsimp only
  rw [le_min_iff]
  constructor <;> positivity

theorem suzukiDF6D4DiagonalFrequencyInterval_contains (mode : Nat) :
    (suzukiDF6D4DiagonalFrequencyInterval mode).Contains
      (suzukiDF6D4DiagonalFrequency mode) := by
  unfold suzukiDF6D4DiagonalFrequencyInterval
    suzukiDF6D4DiagonalFrequency
  simpa only [Rat.cast_natCast] using
    RationalInterval.contains_scale (mode : Rat)
      suzukiDF6D4PiInterval_contains

private def suzukiDF6D4DiagonalXInterval (n : Nat) : RationalInterval :=
  fineAStarInterval.mulNonneg
    (RationalInterval.point (suzukiDF6D4DiagonalDecayRatEval n))

private def suzukiDF6D4DiagonalYInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2

private def suzukiDF6D4DiagonalDInterval (mode n : Nat) : RationalInterval :=
  (suzukiDF6D4DiagonalXInterval n).powNonneg 2 |>.add
    (suzukiDF6D4DiagonalYInterval mode)

private theorem suzukiDF6D4DiagonalXInterval_lower_pos (n : Nat) :
    0 < (suzukiDF6D4DiagonalXInterval n).lower := by
  unfold suzukiDF6D4DiagonalXInterval RationalInterval.mulNonneg
    RationalInterval.point
  dsimp only
  exact mul_pos fineAStarInterval_lower_pos
    (suzukiDF6D4DiagonalDecayRatEval_pos n)

private theorem suzukiDF6D4DiagonalYInterval_lower_nonneg (mode : Nat) :
    0 ≤ (suzukiDF6D4DiagonalYInterval mode).lower := by
  unfold suzukiDF6D4DiagonalYInterval RationalInterval.powNonneg
  exact pow_nonneg
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2

private theorem suzukiDF6D4DiagonalDInterval_lower_pos (mode n : Nat) :
    0 < (suzukiDF6D4DiagonalDInterval mode n).lower := by
  unfold suzukiDF6D4DiagonalDInterval RationalInterval.add
    RationalInterval.powNonneg
  dsimp only
  nlinarith [sq_pos_of_pos (suzukiDF6D4DiagonalXInterval_lower_pos n),
    suzukiDF6D4DiagonalYInterval_lower_nonneg mode]

private theorem suzukiDF6D4DiagonalXInterval_contains (n : Nat) :
    (suzukiDF6D4DiagonalXInterval n).Contains
      (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) := by
  have h := RationalInterval.contains_mulNonneg
    (by exact fineAStarInterval_lower_pos.le)
    (by
      unfold RationalInterval.point
      exact (suzukiDF6D4DiagonalDecayRatEval_pos n).le)
    fineAStarInterval_contains
    (RationalInterval.contains_point (suzukiDF6D4DiagonalDecayRatEval n))
  rw [suzukiDF6D4DiagonalDecayRatEval_cast] at h
  exact h

private theorem suzukiDF6D4DiagonalYInterval_contains (mode : Nat) :
    (suzukiDF6D4DiagonalYInterval mode).Contains
      (suzukiDF6D4DiagonalFrequency mode ^ 2) := by
  exact RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)

private theorem suzukiDF6D4DiagonalDInterval_contains (mode n : Nat) :
    (suzukiDF6D4DiagonalDInterval mode n).Contains
      ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 +
        suzukiDF6D4DiagonalFrequency mode ^ 2) := by
  exact RationalInterval.contains_add
    (RationalInterval.contains_powNonneg 2
      (suzukiDF6D4DiagonalXInterval_lower_pos n).le
      (suzukiDF6D4DiagonalXInterval_contains n))
    (suzukiDF6D4DiagonalYInterval_contains mode)

private def suzukiDF6D4EvenDiagonalBasePolynomialInterval
    (mode n : Nat) : RationalInterval :=
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  (RationalInterval.scale 2 (X.powNonneg 3)).add
    ((X.powNonneg 2).mulNonneg Y) |>.add
    (X.mulNonneg Y) |>.add
    (Y.powNonneg 2)

private def suzukiDF6D4OddDiagonalBasePolynomialInterval
    (mode n : Nat) : RationalInterval :=
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  (X.powNonneg 3).add ((X.powNonneg 2).mulNonneg Y) |>.add
    (Y.powNonneg 2)

private theorem suzukiDF6D4EvenDiagonalBasePolynomialInterval_lower_nonneg
    (mode n : Nat) :
    0 ≤ (suzukiDF6D4EvenDiagonalBasePolynomialInterval mode n).lower := by
  unfold suzukiDF6D4EvenDiagonalBasePolynomialInterval
    RationalInterval.add RationalInterval.scale RationalInterval.powNonneg
    RationalInterval.mulNonneg
  dsimp only
  have hx := (suzukiDF6D4DiagonalXInterval_lower_pos n).le
  have hy := suzukiDF6D4DiagonalYInterval_lower_nonneg mode
  have h2x :
      0 ≤ min (2 * (suzukiDF6D4DiagonalXInterval n).lower ^ 3)
        (2 * (suzukiDF6D4DiagonalXInterval n).upper ^ 3) := by
    rw [le_min_iff]
    constructor
    · positivity
    · have hcontains := suzukiDF6D4DiagonalXInterval_contains n
      have hupper : 0 ≤ (suzukiDF6D4DiagonalXInterval n).upper := by
        have hxReal : 0 ≤
            suzukiProjectAStar * suzukiDF6D4DiagonalDecay n := by
          apply mul_nonneg suzukiProjectAStar_pos.le
          unfold suzukiDF6D4DiagonalDecay
          positivity
        have huReal : (0 : Real) ≤
            ((suzukiDF6D4DiagonalXInterval n).upper : Real) :=
          hxReal.trans hcontains.2
        exact_mod_cast huReal
      positivity
  positivity

private theorem suzukiDF6D4OddDiagonalBasePolynomialInterval_lower_nonneg
    (mode n : Nat) :
    0 ≤ (suzukiDF6D4OddDiagonalBasePolynomialInterval mode n).lower := by
  unfold suzukiDF6D4OddDiagonalBasePolynomialInterval
    RationalInterval.add RationalInterval.powNonneg
    RationalInterval.mulNonneg
  dsimp only
  have hx := (suzukiDF6D4DiagonalXInterval_lower_pos n).le
  have hy := suzukiDF6D4DiagonalYInterval_lower_nonneg mode
  positivity

private theorem suzukiDF6D4EvenDiagonalBasePolynomialInterval_contains
    (mode n : Nat) :
    (suzukiDF6D4EvenDiagonalBasePolynomialInterval mode n).Contains
      (2 * (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 3 +
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 *
          suzukiDF6D4DiagonalFrequency mode ^ 2 +
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) *
          suzukiDF6D4DiagonalFrequency mode ^ 2 +
        (suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2) := by
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  have hX := suzukiDF6D4DiagonalXInterval_contains n
  have hY := suzukiDF6D4DiagonalYInterval_contains mode
  have hX2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le hX
  have hX3 := RationalInterval.contains_powNonneg 3
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le hX
  have hY2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode) hY
  have hX2Y := RationalInterval.contains_mulNonneg
    (by unfold RationalInterval.powNonneg; positivity)
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode) hX2 hY
  have hXY := RationalInterval.contains_mulNonneg
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode) hX hY
  have h := RationalInterval.contains_add
    (RationalInterval.contains_add
      (RationalInterval.contains_add
        (RationalInterval.contains_scale 2 hX3) hX2Y) hXY) hY2
  unfold suzukiDF6D4EvenDiagonalBasePolynomialInterval
  dsimp only [X, Y] at h ⊢
  convert h using 1 <;> ring

private theorem suzukiDF6D4OddDiagonalBasePolynomialInterval_contains
    (mode n : Nat) :
    (suzukiDF6D4OddDiagonalBasePolynomialInterval mode n).Contains
      ((suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 3 +
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay n) ^ 2 *
          suzukiDF6D4DiagonalFrequency mode ^ 2 +
        (suzukiDF6D4DiagonalFrequency mode ^ 2) ^ 2) := by
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  have hX := suzukiDF6D4DiagonalXInterval_contains n
  have hY := suzukiDF6D4DiagonalYInterval_contains mode
  have hX2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le hX
  have hX3 := RationalInterval.contains_powNonneg 3
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le hX
  have hY2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode) hY
  have hX2Y := RationalInterval.contains_mulNonneg
    (by unfold RationalInterval.powNonneg; positivity)
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode) hX2 hY
  have h := RationalInterval.contains_add
    (RationalInterval.contains_add hX3 hX2Y) hY2
  unfold suzukiDF6D4OddDiagonalBasePolynomialInterval
  dsimp only [X, Y] at h ⊢
  convert h using 1 <;> ring

def suzukiDF6D4EvenDiagonalBaseTermInterval
    (mode n : Nat) : RationalInterval :=
  let A := fineAStarInterval
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  let D := suzukiDF6D4DiagonalDInterval mode n
  let P := suzukiDF6D4EvenDiagonalBasePolynomialInterval mode n
  let numerator := (A.mulNonneg Y).mulNonneg P
  let denominator := (X.powNonneg 3).mulNonneg (D.powNonneg 2)
  numerator.divNonneg denominator

def suzukiDF6D4OddDiagonalBaseTermInterval
    (mode n : Nat) : RationalInterval :=
  let A := fineAStarInterval
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  let D := suzukiDF6D4DiagonalDInterval mode n
  let P := suzukiDF6D4OddDiagonalBasePolynomialInterval mode n
  let numerator := (A.mulNonneg Y).mulNonneg P
  let denominator := (X.powNonneg 3).mulNonneg (D.powNonneg 2)
  numerator.divNonneg denominator

private theorem suzukiDF6D4EvenDiagonalBaseNumerator_lower_nonneg
    (mode n : Nat) :
    0 ≤ ((fineAStarInterval.mulNonneg
        (suzukiDF6D4DiagonalYInterval mode)).mulNonneg
      (suzukiDF6D4EvenDiagonalBasePolynomialInterval mode n)).lower := by
  unfold RationalInterval.mulNonneg
  dsimp only
  have ha := fineAStarInterval_lower_pos.le
  have hy := suzukiDF6D4DiagonalYInterval_lower_nonneg mode
  have hp :=
    suzukiDF6D4EvenDiagonalBasePolynomialInterval_lower_nonneg mode n
  exact mul_nonneg (mul_nonneg ha hy) hp

private theorem suzukiDF6D4OddDiagonalBaseNumerator_lower_nonneg
    (mode n : Nat) :
    0 ≤ ((fineAStarInterval.mulNonneg
        (suzukiDF6D4DiagonalYInterval mode)).mulNonneg
      (suzukiDF6D4OddDiagonalBasePolynomialInterval mode n)).lower := by
  unfold RationalInterval.mulNonneg
  dsimp only
  have ha := fineAStarInterval_lower_pos.le
  have hy := suzukiDF6D4DiagonalYInterval_lower_nonneg mode
  have hp :=
    suzukiDF6D4OddDiagonalBasePolynomialInterval_lower_nonneg mode n
  exact mul_nonneg (mul_nonneg ha hy) hp

private theorem suzukiDF6D4DiagonalBaseDenominator_lower_pos
    (mode n : Nat) :
    0 < ((suzukiDF6D4DiagonalXInterval n).powNonneg 3 |>.mulNonneg
      ((suzukiDF6D4DiagonalDInterval mode n).powNonneg 2)).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.powNonneg
  dsimp only
  exact mul_pos
    (pow_pos (suzukiDF6D4DiagonalXInterval_lower_pos n) 3)
    (pow_pos (suzukiDF6D4DiagonalDInterval_lower_pos mode n) 2)

theorem suzukiDF6D4EvenDiagonalBaseTermInterval_contains (mode n : Nat) :
    (suzukiDF6D4EvenDiagonalBaseTermInterval mode n).Contains
      (suzukiDF6D4EvenDiagonalBaseTerm mode n) := by
  let A := fineAStarInterval
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  let D := suzukiDF6D4DiagonalDInterval mode n
  let P := suzukiDF6D4EvenDiagonalBasePolynomialInterval mode n
  have hAY := RationalInterval.contains_mulNonneg
    fineAStarInterval_lower_pos.le
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode)
    fineAStarInterval_contains
    (suzukiDF6D4DiagonalYInterval_contains mode)
  have hNumerator := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.mulNonneg
      exact mul_nonneg fineAStarInterval_lower_pos.le
        (suzukiDF6D4DiagonalYInterval_lower_nonneg mode))
    (suzukiDF6D4EvenDiagonalBasePolynomialInterval_lower_nonneg mode n)
    hAY (suzukiDF6D4EvenDiagonalBasePolynomialInterval_contains mode n)
  have hX3 := RationalInterval.contains_powNonneg 3
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le
    (suzukiDF6D4DiagonalXInterval_contains n)
  have hD2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalDInterval_lower_pos mode n).le
    (suzukiDF6D4DiagonalDInterval_contains mode n)
  have hDenominator := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg (suzukiDF6D4DiagonalXInterval_lower_pos n).le 3)
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg
        (suzukiDF6D4DiagonalDInterval_lower_pos mode n).le 2) hX3 hD2
  have h := RationalInterval.contains_divNonneg
    (suzukiDF6D4EvenDiagonalBaseNumerator_lower_nonneg mode n)
    (suzukiDF6D4DiagonalBaseDenominator_lower_pos mode n)
    hNumerator hDenominator
  unfold suzukiDF6D4EvenDiagonalBaseTermInterval
    suzukiDF6D4EvenDiagonalBaseTerm
  dsimp only [A, X, Y, D, P] at h ⊢
  convert h using 1 <;> ring

theorem suzukiDF6D4OddDiagonalBaseTermInterval_contains (mode n : Nat) :
    (suzukiDF6D4OddDiagonalBaseTermInterval mode n).Contains
      (suzukiDF6D4OddDiagonalBaseTerm mode n) := by
  let A := fineAStarInterval
  let X := suzukiDF6D4DiagonalXInterval n
  let Y := suzukiDF6D4DiagonalYInterval mode
  let D := suzukiDF6D4DiagonalDInterval mode n
  let P := suzukiDF6D4OddDiagonalBasePolynomialInterval mode n
  have hAY := RationalInterval.contains_mulNonneg
    fineAStarInterval_lower_pos.le
    (suzukiDF6D4DiagonalYInterval_lower_nonneg mode)
    fineAStarInterval_contains
    (suzukiDF6D4DiagonalYInterval_contains mode)
  have hNumerator := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.mulNonneg
      exact mul_nonneg fineAStarInterval_lower_pos.le
        (suzukiDF6D4DiagonalYInterval_lower_nonneg mode))
    (suzukiDF6D4OddDiagonalBasePolynomialInterval_lower_nonneg mode n)
    hAY (suzukiDF6D4OddDiagonalBasePolynomialInterval_contains mode n)
  have hX3 := RationalInterval.contains_powNonneg 3
    (suzukiDF6D4DiagonalXInterval_lower_pos n).le
    (suzukiDF6D4DiagonalXInterval_contains n)
  have hD2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalDInterval_lower_pos mode n).le
    (suzukiDF6D4DiagonalDInterval_contains mode n)
  have hDenominator := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg (suzukiDF6D4DiagonalXInterval_lower_pos n).le 3)
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg
        (suzukiDF6D4DiagonalDInterval_lower_pos mode n).le 2) hX3 hD2
  have h := RationalInterval.contains_divNonneg
    (suzukiDF6D4OddDiagonalBaseNumerator_lower_nonneg mode n)
    (suzukiDF6D4DiagonalBaseDenominator_lower_pos mode n)
    hNumerator hDenominator
  unfold suzukiDF6D4OddDiagonalBaseTermInterval
    suzukiDF6D4OddDiagonalBaseTerm
  dsimp only [A, X, Y, D, P] at h ⊢
  convert h using 1 <;> ring

def suzukiDF6D4EvenDiagonalBasePartialInterval (D : Nat) :
    Nat → Nat → RationalInterval
  | _, 0 => RationalInterval.point 0
  | mode, N + 1 => RationalInterval.roundOut D
      ((suzukiDF6D4EvenDiagonalBasePartialInterval D mode N).add
        (suzukiDF6D4EvenDiagonalBaseTermInterval mode N))

def suzukiDF6D4OddDiagonalBasePartialInterval (D : Nat) :
    Nat → Nat → RationalInterval
  | _, 0 => RationalInterval.point 0
  | mode, N + 1 => RationalInterval.roundOut D
      ((suzukiDF6D4OddDiagonalBasePartialInterval D mode N).add
        (suzukiDF6D4OddDiagonalBaseTermInterval mode N))

theorem suzukiDF6D4EvenDiagonalBasePartialInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4EvenDiagonalBasePartialInterval D mode N).Contains
      (∑ n ∈ Finset.range N, suzukiDF6D4EvenDiagonalBaseTerm mode n) := by
  induction N with
  | zero =>
      simpa [suzukiDF6D4EvenDiagonalBasePartialInterval] using
        RationalInterval.contains_point 0
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact RationalInterval.contains_roundOut hD
        (RationalInterval.contains_add ih
          (suzukiDF6D4EvenDiagonalBaseTermInterval_contains mode N))

theorem suzukiDF6D4OddDiagonalBasePartialInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4OddDiagonalBasePartialInterval D mode N).Contains
      (∑ n ∈ Finset.range N, suzukiDF6D4OddDiagonalBaseTerm mode n) := by
  induction N with
  | zero =>
      simpa [suzukiDF6D4OddDiagonalBasePartialInterval] using
        RationalInterval.contains_point 0
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact RationalInterval.contains_roundOut hD
        (RationalInterval.contains_add ih
          (suzukiDF6D4OddDiagonalBaseTermInterval_contains mode N))

def suzukiDF6D4DiagonalThirdBoundInterval (mode : Nat) : RationalInterval :=
  let F := suzukiDF6D4DiagonalFrequencyInterval mode
  let numerator := (RationalInterval.scale 2 (F.powNonneg 3)).add
    (RationalInterval.scale 3 (F.powNonneg 2))
  numerator.divNonneg (fineAStarInterval.powNonneg 3)

private theorem suzukiDF6D4DiagonalThirdNumerator_lower_nonneg
    (mode : Nat) :
    0 ≤ ((RationalInterval.scale 2
        ((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 3)).add
      (RationalInterval.scale 3
        ((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2))).lower := by
  unfold RationalInterval.add RationalInterval.scale
    RationalInterval.powNonneg
  dsimp only
  have hf := suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode
  have hcontains := suzukiDF6D4DiagonalFrequencyInterval_contains mode
  have hupper : 0 ≤ (suzukiDF6D4DiagonalFrequencyInterval mode).upper := by
    have hfReal : 0 ≤ suzukiDF6D4DiagonalFrequency mode := by
      unfold suzukiDF6D4DiagonalFrequency
      positivity
    have huReal : (0 : Real) ≤
        ((suzukiDF6D4DiagonalFrequencyInterval mode).upper : Real) :=
      hfReal.trans hcontains.2
    exact_mod_cast huReal
  apply add_nonneg <;> rw [le_min_iff] <;> constructor <;> positivity

private theorem fineAStarCubeInterval_lower_pos :
    0 < (fineAStarInterval.powNonneg 3).lower := by
  unfold RationalInterval.powNonneg
  positivity [fineAStarInterval_lower_pos]

theorem suzukiDF6D4DiagonalThirdBoundInterval_contains (mode : Nat) :
    (suzukiDF6D4DiagonalThirdBoundInterval mode).Contains
      (suzukiDF6D4DiagonalThirdBound mode) := by
  have hF := suzukiDF6D4DiagonalFrequencyInterval_contains mode
  have hF2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) hF
  have hF3 := RationalInterval.contains_powNonneg 3
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) hF
  have hNumerator := RationalInterval.contains_add
    (RationalInterval.contains_scale 2 hF3)
    (RationalInterval.contains_scale 3 hF2)
  have hA3 := RationalInterval.contains_powNonneg 3
    fineAStarInterval_lower_pos.le fineAStarInterval_contains
  have h := RationalInterval.contains_divNonneg
    (suzukiDF6D4DiagonalThirdNumerator_lower_nonneg mode)
    fineAStarCubeInterval_lower_pos hNumerator hA3
  unfold suzukiDF6D4DiagonalThirdBoundInterval
    suzukiDF6D4DiagonalThirdBound
  dsimp only at h ⊢
  convert h using 1 <;> ring

def suzukiDF6D4DiagonalFourthTailFactorRat (N : Nat) : Rat :=
  1 / suzukiDF6D4DiagonalDecayRatEval N ^ 4 +
    1 / (6 * suzukiDF6D4DiagonalDecayRatEval N ^ 3)

def suzukiDF6D4DiagonalBaseTailBoundInterval
    (mode N : Nat) : RationalInterval :=
  (suzukiDF6D4DiagonalThirdBoundInterval mode).mulNonneg
    (RationalInterval.point (suzukiDF6D4DiagonalFourthTailFactorRat N))

private theorem suzukiDF6D4DiagonalThirdBoundInterval_lower_nonneg
    (mode : Nat) :
    0 ≤ (suzukiDF6D4DiagonalThirdBoundInterval mode).lower := by
  unfold suzukiDF6D4DiagonalThirdBoundInterval
    RationalInterval.divNonneg RationalInterval.mulNonneg
    RationalInterval.invPos
  dsimp only
  have hn := suzukiDF6D4DiagonalThirdNumerator_lower_nonneg mode
  have hdenUpper : 0 ≤ (fineAStarInterval.powNonneg 3).upper := by
    unfold RationalInterval.powNonneg fineAStarInterval
    norm_num
  exact mul_nonneg hn (inv_nonneg.mpr hdenUpper)

private theorem suzukiDF6D4DiagonalFourthTailFactorRat_nonneg (N : Nat) :
    0 ≤ suzukiDF6D4DiagonalFourthTailFactorRat N := by
  unfold suzukiDF6D4DiagonalFourthTailFactorRat
  have hd := (suzukiDF6D4DiagonalDecayRatEval_pos N).le
  exact add_nonneg
    (one_div_nonneg.mpr (pow_nonneg hd 4))
    (one_div_nonneg.mpr (mul_nonneg (by norm_num) (pow_nonneg hd 3)))

theorem suzukiDF6D4DiagonalBaseTailBoundInterval_contains (mode N : Nat) :
    (suzukiDF6D4DiagonalBaseTailBoundInterval mode N).Contains
      (suzukiDF6D4DiagonalThirdBound mode *
        (1 / suzukiDF6D4DiagonalDecay N ^ 4 +
          1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3))) := by
  have h := RationalInterval.contains_mulNonneg
    (suzukiDF6D4DiagonalThirdBoundInterval_lower_nonneg mode)
    (by
      unfold RationalInterval.point
      exact suzukiDF6D4DiagonalFourthTailFactorRat_nonneg N)
    (suzukiDF6D4DiagonalThirdBoundInterval_contains mode)
    (RationalInterval.contains_point
      (suzukiDF6D4DiagonalFourthTailFactorRat N))
  unfold suzukiDF6D4DiagonalBaseTailBoundInterval
    suzukiDF6D4DiagonalFourthTailFactorRat at h ⊢
  have hfactor :
      (((1 / suzukiDF6D4DiagonalDecayRatEval N ^ 4 +
          1 / (6 * suzukiDF6D4DiagonalDecayRatEval N ^ 3) : Rat)) : Real) =
        1 / suzukiDF6D4DiagonalDecay N ^ 4 +
          1 / (6 * suzukiDF6D4DiagonalDecay N ^ 3) := by
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat]
    rw [suzukiDF6D4DiagonalDecayRatEval_cast]
  rw [hfactor] at h
  exact h

def suzukiDF6D4EvenDiagonalBaseTailInterval
    (mode N : Nat) : RationalInterval :=
  ⟨0, (suzukiDF6D4DiagonalBaseTailBoundInterval mode N).upper⟩

def suzukiDF6D4OddDiagonalBaseTailInterval
    (mode N : Nat) : RationalInterval :=
  ⟨0, (suzukiDF6D4DiagonalBaseTailBoundInterval mode N).upper⟩

theorem suzukiDF6D4EvenDiagonalBaseTailInterval_contains (mode N : Nat) :
    (suzukiDF6D4EvenDiagonalBaseTailInterval mode N).Contains
      (suzukiDF6D4EvenDiagonalBaseTail mode N) := by
  have htail := suzukiDF6D4EvenDiagonalBaseTail_bounds mode N
  have hbound := suzukiDF6D4DiagonalBaseTailBoundInterval_contains mode N
  unfold suzukiDF6D4EvenDiagonalBaseTailInterval RationalInterval.Contains
  norm_num
  exact ⟨htail.1, htail.2.trans hbound.2⟩

theorem suzukiDF6D4OddDiagonalBaseTailInterval_contains
    (mode N : Nat) (hmode : 0 < mode) :
    (suzukiDF6D4OddDiagonalBaseTailInterval mode N).Contains
      (suzukiDF6D4OddDiagonalBaseTail mode N) := by
  have htail := suzukiDF6D4OddDiagonalBaseTail_bounds mode N hmode
  have hbound := suzukiDF6D4DiagonalBaseTailBoundInterval_contains mode N
  unfold suzukiDF6D4OddDiagonalBaseTailInterval RationalInterval.Contains
  norm_num
  exact ⟨htail.1, htail.2.trans hbound.2⟩

def suzukiDF6D4EvenDiagonalBaseInterval
    (D mode N : Nat) : RationalInterval :=
  (suzukiDF6D4EvenDiagonalBasePartialInterval D mode N).add
    (suzukiDF6D4EvenDiagonalBaseTailInterval mode N)

def suzukiDF6D4OddDiagonalBaseInterval
    (D mode N : Nat) : RationalInterval :=
  (suzukiDF6D4OddDiagonalBasePartialInterval D mode N).add
    (suzukiDF6D4OddDiagonalBaseTailInterval mode N)

theorem suzukiDF6D4EvenDiagonalBaseInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4EvenDiagonalBaseInterval D mode N).Contains
      (∑' n : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode n) := by
  have hPartial :=
    suzukiDF6D4EvenDiagonalBasePartialInterval_contains D mode N hD
  have hTail := suzukiDF6D4EvenDiagonalBaseTailInterval_contains mode N
  have hAdd := RationalInterval.contains_add hPartial hTail
  have hsplit := (summable_suzukiDF6D4EvenDiagonalBaseTerm mode).sum_add_tsum_nat_add N
  have hsplit' :
      (∑ n ∈ Finset.range N, suzukiDF6D4EvenDiagonalBaseTerm mode n) +
          (∑' n : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode (N + n)) =
        ∑' n : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode n := by
    simpa only [Nat.add_comm] using hsplit
  unfold suzukiDF6D4EvenDiagonalBaseInterval
  unfold suzukiDF6D4EvenDiagonalBaseTail at hAdd
  rw [← hsplit']
  exact hAdd

theorem suzukiDF6D4OddDiagonalBaseInterval_contains
    (D mode N : Nat) (hD : 0 < D) (hmode : 0 < mode) :
    (suzukiDF6D4OddDiagonalBaseInterval D mode N).Contains
      (∑' n : Nat, suzukiDF6D4OddDiagonalBaseTerm mode n) := by
  have hPartial :=
    suzukiDF6D4OddDiagonalBasePartialInterval_contains D mode N hD
  have hTail := suzukiDF6D4OddDiagonalBaseTailInterval_contains mode N hmode
  have hAdd := RationalInterval.contains_add hPartial hTail
  have hsplit :=
    (summable_suzukiDF6D4OddDiagonalBaseTerm mode hmode).sum_add_tsum_nat_add N
  have hsplit' :
      (∑ n ∈ Finset.range N, suzukiDF6D4OddDiagonalBaseTerm mode n) +
          (∑' n : Nat, suzukiDF6D4OddDiagonalBaseTerm mode (N + n)) =
        ∑' n : Nat, suzukiDF6D4OddDiagonalBaseTerm mode n := by
    simpa only [Nat.add_comm] using hsplit
  unfold suzukiDF6D4OddDiagonalBaseInterval
  unfold suzukiDF6D4OddDiagonalBaseTail at hAdd
  rw [← hsplit']
  exact hAdd

/-! ## Exponential endpoint-correction evaluator -/

private theorem fineExpNegAStarInterval_lower_nonneg_diag :
    0 ≤ fineExpNegAStarInterval.lower := by
  norm_num [fineExpNegAStarInterval]

private theorem fineExpNegAStarInterval_upper_nonneg_diag :
    0 ≤ fineExpNegAStarInterval.upper := by
  norm_num [fineExpNegAStarInterval]

private theorem fineExpNegAStarPowerInterval_lower_nonneg_diag (k : Nat) :
    0 ≤ (fineExpNegAStarInterval.powNonneg k).lower := by
  unfold RationalInterval.powNonneg
  exact pow_nonneg fineExpNegAStarInterval_lower_nonneg_diag k

def suzukiDF6D4EvenDiagonalExpTermInterval
    (mode n : Nat) : RationalInterval :=
  let A := fineAStarInterval
  let X := suzukiDF6D4DiagonalXInterval n
  let D := suzukiDF6D4DiagonalDInterval mode n
  let E := fineExpNegAStarInterval.powNonneg (4 * n + 1)
  if mode = 0 then
    E.divNonneg (RationalInterval.scale 2
      (A.mulNonneg (RationalInterval.point
        (suzukiDF6D4DiagonalDecayRatEval n ^ 2))))
  else
    ((A.mulNonneg (X.powNonneg 2)).mulNonneg E).divNonneg
      (D.powNonneg 2)

def suzukiDF6D4OddDiagonalExpMagnitudeTermInterval
    (mode n : Nat) : RationalInterval :=
  let A := fineAStarInterval
  let F := suzukiDF6D4DiagonalFrequencyInterval mode
  let D := suzukiDF6D4DiagonalDInterval mode n
  let E := fineExpNegAStarInterval.powNonneg (4 * n + 1)
  ((A.mulNonneg (F.powNonneg 2)).mulNonneg E).divNonneg
    (D.powNonneg 2)

private theorem suzukiDF6D4EvenDiagonalExpZeroDenominator_lower_pos
    (n : Nat) :
    0 < (RationalInterval.scale 2
      (fineAStarInterval.mulNonneg (RationalInterval.point
        (suzukiDF6D4DiagonalDecayRatEval n ^ 2)))).lower := by
  unfold RationalInterval.scale RationalInterval.mulNonneg
    RationalInterval.point
  dsimp only
  have ha := fineAStarInterval_lower_pos
  have hd := suzukiDF6D4DiagonalDecayRatEval_pos n
  have haUpper : 0 < fineAStarInterval.upper := by
    norm_num [fineAStarInterval]
  rw [lt_min_iff]
  constructor
  · positivity
  · positivity

private theorem suzukiDF6D4EvenDiagonalExpNumerator_lower_nonneg
    (n : Nat) :
    0 ≤ ((fineAStarInterval.mulNonneg
        ((suzukiDF6D4DiagonalXInterval n).powNonneg 2)).mulNonneg
      (fineExpNegAStarInterval.powNonneg (4 * n + 1))).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.powNonneg
  dsimp only
  exact mul_nonneg
    (mul_nonneg fineAStarInterval_lower_pos.le
      (pow_nonneg (suzukiDF6D4DiagonalXInterval_lower_pos n).le 2))
    (pow_nonneg fineExpNegAStarInterval_lower_nonneg_diag _)

private theorem suzukiDF6D4OddDiagonalExpNumerator_lower_nonneg
    (mode n : Nat) :
    0 ≤ ((fineAStarInterval.mulNonneg
        ((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2)).mulNonneg
      (fineExpNegAStarInterval.powNonneg (4 * n + 1))).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.powNonneg
  dsimp only
  exact mul_nonneg
    (mul_nonneg fineAStarInterval_lower_pos.le
      (pow_nonneg
        (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2))
    (pow_nonneg fineExpNegAStarInterval_lower_nonneg_diag _)

private theorem suzukiDF6D4DiagonalDSquareInterval_lower_pos
    (mode n : Nat) :
    0 < ((suzukiDF6D4DiagonalDInterval mode n).powNonneg 2).lower := by
  unfold RationalInterval.powNonneg
  exact pow_pos (suzukiDF6D4DiagonalDInterval_lower_pos mode n) 2

theorem suzukiDF6D4EvenDiagonalExpTermInterval_contains (mode n : Nat) :
    (suzukiDF6D4EvenDiagonalExpTermInterval mode n).Contains
      (suzukiDF6D4EvenDiagonalExpTerm mode n) := by
  let A := fineAStarInterval
  let X := suzukiDF6D4DiagonalXInterval n
  let D := suzukiDF6D4DiagonalDInterval mode n
  let E := fineExpNegAStarInterval.powNonneg (4 * n + 1)
  have hE := RationalInterval.contains_powNonneg (4 * n + 1)
    fineExpNegAStarInterval_lower_nonneg_diag
    fineExpNegAStarInterval_contains
  by_cases hmode : mode = 0
  · subst mode
    have hDecaySq :
        (((suzukiDF6D4DiagonalDecayRatEval n ^ 2 : Rat)) : Real) =
          suzukiDF6D4DiagonalDecay n ^ 2 := by
      norm_num only [Rat.cast_pow]
      rw [suzukiDF6D4DiagonalDecayRatEval_cast]
    have hAR := RationalInterval.contains_mulNonneg
      fineAStarInterval_lower_pos.le
      (by
        unfold RationalInterval.point
        exact pow_nonneg (suzukiDF6D4DiagonalDecayRatEval_pos n).le 2)
      fineAStarInterval_contains
      (RationalInterval.contains_point
        (suzukiDF6D4DiagonalDecayRatEval n ^ 2))
    rw [hDecaySq] at hAR
    have hDen := RationalInterval.contains_scale 2 hAR
    have h := RationalInterval.contains_divNonneg
      (fineExpNegAStarPowerInterval_lower_nonneg_diag (4 * n + 1))
      (suzukiDF6D4EvenDiagonalExpZeroDenominator_lower_pos n)
      hE hDen
    unfold suzukiDF6D4EvenDiagonalExpTermInterval
      suzukiDF6D4EvenDiagonalExpTerm
    simp only [if_pos]
    convert h using 1 <;> ring
  · have hX2 := RationalInterval.contains_powNonneg 2
      (suzukiDF6D4DiagonalXInterval_lower_pos n).le
      (suzukiDF6D4DiagonalXInterval_contains n)
    have hAX2 := RationalInterval.contains_mulNonneg
      fineAStarInterval_lower_pos.le
      (by
        unfold RationalInterval.powNonneg
        exact pow_nonneg (suzukiDF6D4DiagonalXInterval_lower_pos n).le 2)
      fineAStarInterval_contains hX2
    have hNum := RationalInterval.contains_mulNonneg
      (by
        unfold RationalInterval.mulNonneg RationalInterval.powNonneg
        exact mul_nonneg fineAStarInterval_lower_pos.le
          (pow_nonneg (suzukiDF6D4DiagonalXInterval_lower_pos n).le 2))
      (fineExpNegAStarPowerInterval_lower_nonneg_diag (4 * n + 1))
      hAX2 hE
    have hD2 := RationalInterval.contains_powNonneg 2
      (suzukiDF6D4DiagonalDInterval_lower_pos mode n).le
      (suzukiDF6D4DiagonalDInterval_contains mode n)
    have h := RationalInterval.contains_divNonneg
      (suzukiDF6D4EvenDiagonalExpNumerator_lower_nonneg n)
      (suzukiDF6D4DiagonalDSquareInterval_lower_pos mode n)
      hNum hD2
    unfold suzukiDF6D4EvenDiagonalExpTermInterval
      suzukiDF6D4EvenDiagonalExpTerm
    simp only [hmode, if_false]
    convert h using 1 <;> ring

theorem suzukiDF6D4OddDiagonalExpMagnitudeTermInterval_contains
    (mode n : Nat) :
    (suzukiDF6D4OddDiagonalExpMagnitudeTermInterval mode n).Contains
      (suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) := by
  let A := fineAStarInterval
  let F := suzukiDF6D4DiagonalFrequencyInterval mode
  let D := suzukiDF6D4DiagonalDInterval mode n
  let E := fineExpNegAStarInterval.powNonneg (4 * n + 1)
  have hF2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)
  have hAF2 := RationalInterval.contains_mulNonneg
    fineAStarInterval_lower_pos.le
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg
        (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2)
    fineAStarInterval_contains hF2
  have hE := RationalInterval.contains_powNonneg (4 * n + 1)
    fineExpNegAStarInterval_lower_nonneg_diag
    fineExpNegAStarInterval_contains
  have hNum := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.mulNonneg RationalInterval.powNonneg
      exact mul_nonneg fineAStarInterval_lower_pos.le
        (pow_nonneg
          (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2))
    (fineExpNegAStarPowerInterval_lower_nonneg_diag (4 * n + 1))
    hAF2 hE
  have hD2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalDInterval_lower_pos mode n).le
    (suzukiDF6D4DiagonalDInterval_contains mode n)
  have h := RationalInterval.contains_divNonneg
    (suzukiDF6D4OddDiagonalExpNumerator_lower_nonneg mode n)
    (suzukiDF6D4DiagonalDSquareInterval_lower_pos mode n)
    hNum hD2
  unfold suzukiDF6D4OddDiagonalExpMagnitudeTermInterval
    suzukiDF6D4OddDiagonalExpMagnitudeTerm
  dsimp only [A, F, D, E] at h ⊢
  convert h using 1 <;> ring

def suzukiDF6D4EvenDiagonalExpPartialInterval (D : Nat) :
    Nat → Nat → RationalInterval
  | _, 0 => RationalInterval.point 0
  | mode, N + 1 => RationalInterval.roundOut D
      ((suzukiDF6D4EvenDiagonalExpPartialInterval D mode N).add
        (suzukiDF6D4EvenDiagonalExpTermInterval mode N))

def suzukiDF6D4OddDiagonalExpMagnitudePartialInterval (D : Nat) :
    Nat → Nat → RationalInterval
  | _, 0 => RationalInterval.point 0
  | mode, N + 1 => RationalInterval.roundOut D
      ((suzukiDF6D4OddDiagonalExpMagnitudePartialInterval D mode N).add
        (suzukiDF6D4OddDiagonalExpMagnitudeTermInterval mode N))

theorem suzukiDF6D4EvenDiagonalExpPartialInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4EvenDiagonalExpPartialInterval D mode N).Contains
      (∑ n ∈ Finset.range N, suzukiDF6D4EvenDiagonalExpTerm mode n) := by
  induction N with
  | zero =>
      simpa [suzukiDF6D4EvenDiagonalExpPartialInterval] using
        RationalInterval.contains_point 0
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact RationalInterval.contains_roundOut hD
        (RationalInterval.contains_add ih
          (suzukiDF6D4EvenDiagonalExpTermInterval_contains mode N))

theorem suzukiDF6D4OddDiagonalExpMagnitudePartialInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4OddDiagonalExpMagnitudePartialInterval D mode N).Contains
      (∑ n ∈ Finset.range N,
        suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) := by
  induction N with
  | zero =>
      simpa [suzukiDF6D4OddDiagonalExpMagnitudePartialInterval] using
        RationalInterval.contains_point 0
  | succ N ih =>
      rw [Finset.sum_range_succ]
      exact RationalInterval.contains_roundOut hD
        (RationalInterval.contains_add ih
          (suzukiDF6D4OddDiagonalExpMagnitudeTermInterval_contains mode N))

private def suzukiDF6D4DiagonalExpRatioDenominatorInterval :
    RationalInterval :=
  (RationalInterval.point 1).sub (fineExpNegAStarInterval.powNonneg 4)

private theorem suzukiDF6D4DiagonalExpRatioDenominatorInterval_lower_pos :
    0 < suzukiDF6D4DiagonalExpRatioDenominatorInterval.lower := by
  norm_num [suzukiDF6D4DiagonalExpRatioDenominatorInterval,
    RationalInterval.point, RationalInterval.sub, RationalInterval.add,
    RationalInterval.neg, RationalInterval.powNonneg,
    fineExpNegAStarInterval]

private theorem suzukiDF6D4DiagonalExpRatioDenominatorInterval_contains :
    suzukiDF6D4DiagonalExpRatioDenominatorInterval.Contains
      (1 - Real.exp (-suzukiProjectAStar) ^ 4) := by
  unfold suzukiDF6D4DiagonalExpRatioDenominatorInterval
  have hOne : (RationalInterval.point (1 : Rat)).Contains (1 : Real) := by
    simpa using RationalInterval.contains_point (1 : Rat)
  exact RationalInterval.contains_sub hOne
    (RationalInterval.contains_powNonneg 4
      fineExpNegAStarInterval_lower_nonneg_diag
      fineExpNegAStarInterval_contains)

def suzukiDF6D4EvenDiagonalExpTailBoundInterval
    (mode N : Nat) : RationalInterval :=
  let E := fineExpNegAStarInterval.powNonneg (4 * N + 1)
  let denominator := fineAStarInterval.mulNonneg
    (RationalInterval.point (suzukiDF6D4DiagonalDecayRatEval N ^ 2))
  (E.divNonneg denominator).divNonneg
    suzukiDF6D4DiagonalExpRatioDenominatorInterval

def suzukiDF6D4OddDiagonalExpTailBoundInterval
    (mode N : Nat) : RationalInterval :=
  let F2 := (suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2
  let E := fineExpNegAStarInterval.powNonneg (4 * N + 1)
  let numerator := F2.mulNonneg E
  let denominator := (fineAStarInterval.powNonneg 3).mulNonneg
    (RationalInterval.point (suzukiDF6D4DiagonalDecayRatEval N ^ 4))
  (numerator.divNonneg denominator).divNonneg
    suzukiDF6D4DiagonalExpRatioDenominatorInterval

private theorem suzukiDF6D4EvenDiagonalExpTailFirstDenominator_lower_pos
    (N : Nat) :
    0 < (fineAStarInterval.mulNonneg
      (RationalInterval.point
        (suzukiDF6D4DiagonalDecayRatEval N ^ 2))).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.point
  dsimp only
  exact mul_pos fineAStarInterval_lower_pos
    (pow_pos (suzukiDF6D4DiagonalDecayRatEval_pos N) 2)

private theorem suzukiDF6D4OddDiagonalExpTailNumerator_lower_nonneg
    (mode N : Nat) :
    0 ≤ (((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2).mulNonneg
      (fineExpNegAStarInterval.powNonneg (4 * N + 1))).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.powNonneg
  dsimp only
  exact mul_nonneg
    (pow_nonneg
      (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2)
    (pow_nonneg fineExpNegAStarInterval_lower_nonneg_diag _)

private theorem suzukiDF6D4OddDiagonalExpTailDenominator_lower_pos
    (N : Nat) :
    0 < ((fineAStarInterval.powNonneg 3).mulNonneg
      (RationalInterval.point
        (suzukiDF6D4DiagonalDecayRatEval N ^ 4))).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.powNonneg
    RationalInterval.point
  dsimp only
  exact mul_pos (pow_pos fineAStarInterval_lower_pos 3)
    (pow_pos (suzukiDF6D4DiagonalDecayRatEval_pos N) 4)

theorem suzukiDF6D4EvenDiagonalExpTailBoundInterval_contains
    (mode N : Nat) :
    (suzukiDF6D4EvenDiagonalExpTailBoundInterval mode N).Contains
      (Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
        (suzukiProjectAStar * suzukiDF6D4DiagonalDecay N ^ 2) /
        (1 - Real.exp (-suzukiProjectAStar) ^ 4)) := by
  have hE := RationalInterval.contains_powNonneg (4 * N + 1)
    fineExpNegAStarInterval_lower_nonneg_diag
    fineExpNegAStarInterval_contains
  have hDecaySq :
      (((suzukiDF6D4DiagonalDecayRatEval N ^ 2 : Rat)) : Real) =
        suzukiDF6D4DiagonalDecay N ^ 2 := by
    norm_num only [Rat.cast_pow]
    rw [suzukiDF6D4DiagonalDecayRatEval_cast]
  have hDen := RationalInterval.contains_mulNonneg
    fineAStarInterval_lower_pos.le
    (by
      unfold RationalInterval.point
      exact pow_nonneg (suzukiDF6D4DiagonalDecayRatEval_pos N).le 2)
    fineAStarInterval_contains
    (RationalInterval.contains_point
      (suzukiDF6D4DiagonalDecayRatEval N ^ 2))
  rw [hDecaySq] at hDen
  have hFirst := RationalInterval.contains_divNonneg
    (fineExpNegAStarPowerInterval_lower_nonneg_diag (4 * N + 1))
    (suzukiDF6D4EvenDiagonalExpTailFirstDenominator_lower_pos N)
    hE hDen
  have hFirstLower :
      0 ≤ ((fineExpNegAStarInterval.powNonneg (4 * N + 1)).divNonneg
        (fineAStarInterval.mulNonneg (RationalInterval.point
          (suzukiDF6D4DiagonalDecayRatEval N ^ 2)))).lower := by
    unfold RationalInterval.divNonneg RationalInterval.mulNonneg
      RationalInterval.invPos RationalInterval.point RationalInterval.powNonneg
    dsimp only
    have haUpper : 0 ≤ fineAStarInterval.upper := by
      norm_num [fineAStarInterval]
    exact mul_nonneg
      (pow_nonneg fineExpNegAStarInterval_lower_nonneg_diag _)
      (inv_nonneg.mpr (mul_nonneg haUpper
        (pow_nonneg (suzukiDF6D4DiagonalDecayRatEval_pos N).le 2)))
  have h := RationalInterval.contains_divNonneg hFirstLower
    suzukiDF6D4DiagonalExpRatioDenominatorInterval_lower_pos
    hFirst suzukiDF6D4DiagonalExpRatioDenominatorInterval_contains
  unfold suzukiDF6D4EvenDiagonalExpTailBoundInterval
  dsimp only at h ⊢
  exact h

theorem suzukiDF6D4OddDiagonalExpTailBoundInterval_contains
    (mode N : Nat) :
    (suzukiDF6D4OddDiagonalExpTailBoundInterval mode N).Contains
      (suzukiDF6D4DiagonalFrequency mode ^ 2 *
        Real.exp (-suzukiProjectAStar) ^ (4 * N + 1) /
        (suzukiProjectAStar ^ 3 * suzukiDF6D4DiagonalDecay N ^ 4) /
        (1 - Real.exp (-suzukiProjectAStar) ^ 4)) := by
  have hF2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)
  have hE := RationalInterval.contains_powNonneg (4 * N + 1)
    fineExpNegAStarInterval_lower_nonneg_diag
    fineExpNegAStarInterval_contains
  have hNum := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg
        (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2)
    (fineExpNegAStarPowerInterval_lower_nonneg_diag (4 * N + 1))
    hF2 hE
  have hA3 := RationalInterval.contains_powNonneg 3
    fineAStarInterval_lower_pos.le fineAStarInterval_contains
  have hDecay4 :
      (((suzukiDF6D4DiagonalDecayRatEval N ^ 4 : Rat)) : Real) =
        suzukiDF6D4DiagonalDecay N ^ 4 := by
    norm_num only [Rat.cast_pow]
    rw [suzukiDF6D4DiagonalDecayRatEval_cast]
  have hDen := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg fineAStarInterval_lower_pos.le 3)
    (by
      unfold RationalInterval.point
      exact pow_nonneg (suzukiDF6D4DiagonalDecayRatEval_pos N).le 4)
    hA3 (RationalInterval.contains_point
      (suzukiDF6D4DiagonalDecayRatEval N ^ 4))
  rw [hDecay4] at hDen
  have hFirst := RationalInterval.contains_divNonneg
    (suzukiDF6D4OddDiagonalExpTailNumerator_lower_nonneg mode N)
    (suzukiDF6D4OddDiagonalExpTailDenominator_lower_pos N)
    hNum hDen
  have hFirstLower :
      0 ≤ ((((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2).mulNonneg
          (fineExpNegAStarInterval.powNonneg (4 * N + 1))).divNonneg
        ((fineAStarInterval.powNonneg 3).mulNonneg
          (RationalInterval.point
            (suzukiDF6D4DiagonalDecayRatEval N ^ 4)))).lower := by
    unfold RationalInterval.divNonneg RationalInterval.mulNonneg
      RationalInterval.invPos RationalInterval.point RationalInterval.powNonneg
    dsimp only
    have haUpper : 0 ≤ fineAStarInterval.upper := by
      norm_num [fineAStarInterval]
    exact mul_nonneg
      (mul_nonneg
        (pow_nonneg
          (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2)
        (pow_nonneg fineExpNegAStarInterval_lower_nonneg_diag _))
      (inv_nonneg.mpr (mul_nonneg (pow_nonneg haUpper 3)
        (pow_nonneg (suzukiDF6D4DiagonalDecayRatEval_pos N).le 4)))
  have h := RationalInterval.contains_divNonneg hFirstLower
    suzukiDF6D4DiagonalExpRatioDenominatorInterval_lower_pos
    hFirst suzukiDF6D4DiagonalExpRatioDenominatorInterval_contains
  unfold suzukiDF6D4OddDiagonalExpTailBoundInterval
  dsimp only at h ⊢
  exact h

def suzukiDF6D4EvenDiagonalExpTailInterval
    (mode N : Nat) : RationalInterval :=
  ⟨0, (suzukiDF6D4EvenDiagonalExpTailBoundInterval mode N).upper⟩

def suzukiDF6D4OddDiagonalExpMagnitudeTailInterval
    (mode N : Nat) : RationalInterval :=
  ⟨0, (suzukiDF6D4OddDiagonalExpTailBoundInterval mode N).upper⟩

theorem suzukiDF6D4EvenDiagonalExpTailInterval_contains (mode N : Nat) :
    (suzukiDF6D4EvenDiagonalExpTailInterval mode N).Contains
      (suzukiDF6D4EvenDiagonalExpTail mode N) := by
  have htail := suzukiDF6D4EvenDiagonalExpTail_bounds mode N
  have hbound := suzukiDF6D4EvenDiagonalExpTailBoundInterval_contains mode N
  unfold suzukiDF6D4EvenDiagonalExpTailInterval RationalInterval.Contains
  norm_num
  exact ⟨htail.1, htail.2.trans hbound.2⟩

theorem suzukiDF6D4OddDiagonalExpMagnitudeTailInterval_contains
    (mode N : Nat) :
    (suzukiDF6D4OddDiagonalExpMagnitudeTailInterval mode N).Contains
      (suzukiDF6D4OddDiagonalExpMagnitudeTail mode N) := by
  have htail := suzukiDF6D4OddDiagonalExpMagnitudeTail_bounds mode N
  have hbound := suzukiDF6D4OddDiagonalExpTailBoundInterval_contains mode N
  unfold suzukiDF6D4OddDiagonalExpMagnitudeTailInterval
    RationalInterval.Contains
  norm_num
  exact ⟨htail.1, htail.2.trans hbound.2⟩

def suzukiDF6D4EvenDiagonalExpInterval
    (D mode N : Nat) : RationalInterval :=
  (suzukiDF6D4EvenDiagonalExpPartialInterval D mode N).add
    (suzukiDF6D4EvenDiagonalExpTailInterval mode N)

def suzukiDF6D4OddDiagonalExpMagnitudeInterval
    (D mode N : Nat) : RationalInterval :=
  (suzukiDF6D4OddDiagonalExpMagnitudePartialInterval D mode N).add
    (suzukiDF6D4OddDiagonalExpMagnitudeTailInterval mode N)

theorem suzukiDF6D4EvenDiagonalExpInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4EvenDiagonalExpInterval D mode N).Contains
      (∑' n : Nat, suzukiDF6D4EvenDiagonalExpTerm mode n) := by
  have hPartial :=
    suzukiDF6D4EvenDiagonalExpPartialInterval_contains D mode N hD
  have hTail := suzukiDF6D4EvenDiagonalExpTailInterval_contains mode N
  have hAdd := RationalInterval.contains_add hPartial hTail
  have hsplit :=
    (summable_suzukiDF6D4EvenDiagonalExpTerm mode).sum_add_tsum_nat_add N
  have hsplit' :
      (∑ n ∈ Finset.range N, suzukiDF6D4EvenDiagonalExpTerm mode n) +
          (∑' n : Nat, suzukiDF6D4EvenDiagonalExpTerm mode (N + n)) =
        ∑' n : Nat, suzukiDF6D4EvenDiagonalExpTerm mode n := by
    simpa only [Nat.add_comm] using hsplit
  unfold suzukiDF6D4EvenDiagonalExpInterval
  unfold suzukiDF6D4EvenDiagonalExpTail at hAdd
  rw [← hsplit']
  exact hAdd

theorem suzukiDF6D4OddDiagonalExpMagnitudeInterval_contains
    (D mode N : Nat) (hD : 0 < D) :
    (suzukiDF6D4OddDiagonalExpMagnitudeInterval D mode N).Contains
      (∑' n : Nat, suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) := by
  have hPartial :=
    suzukiDF6D4OddDiagonalExpMagnitudePartialInterval_contains D mode N hD
  have hTail :=
    suzukiDF6D4OddDiagonalExpMagnitudeTailInterval_contains mode N
  have hAdd := RationalInterval.contains_add hPartial hTail
  have hsplit :=
    (summable_suzukiDF6D4OddDiagonalExpMagnitudeTerm mode).sum_add_tsum_nat_add N
  have hsplit' :
      (∑ n ∈ Finset.range N,
          suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) +
          (∑' n : Nat,
            suzukiDF6D4OddDiagonalExpMagnitudeTerm mode (N + n)) =
        ∑' n : Nat, suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n := by
    simpa only [Nat.add_comm] using hsplit
  unfold suzukiDF6D4OddDiagonalExpMagnitudeInterval
  unfold suzukiDF6D4OddDiagonalExpMagnitudeTail at hAdd
  rw [← hsplit']
  exact hAdd

/-! ## Frozen complete Gamma contribution -/

def suzukiDF6D4FrozenEvenDiagonalBaseInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 100000000000000
    (suzukiDF6D4EvenDiagonalBaseInterval
      1000000000000000000 mode 16384)

def suzukiDF6D4FrozenOddDiagonalBaseInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 100000000000000
    (suzukiDF6D4OddDiagonalBaseInterval
      1000000000000000000 mode 16384)

def suzukiDF6D4FrozenEvenDiagonalExpInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 100000000000000
    (suzukiDF6D4EvenDiagonalExpInterval
      1000000000000000000 mode 32)

def suzukiDF6D4FrozenOddDiagonalExpMagnitudeInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 100000000000000
    (suzukiDF6D4OddDiagonalExpMagnitudeInterval
      1000000000000000000 mode 32)

theorem suzukiDF6D4FrozenEvenDiagonalBaseInterval_contains (mode : Nat) :
    (suzukiDF6D4FrozenEvenDiagonalBaseInterval mode).Contains
      (∑' n : Nat, suzukiDF6D4EvenDiagonalBaseTerm mode n) := by
  unfold suzukiDF6D4FrozenEvenDiagonalBaseInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4EvenDiagonalBaseInterval_contains
      1000000000000000000 mode 16384 (by norm_num))

theorem suzukiDF6D4FrozenOddDiagonalBaseInterval_contains
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiDF6D4FrozenOddDiagonalBaseInterval mode).Contains
      (∑' n : Nat, suzukiDF6D4OddDiagonalBaseTerm mode n) := by
  unfold suzukiDF6D4FrozenOddDiagonalBaseInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4OddDiagonalBaseInterval_contains
      1000000000000000000 mode 16384 (by norm_num) hmode)

theorem suzukiDF6D4FrozenEvenDiagonalExpInterval_contains (mode : Nat) :
    (suzukiDF6D4FrozenEvenDiagonalExpInterval mode).Contains
      (∑' n : Nat, suzukiDF6D4EvenDiagonalExpTerm mode n) := by
  unfold suzukiDF6D4FrozenEvenDiagonalExpInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4EvenDiagonalExpInterval_contains
      1000000000000000000 mode 32 (by norm_num))

theorem suzukiDF6D4FrozenOddDiagonalExpMagnitudeInterval_contains
    (mode : Nat) :
    (suzukiDF6D4FrozenOddDiagonalExpMagnitudeInterval mode).Contains
      (∑' n : Nat,
        suzukiDF6D4OddDiagonalExpMagnitudeTerm mode n) := by
  unfold suzukiDF6D4FrozenOddDiagonalExpMagnitudeInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4OddDiagonalExpMagnitudeInterval_contains
      1000000000000000000 mode 32 (by norm_num))

def suzukiDF6D4EvenDiagonalOriginSlopeInterval
    (mode : Nat) : RationalInterval :=
  if mode = 0 then RationalInterval.scale (-1 / 2) fineAStarInterval.invPos
  else RationalInterval.scale (-1) fineAStarInterval.invPos

def suzukiDF6D4DiagonalOriginSecondInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.scale (-1)
    (((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2).divNonneg
      (fineAStarInterval.powNonneg 2))

private theorem fineAStarSquareInterval_lower_pos :
    0 < (fineAStarInterval.powNonneg 2).lower := by
  unfold RationalInterval.powNonneg
  exact pow_pos fineAStarInterval_lower_pos 2

theorem suzukiDF6D4EvenDiagonalOriginSlopeInterval_contains (mode : Nat) :
    (suzukiDF6D4EvenDiagonalOriginSlopeInterval mode).Contains
      (suzukiDF6D4EvenDiagonalOriginSlope mode) := by
  have hInv := RationalInterval.contains_invPos fineAStarInterval_lower_pos
    fineAStarInterval_contains
  by_cases hmode : mode = 0
  · subst mode
    have h := RationalInterval.contains_scale (-1 / 2) hInv
    unfold suzukiDF6D4EvenDiagonalOriginSlopeInterval
      suzukiDF6D4EvenDiagonalOriginSlope
    simp only [if_pos]
    convert h using 1
    ring
  · have h := RationalInterval.contains_scale (-1) hInv
    unfold suzukiDF6D4EvenDiagonalOriginSlopeInterval
      suzukiDF6D4EvenDiagonalOriginSlope
    simp only [hmode, if_false]
    convert h using 1
    ring

theorem suzukiDF6D4DiagonalOriginSecondInterval_contains (mode : Nat) :
    (suzukiDF6D4DiagonalOriginSecondInterval mode).Contains
      (suzukiDF6D4DiagonalOriginSecond mode) := by
  have hF2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)
  have hA2 := RationalInterval.contains_powNonneg 2
    fineAStarInterval_lower_pos.le fineAStarInterval_contains
  have hQuotient := RationalInterval.contains_divNonneg
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg
        (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2)
    fineAStarSquareInterval_lower_pos hF2 hA2
  have h := RationalInterval.contains_scale (-1) hQuotient
  unfold suzukiDF6D4DiagonalOriginSecondInterval
    suzukiDF6D4DiagonalOriginSecond
  convert h using 1 <;> ring

private theorem suzukiDF6D4DiagonalReciprocalSquareInterval_lower_nonneg :
    0 ≤ suzukiDF6D4DiagonalReciprocalSquareInterval.lower := by
  norm_num [suzukiDF6D4DiagonalReciprocalSquareInterval]

private theorem suzukiDF6D4DiagonalReciprocalCubeInterval_lower_nonneg :
    0 ≤ suzukiDF6D4DiagonalReciprocalCubeInterval.lower := by
  norm_num [suzukiDF6D4DiagonalReciprocalCubeInterval]

def suzukiDF6D4EvenDiagonalGammaCoreInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4FrozenEvenDiagonalBaseInterval mode).add
    (suzukiDF6D4FrozenEvenDiagonalExpInterval mode) |>.add
    (suzukiDF6D4DiagonalReciprocalSquareInterval.mulLeftNonneg
      (suzukiDF6D4EvenDiagonalOriginSlopeInterval mode)) |>.add
    (suzukiDF6D4DiagonalReciprocalCubeInterval.mulLeftNonneg
      (suzukiDF6D4DiagonalOriginSecondInterval mode))

def suzukiDF6D4OddDiagonalGammaCoreInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4FrozenOddDiagonalBaseInterval mode).sub
    (suzukiDF6D4FrozenOddDiagonalExpMagnitudeInterval mode) |>.add
    (suzukiDF6D4DiagonalReciprocalCubeInterval.mulLeftNonneg
      (suzukiDF6D4DiagonalOriginSecondInterval mode))

theorem suzukiDF6D4EvenDiagonalGammaCoreInterval_contains (mode : Nat) :
    (suzukiDF6D4EvenDiagonalGammaCoreInterval mode).Contains
      (suzukiDF6D4EvenDiagonalGammaCore mode) := by
  have hBase := suzukiDF6D4FrozenEvenDiagonalBaseInterval_contains mode
  have hExp := suzukiDF6D4FrozenEvenDiagonalExpInterval_contains mode
  have hSlope := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4DiagonalReciprocalSquareInterval_lower_nonneg
    suzukiDF6D4DiagonalReciprocalSquareInterval_contains
    (suzukiDF6D4EvenDiagonalOriginSlopeInterval_contains mode)
  have hSecond := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4DiagonalReciprocalCubeInterval_lower_nonneg
    suzukiDF6D4DiagonalReciprocalCubeInterval_contains
    (suzukiDF6D4DiagonalOriginSecondInterval_contains mode)
  have h := RationalInterval.contains_add
    (RationalInterval.contains_add
      (RationalInterval.contains_add hBase hExp) hSlope) hSecond
  unfold suzukiDF6D4EvenDiagonalGammaCoreInterval
    suzukiDF6D4EvenDiagonalGammaCore
  convert h using 1 <;> ring

theorem suzukiDF6D4OddDiagonalGammaCoreInterval_contains
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiDF6D4OddDiagonalGammaCoreInterval mode).Contains
      (suzukiDF6D4OddDiagonalGammaCore mode) := by
  have hBase := suzukiDF6D4FrozenOddDiagonalBaseInterval_contains mode hmode
  have hExp := suzukiDF6D4FrozenOddDiagonalExpMagnitudeInterval_contains mode
  have hSecond := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4DiagonalReciprocalCubeInterval_lower_nonneg
    suzukiDF6D4DiagonalReciprocalCubeInterval_contains
    (suzukiDF6D4DiagonalOriginSecondInterval_contains mode)
  have h := RationalInterval.contains_add
    (RationalInterval.contains_sub hBase hExp) hSecond
  unfold suzukiDF6D4OddDiagonalGammaCoreInterval
    suzukiDF6D4OddDiagonalGammaCore
  convert h using 1 <;> ring

private def suzukiDF6D4DiagonalGammaRestorationInterval :
    RationalInterval :=
  (RationalInterval.scale (1 / 4) suzukiDF6D4PiInterval).add
    (RationalInterval.scale (1 / 2) fineLogTwoInterval)

private theorem suzukiDF6D4DiagonalGammaRestorationInterval_contains :
    suzukiDF6D4DiagonalGammaRestorationInterval.Contains
      (Real.pi / 4 + Real.log 2 / 2) := by
  have h := RationalInterval.contains_add
    (RationalInterval.contains_scale (1 / 4)
      suzukiDF6D4PiInterval_contains)
    (RationalInterval.contains_scale (1 / 2)
      fineLogTwoInterval_contains)
  unfold suzukiDF6D4DiagonalGammaRestorationInterval
  convert h using 1 <;> ring

def suzukiDF6D4EvenDiagonalGammaTermInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.scale (-2)
    (suzukiDF6D4DiagonalGammaRestorationInterval.add
      (suzukiDF6D4EvenDiagonalGammaCoreInterval mode))

def suzukiDF6D4OddDiagonalGammaTermInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.scale (-2)
    (suzukiDF6D4DiagonalGammaRestorationInterval.add
      (suzukiDF6D4OddDiagonalGammaCoreInterval mode))

theorem suzukiDF6D4EvenDiagonalGammaTermInterval_contains (mode : Nat) :
    (suzukiDF6D4EvenDiagonalGammaTermInterval mode).Contains
      (suzukiDF6D4EvenDiagonalGammaTerm mode) := by
  have hAdd := RationalInterval.contains_add
    suzukiDF6D4DiagonalGammaRestorationInterval_contains
    (suzukiDF6D4EvenDiagonalGammaCoreInterval_contains mode)
  have h := RationalInterval.contains_scale (-2) hAdd
  unfold suzukiDF6D4EvenDiagonalGammaTermInterval
    suzukiDF6D4EvenDiagonalGammaTerm
  convert h using 1 <;> norm_num

theorem suzukiDF6D4OddDiagonalGammaTermInterval_contains
    (mode : Nat) (hmode : 0 < mode) :
    (suzukiDF6D4OddDiagonalGammaTermInterval mode).Contains
      (suzukiDF6D4OddDiagonalGammaTerm mode) := by
  have hAdd := RationalInterval.contains_add
    suzukiDF6D4DiagonalGammaRestorationInterval_contains
    (suzukiDF6D4OddDiagonalGammaCoreInterval_contains mode hmode)
  have h := RationalInterval.contains_scale (-2) hAdd
  unfold suzukiDF6D4OddDiagonalGammaTermInterval
    suzukiDF6D4OddDiagonalGammaTerm
  convert h using 1 <;> norm_num

/-! ## Pole, prime, scalar, and complete diagonal entries -/

def suzukiDF6D4DiagonalPoleFactorInterval : RationalInterval :=
  (fineExpNegAStarInterval.add fineExpNegAStarInterval.invPos).sub
    (RationalInterval.point 2)

private theorem fineExpNegAStarInterval_lower_pos_diag :
    0 < fineExpNegAStarInterval.lower := by
  norm_num [fineExpNegAStarInterval]

theorem suzukiDF6D4DiagonalPoleFactorInterval_contains :
    suzukiDF6D4DiagonalPoleFactorInterval.Contains
      suzukiDF6D4DiagonalPoleFactor := by
  have hInv := RationalInterval.contains_invPos
    fineExpNegAStarInterval_lower_pos_diag
    fineExpNegAStarInterval_contains
  have hTwo : (RationalInterval.point (2 : Rat)).Contains (2 : Real) := by
    simpa using RationalInterval.contains_point (2 : Rat)
  have h := RationalInterval.contains_sub
    (RationalInterval.contains_add fineExpNegAStarInterval_contains hInv)
    hTwo
  unfold suzukiDF6D4DiagonalPoleFactorInterval
    suzukiDF6D4DiagonalPoleFactor
  exact h

private theorem suzukiDF6D4DiagonalPoleFactorInterval_lower_nonneg :
    0 ≤ suzukiDF6D4DiagonalPoleFactorInterval.lower := by
  norm_num [suzukiDF6D4DiagonalPoleFactorInterval,
    RationalInterval.add, RationalInterval.sub, RationalInterval.neg,
    RationalInterval.invPos, RationalInterval.point,
    fineExpNegAStarInterval]

private theorem suzukiDF6D4DiagonalPoleFactorInterval_upper_nonneg :
    0 ≤ suzukiDF6D4DiagonalPoleFactorInterval.upper := by
  norm_num [suzukiDF6D4DiagonalPoleFactorInterval,
    RationalInterval.add, RationalInterval.sub, RationalInterval.neg,
    RationalInterval.invPos, RationalInterval.point,
    fineExpNegAStarInterval]

private def suzukiDF6D4DiagonalPoleDenominatorInterval
    (mode : Nat) : RationalInterval :=
  (RationalInterval.scale (1 / 4) (fineAStarInterval.powNonneg 2)).add
    ((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2)

private theorem suzukiDF6D4DiagonalPoleDenominatorInterval_lower_pos
    (mode : Nat) :
    0 < (suzukiDF6D4DiagonalPoleDenominatorInterval mode).lower := by
  unfold suzukiDF6D4DiagonalPoleDenominatorInterval
    RationalInterval.add RationalInterval.scale RationalInterval.powNonneg
  dsimp only
  have ha := fineAStarInterval_lower_pos
  have haUpper : 0 < fineAStarInterval.upper := by
    norm_num [fineAStarInterval]
  have hQuarter :
      0 < min (1 / 4 * fineAStarInterval.lower ^ 2)
        (1 / 4 * fineAStarInterval.upper ^ 2) := by
    rw [lt_min_iff]
    constructor <;> positivity
  nlinarith [suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode]

private theorem suzukiDF6D4DiagonalPoleDenominatorInterval_contains
    (mode : Nat) :
    (suzukiDF6D4DiagonalPoleDenominatorInterval mode).Contains
      (suzukiProjectAStar ^ 2 / 4 +
        suzukiDF6D4DiagonalFrequency mode ^ 2) := by
  have hA2 := RationalInterval.contains_powNonneg 2
    fineAStarInterval_lower_pos.le fineAStarInterval_contains
  have hF2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)
  have h := RationalInterval.contains_add
    (RationalInterval.contains_scale (1 / 4) hA2) hF2
  unfold suzukiDF6D4DiagonalPoleDenominatorInterval
  convert h using 1 <;> ring

def suzukiDF6D4EvenDiagonalPoleTermInterval
    (mode : Nat) : RationalInterval :=
  if mode = 0 then
    (RationalInterval.scale 4 suzukiDF6D4DiagonalPoleFactorInterval).divNonneg
      fineAStarInterval
  else
    ((RationalInterval.scale (1 / 2) (fineAStarInterval.powNonneg 3)).mulNonneg
      suzukiDF6D4DiagonalPoleFactorInterval).divNonneg
        ((suzukiDF6D4DiagonalPoleDenominatorInterval mode).powNonneg 2)

def suzukiDF6D4OddDiagonalPoleTermInterval
    (mode : Nat) : RationalInterval :=
  let numerator :=
    ((fineAStarInterval.mulNonneg
      ((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2)).mulNonneg
        suzukiDF6D4DiagonalPoleFactorInterval)
  RationalInterval.scale (-2)
    (numerator.divNonneg
      ((suzukiDF6D4DiagonalPoleDenominatorInterval mode).powNonneg 2))

private theorem suzukiDF6D4EvenDiagonalPoleZeroNumerator_lower_nonneg :
    0 ≤ (RationalInterval.scale 4
      suzukiDF6D4DiagonalPoleFactorInterval).lower := by
  unfold RationalInterval.scale
  rw [le_min_iff]
  constructor
  · exact mul_nonneg (by norm_num)
      suzukiDF6D4DiagonalPoleFactorInterval_lower_nonneg
  · exact mul_nonneg (by norm_num)
      suzukiDF6D4DiagonalPoleFactorInterval_upper_nonneg

private theorem suzukiDF6D4EvenDiagonalPoleNumerator_lower_nonneg :
    0 ≤ ((RationalInterval.scale (1 / 2)
      (fineAStarInterval.powNonneg 3)).mulNonneg
        suzukiDF6D4DiagonalPoleFactorInterval).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.scale
    RationalInterval.powNonneg
  dsimp only
  have haUpper : 0 ≤ fineAStarInterval.upper := by
    norm_num [fineAStarInterval]
  have hscale :
      0 ≤ min (1 / 2 * fineAStarInterval.lower ^ 3)
        (1 / 2 * fineAStarInterval.upper ^ 3) := by
    rw [le_min_iff]
    constructor <;> positivity [fineAStarInterval_lower_pos]
  exact mul_nonneg hscale
    suzukiDF6D4DiagonalPoleFactorInterval_lower_nonneg

private theorem suzukiDF6D4OddDiagonalPoleNumerator_lower_nonneg
    (mode : Nat) :
    0 ≤ ((fineAStarInterval.mulNonneg
      ((suzukiDF6D4DiagonalFrequencyInterval mode).powNonneg 2)).mulNonneg
        suzukiDF6D4DiagonalPoleFactorInterval).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.powNonneg
  dsimp only
  exact mul_nonneg
    (mul_nonneg fineAStarInterval_lower_pos.le
      (pow_nonneg
        (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2))
    suzukiDF6D4DiagonalPoleFactorInterval_lower_nonneg

theorem suzukiDF6D4EvenDiagonalPoleTermInterval_contains (mode : Nat) :
    (suzukiDF6D4EvenDiagonalPoleTermInterval mode).Contains
      (suzukiDF6D4EvenDiagonalPoleTerm mode) := by
  by_cases hmode : mode = 0
  · subst mode
    have hNum := RationalInterval.contains_scale 4
      suzukiDF6D4DiagonalPoleFactorInterval_contains
    have h := RationalInterval.contains_divNonneg
      suzukiDF6D4EvenDiagonalPoleZeroNumerator_lower_nonneg
      fineAStarInterval_lower_pos hNum fineAStarInterval_contains
    unfold suzukiDF6D4EvenDiagonalPoleTermInterval
      suzukiDF6D4EvenDiagonalPoleTerm
    simp only [if_pos]
    convert h using 1 <;> ring
  · have hA3 := RationalInterval.contains_powNonneg 3
      fineAStarInterval_lower_pos.le fineAStarInterval_contains
    have hScale := RationalInterval.contains_scale (1 / 2) hA3
    have hNum := RationalInterval.contains_mulNonneg
      (by
        unfold RationalInterval.scale RationalInterval.powNonneg
        rw [le_min_iff]
        constructor
        · positivity [fineAStarInterval_lower_pos]
        · have haUpper : 0 ≤ fineAStarInterval.upper := by
            norm_num [fineAStarInterval]
          positivity)
      suzukiDF6D4DiagonalPoleFactorInterval_lower_nonneg
      hScale suzukiDF6D4DiagonalPoleFactorInterval_contains
    have hDen := RationalInterval.contains_powNonneg 2
      (suzukiDF6D4DiagonalPoleDenominatorInterval_lower_pos mode).le
      (suzukiDF6D4DiagonalPoleDenominatorInterval_contains mode)
    have h := RationalInterval.contains_divNonneg
      suzukiDF6D4EvenDiagonalPoleNumerator_lower_nonneg
      (by
        unfold RationalInterval.powNonneg
        exact pow_pos
          (suzukiDF6D4DiagonalPoleDenominatorInterval_lower_pos mode) 2)
      hNum hDen
    unfold suzukiDF6D4EvenDiagonalPoleTermInterval
      suzukiDF6D4EvenDiagonalPoleTerm
    simp only [hmode, if_false]
    convert h using 1 <;> ring

theorem suzukiDF6D4OddDiagonalPoleTermInterval_contains (mode : Nat) :
    (suzukiDF6D4OddDiagonalPoleTermInterval mode).Contains
      (suzukiDF6D4OddDiagonalPoleTerm mode) := by
  have hF2 := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)
  have hAF2 := RationalInterval.contains_mulNonneg
    fineAStarInterval_lower_pos.le
    (by
      unfold RationalInterval.powNonneg
      exact pow_nonneg
        (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2)
    fineAStarInterval_contains hF2
  have hNum := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.mulNonneg RationalInterval.powNonneg
      exact mul_nonneg fineAStarInterval_lower_pos.le
        (pow_nonneg
          (suzukiDF6D4DiagonalFrequencyInterval_lower_nonneg mode) 2))
    suzukiDF6D4DiagonalPoleFactorInterval_lower_nonneg hAF2
    suzukiDF6D4DiagonalPoleFactorInterval_contains
  have hDen := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4DiagonalPoleDenominatorInterval_lower_pos mode).le
    (suzukiDF6D4DiagonalPoleDenominatorInterval_contains mode)
  have hQuotient := RationalInterval.contains_divNonneg
    (suzukiDF6D4OddDiagonalPoleNumerator_lower_nonneg mode)
    (by
      unfold RationalInterval.powNonneg
      exact pow_pos
        (suzukiDF6D4DiagonalPoleDenominatorInterval_lower_pos mode) 2)
    hNum hDen
  have h := RationalInterval.contains_scale (-2) hQuotient
  unfold suzukiDF6D4OddDiagonalPoleTermInterval
    suzukiDF6D4OddDiagonalPoleTerm
  dsimp only
  convert h using 1 <;> norm_num <;> ring

def suzukiDF6D4DiagonalPrimeDisplacementInterval : RationalInterval :=
  fineLogTwoInterval.divNonneg fineAStarInterval

private theorem fineLogTwoInterval_lower_nonneg_diag :
    0 ≤ fineLogTwoInterval.lower := by
  norm_num [fineLogTwoInterval]

theorem suzukiDF6D4DiagonalPrimeDisplacementInterval_contains :
    suzukiDF6D4DiagonalPrimeDisplacementInterval.Contains
      suzukiDF6D4DiagonalPrimeDisplacement := by
  have h := RationalInterval.contains_divNonneg
    fineLogTwoInterval_lower_nonneg_diag fineAStarInterval_lower_pos
    fineLogTwoInterval_contains fineAStarInterval_contains
  unfold suzukiDF6D4DiagonalPrimeDisplacementInterval
    suzukiDF6D4DiagonalPrimeDisplacement
  exact h

private def suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval :
    RationalInterval :=
  (RationalInterval.point 2).sub
    suzukiDF6D4DiagonalPrimeDisplacementInterval

private theorem suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval_contains :
    suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval.Contains
      (2 - suzukiDF6D4DiagonalPrimeDisplacement) := by
  have hTwo : (RationalInterval.point (2 : Rat)).Contains (2 : Real) := by
    simpa using RationalInterval.contains_point (2 : Rat)
  exact RationalInterval.contains_sub hTwo
    suzukiDF6D4DiagonalPrimeDisplacementInterval_contains

private theorem suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval_lower_nonneg :
    0 ≤ suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval.lower := by
  norm_num [suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval,
    suzukiDF6D4DiagonalPrimeDisplacementInterval,
    RationalInterval.point, RationalInterval.sub, RationalInterval.add,
    RationalInterval.neg, RationalInterval.divNonneg,
    RationalInterval.mulNonneg, RationalInterval.invPos,
    fineLogTwoInterval, fineAStarInterval]

private theorem suzukiDF6D4DiagonalFrequencyInterval_lower_pos
    (mode : Nat) (hmode : 0 < mode) :
    0 < (suzukiDF6D4DiagonalFrequencyInterval mode).lower := by
  unfold suzukiDF6D4DiagonalFrequencyInterval RationalInterval.scale
    suzukiDF6D4PiInterval
  dsimp only
  have hm : (0 : Rat) < mode := by exact_mod_cast hmode
  rw [lt_min_iff]
  constructor <;> positivity

private theorem suzukiDF6D4DiagonalFrequencyInverseInterval_lower_nonneg
    (mode : Nat) (hmode : 0 < mode) :
    0 ≤ (suzukiDF6D4DiagonalFrequencyInterval mode).invPos.lower := by
  unfold RationalInterval.invPos
  have hcontains := suzukiDF6D4DiagonalFrequencyInterval_contains mode
  have hf : 0 < suzukiDF6D4DiagonalFrequency mode := by
    unfold suzukiDF6D4DiagonalFrequency
    positivity
  have hupperReal : (0 : Real) <
      ((suzukiDF6D4DiagonalFrequencyInterval mode).upper : Real) :=
    hf.trans_le hcontains.2
  have hupper : (0 : Rat) <
      (suzukiDF6D4DiagonalFrequencyInterval mode).upper := by
    exact_mod_cast hupperReal
  exact inv_nonneg.mpr hupper.le

private def suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval
    (mode : Nat) : RationalInterval :=
  (suzukiDF6D4DiagonalFrequencyInterval mode).invPos.mulLeftNonneg
    (suzukiDF6D4FrozenPrimeSineInterval mode)

private theorem suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval_contains
    (mode : Nat) (hmode : 0 < mode) (hmax : mode ≤ 44) :
    (suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval mode).Contains
      (Real.sin (suzukiDF6D4DiagonalFrequency mode *
        suzukiDF6D4DiagonalPrimeDisplacement) /
          suzukiDF6D4DiagonalFrequency mode) := by
  have hInv := RationalInterval.contains_invPos
    (suzukiDF6D4DiagonalFrequencyInterval_lower_pos mode hmode)
    (suzukiDF6D4DiagonalFrequencyInterval_contains mode)
  have hSin := suzukiDF6D4FrozenPrimeSineInterval_contains mode
    (hmax.trans (by norm_num))
  have h := RationalInterval.contains_mulLeftNonneg
    (suzukiDF6D4DiagonalFrequencyInverseInterval_lower_nonneg mode hmode)
    hInv hSin
  have hangle :
      suzukiDF6D4DiagonalFrequency mode *
          suzukiDF6D4DiagonalPrimeDisplacement =
        (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar := by
    unfold suzukiDF6D4DiagonalFrequency
      suzukiDF6D4DiagonalPrimeDisplacement
    ring
  unfold suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval
  rw [hangle]
  simpa [div_eq_mul_inv, mul_comm] using h

def suzukiDF6D4EvenDiagonalPrimeCorrelationInterval
    (mode : Nat) : RationalInterval :=
  if mode = 0 then
    (RationalInterval.point 1).sub
      (RationalInterval.scale (1 / 2)
        suzukiDF6D4DiagonalPrimeDisplacementInterval)
  else
    RationalInterval.scale (1 / 2)
      ((suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval.mulLeftNonneg
        (suzukiDF6D4FrozenPrimeCosineInterval mode)).sub
          (suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval mode))

def suzukiDF6D4OddDiagonalPrimeCorrelationInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.scale (1 / 2)
    ((suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval.mulLeftNonneg
      (suzukiDF6D4FrozenPrimeCosineInterval mode)).add
        (suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval mode))

theorem suzukiDF6D4EvenDiagonalPrimeCorrelationInterval_contains
    (mode : Nat) (hmax : mode ≤ 44) :
    (suzukiDF6D4EvenDiagonalPrimeCorrelationInterval mode).Contains
      (suzukiDF6D4EvenDiagonalPrimeCorrelation mode) := by
  by_cases hmode : mode = 0
  · subst mode
    have hOne : (RationalInterval.point (1 : Rat)).Contains (1 : Real) := by
      simpa using RationalInterval.contains_point (1 : Rat)
    have h := RationalInterval.contains_sub hOne
      (RationalInterval.contains_scale (1 / 2)
        suzukiDF6D4DiagonalPrimeDisplacementInterval_contains)
    unfold suzukiDF6D4EvenDiagonalPrimeCorrelationInterval
      suzukiDF6D4EvenDiagonalPrimeCorrelation
    simp only [if_pos]
    convert h using 1 <;> ring
  · have hmodePos : 0 < mode := Nat.pos_of_ne_zero hmode
    have hCos := suzukiDF6D4FrozenPrimeCosineInterval_contains mode
      (hmax.trans (by norm_num))
    have hProduct := RationalInterval.contains_mulLeftNonneg
      suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval_lower_nonneg
      suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval_contains hCos
    have hSinOver :=
      suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval_contains
        mode hmodePos hmax
    have h := RationalInterval.contains_scale (1 / 2)
      (RationalInterval.contains_sub hProduct hSinOver)
    unfold suzukiDF6D4EvenDiagonalPrimeCorrelationInterval
      suzukiDF6D4EvenDiagonalPrimeCorrelation
    simp only [hmode, if_false]
    have hangle :
        suzukiDF6D4DiagonalFrequency mode *
            suzukiDF6D4DiagonalPrimeDisplacement =
          (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar := by
      unfold suzukiDF6D4DiagonalFrequency
        suzukiDF6D4DiagonalPrimeDisplacement
      ring
    rw [hangle] at h ⊢
    convert h using 1 <;> ring

theorem suzukiDF6D4OddDiagonalPrimeCorrelationInterval_contains
    (mode : Nat) (hmode : 0 < mode) (hmax : mode ≤ 44) :
    (suzukiDF6D4OddDiagonalPrimeCorrelationInterval mode).Contains
      (suzukiDF6D4OddDiagonalPrimeCorrelation mode) := by
  have hCos := suzukiDF6D4FrozenPrimeCosineInterval_contains mode
    (hmax.trans (by norm_num))
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval_lower_nonneg
    suzukiDF6D4DiagonalPrimeTwoMinusDisplacementInterval_contains hCos
  have hSinOver :=
    suzukiDF6D4DiagonalPrimeSineOverFrequencyInterval_contains
      mode hmode hmax
  have h := RationalInterval.contains_scale (1 / 2)
    (RationalInterval.contains_add hProduct hSinOver)
  unfold suzukiDF6D4OddDiagonalPrimeCorrelationInterval
    suzukiDF6D4OddDiagonalPrimeCorrelation
  dsimp only
  have hangle :
      suzukiDF6D4DiagonalFrequency mode *
          suzukiDF6D4DiagonalPrimeDisplacement =
        (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar := by
    unfold suzukiDF6D4DiagonalFrequency
      suzukiDF6D4DiagonalPrimeDisplacement
    ring
  rw [hangle] at h ⊢
  convert h using 1 <;> ring

private def suzukiDF6D4DiagonalPrimeCoefficientInterval : RationalInterval :=
  fineSqrtTwoInterval.mulNonneg fineLogTwoInterval

private theorem suzukiDF6D4DiagonalPrimeCoefficientInterval_lower_nonneg :
    0 ≤ suzukiDF6D4DiagonalPrimeCoefficientInterval.lower := by
  norm_num [suzukiDF6D4DiagonalPrimeCoefficientInterval,
    RationalInterval.mulNonneg, fineSqrtTwoInterval, fineLogTwoInterval]

private theorem suzukiDF6D4DiagonalPrimeCoefficientInterval_contains :
    suzukiDF6D4DiagonalPrimeCoefficientInterval.Contains
      (Real.sqrt 2 * Real.log 2) := by
  exact RationalInterval.contains_mulNonneg
    (by norm_num [fineSqrtTwoInterval])
    fineLogTwoInterval_lower_nonneg_diag
    fineSqrtTwoInterval_contains fineLogTwoInterval_contains

def suzukiDF6D4EvenDiagonalPrimeTermInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.scale (-1)
    (suzukiDF6D4DiagonalPrimeCoefficientInterval.mulLeftNonneg
      (suzukiDF6D4EvenDiagonalPrimeCorrelationInterval mode))

def suzukiDF6D4OddDiagonalPrimeTermInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.scale (-1)
    (suzukiDF6D4DiagonalPrimeCoefficientInterval.mulLeftNonneg
      (suzukiDF6D4OddDiagonalPrimeCorrelationInterval mode))

theorem suzukiDF6D4EvenDiagonalPrimeTermInterval_contains
    (mode : Nat) (hmax : mode ≤ 44) :
    (suzukiDF6D4EvenDiagonalPrimeTermInterval mode).Contains
      (suzukiDF6D4EvenDiagonalPrimeTerm mode) := by
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4DiagonalPrimeCoefficientInterval_lower_nonneg
    suzukiDF6D4DiagonalPrimeCoefficientInterval_contains
    (suzukiDF6D4EvenDiagonalPrimeCorrelationInterval_contains mode hmax)
  have h := RationalInterval.contains_scale (-1) hProduct
  unfold suzukiDF6D4EvenDiagonalPrimeTermInterval
    suzukiDF6D4EvenDiagonalPrimeTerm
  convert h using 1 <;> norm_num <;> ring

theorem suzukiDF6D4OddDiagonalPrimeTermInterval_contains
    (mode : Nat) (hmode : 0 < mode) (hmax : mode ≤ 44) :
    (suzukiDF6D4OddDiagonalPrimeTermInterval mode).Contains
      (suzukiDF6D4OddDiagonalPrimeTerm mode) := by
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4DiagonalPrimeCoefficientInterval_lower_nonneg
    suzukiDF6D4DiagonalPrimeCoefficientInterval_contains
    (suzukiDF6D4OddDiagonalPrimeCorrelationInterval_contains mode hmode hmax)
  have h := RationalInterval.contains_scale (-1) hProduct
  unfold suzukiDF6D4OddDiagonalPrimeTermInterval
    suzukiDF6D4OddDiagonalPrimeTerm
  convert h using 1 <;> norm_num <;> ring

def suzukiDF6D4DiagonalConstantTermInterval : RationalInterval :=
  (fineLogFourPiInterval.add fineEulerInterval).neg

theorem suzukiDF6D4DiagonalConstantTermInterval_contains :
    suzukiDF6D4DiagonalConstantTermInterval.Contains
      suzukiDF6D4DiagonalConstantTerm := by
  have h := RationalInterval.contains_neg
    (RationalInterval.contains_add fineLogFourPiInterval_contains
      fineEulerInterval_contains)
  unfold suzukiDF6D4DiagonalConstantTermInterval
    suzukiDF6D4DiagonalConstantTerm
  exact h

def suzukiDF6D4EvenDiagonalEntryInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4EvenDiagonalPoleTermInterval mode).add
    (suzukiDF6D4EvenDiagonalPrimeTermInterval mode) |>.add
    suzukiDF6D4DiagonalConstantTermInterval |>.add
    (suzukiDF6D4EvenDiagonalGammaTermInterval mode)

def suzukiDF6D4OddDiagonalEntryInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4OddDiagonalPoleTermInterval mode).add
    (suzukiDF6D4OddDiagonalPrimeTermInterval mode) |>.add
    suzukiDF6D4DiagonalConstantTermInterval |>.add
    (suzukiDF6D4OddDiagonalGammaTermInterval mode)

theorem suzukiDF6D4EvenDiagonalEntryInterval_contains
    (mode : Nat) (hmax : mode ≤ 44) :
    (suzukiDF6D4EvenDiagonalEntryInterval mode).Contains
      (suzukiDF6D4EvenDiagonalEntry mode) := by
  have h := RationalInterval.contains_add
    (RationalInterval.contains_add
      (RationalInterval.contains_add
        (suzukiDF6D4EvenDiagonalPoleTermInterval_contains mode)
        (suzukiDF6D4EvenDiagonalPrimeTermInterval_contains mode hmax))
      suzukiDF6D4DiagonalConstantTermInterval_contains)
    (suzukiDF6D4EvenDiagonalGammaTermInterval_contains mode)
  unfold suzukiDF6D4EvenDiagonalEntryInterval
    suzukiDF6D4EvenDiagonalEntry
  exact h

theorem suzukiDF6D4OddDiagonalEntryInterval_contains
    (mode : Nat) (hmode : 0 < mode) (hmax : mode ≤ 44) :
    (suzukiDF6D4OddDiagonalEntryInterval mode).Contains
      (suzukiDF6D4OddDiagonalEntry mode) := by
  have h := RationalInterval.contains_add
    (RationalInterval.contains_add
      (RationalInterval.contains_add
        (suzukiDF6D4OddDiagonalPoleTermInterval_contains mode)
        (suzukiDF6D4OddDiagonalPrimeTermInterval_contains mode hmode hmax))
      suzukiDF6D4DiagonalConstantTermInterval_contains)
    (suzukiDF6D4OddDiagonalGammaTermInterval_contains mode hmode)
  unfold suzukiDF6D4OddDiagonalEntryInterval
    suzukiDF6D4OddDiagonalEntry
  exact h

def suzukiDF6D4FrozenEvenDiagonalEntryInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 1000000000000
    (suzukiDF6D4EvenDiagonalEntryInterval mode)

def suzukiDF6D4FrozenOddDiagonalEntryInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 1000000000000
    (suzukiDF6D4OddDiagonalEntryInterval mode)

theorem suzukiDF6D4FrozenEvenDiagonalEntryInterval_contains
    (mode : Nat) (hmax : mode ≤ 44) :
    (suzukiDF6D4FrozenEvenDiagonalEntryInterval mode).Contains
      (suzukiDF6D4EvenDiagonalEntry mode) := by
  unfold suzukiDF6D4FrozenEvenDiagonalEntryInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4EvenDiagonalEntryInterval_contains mode hmax)

theorem suzukiDF6D4FrozenOddDiagonalEntryInterval_contains
    (mode : Nat) (hmode : 0 < mode) (hmax : mode ≤ 44) :
    (suzukiDF6D4FrozenOddDiagonalEntryInterval mode).Contains
      (suzukiDF6D4OddDiagonalEntry mode) := by
  unfold suzukiDF6D4FrozenOddDiagonalEntryInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4OddDiagonalEntryInterval_contains mode hmode hmax)

end

end RiemannHypothesisProject.Experiments.M100
