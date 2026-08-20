import RiemannHypothesisProject.Experiments.M100.RationalTrigonometricEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDigammaIntervalEvaluator

/-!
# Frozen prime-angle sine enclosures for M100-DF6D4

The first-prime contribution uses `sin (mode * pi * log 2 / a*)`.  Every mode
through the frozen oscillatory cutoff `20000` is reduced to a residual of absolute
value below one; seven-term alternating Taylor enclosures then give exact
rational bounds.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Nearest quarter-turn used for prime-angle range reduction.  The rational
coefficient is a frozen 15-decimal enclosure midpoint for
`2 * log 2 / a*`; the subsequent exact residual checks, rather than this
comment, certify that it selects a valid quadrant through mode `20000`. -/
def suzukiDF6D4PrimeQuadrant (mode : Nat) : Nat :=
  (3233881577099095 * mode + 500000000000000) / 1000000000000000

/-- Interval for the unreduced prime angle. -/
def suzukiDF6D4PrimeAngleInterval (mode : Nat) : RationalInterval :=
  ((RationalInterval.scale (mode : Rat) suzukiDF6D4PiInterval).mulNonneg
      fineLogTwoInterval).divNonneg fineAStarInterval

private theorem suzukiDF6D4PrimeAngleNumerator_lower_nonneg (mode : Nat) :
    0 ≤ ((RationalInterval.scale (mode : Rat) suzukiDF6D4PiInterval).mulNonneg
      fineLogTwoInterval).lower := by
  unfold RationalInterval.mulNonneg RationalInterval.scale
    suzukiDF6D4PiInterval fineLogTwoInterval
  norm_num

theorem suzukiDF6D4PrimeAngleInterval_contains (mode : Nat) :
    (suzukiDF6D4PrimeAngleInterval mode).Contains
      ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar) := by
  have hPi := RationalInterval.contains_scale (mode : Rat)
    suzukiDF6D4PiInterval_contains
  have hProduct := RationalInterval.contains_mulNonneg
    (by
      unfold RationalInterval.scale suzukiDF6D4PiInterval
      norm_num)
    (by norm_num [fineLogTwoInterval]) hPi
    fineLogTwoInterval_contains
  have hQuotient := RationalInterval.contains_divNonneg
    (suzukiDF6D4PrimeAngleNumerator_lower_nonneg mode)
    (by norm_num [fineAStarInterval]) hProduct
    fineAStarInterval_contains
  unfold suzukiDF6D4PrimeAngleInterval
  convert hQuotient using 1
  norm_num

/-- Interval after subtracting the frozen nearest multiple of `pi / 2`. -/
def suzukiDF6D4PrimeResidualInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4PrimeAngleInterval mode).sub
    (RationalInterval.scale
      (suzukiDF6D4PrimeQuadrant mode / 2 : Rat) suzukiDF6D4PiInterval)

theorem suzukiDF6D4PrimeResidualInterval_contains (mode : Nat) :
    (suzukiDF6D4PrimeResidualInterval mode).Contains
      ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
        (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2) := by
  have hShift := RationalInterval.contains_scale
    (suzukiDF6D4PrimeQuadrant mode / 2 : Rat)
    suzukiDF6D4PiInterval_contains
  have hSub := RationalInterval.contains_sub
    (suzukiDF6D4PrimeAngleInterval_contains mode) hShift
  unfold suzukiDF6D4PrimeResidualInterval
  convert hSub using 1
  norm_num
  push_cast
  ring

/-- Nonnegative interval for the absolute reduced residual. -/
def suzukiDF6D4PrimeAbsResidualInterval (mode : Nat) : RationalInterval :=
  let R := suzukiDF6D4PrimeResidualInterval mode
  if R.upper ≤ 0 then R.neg else R

private theorem suzukiDF6D4PrimeResidualInterval_has_fixed_sign
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeResidualInterval mode).upper ≤ 0 ∨
      0 ≤ (suzukiDF6D4PrimeResidualInterval mode).lower := by
  have h : ∀ m : Fin 20001,
      (suzukiDF6D4PrimeResidualInterval m.val).upper ≤ 0 ∨
        0 ≤ (suzukiDF6D4PrimeResidualInterval m.val).lower := by
    native_decide
  exact h ⟨mode, by omega⟩

theorem suzukiDF6D4PrimeAbsResidualInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeAbsResidualInterval mode).Contains
      |(mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
        (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2| := by
  let r : Real :=
    (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
      (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2
  have hR := suzukiDF6D4PrimeResidualInterval_contains mode
  unfold suzukiDF6D4PrimeAbsResidualInterval
  dsimp only
  split_ifs with hNegative
  · have hNegativeReal :
        ((suzukiDF6D4PrimeResidualInterval mode).upper : Real) ≤ 0 := by
      exact_mod_cast hNegative
    have hr : r ≤ 0 := hR.2.trans hNegativeReal
    have hNeg := RationalInterval.contains_neg hR
    dsimp only [r] at hNeg hr ⊢
    simpa [abs_of_nonpos hr] using hNeg
  · have hLower :
        0 ≤ (suzukiDF6D4PrimeResidualInterval mode).lower := by
      rcases suzukiDF6D4PrimeResidualInterval_has_fixed_sign mode hmode with
        hContradiction | hLower
      · exact False.elim (hNegative hContradiction)
      · exact hLower
    have hLowerReal :
        (0 : Real) ≤ ((suzukiDF6D4PrimeResidualInterval mode).lower : Real) := by
      exact_mod_cast hLower
    have hr : 0 ≤ r := hLowerReal.trans hR.1
    dsimp only [r] at hr ⊢
    simpa [abs_of_nonneg hr] using hR

theorem suzukiDF6D4PrimeAbsResidualInterval_lower_nonneg
    (mode : Nat) (hmode : mode ≤ 20000) :
    0 ≤ (suzukiDF6D4PrimeAbsResidualInterval mode).lower := by
  have h : ∀ m : Fin 20001,
      0 ≤ (suzukiDF6D4PrimeAbsResidualInterval m.val).lower := by
    native_decide
  exact h ⟨mode, by omega⟩

theorem suzukiDF6D4PrimeAbsResidualInterval_upper_le_one
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeAbsResidualInterval mode).upper ≤ 1 := by
  have h : ∀ m : Fin 20001,
      (suzukiDF6D4PrimeAbsResidualInterval m.val).upper ≤ 1 := by
    native_decide
  exact h ⟨mode, by omega⟩

/-- The sine of a quarter-turn-shifted residual, represented recursively so
that interval transport uses only negation. -/
def suzukiDF6D4QuarterSine : Nat → Real → Real
  | 0, x => Real.sin x
  | 1, x => Real.cos x
  | n + 2, x => -suzukiDF6D4QuarterSine n x

theorem suzukiDF6D4_sin_add_quarter_turn
    (q : Nat) (x : Real) :
    Real.sin (x + (q : Real) * Real.pi / 2) =
      suzukiDF6D4QuarterSine q x := by
  induction q using Nat.twoStepInduction with
  | zero => simp [suzukiDF6D4QuarterSine]
  | one => simpa [suzukiDF6D4QuarterSine] using Real.sin_add_pi_div_two x
  | more q ih0 ih1 =>
      rw [show x + ((q + 2 : Nat) : Real) * Real.pi / 2 =
          (x + (q : Real) * Real.pi / 2) + Real.pi by
        push_cast
        ring,
        Real.sin_add_pi, ih0]
      rfl

def suzukiDF6D4QuarterSineInterval :
    Nat → RationalInterval → RationalInterval → RationalInterval
  | 0, S, _ => S
  | 1, _, C => C
  | n + 2, S, C => (suzukiDF6D4QuarterSineInterval n S C).neg

theorem suzukiDF6D4QuarterSineInterval_contains
    (q : Nat) {S C : RationalInterval} {x : Real}
    (hS : S.Contains (Real.sin x)) (hC : C.Contains (Real.cos x)) :
    (suzukiDF6D4QuarterSineInterval q S C).Contains
      (suzukiDF6D4QuarterSine q x) := by
  induction q using Nat.twoStepInduction with
  | zero => exact hS
  | one => exact hC
  | more q ih0 ih1 =>
      exact RationalInterval.contains_neg ih0

def suzukiDF6D4PrimeResidualSineInterval (mode : Nat) : RationalInterval :=
  let R := suzukiDF6D4PrimeResidualInterval mode
  let Y := suzukiDF6D4PrimeAbsResidualInterval mode
  let S := RationalInterval.sineTaylor 7 Y
  if R.upper ≤ 0 then S.neg else S

def suzukiDF6D4PrimeResidualCosineInterval (mode : Nat) : RationalInterval :=
  RationalInterval.cosineTaylor 7
    (suzukiDF6D4PrimeAbsResidualInterval mode)

private theorem suzukiDF6D4PrimeResidualSineInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeResidualSineInterval mode).Contains
      (Real.sin
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
          (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2)) := by
  let r : Real :=
    (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
      (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2
  let Y := suzukiDF6D4PrimeAbsResidualInterval mode
  have hY : Y.Contains |r| := by
    dsimp only [Y, r]
    exact suzukiDF6D4PrimeAbsResidualInterval_contains mode hmode
  have hTaylor := RationalInterval.contains_sineTaylor 7
    (suzukiDF6D4PrimeAbsResidualInterval_lower_nonneg mode hmode)
    (suzukiDF6D4PrimeAbsResidualInterval_upper_le_one mode hmode) hY
  unfold suzukiDF6D4PrimeResidualSineInterval
  dsimp only [Y]
  split_ifs with hNegative
  · have hR := suzukiDF6D4PrimeResidualInterval_contains mode
    have hNegativeReal :
        ((suzukiDF6D4PrimeResidualInterval mode).upper : Real) ≤ 0 := by
      exact_mod_cast hNegative
    have hr : r ≤ 0 := hR.2.trans hNegativeReal
    have hNeg := RationalInterval.contains_neg hTaylor
    have hValue : -Real.sin |r| = Real.sin r := by
      rw [abs_of_nonpos hr, Real.sin_neg]
      ring
    rw [hValue] at hNeg
    simpa only [r] using hNeg
  · have hLower :
        0 ≤ (suzukiDF6D4PrimeResidualInterval mode).lower := by
      rcases suzukiDF6D4PrimeResidualInterval_has_fixed_sign mode hmode with
        hContradiction | hLower
      · exact False.elim (hNegative hContradiction)
      · exact hLower
    have hR := suzukiDF6D4PrimeResidualInterval_contains mode
    have hLowerReal :
        (0 : Real) ≤ ((suzukiDF6D4PrimeResidualInterval mode).lower : Real) := by
      exact_mod_cast hLower
    have hr : 0 ≤ r := hLowerReal.trans hR.1
    have hValue : Real.sin |r| = Real.sin r := by
      rw [abs_of_nonneg hr]
    rw [hValue] at hTaylor
    simpa only [r] using hTaylor

private theorem suzukiDF6D4PrimeResidualCosineInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeResidualCosineInterval mode).Contains
      (Real.cos
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
          (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2)) := by
  let r : Real :=
    (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
      (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2
  let Y := suzukiDF6D4PrimeAbsResidualInterval mode
  have hY : Y.Contains |r| := by
    dsimp only [Y, r]
    exact suzukiDF6D4PrimeAbsResidualInterval_contains mode hmode
  have hTaylor := RationalInterval.contains_cosineTaylor 7
    (suzukiDF6D4PrimeAbsResidualInterval_lower_nonneg mode hmode)
    (suzukiDF6D4PrimeAbsResidualInterval_upper_le_one mode hmode) hY
  unfold suzukiDF6D4PrimeResidualCosineInterval
  rcases le_total r 0 with hr | hr
  · dsimp only [Y, r] at hTaylor ⊢
    simpa [abs_of_nonpos hr, Real.cos_neg] using hTaylor
  · dsimp only [Y, r] at hTaylor ⊢
    simpa [abs_of_nonneg hr] using hTaylor

/-- Complete sine enclosure after restoring the frozen quarter-turn. -/
def suzukiDF6D4PrimeSineInterval (mode : Nat) : RationalInterval :=
  suzukiDF6D4QuarterSineInterval (suzukiDF6D4PrimeQuadrant mode)
    (suzukiDF6D4PrimeResidualSineInterval mode)
    (suzukiDF6D4PrimeResidualCosineInterval mode)

theorem suzukiDF6D4PrimeSineInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeSineInterval mode).Contains
      (Real.sin
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar)) := by
  let r : Real :=
    (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
      (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2
  have hQuarter := suzukiDF6D4QuarterSineInterval_contains
    (suzukiDF6D4PrimeQuadrant mode)
    (suzukiDF6D4PrimeResidualSineInterval_contains mode hmode)
    (suzukiDF6D4PrimeResidualCosineInterval_contains mode hmode)
  have hIdentity := suzukiDF6D4_sin_add_quarter_turn
    (suzukiDF6D4PrimeQuadrant mode) r
  unfold suzukiDF6D4PrimeSineInterval
  rw [← hIdentity] at hQuarter
  convert hQuarter using 1
  dsimp only [r]
  ring

def suzukiDF6D4FrozenPrimeSineInterval (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4PrimeSineInterval mode)

theorem suzukiDF6D4FrozenPrimeSineInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4FrozenPrimeSineInterval mode).Contains
      (Real.sin
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar)) := by
  unfold suzukiDF6D4FrozenPrimeSineInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4PrimeSineInterval_contains mode hmode)

/-- Complete cosine enclosure obtained by advancing the same frozen
quarter-turn reconstruction by one step. -/
def suzukiDF6D4PrimeCosineInterval (mode : Nat) : RationalInterval :=
  suzukiDF6D4QuarterSineInterval (suzukiDF6D4PrimeQuadrant mode + 1)
    (suzukiDF6D4PrimeResidualSineInterval mode)
    (suzukiDF6D4PrimeResidualCosineInterval mode)

theorem suzukiDF6D4PrimeCosineInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4PrimeCosineInterval mode).Contains
      (Real.cos
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar)) := by
  let r : Real :=
    (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar -
      (suzukiDF6D4PrimeQuadrant mode : Real) * Real.pi / 2
  have hQuarter := suzukiDF6D4QuarterSineInterval_contains
    (suzukiDF6D4PrimeQuadrant mode + 1)
    (suzukiDF6D4PrimeResidualSineInterval_contains mode hmode)
    (suzukiDF6D4PrimeResidualCosineInterval_contains mode hmode)
  have hIdentity := suzukiDF6D4_sin_add_quarter_turn
    (suzukiDF6D4PrimeQuadrant mode + 1) r
  unfold suzukiDF6D4PrimeCosineInterval
  rw [← hIdentity] at hQuarter
  have hAngle :
      r + ((suzukiDF6D4PrimeQuadrant mode + 1 : Nat) : Real) * Real.pi / 2 =
        (mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar +
          Real.pi / 2 := by
    dsimp only [r]
    push_cast
    ring
  rw [hAngle, Real.sin_add_pi_div_two] at hQuarter
  exact hQuarter

def suzukiDF6D4FrozenPrimeCosineInterval (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4PrimeCosineInterval mode)

theorem suzukiDF6D4FrozenPrimeCosineInterval_contains
    (mode : Nat) (hmode : mode ≤ 20000) :
    (suzukiDF6D4FrozenPrimeCosineInterval mode).Contains
      (Real.cos
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar)) := by
  unfold suzukiDF6D4FrozenPrimeCosineInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4PrimeCosineInterval_contains mode hmode)

end

end RiemannHypothesisProject.Experiments.M100
