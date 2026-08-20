import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointPrimeSineEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointRestorationIntervalEvaluator

/-!
# Complete endpoint sine-transform enclosures for M100-DF6D4

This module assembles the pole, archimedean, restoration, and first-prime
pieces into the exact complete transforms `J_n` used by the off-diagonal
convolution reconstruction.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Exact analytic pole contribution to the complete sine transform. -/
def suzukiDF6D4PoleSineTransform (mode : Nat) : Real :=
  let w := (mode : Real) * Real.pi / suzukiProjectAStar
  4 * w * (1 - Real.cosh suzukiProjectAStar) / (w ^ 2 + 1 / 4)

/-- Exact analytic first-prime contribution. -/
def suzukiDF6D4PrimeSineTransform (mode : Nat) : Real :=
  -Real.sqrt 2 * Real.log 2 *
    Real.sin ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar)

/-- The complete transform reconstructed by the frozen endpoint script. -/
def suzukiDF6D4CompleteSineTransform (mode : Nat) : Real :=
  suzukiDF6D4PoleSineTransform mode -
      ((Complex.digamma
        ((1 / 4 : Complex) +
          (((mode : Real) * Real.pi / suzukiProjectAStar) / 2) *
            Complex.I)).im -
        ∑' k : Nat, suzukiDF6D4RestorationTerm mode k) +
    suzukiDF6D4PrimeSineTransform mode

/-- `exp (a*)` obtained by reciprocal transport from the admitted
`exp (-a*)` interval. -/
def suzukiDF6D4ExpAStarInterval : RationalInterval :=
  fineExpNegAStarInterval.invPos

theorem suzukiDF6D4ExpAStarInterval_contains :
    suzukiDF6D4ExpAStarInterval.Contains
      (Real.exp suzukiProjectAStar) := by
  have hInv := RationalInterval.contains_invPos
    (by norm_num [fineExpNegAStarInterval])
    fineExpNegAStarInterval_contains
  unfold suzukiDF6D4ExpAStarInterval
  convert hInv using 1
  rw [Real.exp_neg]
  exact (inv_inv (Real.exp suzukiProjectAStar)).symm

/-- Cosh enclosure sharing the same admitted exponential dependency. -/
def suzukiDF6D4CoshAStarInterval : RationalInterval :=
  RationalInterval.scale (1 / 2)
    (suzukiDF6D4ExpAStarInterval.add fineExpNegAStarInterval)

theorem suzukiDF6D4CoshAStarInterval_contains :
    suzukiDF6D4CoshAStarInterval.Contains
      (Real.cosh suzukiProjectAStar) := by
  have hAdd := RationalInterval.contains_add
    suzukiDF6D4ExpAStarInterval_contains
    fineExpNegAStarInterval_contains
  have hScale := RationalInterval.contains_scale (1 / 2) hAdd
  unfold suzukiDF6D4CoshAStarInterval
  rw [Real.cosh_eq]
  convert hScale using 1
  norm_num
  ring

def suzukiDF6D4CoshMinusOneInterval : RationalInterval :=
  suzukiDF6D4CoshAStarInterval.sub (RationalInterval.point 1)

private theorem suzukiDF6D4CoshMinusOneInterval_lower_nonneg :
    0 ≤ suzukiDF6D4CoshMinusOneInterval.lower := by
  norm_num [suzukiDF6D4CoshMinusOneInterval,
    suzukiDF6D4CoshAStarInterval, suzukiDF6D4ExpAStarInterval,
    fineExpNegAStarInterval, RationalInterval.scale,
    RationalInterval.sub, RationalInterval.add, RationalInterval.neg,
    RationalInterval.point, RationalInterval.invPos]

private theorem suzukiDF6D4CoshMinusOneInterval_contains :
    suzukiDF6D4CoshMinusOneInterval.Contains
      (Real.cosh suzukiProjectAStar - 1) := by
  unfold suzukiDF6D4CoshMinusOneInterval
  have hOne : (RationalInterval.point (1 : Rat)).Contains (1 : Real) := by
    simpa using RationalInterval.contains_point (1 : Rat)
  exact RationalInterval.contains_sub suzukiDF6D4CoshAStarInterval_contains
    hOne

def suzukiDF6D4PoleDenominatorInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4WaveNumberInterval mode).powNonneg 2 |>.add
    (RationalInterval.point (1 / 4))

private theorem suzukiDF6D4PoleDenominatorInterval_lower_pos
    (mode : Nat) :
    0 < (suzukiDF6D4PoleDenominatorInterval mode).lower := by
  unfold suzukiDF6D4PoleDenominatorInterval RationalInterval.add
    RationalInterval.powNonneg RationalInterval.point
  dsimp only
  nlinarith [sq_nonneg (suzukiDF6D4WaveNumberInterval mode).lower]

def suzukiDF6D4PoleSineTransformInterval (mode : Nat) : RationalInterval :=
  let magnitudeNumerator :=
    (suzukiDF6D4WaveNumberInterval mode).mulNonneg
      suzukiDF6D4CoshMinusOneInterval
  RationalInterval.scale (-4)
    (magnitudeNumerator.divNonneg
      (suzukiDF6D4PoleDenominatorInterval mode))

theorem suzukiDF6D4PoleSineTransformInterval_contains (mode : Nat) :
    (suzukiDF6D4PoleSineTransformInterval mode).Contains
      (suzukiDF6D4PoleSineTransform mode) := by
  let W := suzukiDF6D4WaveNumberInterval mode
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hW : W.Contains w := by
    dsimp only [W, w]
    exact suzukiDF6D4WaveNumberInterval_contains mode
  have hNumerator := RationalInterval.contains_mulNonneg
    (suzukiDF6D4WaveNumberInterval_lower_nonneg mode)
    suzukiDF6D4CoshMinusOneInterval_lower_nonneg hW
    suzukiDF6D4CoshMinusOneInterval_contains
  have hWSq := RationalInterval.contains_powNonneg 2
    (suzukiDF6D4WaveNumberInterval_lower_nonneg mode) hW
  have hDenominator := RationalInterval.contains_add hWSq
    (RationalInterval.contains_point (1 / 4))
  have hNumeratorLower :
      0 ≤ (W.mulNonneg suzukiDF6D4CoshMinusOneInterval).lower := by
    unfold RationalInterval.mulNonneg
    exact mul_nonneg (suzukiDF6D4WaveNumberInterval_lower_nonneg mode)
      suzukiDF6D4CoshMinusOneInterval_lower_nonneg
  have hBase := RationalInterval.contains_divNonneg hNumeratorLower
    (suzukiDF6D4PoleDenominatorInterval_lower_pos mode)
    hNumerator hDenominator
  have hScaled := RationalInterval.contains_scale (-4) hBase
  unfold suzukiDF6D4PoleSineTransformInterval
  dsimp only [W] at hScaled ⊢
  unfold suzukiDF6D4PoleSineTransform
  dsimp only [w]
  convert hScaled using 1
  ring

def suzukiDF6D4PrimeCoefficientInterval : RationalInterval :=
  fineSqrtTwoInterval.mulNonneg fineLogTwoInterval

private theorem suzukiDF6D4PrimeCoefficientInterval_lower_nonneg :
    0 ≤ suzukiDF6D4PrimeCoefficientInterval.lower := by
  norm_num [suzukiDF6D4PrimeCoefficientInterval,
    RationalInterval.mulNonneg, fineSqrtTwoInterval,
    fineLogTwoInterval]

private theorem suzukiDF6D4PrimeCoefficientInterval_contains :
    suzukiDF6D4PrimeCoefficientInterval.Contains
      (Real.sqrt 2 * Real.log 2) :=
  RationalInterval.contains_mulNonneg
    (by norm_num [fineSqrtTwoInterval])
    (by norm_num [fineLogTwoInterval])
    fineSqrtTwoInterval_contains fineLogTwoInterval_contains

def suzukiDF6D4PrimeSineTransformInterval (mode : Nat) : RationalInterval :=
  RationalInterval.scale (-1)
    (suzukiDF6D4PrimeCoefficientInterval.mulLeftNonneg
      (suzukiDF6D4FrozenPrimeSineInterval mode))

theorem suzukiDF6D4PrimeSineTransformInterval_contains
    (mode : Nat) (hmode : mode ≤ 602) :
    (suzukiDF6D4PrimeSineTransformInterval mode).Contains
      (suzukiDF6D4PrimeSineTransform mode) := by
  have hProduct := RationalInterval.contains_mulLeftNonneg
    suzukiDF6D4PrimeCoefficientInterval_lower_nonneg
    suzukiDF6D4PrimeCoefficientInterval_contains
    (suzukiDF6D4FrozenPrimeSineInterval_contains mode
      (hmode.trans (by norm_num)))
  have hNeg := RationalInterval.contains_scale (-1) hProduct
  unfold suzukiDF6D4PrimeSineTransformInterval
  unfold suzukiDF6D4PrimeSineTransform
  convert hNeg using 1
  norm_num

/-- Complete exact-rational `J_n` enclosure. -/
def suzukiDF6D4CompleteSineTransformInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4PoleSineTransformInterval mode).sub
      ((suzukiDF6D4FrozenDigammaInterval mode).sub
        (suzukiDF6D4FrozenRestorationInterval mode)) |>.add
    (suzukiDF6D4PrimeSineTransformInterval mode)

theorem suzukiDF6D4CompleteSineTransformInterval_contains
    (mode : Nat) (hmode : mode ≤ 602) :
    (suzukiDF6D4CompleteSineTransformInterval mode).Contains
      (suzukiDF6D4CompleteSineTransform mode) := by
  have hArch := RationalInterval.contains_sub
    (suzukiDF6D4FrozenDigammaInterval_contains mode hmode)
    (suzukiDF6D4FrozenRestorationInterval_contains mode)
  have hPoleArch := RationalInterval.contains_sub
    (suzukiDF6D4PoleSineTransformInterval_contains mode) hArch
  have hComplete := RationalInterval.contains_add hPoleArch
    (suzukiDF6D4PrimeSineTransformInterval_contains mode hmode)
  unfold suzukiDF6D4CompleteSineTransformInterval
  unfold suzukiDF6D4CompleteSineTransform
  exact hComplete

/-- Frozen output grid for the 44 nonzero convolution transforms. -/
def suzukiDF6D4FrozenCompleteSineTransformInterval
    (mode : Nat) : RationalInterval :=
  RationalInterval.roundOut 10000000000000000
    (suzukiDF6D4CompleteSineTransformInterval mode)

theorem suzukiDF6D4FrozenCompleteSineTransformInterval_contains
    (mode : Nat) (hmode : mode ≤ 602) :
    (suzukiDF6D4FrozenCompleteSineTransformInterval mode).Contains
      (suzukiDF6D4CompleteSineTransform mode) := by
  unfold suzukiDF6D4FrozenCompleteSineTransformInterval
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4CompleteSineTransformInterval_contains mode hmode)

end

end RiemannHypothesisProject.Experiments.M100
