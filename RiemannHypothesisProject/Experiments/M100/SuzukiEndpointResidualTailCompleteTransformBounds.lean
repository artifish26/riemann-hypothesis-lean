import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDF0Enclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailTransformBounds

/-!
# Complete-transform tail receiving surface for M100-DF6D4

The comparison and prime pieces of the large-mode transform bound are proved
here.  The only remaining analytic input is stated narrowly as a bound on the
smooth-transform difference.  It is the Fourier consequence of the X21/FT3
total-variation argument and is not hidden in an endpoint certificate record.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- Exact decimal upper bound used by the FT3 and DF1 scripts. -/
def suzukiDF6D4RemainderVariationUpper : Real :=
  225416424470513 / 500000000000000

theorem suzukiDF6D4RemainderVariation_nonneg :
    0 ≤ suzukiDF6D4DF0RemainderVariation := by
  have hcontains := suzukiDF6D4DF0RemainderVariationInterval_contains
  have hlower : (0 : Rat) ≤
      suzukiDF6D4DF0RemainderVariationInterval.lower := by native_decide
  have hzero : (0 : Real) ≤
      (suzukiDF6D4DF0RemainderVariationInterval.lower : Rat) := by
    exact_mod_cast hlower
  exact hzero.trans hcontains.1

theorem suzukiDF6D4RemainderVariation_le_upper :
    suzukiDF6D4DF0RemainderVariation ≤
      suzukiDF6D4RemainderVariationUpper := by
  have hcontains := suzukiDF6D4DF0RemainderVariationInterval_contains
  have hupper :
      suzukiDF6D4DF0RemainderVariationInterval.upper ≤
        (225416424470513 / 500000000000000 : Rat) := by native_decide
  have hupperReal :
      (suzukiDF6D4DF0RemainderVariationInterval.upper : Rat) ≤
        suzukiDF6D4RemainderVariationUpper := by
    have hcast := (Rat.cast_le (K := Real)).2 hupper
    simpa [suzukiDF6D4RemainderVariationUpper] using hcast
  exact hcontains.2.trans hupperReal

/-- The first-prime oscillation has amplitude at most `sqrt(2) * log(2)`. -/
theorem suzukiDF6D4PrimeSineTransform_abs_le (mode : Nat) :
    |suzukiDF6D4PrimeSineTransform mode| ≤ Real.sqrt 2 * Real.log 2 := by
  have hcoeff : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg 2) (Real.log_nonneg (by norm_num))
  unfold suzukiDF6D4PrimeSineTransform
  rw [abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (Real.sqrt_nonneg 2),
    abs_of_nonneg (Real.log_nonneg (by norm_num))]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left
      (Real.abs_sin_le_one
        ((mode : Real) * Real.pi * Real.log 2 / suzukiProjectAStar))
      hcoeff

/-- The smooth part left after removing the comparison transform and the
explicit prime-2 oscillation. -/
def suzukiDF6D4SmoothTransformDifference (mode : Nat) : Real :=
  suzukiDF6D4CompleteSineTransform mode -
    suzukiDF6D4ComparisonSineTransform mode -
      suzukiDF6D4PrimeSineTransform mode

theorem suzukiDF6D4Complete_sub_comparison_eq
    (mode : Nat) :
    suzukiDF6D4CompleteSineTransform mode -
        suzukiDF6D4ComparisonSineTransform mode =
      suzukiDF6D4PrimeSineTransform mode +
        suzukiDF6D4SmoothTransformDifference mode := by
  unfold suzukiDF6D4SmoothTransformDifference
  ring

/-- Narrow receiving theorem for the X21/FT3 smooth-variation Fourier bound. -/
theorem suzukiDF6D4Complete_sub_comparison_abs_le_of_smooth
    (mode : Nat) (smoothBound : Real)
    (hsmooth : |suzukiDF6D4SmoothTransformDifference mode| ≤ smoothBound) :
    |suzukiDF6D4CompleteSineTransform mode -
        suzukiDF6D4ComparisonSineTransform mode| ≤
      Real.sqrt 2 * Real.log 2 + smoothBound := by
  rw [suzukiDF6D4Complete_sub_comparison_eq]
  exact (abs_add_le _ _).trans
    (add_le_add (suzukiDF6D4PrimeSineTransform_abs_le mode) hsmooth)

/-- Complete-transform bound assembled from the proved comparison/prime
estimates and the one visible smooth-transform premise. -/
theorem suzukiDF6D4CompleteSineTransform_abs_le_of_smooth
    (mode : Nat) (hmode : 1 ≤ mode) (smoothBound : Real)
    (hsmooth : |suzukiDF6D4SmoothTransformDifference mode| ≤ smoothBound) :
    |suzukiDF6D4CompleteSineTransform mode| ≤
      Real.pi / 2 + 1 / (Real.pi * mode) +
        Real.sqrt 2 * Real.log 2 + smoothBound := by
  have hcomparison := suzukiDF6D4ComparisonSineTransform_abs_le mode hmode
  have hdelta := suzukiDF6D4Complete_sub_comparison_abs_le_of_smooth
    mode smoothBound hsmooth
  have hdecomp :
      suzukiDF6D4CompleteSineTransform mode =
        suzukiDF6D4ComparisonSineTransform mode +
          (suzukiDF6D4CompleteSineTransform mode -
            suzukiDF6D4ComparisonSineTransform mode) := by ring
  rw [hdecomp]
  calc
    |suzukiDF6D4ComparisonSineTransform mode +
        (suzukiDF6D4CompleteSineTransform mode -
          suzukiDF6D4ComparisonSineTransform mode)| ≤
      |suzukiDF6D4ComparisonSineTransform mode| +
        |suzukiDF6D4CompleteSineTransform mode -
          suzukiDF6D4ComparisonSineTransform mode| := abs_add_le _ _
    _ ≤ (Real.pi / 2 + 1 / (Real.pi * mode)) +
        (Real.sqrt 2 * Real.log 2 + smoothBound) :=
      add_le_add hcomparison hdelta
    _ = Real.pi / 2 + 1 / (Real.pi * mode) +
        Real.sqrt 2 * Real.log 2 + smoothBound := by ring

/-- Frozen mode-601 receiving surface in precisely the script's constants.
The premise is the still-open smooth-variation Fourier estimate. -/
theorem suzukiDF6D4CompleteSineTransform_abs_le_frozen_of_smoothVariation
    (mode : Nat) (hmode : 601 ≤ mode)
    (hsmooth :
      |suzukiDF6D4SmoothTransformDifference mode| ≤
        (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
          Real.pi) / mode) :
    |suzukiDF6D4CompleteSineTransform mode| ≤
      Real.pi / 2 + 1 / (Real.pi * 601) +
        Real.sqrt 2 * Real.log 2 +
          (2 * suzukiDF6D4RemainderVariationUpper * suzukiProjectAStar /
            Real.pi) / 601 := by
  have hmodeOne : 1 ≤ mode := by omega
  have hmodeReal : (601 : Real) ≤ mode := by exact_mod_cast hmode
  have hcomparisonDenom :
      1 / (Real.pi * mode) ≤ 1 / (Real.pi * 601) := by
    exact div_le_div_of_nonneg_left (by norm_num)
      (mul_pos Real.pi_pos (by norm_num))
      (mul_le_mul_of_nonneg_left hmodeReal Real.pi_pos.le)
  have hvariationNumeratorNonneg :
      0 ≤ 2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
        Real.pi := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) suzukiDF6D4RemainderVariation_nonneg)
        suzukiProjectAStar_pos.le)
      Real.pi_pos.le
  have hsmoothMode :
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
          Real.pi) / mode ≤
        (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
          Real.pi) / 601 := by
    exact div_le_div_of_nonneg_left hvariationNumeratorNonneg
      (by norm_num) hmodeReal
  have hvariationUpper :
      (2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
          Real.pi) / 601 ≤
        (2 * suzukiDF6D4RemainderVariationUpper * suzukiProjectAStar /
          Real.pi) / 601 := by
    gcongr
    · exact suzukiProjectAStar_pos.le
    exact suzukiDF6D4RemainderVariation_le_upper
  have hcomplete := suzukiDF6D4CompleteSineTransform_abs_le_of_smooth
    mode hmodeOne
    ((2 * suzukiDF6D4DF0RemainderVariation * suzukiProjectAStar /
      Real.pi) / mode) hsmooth
  linarith

end

end RiemannHypothesisProject.Experiments.M100
