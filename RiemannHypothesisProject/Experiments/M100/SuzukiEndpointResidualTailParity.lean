import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFullConvolutionEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailExpansion

/-!
# Parity-normalized residual tails for M100-DF6D4

This module connects the actual project convolution definitions to the shared
even and odd normalized-resolvent kernels.  It proves only exact parity and
algebraic identities; the large-mode transform bounds remain a separate
analytic layer.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- The difference and total frequencies have the same parity. -/
theorem suzukiDF6D4AlternatingSign_sub_eq_add
    (left right : Nat) (hleftRight : left ≤ right) :
    suzukiDF6D4AlternatingSign (right - left) =
      suzukiDF6D4AlternatingSign (left + right) := by
  unfold suzukiDF6D4AlternatingSign
  have hparity : (right - left) % 2 = (left + right) % 2 := by omega
  rw [hparity]

/-- Every parity coefficient has unit absolute value after casting to `Real`. -/
theorem suzukiDF6D4AlternatingSign_real_abs (mode : Nat) :
    |(((suzukiDF6D4AlternatingSign mode : Rat) : Real))| = 1 := by
  unfold suzukiDF6D4AlternatingSign
  split <;> norm_num

/-- The chosen `±1` convention is the negative of the usual parity
character, so addition introduces one extra minus sign. -/
theorem suzukiDF6D4AlternatingSign_add
    (left right : Nat) :
    suzukiDF6D4AlternatingSign (left + right) =
      -suzukiDF6D4AlternatingSign left *
        suzukiDF6D4AlternatingSign right := by
  unfold suzukiDF6D4AlternatingSign
  split <;> split <;> split <;> norm_num <;> omega

/-- Tail parity factor shared by every row of a fixed residual column. -/
def suzukiDF6D4TailParity (mode : Nat) : Rat :=
  -suzukiDF6D4AlternatingSign mode

theorem suzukiDF6D4AlternatingSign_sub_factor
    (left right : Nat) (hleftRight : left ≤ right) :
    suzukiDF6D4AlternatingSign (right - left) =
      suzukiDF6D4TailParity right *
        suzukiDF6D4AlternatingSign left := by
  rw [suzukiDF6D4AlternatingSign_sub_eq_add left right hleftRight]
  rw [suzukiDF6D4AlternatingSign_add]
  unfold suzukiDF6D4TailParity
  ring

theorem suzukiDF6D4TailParity_real_abs (mode : Nat) :
    |(((suzukiDF6D4TailParity mode : Rat) : Real))| = 1 := by
  unfold suzukiDF6D4TailParity
  push_cast
  rw [abs_neg, suzukiDF6D4AlternatingSign_real_abs]

/-- The actual even off-diagonal entry is the signed normalized even kernel.
This is the exact identity expanded by the FT3 residual-tail script. -/
theorem suzukiDF6D4EvenOffDiagonal_eq_signedNormalizedKernel
    (left right : Nat) (hleftRight : left < right) :
    suzukiDF6D4EvenOffDiagonal left right =
      suzukiDF6D4EvenModeScale left *
        suzukiDF6D4EvenModeScale right * Real.pi⁻¹ *
        (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
          (((right : Real) * suzukiDF6D4CompleteSineTransform right -
              (left : Real) * suzukiDF6D4CompleteSineTransform left) /
            ((right : Real) ^ 2 - (left : Real) ^ 2))) := by
  have hle : left ≤ right := Nat.le_of_lt hleftRight
  have hsub : (right : Real) - left ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hleftRight.ne')
  have hrightPos : (0 : Real) < right := by
    exact_mod_cast (by omega : 0 < right)
  have hadd : (right : Real) + left ≠ 0 := ne_of_gt (by positivity)
  have hfactor : (right : Real) ^ 2 - (left : Real) ^ 2 =
      ((right : Real) - left) * ((right : Real) + left) := by ring
  have hsquare : (right : Real) ^ 2 - (left : Real) ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hsub hadd
  unfold suzukiDF6D4EvenOffDiagonal
  dsimp only
  rw [suzukiDF6D4AlternatingSign_sub_eq_add left right hle]
  push_cast
  rw [Nat.cast_sub hle]
  field_simp [hsub, hadd, hsquare]
  ring

/-- The actual odd off-diagonal entry is the signed normalized odd kernel.
This is the exact identity expanded by the DF1 residual-tail script. -/
theorem suzukiDF6D4OddOffDiagonal_eq_signedNormalizedKernel
    (left right : Nat) (hleftRight : left < right) :
    suzukiDF6D4OddOffDiagonal left right =
      Real.pi⁻¹ *
        (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
          (((left : Real) * suzukiDF6D4CompleteSineTransform right -
              (right : Real) * suzukiDF6D4CompleteSineTransform left) /
            ((right : Real) ^ 2 - (left : Real) ^ 2))) := by
  have hle : left ≤ right := Nat.le_of_lt hleftRight
  have hsub : (right : Real) - left ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hleftRight.ne')
  have hrightPos : (0 : Real) < right := by
    exact_mod_cast (by omega : 0 < right)
  have hadd : (right : Real) + left ≠ 0 := ne_of_gt (by positivity)
  have hfactor : (right : Real) ^ 2 - (left : Real) ^ 2 =
      ((right : Real) - left) * ((right : Real) + left) := by ring
  have hsquare : (right : Real) ^ 2 - (left : Real) ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hsub hadd
  unfold suzukiDF6D4OddOffDiagonal
  dsimp only
  rw [suzukiDF6D4AlternatingSign_sub_eq_add left right hle]
  push_cast
  rw [Nat.cast_sub hle]
  field_simp [hsub, hadd, hsquare]
  ring

/-- The comparison even off-diagonal entry has the same signed normalized
kernel as the complete entry, with the comparison transform substituted for
the complete transform. -/
theorem suzukiDF6D4ComparisonEvenOffDiagonal_eq_signedNormalizedKernel
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right) :
    suzukiDF6D4ComparisonEvenOffDiagonal left right =
      suzukiDF6D4EvenModeScale left *
        suzukiDF6D4EvenModeScale right * Real.pi⁻¹ *
        (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
          (((right : Real) * suzukiDF6D4ComparisonSineTransform right -
              (left : Real) * suzukiDF6D4ComparisonSineTransform left) /
            ((right : Real) ^ 2 - (left : Real) ^ 2))) := by
  have hle : left ≤ right := Nat.le_of_lt hleftRight
  have hsub : (right : Real) - left ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hleftRight.ne')
  have hrightPos : (0 : Real) < right := by
    exact_mod_cast (by omega : 0 < right)
  have hadd : (right : Real) + left ≠ 0 := ne_of_gt (by positivity)
  have hfactor : (right : Real) ^ 2 - (left : Real) ^ 2 =
      ((right : Real) - left) * ((right : Real) + left) := by ring
  have hsquare : (right : Real) ^ 2 - (left : Real) ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hsub hadd
  unfold suzukiDF6D4ComparisonEvenOffDiagonal
  dsimp only
  rw [suzukiDF6D4AlternatingSign_sub_eq_add left right hle]
  push_cast
  rw [Nat.cast_sub hle]
  field_simp [hsub, hadd, hsquare]
  ring

/-- The comparison odd off-diagonal entry has the same signed normalized
kernel as the complete entry, with the comparison transform substituted for
the complete transform. -/
theorem suzukiDF6D4ComparisonOddOffDiagonal_eq_signedNormalizedKernel
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right) :
    suzukiDF6D4ComparisonOddOffDiagonal left right =
      Real.pi⁻¹ *
        (((suzukiDF6D4AlternatingSign (right - left) : Rat) : Real) *
          (((left : Real) * suzukiDF6D4ComparisonSineTransform right -
              (right : Real) * suzukiDF6D4ComparisonSineTransform left) /
            ((right : Real) ^ 2 - (left : Real) ^ 2))) := by
  have hle : left ≤ right := Nat.le_of_lt hleftRight
  have hsub : (right : Real) - left ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hleftRight.ne')
  have hrightPos : (0 : Real) < right := by
    exact_mod_cast (by omega : 0 < right)
  have hadd : (right : Real) + left ≠ 0 := ne_of_gt (by positivity)
  have hfactor : (right : Real) ^ 2 - (left : Real) ^ 2 =
      ((right : Real) - left) * ((right : Real) + left) := by ring
  have hsquare : (right : Real) ^ 2 - (left : Real) ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hsub hadd
  unfold suzukiDF6D4ComparisonOddOffDiagonal
  dsimp only
  rw [suzukiDF6D4AlternatingSign_sub_eq_add left right hle]
  push_cast
  rw [Nat.cast_sub hle]
  field_simp [hsub, hadd, hsquare]
  ring

end

end RiemannHypothesisProject.Experiments.M100
