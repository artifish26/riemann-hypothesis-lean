import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonEnclosures

/-!
# Large-mode transform bounds for M100-DF6D4

This module proves the uniform comparison-transform estimate used by both
endpoint residual-tail scripts.  The complete-transform difference estimate
is deliberately not folded into this theorem: it requires its own Suzuki
source/variation argument.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

/-- Six-term triangle inequality in the alternating shape of the comparison
sine-tail expansion. -/
theorem suzukiDF6D4AbsAlternatingSix_le
    (a b c d e f : Real) :
    |a - b + c - d + e - f| ≤
      |a| + |b| + |c| + |d| + |e| + |f| := by
  calc
    |a - b + c - d + e - f| ≤ |a - b + c - d + e| + |f| :=
      abs_sub _ _
    _ ≤ (|a - b + c - d| + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|a - b + c| + |d|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ ≤ (((|a - b| + |c|) + |d|) + |e|) + |f| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((((|a| + |b|) + |c|) + |d|) + |e|) + |f| := by
      gcongr
      exact abs_sub _ _
    _ = |a| + |b| + |c| + |d| + |e| + |f| := by ring

/-- Elementary polynomial estimate underlying the crude comparison-tail
bound.  The threshold `6` is below every positive comparison wave `2*n*pi`. -/
theorem suzukiDF6D4ComparisonTailPolynomial_le
    {x : Real} (hx : 6 ≤ x) :
    1 / x + 2 / x ^ 3 + 24 / x ^ 5 + 720 / x ^ 7 +
        80640 / x ^ 9 ≤
      2 / x := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hpoly :
      x ^ 8 + 2 * x ^ 6 + 24 * x ^ 4 + 720 * x ^ 2 + 80640 ≤
        2 * x ^ 8 := by
    let y := x - 6
    have hy : 0 ≤ y := by exact sub_nonneg.mpr hx
    have hxEq : x = y + 6 := by
      dsimp only [y]
      ring
    rw [hxEq]
    rw [← sub_nonneg]
    have hidentity :
        2 * (y + 6) ^ 8 -
            ((y + 6) ^ 8 + 2 * (y + 6) ^ 6 +
              24 * (y + 6) ^ 4 + 720 * (y + 6) ^ 2 + 80640) =
          y ^ 8 + 48 * y ^ 7 + 1006 * y ^ 6 + 12024 * y ^ 5 +
            89616 * y ^ 4 + 426240 * y ^ 3 + 1261584 * y ^ 2 +
              2116800 * y + 1448640 := by ring
    rw [hidentity]
    positivity
  have hleft :
      1 / x + 2 / x ^ 3 + 24 / x ^ 5 + 720 / x ^ 7 +
          80640 / x ^ 9 =
        (x ^ 8 + 2 * x ^ 6 + 24 * x ^ 4 + 720 * x ^ 2 + 80640) /
          x ^ 9 := by
    field_simp [hxpos.ne']
  have hright : 2 / x = (2 * x ^ 8) / x ^ 9 := by
    field_simp [hxpos.ne']
  rw [hleft, hright]
  exact (div_le_div_iff_of_pos_right (pow_pos hxpos 9)).2 hpoly

/-- The exact five-term comparison sine tail is bounded by `2/x`. -/
theorem suzukiDF6D4ComparisonSineTail_abs_le_two_div_wave
    (mode : Nat) (hmode : 1 ≤ mode) :
    |suzukiDF6D4ComparisonSineTail mode| ≤
      2 / suzukiDF6D4ComparisonWave mode := by
  let x := suzukiDF6D4ComparisonWave mode
  let remainder := ∫ t : Real in Set.Ioi x, Real.cos t / t ^ 10
  have hxpos : 0 < x := by
    unfold x suzukiDF6D4ComparisonWave
    positivity
  have hxSix : 6 ≤ x := by
    have hmodeReal : (1 : Real) ≤ mode := by exact_mod_cast hmode
    unfold x suzukiDF6D4ComparisonWave
    calc
      (6 : Real) = 2 * 1 * 3 := by norm_num
      _ ≤ 2 * (mode : Real) * 3 := by gcongr
      _ ≤ 2 * (mode : Real) * Real.pi := by
        have hmodePos : (0 : Real) < mode := lt_of_lt_of_le (by norm_num) hmodeReal
        exact (mul_lt_mul_of_pos_left Real.pi_gt_three
          (mul_pos (by norm_num) hmodePos)).le
  have hremainder := suzukiDF6D4_abs_cos_tail_tenth_le hxpos
  have htriangle := suzukiDF6D4AbsAlternatingSix_le
    (1 / x) (2 / x ^ 3) (24 / x ^ 5) (720 / x ^ 7)
    (40320 / x ^ 9) (362880 * remainder)
  have h1 : |1 / x| = 1 / x := abs_of_pos (one_div_pos.mpr hxpos)
  have h3 : |2 / x ^ 3| = 2 / x ^ 3 :=
    abs_of_pos (div_pos (by norm_num) (pow_pos hxpos 3))
  have h5 : |24 / x ^ 5| = 24 / x ^ 5 :=
    abs_of_pos (div_pos (by norm_num) (pow_pos hxpos 5))
  have h7 : |720 / x ^ 7| = 720 / x ^ 7 :=
    abs_of_pos (div_pos (by norm_num) (pow_pos hxpos 7))
  have h9 : |40320 / x ^ 9| = 40320 / x ^ 9 :=
    abs_of_pos (div_pos (by norm_num) (pow_pos hxpos 9))
  have hremAbs : |362880 * remainder| = 362880 * |remainder| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 362880)]
  unfold suzukiDF6D4ComparisonSineTail
  dsimp only [x]
  change |1 / x - 2 / x ^ 3 + 24 / x ^ 5 - 720 / x ^ 7 +
      40320 / x ^ 9 - 362880 * remainder| ≤ 2 / x
  calc
    |1 / x - 2 / x ^ 3 + 24 / x ^ 5 - 720 / x ^ 7 +
        40320 / x ^ 9 - 362880 * remainder| ≤
      |1 / x| + |2 / x ^ 3| + |24 / x ^ 5| + |720 / x ^ 7| +
        |40320 / x ^ 9| + |362880 * remainder| := htriangle
    _ = 1 / x + 2 / x ^ 3 + 24 / x ^ 5 + 720 / x ^ 7 +
        40320 / x ^ 9 + 362880 * |remainder| := by
      rw [h1, h3, h5, h7, h9, hremAbs]
    _ ≤ 1 / x + 2 / x ^ 3 + 24 / x ^ 5 + 720 / x ^ 7 +
        80640 / x ^ 9 := by
      have hscaled : 362880 * |remainder| ≤ 40320 / x ^ 9 := by
        calc
          362880 * |remainder| ≤ 362880 * (1 / (9 * x ^ 9)) :=
            mul_le_mul_of_nonneg_left hremainder (by norm_num)
          _ = 40320 / x ^ 9 := by ring
      have hadd := add_le_add_left hscaled
        (1 / x + 2 / x ^ 3 + 24 / x ^ 5 + 720 / x ^ 7 +
          40320 / x ^ 9)
      convert hadd using 1 <;> ring
    _ ≤ 2 / x := suzukiDF6D4ComparisonTailPolynomial_le hxSix

/-- Script-level large-mode comparison-transform bound. -/
theorem suzukiDF6D4ComparisonSineTransform_abs_le
    (mode : Nat) (hmode : 1 ≤ mode) :
    |suzukiDF6D4ComparisonSineTransform mode| ≤
      Real.pi / 2 + 1 / (Real.pi * mode) := by
  have htail := suzukiDF6D4ComparisonSineTail_abs_le_two_div_wave mode hmode
  have hmodePos : (0 : Real) < mode := by exact_mod_cast (Nat.zero_lt_of_lt hmode)
  have hwave : 2 / suzukiDF6D4ComparisonWave mode =
      1 / (Real.pi * mode) := by
    unfold suzukiDF6D4ComparisonWave
    field_simp [Real.pi_ne_zero, hmodePos.ne']
  rw [hwave] at htail
  unfold suzukiDF6D4ComparisonSineTransform
    suzukiDF6D4ComparisonSineIntegral
  rw [abs_neg]
  calc
    |Real.pi / 2 - suzukiDF6D4ComparisonSineTail mode| ≤
        |Real.pi / 2| + |suzukiDF6D4ComparisonSineTail mode| := abs_sub _ _
    _ = Real.pi / 2 + |suzukiDF6D4ComparisonSineTail mode| := by
      rw [abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    _ ≤ Real.pi / 2 + 1 / (Real.pi * mode) := by linarith

end

end RiemannHypothesisProject.Experiments.M100
