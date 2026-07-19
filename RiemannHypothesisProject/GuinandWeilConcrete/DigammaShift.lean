import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Finite shifts of the digamma function

This source module iterates the classical digamma functional equation on the
open right half-plane.  The resulting finite reciprocal correction is the
form needed when a Guinand-Weil contour is displaced horizontally.
-/

namespace RiemannHypothesisProject

noncomputable section

/-- Iterating the digamma functional equation moves any point in the open
right half-plane by a nonnegative integer, with an explicit finite reciprocal
correction. -/
theorem digamma_add_nat_of_re_pos
    (s : Complex) (hs : 0 < s.re) (n : Nat) :
    Complex.digamma (s + n) =
      Complex.digamma s +
        ∑ k ∈ Finset.range n, (s + (k : Complex))⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hregular :
          ∀ m : Nat, s + (n : Complex) ≠ -(m : Complex) := by
        intro m h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      rw [Nat.cast_succ]
      rw [show s + ((n : Complex) + 1) =
          (s + (n : Complex)) + 1 by ring]
      rw [Complex.digamma_apply_add_one _ hregular, ih,
        Finset.sum_range_succ]
      ring

/-- The finite reciprocal correction is controlled by the corresponding real
harmonic segment. -/
theorem norm_digamma_add_nat_sub_le_reciprocal_sum
    (s : Complex) (hs : 0 < s.re) (n : Nat) :
    norm (Complex.digamma (s + n) - Complex.digamma s) ≤
      ∑ k ∈ Finset.range n, 1 / (s.re + (k : Real)) := by
  rw [digamma_add_nat_of_re_pos s hs n, add_sub_cancel_left]
  calc
    norm (∑ k ∈ Finset.range n, (s + (k : Complex))⁻¹) ≤
        ∑ k ∈ Finset.range n, norm ((s + (k : Complex))⁻¹) :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, 1 / (s.re + (k : Real)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_inv]
      have hre : 0 < s.re + (k : Real) := by positivity
      have hle :
          s.re + (k : Real) ≤ norm (s + (k : Complex)) := by
        calc
          s.re + (k : Real) = (s + (k : Complex)).re := by simp
          _ ≤ norm (s + (k : Complex)) := Complex.re_le_norm _
      simpa [one_div] using one_div_le_one_div_of_le hre hle

/-- The finite-shift formula on the exact digamma line occurring in the
project's Archimedean factor. -/
theorem digamma_quarterLine_add_nat (t : Real) (n : Nat) :
    Complex.digamma
        ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I + n) =
      Complex.digamma
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) +
        ∑ k ∈ Finset.range n,
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I +
            (k : Complex))⁻¹ := by
  apply digamma_add_nat_of_re_pos
  norm_num

/-- Horizontal displacement from the critical-line digamma argument has a
bound independent of the height. -/
theorem norm_digamma_quarterLine_add_nat_sub_le (t : Real) (n : Nat) :
    norm
        (Complex.digamma
            ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I + n) -
          Complex.digamma
            ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I)) ≤
      ∑ k ∈ Finset.range n, 1 / ((1 / 4 : Real) + k) := by
  simpa using
    norm_digamma_add_nat_sub_le_reciprocal_sum
      ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) (by norm_num) n

end

end RiemannHypothesisProject
