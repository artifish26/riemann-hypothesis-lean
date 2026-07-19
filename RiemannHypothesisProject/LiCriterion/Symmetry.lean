import RiemannHypothesisProject.LiCriterion.SummandBounds
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Indexed Li coefficient symmetry

This module contains the indexed critical-line Li coefficient definition and
height-negation, absolute-height, and paired-multiplicity normalization facts.
-/

namespace RiemannHypothesisProject

open ComplexConjugate
/--
An indexed critical-line Li coefficient with nonnegative real multiplicity
weights.  The heights enumerate critical-line zeros, while `multiplicity`
records their nonnegative multiplicities or source weights.
-/
noncomputable def criticalLineLiSeriesCoefficient
    (height multiplicity : Nat -> Real) (n : Nat) : Real :=
  ∑' k : Nat, multiplicity k * criticalLineLiSummand (height k) n

/--
Negating every enumerated critical-line height leaves the indexed Li coefficient
unchanged.  This is the source-side symmetry used when positive and negative
zero ordinates are mirrored.
-/
theorem criticalLineLiSeriesCoefficient_neg_height_eq
    (height multiplicity : Nat -> Real) (n : Nat) :
    criticalLineLiSeriesCoefficient (fun k : Nat => -height k) multiplicity n =
      criticalLineLiSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiSeriesCoefficient
  apply tsum_congr
  intro k
  rw [criticalLineLiSummand_neg]

/--
Replacing every enumerated critical-line height by its absolute value leaves the
indexed Li coefficient unchanged.
-/
theorem criticalLineLiSeriesCoefficient_abs_height_eq
    (height multiplicity : Nat -> Real) (n : Nat) :
    criticalLineLiSeriesCoefficient (fun k : Nat => |height k|) multiplicity n =
      criticalLineLiSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiSeriesCoefficient
  apply tsum_congr
  intro k
  rw [criticalLineLiSummand_abs]

/-- Doubling all multiplicities doubles the indexed critical-line Li coefficient. -/
theorem criticalLineLiSeriesCoefficient_two_mul_multiplicity_eq
    (height multiplicity : Nat -> Real) (n : Nat) :
    criticalLineLiSeriesCoefficient height (fun k : Nat => 2 * multiplicity k) n =
      2 * criticalLineLiSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiSeriesCoefficient
  calc
    (∑' k : Nat, (2 * multiplicity k) * criticalLineLiSummand (height k) n) =
        ∑' k : Nat, 2 * (multiplicity k * criticalLineLiSummand (height k) n) := by
      apply tsum_congr
      intro k
      ring
    _ = 2 * ∑' k : Nat,
        multiplicity k * criticalLineLiSummand (height k) n := by
      rw [tsum_mul_left]

/--
An indexed positive/negative ordinate mirror contributes exactly the same as
doubling the multiplicity on the positive-height normalization.
-/
theorem criticalLineLiSeriesCoefficient_mirror_eq_two_abs_multiplicity
    (height multiplicity : Nat -> Real) (n : Nat) :
    criticalLineLiSeriesCoefficient height multiplicity n +
        criticalLineLiSeriesCoefficient (fun k : Nat => -height k) multiplicity n =
      criticalLineLiSeriesCoefficient
        (fun k : Nat => |height k|) (fun k : Nat => 2 * multiplicity k) n := by
  rw [criticalLineLiSeriesCoefficient_neg_height_eq,
    criticalLineLiSeriesCoefficient_two_mul_multiplicity_eq,
    criticalLineLiSeriesCoefficient_abs_height_eq]
  ring
end RiemannHypothesisProject