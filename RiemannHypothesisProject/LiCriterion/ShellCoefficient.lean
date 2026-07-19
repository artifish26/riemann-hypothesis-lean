import RiemannHypothesisProject.LiCriterion.DyadicShells
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Shell-coded Li coefficients

This module contains the shell-coded critical-line Li coefficient, its symmetry
and paired-multiplicity normalizations, and cumulative dyadic summability and
nonnegativity source theorems.
-/

namespace RiemannHypothesisProject

open ComplexConjugate
/--
A shell-coded critical-line Li coefficient.  The outer index is the dyadic
shell and the dependent fiber is the source enumeration inside that shell.
-/
noncomputable def criticalLineLiShellSeriesCoefficient
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (n : Nat) : Real :=
  ∑' p : Sigma fiber, multiplicity p * criticalLineLiSummand (height p) n

/--
Negating every shell-coded critical-line height leaves the shell-coded Li
coefficient unchanged.
-/
theorem criticalLineLiShellSeriesCoefficient_neg_height_eq
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (n : Nat) :
    criticalLineLiShellSeriesCoefficient
        (fun p : Sigma fiber => -height p) multiplicity n =
      criticalLineLiShellSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiShellSeriesCoefficient
  apply tsum_congr
  intro p
  rw [criticalLineLiSummand_neg]

/--
Replacing every shell-coded critical-line height by its absolute value leaves
the shell-coded Li coefficient unchanged.
-/
theorem criticalLineLiShellSeriesCoefficient_abs_height_eq
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (n : Nat) :
    criticalLineLiShellSeriesCoefficient
        (fun p : Sigma fiber => |height p|) multiplicity n =
      criticalLineLiShellSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiShellSeriesCoefficient
  apply tsum_congr
  intro p
  rw [criticalLineLiSummand_abs]

/-- Doubling all multiplicities doubles the shell-coded critical-line Li coefficient. -/
theorem criticalLineLiShellSeriesCoefficient_two_mul_multiplicity_eq
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (n : Nat) :
    criticalLineLiShellSeriesCoefficient
        height (fun p : Sigma fiber => 2 * multiplicity p) n =
      2 * criticalLineLiShellSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiShellSeriesCoefficient
  calc
    (∑' p : Sigma fiber,
        (2 * multiplicity p) * criticalLineLiSummand (height p) n) =
        ∑' p : Sigma fiber,
          2 * (multiplicity p * criticalLineLiSummand (height p) n) := by
      apply tsum_congr
      intro p
      ring
    _ = 2 * ∑' p : Sigma fiber,
        multiplicity p * criticalLineLiSummand (height p) n := by
      rw [tsum_mul_left]

/--
A shell-coded positive/negative ordinate mirror contributes exactly the same as
doubling the multiplicity on the absolute-height normalization.
-/
theorem criticalLineLiShellSeriesCoefficient_mirror_eq_two_abs_multiplicity
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (n : Nat) :
    criticalLineLiShellSeriesCoefficient height multiplicity n +
        criticalLineLiShellSeriesCoefficient
          (fun p : Sigma fiber => -height p) multiplicity n =
      criticalLineLiShellSeriesCoefficient
        (fun p : Sigma fiber => |height p|)
        (fun p : Sigma fiber => 2 * multiplicity p) n := by
  rw [criticalLineLiShellSeriesCoefficient_neg_height_eq,
    criticalLineLiShellSeriesCoefficient_two_mul_multiplicity_eq,
    criticalLineLiShellSeriesCoefficient_abs_height_eq]
  ring

/-- A shell-coded critical-line Li coefficient is nonnegative term by term. -/
theorem criticalLineLiShellSeriesCoefficient_nonneg
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (n : Nat)
    (hmultiplicity_nonneg : forall p : Sigma fiber, 0 <= multiplicity p) :
    0 <= criticalLineLiShellSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiShellSeriesCoefficient
  exact tsum_nonneg (fun p =>
    mul_nonneg (hmultiplicity_nonneg p)
      (criticalLineLiSummand_nonneg (height p) n))

/--
A shell-coded zero enumeration with finite shell fibers is summable from a
cumulative dyadic `T log T` source bound.

This is the shell-interpretation version of the indexed dyadic majorant theorem:
the source hypotheses expose exactly the zero-counting data still needed for the
zeta specialization.
-/
theorem criticalLineLiShellSeriesCoefficient_summable_of_cumulativeDyadicTlogTBound
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (fiber_fintype : forall m : Nat, Fintype (fiber m))
    (shellMass cumulativeMass : Nat -> Real) (C : Real) (n : Nat)
    (hmultiplicity_nonneg : forall p : Sigma fiber, 0 <= multiplicity p)
    (hheight : forall p : Sigma fiber, (2 : Real) ^ p.1 <= |height p|)
    (hshellMass_eq :
      forall m : Nat,
        shellMass m = ∑' j : fiber m, multiplicity (Sigma.mk m j))
    (hC_nonneg : 0 <= C)
    (hshell_le_cumulative : forall m : Nat, shellMass m <= cumulativeMass m)
    (hcumulative_bound :
      forall m : Nat,
        cumulativeMass m <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun p : Sigma fiber =>
      multiplicity p * criticalLineLiSummand (height p) n) := by
  have hshell_nonneg : forall m : Nat, 0 <= shellMass m := by
    intro m
    rw [hshellMass_eq m]
    exact tsum_nonneg (fun j : fiber m =>
      hmultiplicity_nonneg (Sigma.mk m j))
  have hmajorant :
      Summable (fun m : Nat =>
        shellMass m *
          (((n : Real) ^ 2 / 2) * ((((2 : Real) ^ m) ^ 2)⁻¹))) :=
    summable_dyadicLiShellMajorant_of_cumulativeDyadicTlogTBound
      shellMass cumulativeMass C n hC_nonneg hshell_nonneg
      hshell_le_cumulative hcumulative_bound
  have hshell_tsum_summable :
      Summable (fun m : Nat =>
        ∑' j : fiber m,
          multiplicity (Sigma.mk m j) *
            criticalLineLiSummand (height (Sigma.mk m j)) n) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
    · intro m
      exact tsum_nonneg (fun j : fiber m =>
        mul_nonneg (hmultiplicity_nonneg (Sigma.mk m j))
          (criticalLineLiSummand_nonneg (height (Sigma.mk m j)) n))
    · intro m
      letI : Fintype (fiber m) := fiber_fintype m
      let factor : Real :=
        ((n : Real) ^ 2 / 2) * ((((2 : Real) ^ m) ^ 2)⁻¹)
      have hpoint :
          forall j : fiber m,
            multiplicity (Sigma.mk m j) *
                criticalLineLiSummand (height (Sigma.mk m j)) n <=
              multiplicity (Sigma.mk m j) * factor := by
        intro j
        have hbound :
            criticalLineLiSummand (height (Sigma.mk m j)) n <= factor := by
          simpa [factor] using
            criticalLineLiSummand_le_dyadic_height_decay
              (height (Sigma.mk m j)) n m (hheight (Sigma.mk m j))
        exact mul_le_mul_of_nonneg_left hbound
          (hmultiplicity_nonneg (Sigma.mk m j))
      calc
        (∑' j : fiber m,
            multiplicity (Sigma.mk m j) *
              criticalLineLiSummand (height (Sigma.mk m j)) n) =
            ∑ j : fiber m,
              multiplicity (Sigma.mk m j) *
                criticalLineLiSummand (height (Sigma.mk m j)) n := by
          rw [tsum_fintype]
        _ <= ∑ j : fiber m, multiplicity (Sigma.mk m j) * factor := by
          exact Finset.sum_le_sum (fun j _hj => hpoint j)
        _ = (∑ j : fiber m, multiplicity (Sigma.mk m j)) * factor := by
          rw [← Finset.sum_mul]
        _ = shellMass m * factor := by
          rw [hshellMass_eq m, tsum_fintype]
        _ = shellMass m *
              (((n : Real) ^ 2 / 2) *
                ((((2 : Real) ^ m) ^ 2)⁻¹)) := by
          rfl
  have hterms_nonneg :
      forall p : Sigma fiber,
        0 <= multiplicity p * criticalLineLiSummand (height p) n := by
    intro p
    exact mul_nonneg (hmultiplicity_nonneg p)
      (criticalLineLiSummand_nonneg (height p) n)
  refine (summable_sigma_of_nonneg hterms_nonneg).2 ?_
  constructor
  · intro m
    letI : Fintype (fiber m) := fiber_fintype m
    exact (hasSum_fintype
      (fun j : fiber m =>
        multiplicity (Sigma.mk m j) *
          criticalLineLiSummand (height (Sigma.mk m j)) n)).summable
  · exact hshell_tsum_summable

/--
Cumulative dyadic `T log T` shell-counting data gives a summable, nonnegative
shell-coded critical-line Li coefficient.
-/
theorem criticalLineLiShellSeriesCoefficient_summable_and_nonneg_of_cumulativeDyadicTlogTBound
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (fiber_fintype : forall m : Nat, Fintype (fiber m))
    (shellMass cumulativeMass : Nat -> Real) (C : Real) (n : Nat)
    (hmultiplicity_nonneg : forall p : Sigma fiber, 0 <= multiplicity p)
    (hheight : forall p : Sigma fiber, (2 : Real) ^ p.1 <= |height p|)
    (hshellMass_eq :
      forall m : Nat,
        shellMass m = ∑' j : fiber m, multiplicity (Sigma.mk m j))
    (hC_nonneg : 0 <= C)
    (hshell_le_cumulative : forall m : Nat, shellMass m <= cumulativeMass m)
    (hcumulative_bound :
      forall m : Nat,
        cumulativeMass m <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun p : Sigma fiber =>
        multiplicity p * criticalLineLiSummand (height p) n) ∧
      0 <= criticalLineLiShellSeriesCoefficient height multiplicity n :=
  ⟨criticalLineLiShellSeriesCoefficient_summable_of_cumulativeDyadicTlogTBound
      height multiplicity fiber_fintype shellMass cumulativeMass C n
      hmultiplicity_nonneg hheight hshellMass_eq hC_nonneg
      hshell_le_cumulative hcumulative_bound,
    criticalLineLiShellSeriesCoefficient_nonneg
      height multiplicity n hmultiplicity_nonneg⟩
end RiemannHypothesisProject