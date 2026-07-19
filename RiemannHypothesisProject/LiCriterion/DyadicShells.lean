import RiemannHypothesisProject.LiCriterion.Symmetry
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Dyadic shell summability for Li coefficients

This module contains indexed Li coefficient summability, dyadic shell mass
cleanup, cumulative `T log T` consequences, and shell-level majorant
summability used before shell-coded coefficients are assembled.
-/

namespace RiemannHypothesisProject

open ComplexConjugate
/-- The summand series is summable from the inverse-square height-decay majorant. -/
theorem criticalLineLiSeriesCoefficient_summable_of_height_decay
    (height multiplicity : Nat -> Real) (n : Nat)
    (hmultiplicity_nonneg : forall k : Nat, 0 <= multiplicity k)
    (hdecay :
      Summable (fun k : Nat =>
        multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)) :
    Summable (fun k : Nat =>
      multiplicity k * criticalLineLiSummand (height k) n) := by
  let majorant : Nat -> Real := fun k : Nat =>
    ((n : Real) ^ 2 / 2) *
      (multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)
  have hmajorant_summable : Summable majorant := by
    dsimp [majorant]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      Summable.mul_left ((n : Real) ^ 2 / 2) hdecay
  exact
    @Summable.of_nonneg_of_le Nat majorant
      (fun k : Nat => multiplicity k * criticalLineLiSummand (height k) n)
      (fun k =>
        mul_nonneg (hmultiplicity_nonneg k)
          (criticalLineLiSummand_nonneg (height k) n))
      (fun k => by
        have hbound :=
          criticalLineLiSummand_le_quadratic_height_decay (height k) n
        have hscaled :=
          mul_le_mul_of_nonneg_left hbound (hmultiplicity_nonneg k)
        dsimp [majorant]
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
      hmajorant_summable

/-- The infinite critical-line Li coefficient is nonnegative term by term. -/
theorem criticalLineLiSeriesCoefficient_nonneg
    (height multiplicity : Nat -> Real) (n : Nat)
    (hmultiplicity_nonneg : forall k : Nat, 0 <= multiplicity k) :
    0 <= criticalLineLiSeriesCoefficient height multiplicity n := by
  unfold criticalLineLiSeriesCoefficient
  exact tsum_nonneg (fun k =>
    mul_nonneg (hmultiplicity_nonneg k)
      (criticalLineLiSummand_nonneg (height k) n))

/--
The source-theorem package for an infinite critical-line zero sequence:
inverse-square height decay gives a genuine summable Li coefficient, and
nonnegative multiplicities give coefficient positivity.
-/
theorem criticalLineLiSeriesCoefficient_summable_and_nonneg_of_height_decay
    (height multiplicity : Nat -> Real) (n : Nat)
    (hmultiplicity_nonneg : forall k : Nat, 0 <= multiplicity k)
    (hdecay :
      Summable (fun k : Nat =>
        multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)) :
    Summable (fun k : Nat =>
        multiplicity k * criticalLineLiSummand (height k) n) ∧
      0 <= criticalLineLiSeriesCoefficient height multiplicity n :=
  ⟨criticalLineLiSeriesCoefficient_summable_of_height_decay
      height multiplicity n hmultiplicity_nonneg hdecay,
    criticalLineLiSeriesCoefficient_nonneg
      height multiplicity n hmultiplicity_nonneg⟩

/--
Doubling multiplicities doubles the raw inverse-square height-decay series used
as the source summability hypothesis for indexed critical-line Li coefficients.
-/
theorem criticalLineHeightDecaySeries_two_mul_multiplicity_eq
    (height multiplicity : Nat -> Real) :
    (∑' k : Nat,
        (2 * multiplicity k) *
          (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
      2 * ∑' k : Nat,
        multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  calc
    (∑' k : Nat,
        (2 * multiplicity k) *
          (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
        ∑' k : Nat,
          2 * (multiplicity k *
            (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
      apply tsum_congr
      intro k
      ring
    _ = 2 * ∑' k : Nat,
        multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
      rw [tsum_mul_left]

/--
The raw inverse-square height-decay series for mirrored positive/negative
ordinates equals the doubled-multiplicity series at absolute heights.
-/
theorem criticalLineHeightDecaySeries_mirror_eq_two_abs_multiplicity
    (height multiplicity : Nat -> Real) :
    (∑' k : Nat,
        multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) +
        (∑' k : Nat,
          multiplicity k * ((-height k) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
      ∑' k : Nat,
        (2 * multiplicity k) *
          (|height k| ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  have hneg :
      (∑' k : Nat,
          multiplicity k * ((-height k) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
        ∑' k : Nat,
          multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
    apply tsum_congr
    intro k
    rw [criticalLineHeightDecay_neg]
  have habs :
      (∑' k : Nat,
          multiplicity k * (|height k| ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
        ∑' k : Nat,
          multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
    apply tsum_congr
    intro k
    rw [criticalLineHeightDecay_abs]
  calc
    (∑' k : Nat,
        multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) +
        (∑' k : Nat,
          multiplicity k * ((-height k) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
        (∑' k : Nat,
          multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) +
          (∑' k : Nat,
            multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
      rw [hneg]
    _ = 2 * ∑' k : Nat,
          multiplicity k * (height k ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
      ring
    _ = 2 * ∑' k : Nat,
          multiplicity k * (|height k| ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
      rw [habs]
    _ = ∑' k : Nat,
          (2 * multiplicity k) *
            (|height k| ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
      exact
        (criticalLineHeightDecaySeries_two_mul_multiplicity_eq
          (fun k : Nat => |height k|) multiplicity).symm

/--
An indexed critical-line zero enumeration is summable once each zero is assigned
to a dyadic shell and the resulting fixed-`n` shell majorant is summable.

This is the indexed counterpart to `criticalLineLiSummand_le_dyadic_height_decay`:
the hypothesis `hheight` is the source-side shell interpretation for each
enumerated height.
-/
theorem criticalLineLiSeriesCoefficient_summable_of_dyadic_shell_majorant
    (height multiplicity : Nat -> Real) (shellOf : Nat -> Nat) (n : Nat)
    (hmultiplicity_nonneg : forall k : Nat, 0 <= multiplicity k)
    (hheight : forall k : Nat, (2 : Real) ^ shellOf k <= |height k|)
    (hmajorant :
      Summable (fun k : Nat =>
        multiplicity k *
          (((n : Real) ^ 2 / 2) *
            ((((2 : Real) ^ shellOf k) ^ 2)⁻¹)))) :
    Summable (fun k : Nat =>
      multiplicity k * criticalLineLiSummand (height k) n) := by
  exact
    @Summable.of_nonneg_of_le Nat
      (fun k : Nat =>
        multiplicity k *
          (((n : Real) ^ 2 / 2) *
            ((((2 : Real) ^ shellOf k) ^ 2)⁻¹)))
      (fun k : Nat => multiplicity k * criticalLineLiSummand (height k) n)
      (fun k =>
        mul_nonneg (hmultiplicity_nonneg k)
          (criticalLineLiSummand_nonneg (height k) n))
      (fun k => by
        have hbound :=
          criticalLineLiSummand_le_dyadic_height_decay
            (height k) n (shellOf k) (hheight k)
        exact mul_le_mul_of_nonneg_left hbound (hmultiplicity_nonneg k))
      hmajorant

/--
Dyadic shell-majorant summability plus nonnegative multiplicities gives a
summable, nonnegative indexed critical-line Li coefficient.
-/
theorem criticalLineLiSeriesCoefficient_summable_and_nonneg_of_dyadic_shell_majorant
    (height multiplicity : Nat -> Real) (shellOf : Nat -> Nat) (n : Nat)
    (hmultiplicity_nonneg : forall k : Nat, 0 <= multiplicity k)
    (hheight : forall k : Nat, (2 : Real) ^ shellOf k <= |height k|)
    (hmajorant :
      Summable (fun k : Nat =>
        multiplicity k *
          (((n : Real) ^ 2 / 2) *
            ((((2 : Real) ^ shellOf k) ^ 2)⁻¹)))) :
    Summable (fun k : Nat =>
        multiplicity k * criticalLineLiSummand (height k) n) ∧
      0 <= criticalLineLiSeriesCoefficient height multiplicity n :=
  ⟨criticalLineLiSeriesCoefficient_summable_of_dyadic_shell_majorant
      height multiplicity shellOf n hmultiplicity_nonneg hheight hmajorant,
    criticalLineLiSeriesCoefficient_nonneg
      height multiplicity n hmultiplicity_nonneg⟩

/--
Linear growth times a geometric factor is summable.  This is the elementary
cleanup estimate used by dyadic zero-counting shells: a shell count growing like
`m + 1` after dyadic normalization still gives a convergent majorant.
-/
theorem summable_of_nonneg_le_linear_geometric_half
    (a : Nat -> Real) (C : Real)
    (ha_nonneg : forall m : Nat, 0 <= a m)
    (ha_le :
      forall m : Nat,
        a m <= C * (((m : Real) + 1) * ((1 / 2 : Real) ^ m))) :
    Summable a := by
  have hr : ‖(1 / 2 : Real)‖ < 1 := by norm_num
  have hlinear_part :
      Summable (fun m : Nat => (m : Real) * ((1 / 2 : Real) ^ m)) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 1 (r := (1 / 2 : Real)) hr)
  have hconstant_part :
      Summable (fun m : Nat => ((1 / 2 : Real) ^ m)) :=
    summable_geometric_of_norm_lt_one hr
  have hlinear :
      Summable (fun m : Nat => (((m : Real) + 1) * ((1 / 2 : Real) ^ m))) := by
    simpa [add_mul, one_mul] using hlinear_part.add hconstant_part
  exact Summable.of_nonneg_of_le ha_nonneg ha_le
    (Summable.mul_left C hlinear)

/-- Dyadic inverse-square normalization leaves a geometric `1 / 2` factor. -/
theorem dyadic_height_mul_inv_sq_eq_geometric_half (m : Nat) :
    ((2 : Real) ^ m) * ((((2 : Real) ^ m) ^ 2)⁻¹) =
      ((1 / 2 : Real) ^ m) := by
  have hpow_ne : (2 : Real) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  calc
    ((2 : Real) ^ m) * ((((2 : Real) ^ m) ^ 2)⁻¹) =
        ((2 : Real) ^ m) *
          ((((2 : Real) ^ m) * ((2 : Real) ^ m))⁻¹) := by
      rw [pow_two]
    _ = ((2 : Real) ^ m) *
          (((2 : Real) ^ m)⁻¹ * ((2 : Real) ^ m)⁻¹) := by
      rw [mul_inv_rev]
    _ = (((2 : Real) ^ m) * ((2 : Real) ^ m)⁻¹) *
          ((2 : Real) ^ m)⁻¹ := by
      ring
    _ = ((2 : Real) ^ m)⁻¹ := by
      rw [mul_inv_cancel₀ hpow_ne, one_mul]
    _ = ((1 / 2 : Real) ^ m) := by
      rw [← inv_pow]
      norm_num

/--
A dyadic zero-counting shell bound gives the inverse-square height-decay
summability needed by the critical-line Li source theorem.

The hypothesis `shellMass m <= C * (m + 1) * 2^m` is the dyadic form of the
Riemann-von Mangoldt `T log T` count.  Dividing that shell by the squared dyadic
height `((2^m)^2)` leaves a linear-geometric summable majorant.
-/
theorem summable_dyadicHeightDecayMajorant_of_linearShellBound
    (shellMass : Nat -> Real) (C : Real)
    (hshell_nonneg : forall m : Nat, 0 <= shellMass m)
    (hshell_bound :
      forall m : Nat,
        shellMass m <= C * (((m : Real) + 1) * ((2 : Real) ^ m))) :
    Summable (fun m : Nat =>
      shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹) := by
  refine summable_of_nonneg_le_linear_geometric_half
    (fun m : Nat => shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹) C ?_ ?_
  · intro m
    exact mul_nonneg (hshell_nonneg m) (inv_nonneg.mpr (sq_nonneg _))
  · intro m
    have hscaled :=
      mul_le_mul_of_nonneg_right (hshell_bound m)
        (inv_nonneg.mpr (sq_nonneg (((2 : Real) ^ m))))
    calc
      shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹ <=
          (C * (((m : Real) + 1) * ((2 : Real) ^ m))) *
            (((2 : Real) ^ m) ^ 2)⁻¹ := hscaled
      _ = C *
          (((m : Real) + 1) *
            (((2 : Real) ^ m) * ((((2 : Real) ^ m) ^ 2)⁻¹))) := by
        ring
      _ = C * (((m : Real) + 1) * ((1 / 2 : Real) ^ m)) := by
        rw [dyadic_height_mul_inv_sq_eq_geometric_half m]

/--
A cumulative dyadic Riemann-von-Mangoldt-shaped bound gives the dyadic
inverse-square height-decay summability.

Here `cumulativeMass m` should be read as the source count up to the dyadic
upper endpoint `2^(m+1)`.  If the `m`th shell is dominated by that cumulative
count and the cumulative count has `T log T` shape, the shell masses satisfy the
linear dyadic bound needed for `summable_dyadicHeightDecayMajorant`.
-/
theorem summable_dyadicHeightDecayMajorant_of_cumulativeDyadicTlogTBound
    (shellMass cumulativeMass : Nat -> Real) (C : Real)
    (hC_nonneg : 0 <= C)
    (hshell_nonneg : forall m : Nat, 0 <= shellMass m)
    (hshell_le_cumulative : forall m : Nat, shellMass m <= cumulativeMass m)
    (hcumulative_bound :
      forall m : Nat,
        cumulativeMass m <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun m : Nat =>
      shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹) := by
  refine summable_dyadicHeightDecayMajorant_of_linearShellBound
    shellMass (4 * C) hshell_nonneg ?_
  intro m
  have hshell_bound :
      shellMass m <=
        C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) :=
    (hshell_le_cumulative m).trans (hcumulative_bound m)
  have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
  have hm_shift : (m : Real) + 2 <= 2 * ((m : Real) + 1) := by
    nlinarith
  have hpow_nonneg : 0 <= (2 : Real) ^ m :=
    pow_nonneg (by norm_num) m
  have hinner :
      (((m : Real) + 2) * ((2 : Real) ^ m)) <=
        (2 * ((m : Real) + 1)) * ((2 : Real) ^ m) :=
    mul_le_mul_of_nonneg_right hm_shift hpow_nonneg
  have hscale_nonneg : 0 <= 2 * C :=
    mul_nonneg (by norm_num) hC_nonneg
  calc
    shellMass m <=
        C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) :=
      hshell_bound
    _ = (2 * C) * (((m : Real) + 2) * ((2 : Real) ^ m)) := by
      rw [pow_succ]
      ring
    _ <= (2 * C) * ((2 * ((m : Real) + 1)) * ((2 : Real) ^ m)) :=
      mul_le_mul_of_nonneg_left hinner hscale_nonneg
    _ = (4 * C) * (((m : Real) + 1) * ((2 : Real) ^ m)) := by
      ring

/--
A shell-coded critical-line zero enumeration satisfies inverse-square
height-decay summability once its finite dyadic shell fibers obey a cumulative
`T log T` source bound.

This is the direct height-decay source theorem for the actual zeta-shell
instantiation: it exposes the shell fibers, multiplicities, dyadic lower-edge
height interpretation, and cumulative zero count as separate hypotheses.
-/
theorem criticalLineShellHeightDecay_summable_of_cumulativeDyadicTlogTBound
    {fiber : Nat -> Type} (height multiplicity : Sigma fiber -> Real)
    (fiber_fintype : forall m : Nat, Fintype (fiber m))
    (shellMass cumulativeMass : Nat -> Real) (C : Real)
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
      multiplicity p * (height p ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  have hshell_nonneg : forall m : Nat, 0 <= shellMass m := by
    intro m
    rw [hshellMass_eq m]
    exact tsum_nonneg (fun j : fiber m =>
      hmultiplicity_nonneg (Sigma.mk m j))
  have hmajorant :
      Summable (fun m : Nat =>
        shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹) :=
    summable_dyadicHeightDecayMajorant_of_cumulativeDyadicTlogTBound
      shellMass cumulativeMass C hC_nonneg hshell_nonneg
      hshell_le_cumulative hcumulative_bound
  have hshell_tsum_summable :
      Summable (fun m : Nat =>
        ∑' j : fiber m,
          multiplicity (Sigma.mk m j) *
            (height (Sigma.mk m j) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
    · intro m
      exact tsum_nonneg (fun j : fiber m =>
        mul_nonneg (hmultiplicity_nonneg (Sigma.mk m j))
          (inv_nonneg.mpr
            (add_nonneg (sq_nonneg _) (sq_nonneg _))))
    · intro m
      letI : Fintype (fiber m) := fiber_fintype m
      let factor : Real := ((((2 : Real) ^ m) ^ 2)⁻¹)
      have hpoint :
          forall j : fiber m,
            multiplicity (Sigma.mk m j) *
                (height (Sigma.mk m j) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
              multiplicity (Sigma.mk m j) * factor := by
        intro j
        have hbound :
            (height (Sigma.mk m j) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ <=
              factor := by
          simpa [factor] using
            criticalLineHeightDecay_le_dyadic_height_decay
              (height (Sigma.mk m j)) m (hheight (Sigma.mk m j))
        exact mul_le_mul_of_nonneg_left hbound
          (hmultiplicity_nonneg (Sigma.mk m j))
      calc
        (∑' j : fiber m,
            multiplicity (Sigma.mk m j) *
              (height (Sigma.mk m j) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) =
            ∑ j : fiber m,
              multiplicity (Sigma.mk m j) *
                (height (Sigma.mk m j) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
          rw [tsum_fintype]
        _ <= ∑ j : fiber m, multiplicity (Sigma.mk m j) * factor := by
          exact Finset.sum_le_sum (fun j _hj => hpoint j)
        _ = (∑ j : fiber m, multiplicity (Sigma.mk m j)) * factor := by
          rw [← Finset.sum_mul]
        _ = shellMass m * factor := by
          rw [hshellMass_eq m, tsum_fintype]
        _ = shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹ := by
          rfl
  have hterms_nonneg :
      forall p : Sigma fiber,
        0 <= multiplicity p *
          (height p ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
    intro p
    exact mul_nonneg (hmultiplicity_nonneg p)
      (inv_nonneg.mpr (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  refine (summable_sigma_of_nonneg hterms_nonneg).2 ?_
  constructor
  · intro m
    letI : Fintype (fiber m) := fiber_fintype m
    exact (hasSum_fintype
      (fun j : fiber m =>
        multiplicity (Sigma.mk m j) *
          (height (Sigma.mk m j) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)).summable
  · exact hshell_tsum_summable

/--
A cumulative dyadic `T log T` bound also gives summability of the fixed-`n` Li
shell majorant.  This is the shell-level counterpart of
`criticalLineLiSummand_le_dyadic_height_decay`.
-/
theorem summable_dyadicLiShellMajorant_of_cumulativeDyadicTlogTBound
    (shellMass cumulativeMass : Nat -> Real) (C : Real) (n : Nat)
    (hC_nonneg : 0 <= C)
    (hshell_nonneg : forall m : Nat, 0 <= shellMass m)
    (hshell_le_cumulative : forall m : Nat, shellMass m <= cumulativeMass m)
    (hcumulative_bound :
      forall m : Nat,
        cumulativeMass m <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun m : Nat =>
      shellMass m *
        (((n : Real) ^ 2 / 2) * ((((2 : Real) ^ m) ^ 2)⁻¹))) := by
  have hheight_decay :
      Summable (fun m : Nat =>
        shellMass m * (((2 : Real) ^ m) ^ 2)⁻¹) :=
    summable_dyadicHeightDecayMajorant_of_cumulativeDyadicTlogTBound
      shellMass cumulativeMass C hC_nonneg hshell_nonneg
      hshell_le_cumulative hcumulative_bound
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    Summable.mul_left ((n : Real) ^ 2 / 2) hheight_decay
end RiemannHypothesisProject
