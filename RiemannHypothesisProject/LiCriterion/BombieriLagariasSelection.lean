import RiemannHypothesisProject.LiCriterion.BombieriLagariasDominant

/-!
# Selecting a dominant Bombieri-Lagarias shell

The summability hypotheses force the normalized ratios `1 + u i` to tend to
one along the cofinite filter.  Hence any ratio outside the closed unit disk
belongs to a finite exceptional set.  Taking the largest exceptional modulus
and then the largest remaining modulus supplies the separated shell used by
the dominant-shell exclusion theorem.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Filter
open scoped Topology

noncomputable section

/-- Nonnegativity of every normalized Li power sum excludes a ratio of
modulus greater than one. -/
theorem norm_one_add_le_one_of_bombieriLagarias_nonneg
    {iota : Type*} (u : iota -> Complex)
    (hlinear : Summable (fun i => abs (u i).re))
    (hquadratic : Summable (fun i => norm (u i) ^ 2))
    (hnonneg : forall n : Nat, 0 < n ->
      0 <= ∑' i, bombieriLagariasNormalizedSummand (u i) n) :
    forall i, norm (1 + u i) <= 1 := by
  classical
  intro i0
  by_contra hi0
  let ratio : iota -> Real := fun i => norm (1 + u i)
  have hratio0 : 1 < ratio i0 := by
    exact lt_of_not_ge hi0
  let q0 : Real := (1 + ratio i0) / 2
  have hq0_one : 1 < q0 := by
    dsimp [q0]
    linarith
  have hq0_lt_ratio0 : q0 < ratio i0 := by
    dsimp [q0]
    linarith
  have hdelta_pos : 0 < q0 - 1 := sub_pos.mpr hq0_one
  have heventually_square :
      ∀ᶠ i in cofinite, norm (u i) ^ 2 < (q0 - 1) ^ 2 :=
    hquadratic.tendsto_cofinite_zero.eventually_lt_const
      (sq_pos_of_pos hdelta_pos)
  have heventually_ratio : ∀ᶠ i in cofinite, ratio i <= q0 := by
    filter_upwards [heventually_square] with i hi
    have hnorm_lt : norm (u i) < q0 - 1 :=
      (sq_lt_sq₀ (norm_nonneg _) hdelta_pos.le).mp hi
    calc
      ratio i = norm (1 + u i) := rfl
      _ <= norm (1 : Complex) + norm (u i) := norm_add_le _ _
      _ = 1 + norm (u i) := by norm_num
      _ <= q0 := by linarith
  have hfinite : {i | ¬ ratio i <= q0}.Finite :=
    eventually_cofinite.mp heventually_ratio
  let exceptional : Finset iota := hfinite.toFinset
  have hexceptional_mem (i : iota) :
      i ∈ exceptional ↔ q0 < ratio i := by
    simp [exceptional, not_le]
  have hi0_exceptional : i0 ∈ exceptional :=
    (hexceptional_mem i0).2 hq0_lt_ratio0
  have hexceptional_nonempty : exceptional.Nonempty :=
    ⟨i0, hi0_exceptional⟩
  let r : Real := exceptional.sup' hexceptional_nonempty ratio
  have hratio0_le_r : ratio i0 <= r := by
    dsimp [r]
    exact Finset.le_sup' ratio hi0_exceptional
  have hr : 1 < r := hratio0.trans_le hratio0_le_r
  have hq0_lt_r : q0 < r := hq0_lt_ratio0.trans_le hratio0_le_r
  obtain ⟨imax, himax_exceptional, hr_imax⟩ :=
    Finset.exists_mem_eq_sup' (s := exceptional)
      (H := hexceptional_nonempty) ratio
  let shell : Finset iota := exceptional.filter fun i => ratio i = r
  have himax_shell : imax ∈ shell := by
    apply Finset.mem_filter.mpr
    exact ⟨himax_exceptional, hr_imax.symm⟩
  have hshell_nonempty : shell.Nonempty := ⟨imax, himax_shell⟩
  let remainder : Finset iota := exceptional.filter fun i => i ∉ shell
  let remainingModuli : Finset Real := insert q0 (remainder.image ratio)
  have hremaining_nonempty : remainingModuli.Nonempty := by
    exact ⟨q0, by simp [remainingModuli]⟩
  let q : Real := remainingModuli.max' hremaining_nonempty
  have hq0_mem : q0 ∈ remainingModuli := by
    simp [remainingModuli]
  have hq0_le_q : q0 <= q := by
    change q0 <= remainingModuli.max' hremaining_nonempty
    exact Finset.le_max' _ _ hq0_mem
  have hq_one : 1 <= q := hq0_one.le.trans hq0_le_q
  have hq_lt : q < r := by
    change remainingModuli.max' hremaining_nonempty < r
    rw [Finset.max'_lt_iff]
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hq0_lt_r
    · obtain ⟨i, hi_remainder, rfl⟩ := Finset.mem_image.mp hy
      have hi_parts := Finset.mem_filter.mp hi_remainder
      have hi_le : ratio i <= r := by
        dsimp [r]
        exact Finset.le_sup' ratio hi_parts.1
      have hi_ne : ratio i ≠ r := by
        intro hi_eq
        apply hi_parts.2
        exact Finset.mem_filter.mpr ⟨hi_parts.1, hi_eq⟩
      exact lt_of_le_of_ne hi_le hi_ne
  have hshell (i : iota) (hi : i ∈ shell) :
      norm (1 + u i) = r := by
    have hi_ratio := (Finset.mem_filter.mp hi).2
    exact hi_ratio
  have hrest (i : iota) (hi : i ∉ shell) :
      norm (1 + u i) <= q := by
    by_cases hi_exceptional : i ∈ exceptional
    · have hi_remainder : i ∈ remainder :=
        Finset.mem_filter.mpr ⟨hi_exceptional, hi⟩
      have hi_modulus : ratio i ∈ remainingModuli := by
        apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨i, hi_remainder, rfl⟩
      change ratio i <= q
      change ratio i <= remainingModuli.max' hremaining_nonempty
      exact Finset.le_max' _ _ hi_modulus
    · have hi_not_large : ¬ q0 < ratio i := by
        intro hi_large
        exact hi_exceptional ((hexceptional_mem i).2 hi_large)
      change ratio i <= q
      exact (le_of_not_gt hi_not_large).trans hq0_le_q
  exact (not_nonneg_bombieriLagariasNormalizedSummand_of_dominant_shell
    u hlinear hquadratic shell hshell_nonempty r q hr hq_one hq_lt
      hshell hrest) hnonneg

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
