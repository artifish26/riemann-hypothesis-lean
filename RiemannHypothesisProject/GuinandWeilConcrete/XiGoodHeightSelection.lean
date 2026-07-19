import RiemannHypothesisProject.GuinandWeilConcrete.GoodHeightSelection
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiJensen

/-!
# Canonical good heights for xi

This module applies the finite-set avoidance lemma to the project's exact
positive-ordinate zeta-zero window and then weakens the separation scale to
the canonical multiplicity-aware zero count.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Complex Metric Set

noncomputable section

/-- The distinct ordinates in the canonical positive-zero window. -/
noncomputable def canonicalPositiveZeroOrdinateFinset (T : Real) :
    Finset Real :=
  (canonicalExactPositiveOrdinateZetaZeroWindow.window T).image
    (fun rho : ZetaZeroSubtype => im (rho : Complex))

/-- Every unit interval contains a height separated from every canonical
positive zero below an arbitrary finite cutoff `H`. -/
theorem exists_canonicalXi_goodHeight_below (N : Nat) (H : Real) :
    ∃ T : Real, (N : Real) <= T ∧ T <= N + 1 ∧
      ∀ rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window H,
        1 /
            (4 *
              (canonicalPositiveOrdinateZetaZeroMultiplicityCount H + 1)) <=
          |T - im (rho : Complex)| := by
  let s := canonicalPositiveZeroOrdinateFinset H
  obtain ⟨T, hT, hsep⟩ := exists_mem_Icc_dist_finset_ge s (N : Real)
  refine ⟨T, hT.1, by simpa using hT.2, fun rho hrho => ?_⟩
  have him_mem : im (rho : Complex) ∈ s := by
    dsimp [s, canonicalPositiveZeroOrdinateFinset]
    exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
  have hraw := hsep (im (rho : Complex)) him_mem
  rw [Real.dist_eq] at hraw
  have himage_card :
      ((s.card : Nat) : Real) <=
        ((canonicalExactPositiveOrdinateZetaZeroWindow.window H).card : Nat) := by
    dsimp [s, canonicalPositiveZeroOrdinateFinset]
    exact_mod_cast Finset.card_image_le
  have hwindow_card :
      (((canonicalExactPositiveOrdinateZetaZeroWindow.window H).card : Nat) : Real) <=
        canonicalPositiveOrdinateZetaZeroMultiplicityCount H := by
    apply positiveFiniteWindow_card_le_canonicalMultiplicityCount
    intro z hz
    exact
      (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff H z).mp hz
  have hcard :
      (s.card : Real) <= canonicalPositiveOrdinateZetaZeroMultiplicityCount H :=
    himage_card.trans hwindow_card
  have hdenom :
      4 * ((s.card : Real) + 1) <=
        4 * (canonicalPositiveOrdinateZetaZeroMultiplicityCount H + 1) := by
    linarith
  have hrecip :
      1 /
          (4 * (canonicalPositiveOrdinateZetaZeroMultiplicityCount H + 1)) <=
        1 / (4 * ((s.card : Real) + 1)) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  exact hrecip.trans hraw

/-- Every unit interval contains a height separated from every canonical
positive zero below `N + 2`, at the reciprocal multiplicity-count scale. -/
theorem exists_canonicalXi_goodHeight (N : Nat) :
    ∃ T : Real, (N : Real) <= T ∧ T <= N + 1 ∧
      ∀ rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 2),
        1 /
            (4 *
              (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) + 1)) <=
          |T - im (rho : Complex)| := by
  let s := canonicalPositiveZeroOrdinateFinset (N + 2)
  obtain ⟨T, hT, hsep⟩ := exists_mem_Icc_dist_finset_ge s (N : Real)
  refine ⟨T, hT.1, by simpa using hT.2, fun rho hrho => ?_⟩
  have him_mem : im (rho : Complex) ∈ s := by
    dsimp [s, canonicalPositiveZeroOrdinateFinset]
    exact Finset.mem_image.mpr ⟨rho, hrho, rfl⟩
  have hraw := hsep (im (rho : Complex)) him_mem
  rw [Real.dist_eq] at hraw
  have himage_card :
      ((s.card : Nat) : Real) <=
        ((canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 2)).card : Nat) := by
    dsimp [s, canonicalPositiveZeroOrdinateFinset]
    exact_mod_cast Finset.card_image_le
  have hwindow_card :
      (((canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 2)).card : Nat) : Real) <=
        canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) := by
    apply positiveFiniteWindow_card_le_canonicalMultiplicityCount
    intro z hz
    exact
      (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff (N + 2) z).mp hz
  have hcard :
      (s.card : Real) <=
        canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) :=
    himage_card.trans hwindow_card
  have hdenom :
      4 * ((s.card : Real) + 1) <=
        4 *
          (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) + 1) := by
    linarith
  have hrecip :
      1 /
          (4 *
            (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) + 1)) <=
        1 / (4 * ((s.card : Real) + 1)) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  exact hrecip.trans hraw

/-- At the selected height, the full canonical positive-window principal-part
sum has a quadratic bound in the multiplicity-aware count.  This deliberately
uses a coarse global count; Gaussian decay does not require the sharp
classical local `O(log T)` estimate. -/
theorem exists_canonicalXi_goodHeight_principalPart_bound (N : Nat) :
    ∃ T : Real, (N : Real) <= T ∧ T <= N + 1 ∧
      ∀ sigma : Real,
        norm
            (∑ rho ∈
                canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 2),
              (zetaZeroMultiplicity rho : Complex) /
                ((sigma : Complex) + Complex.I * T - (rho : Complex))) <=
          4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) *
            (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) + 1) := by
  obtain ⟨T, hTN, hTN1, hsep⟩ := exists_canonicalXi_goodHeight N
  refine ⟨T, hTN, hTN1, fun sigma => ?_⟩
  let C : Real := canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2)
  let window := canonicalExactPositiveOrdinateZetaZeroWindow.window (N + 2)
  have hC : 0 <= C := by
    dsimp [C]
    exact canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg _
  have hcount_eq :
      (∑ rho ∈ window, zetaZeroMultiplicityReal rho) = C := by
    dsimp [C, window]
    unfold canonicalPositiveOrdinateZetaZeroMultiplicityCount
      multiplicityWeightedPositiveOrdinateHeightCountReal
    rw [← Finset.sum_attach]
    simp only [Finset.attach_eq_univ]
  have hterm : ∀ rho ∈ window,
      norm
          ((zetaZeroMultiplicity rho : Complex) /
            ((sigma : Complex) + Complex.I * T - (rho : Complex))) <=
        zetaZeroMultiplicityReal rho * (4 * (C + 1)) := by
    intro rho hrho
    have hsep_rho : 1 / (4 * (C + 1)) <= |T - im (rho : Complex)| := by
      simpa [C, window] using hsep rho hrho
    have hnorm_denom :
        |T - im (rho : Complex)| <=
          norm ((sigma : Complex) + Complex.I * T - (rho : Complex)) := by
      have him := Complex.abs_im_le_norm
        ((sigma : Complex) + Complex.I * T - (rho : Complex))
      simpa using him
    have hdelta :
        1 / (4 * (C + 1)) <=
          norm ((sigma : Complex) + Complex.I * T - (rho : Complex)) :=
      hsep_rho.trans hnorm_denom
    have hdelta_pos : 0 < 1 / (4 * (C + 1)) := by positivity
    have hdenom_pos :
        0 < norm ((sigma : Complex) + Complex.I * T - (rho : Complex)) :=
      hdelta_pos.trans_le hdelta
    rw [norm_div, norm_natCast]
    have hdiv :
        (zetaZeroMultiplicity rho : Real) /
            norm ((sigma : Complex) + Complex.I * T - (rho : Complex)) <=
          (zetaZeroMultiplicity rho : Real) / (1 / (4 * (C + 1))) := by
      exact div_le_div_of_nonneg_left (by positivity) hdelta_pos hdelta
    calc
      (zetaZeroMultiplicity rho : Real) /
          norm ((sigma : Complex) + Complex.I * T - (rho : Complex)) <=
        (zetaZeroMultiplicity rho : Real) / (1 / (4 * (C + 1))) := hdiv
      _ = zetaZeroMultiplicityReal rho * (4 * (C + 1)) := by
        unfold zetaZeroMultiplicityReal
        field_simp
  calc
    norm
        (∑ rho ∈ window,
          (zetaZeroMultiplicity rho : Complex) /
            ((sigma : Complex) + Complex.I * T - (rho : Complex))) <=
      ∑ rho ∈ window,
        norm
          ((zetaZeroMultiplicity rho : Complex) /
            ((sigma : Complex) + Complex.I * T - (rho : Complex))) :=
      norm_sum_le _ _
    _ <= ∑ rho ∈ window,
        zetaZeroMultiplicityReal rho * (4 * (C + 1)) := by
      exact Finset.sum_le_sum fun rho hrho => hterm rho hrho
    _ = 4 * C * (C + 1) := by
      rw [← Finset.sum_mul, hcount_eq]
      ring
    _ = 4 * canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) *
        (canonicalPositiveOrdinateZetaZeroMultiplicityCount (N + 2) + 1) := by
      rfl

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
