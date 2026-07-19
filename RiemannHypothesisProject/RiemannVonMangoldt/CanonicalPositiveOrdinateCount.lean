import RiemannHypothesisProject.CompactZetaZeroWindow
import RiemannHypothesisProject.RiemannVonMangoldtConcretePublishedSources
import RiemannHypothesisProject.RiemannWeilShiftedRadius.TrivialAxisGeometry

/-!
# Canonical positive-ordinate zeta-zero count

This module constructs the actual finite distinct-zero counting function

`N(T) = #{rho : zeta rho = 0, 0 < im rho <= T}`

from Mathlib's discreteness theorem for Riemann-zeta zeroes.  This is the exact
window needed by the project cardinality arguments.  Bellotti-Wong's
argument-principle count includes analytic multiplicity; the faithful source
target is therefore built from this window in `CanonicalMultiplicityCount`.
-/

namespace RiemannHypothesisProject

open Metric

namespace ComplexCompactExhaustion

noncomputable section

/-- The finite set of actual zeta zeroes with positive ordinate at most `T`. -/
noncomputable def canonicalPositiveOrdinateZetaZeroWindow
    (T : Real) : Finset Complex := by
  classical
  exact if hT : 0 < T then
    (compactZetaZeroFinset
      (closedBall (0 : Complex) (T + 1))
      (isCompact_closedBall (0 : Complex) (T + 1))).filter
        (fun s : Complex => 0 < s.im ∧ s.im <= T)
  else ∅

/-- A positive-ordinate zeta zero is nontrivial. -/
theorem not_isTrivialZetaZero_of_im_pos
    {s : Complex} (him : 0 < s.im) :
    ¬ IsTrivialZetaZero s := by
  rintro ⟨n, rfl⟩
  norm_num at him

/-- Every positive-ordinate zeta zero lies strictly inside the left boundary
of the critical strip.  The boundary case `re s = 0` is ruled out by the
completed-zeta functional equation and nonvanishing on `re s = 1`. -/
theorem IsZetaZero.re_pos_of_im_pos
    {s : Complex} (hz : IsZetaZero s) (him : 0 < s.im) :
    0 < s.re := by
  let rho : ZetaZeroSubtype :=
    ⟨s, by simpa [IsZetaZero, riemannZetaZeros] using hz⟩
  have hre_nonneg : 0 <= s.re := by
    simpa [rho] using
      zetaZeroSubtype_re_nonneg_of_not_trivial rho
        (not_isTrivialZetaZero_of_im_pos him)
  by_contra hre_not_pos
  have hre_zero : s.re = 0 :=
    le_antisymm (le_of_not_gt hre_not_pos) hre_nonneg
  have hs_ne_zero : s ≠ 0 := by
    intro hs
    subst s
    norm_num at him
  have hgamma_ne : Complex.Gammaℝ s ≠ 0 := by
    intro hgamma
    rcases Complex.Gammaℝ_eq_zero_iff.mp hgamma with ⟨n, hn⟩
    have him_eq := congrArg Complex.im hn
    norm_num at him_eq
    linarith
  have hcompleted : completedRiemannZeta s = 0 := by
    have hz' : riemannZeta s = 0 := hz
    rw [riemannZeta_def_of_ne_zero hs_ne_zero] at hz'
    rcases div_eq_zero_iff.mp hz' with hzero | hgamma
    · exact hzero
    · exact (hgamma_ne hgamma).elim
  have hone_sub_ne_zero : 1 - s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [hre_zero] at hre
  have hmirror_zero : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero hone_sub_ne_zero,
      completedRiemannZeta_one_sub, hcompleted]
    simp
  exact
    (riemannZeta_ne_zero_of_one_le_re
      (s := 1 - s) (by simp [hre_zero])) hmirror_zero

/-- Every positive-ordinate zero below `T` lies in the compact ball used to
define the canonical finite window. -/
theorem norm_le_add_one_of_isZetaZero_of_im_pos_le
    {s : Complex} {T : Real}
    (hz : IsZetaZero s) (him : 0 < s.im) (himT : s.im <= T) :
    norm s <= T + 1 := by
  let rho : ZetaZeroSubtype :=
    ⟨s, by simpa [IsZetaZero, riemannZetaZeros] using hz⟩
  have hre_nonneg : 0 <= s.re := by
    simpa [rho] using
      zetaZeroSubtype_re_nonneg_of_not_trivial rho
        (not_isTrivialZetaZero_of_im_pos him)
  have hre_lt_one : s.re < 1 := hz.re_lt_one
  have habs_re : |s.re| <= 1 := by
    rw [abs_of_nonneg hre_nonneg]
    exact hre_lt_one.le
  have habs_im : |s.im| <= T := by
    rw [abs_of_pos him]
    exact himT
  calc
    norm s <= |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
    _ <= 1 + T := add_le_add habs_re habs_im
    _ = T + 1 := by ring

/-- Membership in the canonical finite window is exactly the defining
positive-ordinate zeta-zero condition. -/
theorem mem_canonicalPositiveOrdinateZetaZeroWindow_iff
    (T : Real) (s : Complex) :
    s ∈ canonicalPositiveOrdinateZetaZeroWindow T ↔
      IsZetaZero s ∧ 0 < s.im ∧ s.im <= T := by
  classical
  constructor
  · intro hs
    by_cases hT : 0 < T
    · rw [canonicalPositiveOrdinateZetaZeroWindow, dif_pos hT,
        Finset.mem_filter] at hs
      have hcompact :=
        (mem_compactZetaZeroFinset
          (isCompact_closedBall (0 : Complex) (T + 1))).mp hs.1
      exact ⟨hcompact.2, hs.2⟩
    · simp [canonicalPositiveOrdinateZetaZeroWindow, hT] at hs
  · rintro ⟨hz, him, himT⟩
    have hT : 0 < T := him.trans_le himT
    rw [canonicalPositiveOrdinateZetaZeroWindow, dif_pos hT,
      Finset.mem_filter]
    refine ⟨?_, him, himT⟩
    rw [mem_compactZetaZeroFinset
      (isCompact_closedBall (0 : Complex) (T + 1))]
    refine ⟨?_, hz⟩
    rw [mem_closedBall, dist_zero_right]
    exact norm_le_add_one_of_isZetaZero_of_im_pos_le hz him himT

/-- The canonical window is exactly the paper convention: nontrivial zeros in
`0 < re s < 1` with `0 < im s <= T`. -/
theorem mem_canonicalPositiveOrdinateZetaZeroWindow_iff_paper
    (T : Real) (s : Complex) :
    s ∈ canonicalPositiveOrdinateZetaZeroWindow T ↔
      IsZetaZero s ∧ 0 < s.re ∧ s.re < 1 ∧
        0 < s.im ∧ s.im <= T := by
  rw [mem_canonicalPositiveOrdinateZetaZeroWindow_iff]
  constructor
  · rintro ⟨hz, him, himT⟩
    exact ⟨hz, IsZetaZero.re_pos_of_im_pos hz him, hz.re_lt_one, him, himT⟩
  · rintro ⟨hz, _hre_pos, _hre_lt, him, himT⟩
    exact ⟨hz, him, himT⟩

/-- The canonical real-valued positive-ordinate zero count. -/
noncomputable def canonicalPositiveOrdinateZetaZeroCount
    (T : Real) : Real :=
  ((canonicalPositiveOrdinateZetaZeroWindow T).card : Nat)

/-- The canonical count is nonnegative. -/
theorem canonicalPositiveOrdinateZetaZeroCount_nonneg
    (T : Real) :
    0 <= canonicalPositiveOrdinateZetaZeroCount T := by
  unfold canonicalPositiveOrdinateZetaZeroCount
  exact_mod_cast
    (Nat.zero_le (canonicalPositiveOrdinateZetaZeroWindow T).card)

/-- The canonical count vanishes at nonpositive heights. -/
theorem canonicalPositiveOrdinateZetaZeroCount_eq_zero_of_nonpos
    {T : Real} (hT : T <= 0) :
    canonicalPositiveOrdinateZetaZeroCount T = 0 := by
  simp [canonicalPositiveOrdinateZetaZeroCount,
    canonicalPositiveOrdinateZetaZeroWindow, not_lt.mpr hT]

/-- The canonical positive-ordinate zero count is monotone. -/
theorem canonicalPositiveOrdinateZetaZeroCount_mono
    {T U : Real} (hTU : T <= U) :
    canonicalPositiveOrdinateZetaZeroCount T <=
      canonicalPositiveOrdinateZetaZeroCount U := by
  unfold canonicalPositiveOrdinateZetaZeroCount
  exact_mod_cast Finset.card_le_card (by
    intro s hs
    have hmem :=
      (mem_canonicalPositiveOrdinateZetaZeroWindow_iff T s).mp hs
    exact
      (mem_canonicalPositiveOrdinateZetaZeroWindow_iff U s).mpr
        ⟨hmem.1, hmem.2.1, hmem.2.2.trans hTU⟩)

/-- The canonical count supplies the exact source-shaped finite-window data
expected by published Riemann-von Mangoldt theorems. -/
noncomputable def canonicalSourceExactPositiveOrdinateHeightCountWindow :
    SourceExactPositiveOrdinateHeightCountWindow
      canonicalPositiveOrdinateZetaZeroCount where
  window := canonicalPositiveOrdinateZetaZeroWindow
  mem_window_iff := mem_canonicalPositiveOrdinateZetaZeroWindow_iff
  heightCount_eq_card := fun _T => rfl

/-- A Bellotti-Wong-shaped theorem from an independently proved inequality for
the distinct count.  This is not a direct restatement of the paper theorem
unless zero simplicity is also known; use `CanonicalMultiplicityCount` for the
faithful argument-principle normalization. -/
noncomputable def bellottiWongPublishedExactNTTheorem_of_canonicalCount
    (hpublished :
      ∀ T : Real,
        bellottiWongValidFrom <= T ->
          |canonicalPositiveOrdinateZetaZeroCount T -
              riemannVonMangoldtMainTerm T| <=
            bellottiWongErrorTerm T) :
    BellottiWongPublishedExactNTTheorem where
  heightCount := canonicalPositiveOrdinateZetaZeroCount
  sourceExactHeightWindow :=
    canonicalSourceExactPositiveOrdinateHeightCountWindow
  published_abs_error_le := hpublished

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
