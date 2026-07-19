import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisEndpoints

/-!
# Compact bound for residual real-axis zeta zeroes

Real-axis zero classification is stronger than the p-series counting route
needs.  A residual real zero is nontrivial, hence it lies strictly between
`0` and `1`: the nonpositive half-axis is covered by the proved trivial-zero
classification, and Mathlib gives zeta nonvanishing on `re >= 1`.  Therefore
every residual real-axis window is contained in one fixed compact window.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Any nontrivial real-axis zeta zero belongs to the fixed radius-one
residual window. -/
theorem mem_closedBallZeroResidualRealAxisFinset_one_of_axis_not_trivial
    (rho : ZetaZeroSubtype)
    (haxis : Complex.im (rho : Complex) = 0)
    (hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex)) :
    rho ∈ closedBallZeroResidualRealAxisFinset 1 := by
  have hz : IsZetaZero (rho : Complex) := by
    unfold IsZetaZero
    exact mem_riemannZetaZeros.mp rho.property
  have hre_pos : 0 < Complex.re (rho : Complex) := by
    by_contra hnot
    have hre_nonpos : Complex.re (rho : Complex) <= 0 := le_of_not_gt hnot
    exact hnotTrivial
      (isTrivialZetaZero_of_isZetaZero_of_im_eq_zero_of_re_nonpos
        hz haxis hre_nonpos)
  have hre_lt_one : Complex.re (rho : Complex) < 1 := hz.re_lt_one
  have hnorm_le : norm (rho : Complex) <= 1 := by
    have hcoordinate := Complex.norm_le_abs_re_add_abs_im (rho : Complex)
    rw [haxis, abs_zero, add_zero, abs_of_pos hre_pos] at hcoordinate
    exact hcoordinate.trans (le_of_lt hre_lt_one)
  have hwindow : (rho : Complex) ∈ closedBallZero.window 1 := by
    rw [mem_closedBallZero_iff]
    simpa [dist_eq_norm] using hnorm_le
  have hzeroWindow : rho ∈ closedBallZero.zetaZeroSubtypeFinset 1 :=
    (closedBallZero.mem_zetaZeroSubtypeFinset_iff 1).mpr hwindow
  apply (mem_closedBallZeroResidualRealAxisFinset 1).mpr
  exact ⟨(mem_closedBallZeroAxisOrdinateFinset 1).mpr ⟨hzeroWindow, haxis⟩,
    hnotTrivial⟩

/-- Every residual real-axis zero, regardless of the original closed-ball
radius, already belongs to the radius-one residual window. -/
theorem closedBallZeroResidualRealAxisFinset_subset_one (n : Nat) :
    closedBallZeroResidualRealAxisFinset n ⊆
      closedBallZeroResidualRealAxisFinset 1 := by
  classical
  intro rho hrho
  have hresidual :=
    (mem_closedBallZeroResidualRealAxisFinset n).mp hrho
  have haxisWindow :=
    (mem_closedBallZeroAxisOrdinateFinset n).mp hresidual.1
  have haxis : Complex.im (rho : Complex) = 0 := haxisWindow.2
  exact
    mem_closedBallZeroResidualRealAxisFinset_one_of_axis_not_trivial
      rho haxis hresidual.2

/-- The fixed finite cardinality controlling every residual real-axis
window.  No assertion that this cardinality is zero is required. -/
noncomputable def residualRealAxisCompactCard : Real :=
  ((closedBallZeroResidualRealAxisFinset 1).card : Real)

theorem residualRealAxisCompactCard_nonneg :
    0 <= residualRealAxisCompactCard := by
  unfold residualRealAxisCompactCard
  positivity

/-- Uniform cardinality bound for residual real-axis windows. -/
theorem closedBallZeroResidualRealAxis_card_le_compactCard (n : Nat) :
    ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
      residualRealAxisCompactCard := by
  unfold residualRealAxisCompactCard
  exact_mod_cast Finset.card_le_card
    (closedBallZeroResidualRealAxisFinset_subset_one n)

/-- The full real-axis window is bounded by its elementary linear trivial-zero
part plus the fixed compact residual contribution. -/
theorem closedBallZeroAxis_card_le_linear_add_compactResidual (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
      ((n : Real) + 1) + residualRealAxisCompactCard := by
  rw [closedBallZeroAxis_card_eq_knownTrivial_add_residual_real]
  have hknown := closedBallZeroKnownTrivialAxis_card_le_linear n
  have hresidual := closedBallZeroResidualRealAxis_card_le_compactCard n
  nlinarith

/-- On the cutoff-three tail, the entire real-axis contribution has a
quadratic envelope with a fixed finite constant. -/
theorem closedBallZeroAxis_card_cutoffThree_le_compactQuadratic (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset (n + 3)).card : Real) <=
      (4 + residualRealAxisCompactCard) *
        |(n : Real) + 1| ^ (2 : Real) := by
  let R : Real := |(n : Real) + 1| ^ (2 : Real)
  have hn_nonneg : (0 : Real) <= n := Nat.cast_nonneg n
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    positivity
  have hR_ge_one : 1 <= R := by
    dsimp [R]
    apply Real.one_le_rpow
    · rw [abs_of_nonneg (by positivity)]
      linarith
    · norm_num
  have hlinear : (((n + 3 : Nat) : Real) + 1) <= 4 * R := by
    dsimp [R]
    rw [abs_of_nonneg (by positivity)]
    norm_num [Nat.cast_add]
    nlinarith
  have hresidualScaled :
      residualRealAxisCompactCard <= residualRealAxisCompactCard * R := by
    simpa using
      (mul_le_mul_of_nonneg_left hR_ge_one
        residualRealAxisCompactCard_nonneg)
  have haxis := closedBallZeroAxis_card_le_linear_add_compactResidual (n + 3)
  change
    ((closedBallZeroAxisOrdinateFinset (n + 3)).card : Real) <=
      (4 + residualRealAxisCompactCard) * R
  nlinarith

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
