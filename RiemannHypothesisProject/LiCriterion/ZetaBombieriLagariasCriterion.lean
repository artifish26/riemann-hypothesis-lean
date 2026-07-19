import RiemannHypothesisProject.LiCriterion.ZetaBombieriLagariasSummability
import RiemannHypothesisProject.LiCriterion.ZetaFunctionalReflection
import RiemannHypothesisProject.LiCriterion.ResidualBridgeInput

/-!
# The Bombieri-Lagarias criterion for the full zeta Li coefficients

This endpoint applies the normalized dominant-modulus theorem to the actual
signed, multiplicity-expanded nontrivial zeta-zero multiset.  Nonnegativity of
the M50 coefficients first places every Li ratio in the closed unit disk,
which gives `1 / 2 <= re rho`; completed-zeta reflection gives the opposite
inequality.  The reverse implication is termwise critical-line positivity.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The closed-unit-disk condition for the M50 Li ratio gives the lower
critical half-plane. -/
theorem one_half_le_re_of_norm_one_sub_inv_le_one
    {rho : Complex} (hrho_ne : rho ≠ 0)
    (hratio : norm (1 - rho⁻¹) <= 1) :
    (1 / 2 : Real) <= rho.re := by
  have hratio_eq : 1 - rho⁻¹ = (rho - 1) / rho := by
    field_simp [hrho_ne]
  rw [hratio_eq, norm_div] at hratio
  have hnorm_pos : 0 < norm rho := norm_pos_iff.mpr hrho_ne
  have hnorm_le : norm (rho - 1) <= norm rho :=
    (div_le_one hnorm_pos).mp hratio
  have hsquare : norm (rho - 1) ^ 2 <= norm rho ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm_le
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply] at hsquare
  rw [Complex.sub_re, Complex.sub_im] at hsquare
  simp only [Complex.one_re, Complex.one_im, sub_zero] at hsquare
  nlinarith

/-- Coefficient nonnegativity places every member of the signed expanded zeta
multiset in the lower critical half-plane. -/
theorem signedZetaZeroValue_one_half_le_re_of_fullZetaLiCoefficient_nonneg
    (hli : forall n : Nat, 0 < n -> 0 <= fullZetaLiCoefficient n)
    (i : SignedZetaZeroMultiplicityIndex) :
    (1 / 2 : Real) <= (signedZetaZeroValue i).re := by
  have hlower := bombieriLagarias_lower_half_plane
    signedZetaZeroValue
    signedZetaZeroValue_ne_zero
    signedZetaZeroValue_ne_one
    summable_signedZetaBombieriLagariasSourceWeight
    (fun n hn => by
      have hcoefficient := hli n hn
      rw [fullZetaLiCoefficient_eq_signed_normalized_tsum] at hcoefficient
      simpa [bombieriLagariasLiSummand,
        bombieriLagariasNormalizedSummand,
        signedZetaBombieriLagariasIncrement, sub_eq_add_neg] using
        hcoefficient)
  exact hlower i

/-- Coefficient nonnegativity gives the lower half-plane bound for every
nontrivial zeta zero, using the positive analytic multiplicity to select a
literal member of the expanded multiset. -/
theorem one_half_le_re_of_fullZetaLiCoefficient_nonneg
    (hli : forall n : Nat, 0 < n -> 0 <= fullZetaLiCoefficient n)
    {rho : Complex} (hrho : IsNontrivialZetaZero rho) :
    (1 / 2 : Real) <= rho.re := by
  let rhoSubtype : ZetaZeroSubtype := ⟨rho, hrho.1⟩
  have hmult : 0 < zetaZeroMultiplicity rhoSubtype := by
    exact Nat.zero_lt_of_lt (one_le_zetaZeroMultiplicity rhoSubtype)
  let k : Fin (zetaZeroMultiplicity rhoSubtype) := ⟨0, hmult⟩
  obtain ⟨i, hi⟩ := exists_signedZetaZeroMultiplicityIndex_value_eq
    rhoSubtype hrho.2.1 k
  have hi_lower :=
    signedZetaZeroValue_one_half_le_re_of_fullZetaLiCoefficient_nonneg hli i
  simpa [hi] using hi_lower

/-- The actual Bombieri-Lagarias implication for the full multiplicity-aware
zeta Li coefficients. -/
theorem RHStatement_of_fullZetaLiCoefficient_nonneg
    (hli : forall n : Nat, 0 < n -> 0 <= fullZetaLiCoefficient n) :
    RHStatement := by
  intro rho hrho
  have hlower : (1 / 2 : Real) <= rho.re :=
    one_half_le_re_of_fullZetaLiCoefficient_nonneg hli hrho
  have hmirror_lower : (1 / 2 : Real) <= (1 - rho).re :=
    one_half_le_re_of_fullZetaLiCoefficient_nonneg hli
      (isNontrivialZetaZero_one_sub hrho)
  unfold IsCriticalLine
  change (1 / 2 : Real) <= 1 - rho.re at hmirror_lower
  exact le_antisymm (by linarith) hlower

/-- RH makes every summand in the full coefficient nonnegative. -/
theorem fullZetaLiCoefficient_nonneg_of_RHStatement
    (hRH : RHStatement) (n : Nat) :
    0 <= fullZetaLiCoefficient n := by
  rw [fullZetaLiCoefficient]
  apply tsum_nonneg
  intro rho
  have hnot_trivial : ¬ IsTrivialZetaZero (rho : Complex) :=
    not_isTrivialZetaZero_of_im_ne_zero (ne_of_gt rho.2)
  have hne_one : (rho : Complex) ≠ 1 := by
    intro hrho_one
    have him := congrArg Complex.im hrho_one
    simp at him
    exact (ne_of_gt rho.2) him
  have hnontrivial : IsNontrivialZetaZero (rho : Complex) :=
    ⟨rho.1.property, hnot_trivial, hne_one⟩
  have hline := hRH (rho : Complex) hnontrivial
  have hrho_eq : (rho : Complex) = criticalLinePoint (rho : Complex).im := by
    apply Complex.ext
    · simpa [IsCriticalLine, criticalLinePoint] using hline
    · simp [criticalLinePoint]
  have hsummand :
      (zetaLiComplexSummand (rho : Complex) n).re =
        criticalLineLiSummand (rho : Complex).im n := by
    rw [hrho_eq]
    simp [zetaLiComplexSummand, criticalLineLiSummand,
      criticalLineLiRatio, criticalLinePoint]
  rw [multiplicityWeightedZetaLiRealSummand, hsummand]
  exact mul_nonneg (zetaZeroMultiplicityReal_pos rho.1).le
    (mul_nonneg (by norm_num)
      (criticalLineLiSummand_nonneg (rho : Complex).im n))

/-- Project RH is equivalent to nonnegativity of every full
multiplicity-aware zeta Li coefficient. -/
theorem RHStatement_iff_fullZetaLiCoefficient_nonneg :
    RHStatement ↔
      forall n : Nat, 0 < n -> 0 <= fullZetaLiCoefficient n := by
  constructor
  · intro hRH n _hn
    exact fullZetaLiCoefficient_nonneg_of_RHStatement hRH n
  · exact RHStatement_of_fullZetaLiCoefficient_nonneg

/-- Mathlib's RH statement has the same full zeta Li coefficient criterion. -/
theorem mathlib_RH_iff_fullZetaLiCoefficient_nonneg :
    RiemannHypothesis ↔
      forall n : Nat, 0 < n -> 0 <= fullZetaLiCoefficient n := by
  rw [← RHStatement_iff_mathlib]
  exact RHStatement_iff_fullZetaLiCoefficient_nonneg

/-- The legacy abstract criterion package, now instantiated by the proved
Bombieri-Lagarias implication rather than an assumed implication field. -/
def fullZetaLiCriterionData :
    AbstractLiCriterionData (fun _ : Complex => True) where
  coefficient := fullZetaLiCoefficient
  li_nonneg_implies_RHOn := fun hli =>
    RHStatement_iff_RHOn_univ.mp
      (RHStatement_of_fullZetaLiCoefficient_nonneg hli)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
