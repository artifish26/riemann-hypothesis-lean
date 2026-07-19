import RiemannHypothesisProject.LiCriterion.BombieriLagarias
import RiemannHypothesisProject.LiCriterion.ZetaLiCoefficient

/-!
# Bombieri-Lagarias summability for the zeta multiset

This module places the full signed, multiplicity-expanded zeta-zero multiset
in the normalized coordinates `u rho = -rho⁻¹`.  The resulting power sum
is definitionally the M50 Li summand.  Its two summability inputs are proved
from the unconditional multiplicity-weighted inverse-square height estimate.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate Filter

noncomputable section

/-- The normalized increment whose ratio `1 + u` is the M50 Li ratio. -/
def signedZetaBombieriLagariasIncrement
    (i : SignedZetaZeroMultiplicityIndex) : Complex :=
  -(signedZetaZeroValue i)⁻¹

/-- The normalized Bombieri-Lagarias summand is exactly the real part of the
existing zeta Li summand. -/
theorem bombieriLagariasNormalizedSummand_signedZeta_eq
    (i : SignedZetaZeroMultiplicityIndex) (n : Nat) :
    bombieriLagariasNormalizedSummand
        (signedZetaBombieriLagariasIncrement i) n =
      (zetaLiComplexSummand (signedZetaZeroValue i) n).re := by
  rfl

/-- The multiplicity-weighted inverse-square reciprocal family on distinct
positive-ordinate zeros is summable. -/
theorem summable_positiveOrdinateZetaZero_multiplicity_inv_norm_sq :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        norm ((rho : Complex)⁻¹) ^ 2) := by
  have hmajor : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        positiveOrdinateZetaZeroClampedHeight rho ^ 2) :=
    unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable
  apply Summable.of_norm_bounded_eventually hmajor
  filter_upwards [eventually_one_le_positiveOrdinateZetaZero_im]
    with rho hheight
  have hmult_nonneg : 0 <= zetaZeroMultiplicityReal rho.1 :=
    (zetaZeroMultiplicityReal_pos rho.1).le
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hmult_nonneg (sq_nonneg _))]
  calc
    zetaZeroMultiplicityReal rho.1 * norm ((rho : Complex)⁻¹) ^ 2 <=
        zetaZeroMultiplicityReal rho.1 *
          (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (norm_inv_sq_le_clampedInverseSquare rho hheight) hmult_nonneg
    _ = zetaZeroMultiplicityReal rho.1 /
        positiveOrdinateZetaZeroClampedHeight rho ^ 2 := by
      rw [div_eq_mul_inv]

/-- Expanding analytic multiplicity into the positive index preserves the
unconditional inverse-square summability. -/
theorem summable_positiveOrdinateZetaZeroMultiplicityIndex_inv_norm_sq :
    Summable (fun i : PositiveOrdinateZetaZeroMultiplicityIndex =>
      norm ((i.1 : Complex)⁻¹) ^ 2) := by
  refine (summable_sigma_of_nonneg (fun _ => sq_nonneg _)).2 ⟨?_, ?_⟩
  · intro rho
    exact summable_of_ne_finset_zero (s := Finset.univ) (by simp)
  · simpa [tsum_fintype, zetaZeroMultiplicityReal, nsmul_eq_mul] using
      summable_positiveOrdinateZetaZero_multiplicity_inv_norm_sq

/-- The full signed multiplicity-expanded reciprocal-square family is
unconditionally summable. -/
theorem summable_signedZetaBombieriLagariasIncrement_norm_sq :
    Summable (fun i : SignedZetaZeroMultiplicityIndex =>
      norm (signedZetaBombieriLagariasIncrement i) ^ 2) := by
  apply Summable.sum
  · simpa [signedZetaBombieriLagariasIncrement, signedZetaZeroValue,
      Function.comp_def] using
      summable_positiveOrdinateZetaZeroMultiplicityIndex_inv_norm_sq
  · simpa [signedZetaBombieriLagariasIncrement, signedZetaZeroValue,
      Function.comp_def] using
      summable_positiveOrdinateZetaZeroMultiplicityIndex_inv_norm_sq

/-- In the critical strip, the real part of `-rho⁻¹` is bounded by the
reciprocal norm square. -/
theorem abs_neg_inv_re_le_norm_inv_sq
    {rho : Complex} (hrho_ne : rho ≠ 0)
    (hre_nonneg : 0 <= rho.re) (hre_le_one : rho.re <= 1) :
    abs ((-rho⁻¹).re) <= norm (-rho⁻¹) ^ 2 := by
  have hnormSq_pos : 0 < Complex.normSq rho :=
    Complex.normSq_pos.mpr hrho_ne
  change abs (-(rho⁻¹).re) <= norm (-(rho⁻¹)) ^ 2
  rw [abs_neg, Complex.inv_re]
  rw [abs_of_nonneg (div_nonneg hre_nonneg hnormSq_pos.le)]
  rw [norm_neg, Complex.sq_norm, Complex.normSq_inv]
  simpa [one_div] using
    (div_le_div_of_nonneg_right hre_le_one hnormSq_pos.le)

/-- The real linear terms required by the normalized criterion are absolutely
summable on the full signed zeta multiset. -/
theorem summable_signedZetaBombieriLagariasIncrement_abs_re :
    Summable (fun i : SignedZetaZeroMultiplicityIndex =>
      abs (signedZetaBombieriLagariasIncrement i).re) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
  · intro i
    have hnontrivial := signedZetaZeroValue_isNontrivialZetaZero i
    have hrho_ne : signedZetaZeroValue i ≠ 0 := by
      intro hrho
      have hz := hnontrivial.1
      rw [hrho] at hz
      norm_num [IsZetaZero, riemannZeta_zero] at hz
    have hre_nonneg : 0 <= (signedZetaZeroValue i).re :=
      zetaZeroSubtype_re_nonneg_of_not_trivial
        ⟨signedZetaZeroValue i, hnontrivial.1⟩ hnontrivial.2.1
    exact abs_neg_inv_re_le_norm_inv_sq hrho_ne
      hre_nonneg hnontrivial.re_lt_one.le
  · exact summable_signedZetaBombieriLagariasIncrement_norm_sq

/-- Every member of the signed expanded zeta multiset omits zero. -/
theorem signedZetaZeroValue_ne_zero
    (i : SignedZetaZeroMultiplicityIndex) :
    signedZetaZeroValue i ≠ 0 := by
  intro hrho
  have hz := signedZetaZeroValue_isZetaZero i
  rw [hrho] at hz
  norm_num [IsZetaZero, riemannZeta_zero] at hz

/-- Every member of the signed expanded zeta multiset omits one. -/
theorem signedZetaZeroValue_ne_one
    (i : SignedZetaZeroMultiplicityIndex) :
    signedZetaZeroValue i ≠ 1 :=
  (signedZetaZeroValue_isNontrivialZetaZero i).2.2

/-- On the nontrivial strip, the Bombieri-Lagarias source weight is bounded
by twice reciprocal norm square. -/
theorem bombieriLagariasSourceWeight_le_two_mul_norm_neg_inv_sq
    {rho : Complex} (hrho_ne : rho ≠ 0)
    (hre_nonneg : 0 <= rho.re) (hre_le_one : rho.re <= 1) :
    bombieriLagariasSourceWeight rho <= 2 * norm (-rho⁻¹) ^ 2 := by
  have hnorm_pos : 0 < norm rho := norm_pos_iff.mpr hrho_ne
  have hnorm_sq_pos : 0 < norm rho ^ 2 := sq_pos_of_pos hnorm_pos
  have hden_pos : 0 < (1 + norm rho) ^ 2 := by positivity
  have hnum_le : 1 + abs rho.re <= 2 := by
    rw [abs_of_nonneg hre_nonneg]
    linarith
  have hden_ge : norm rho ^ 2 <= (1 + norm rho) ^ 2 := by
    nlinarith [norm_nonneg rho]
  rw [norm_neg, norm_inv, inv_pow]
  unfold bombieriLagariasSourceWeight
  rw [show 2 * (norm rho ^ 2)⁻¹ = 2 / norm rho ^ 2 by
    rw [div_eq_mul_inv]]
  rw [div_le_div_iff₀ hden_pos hnorm_sq_pos]
  calc
    (1 + abs rho.re) * norm rho ^ 2 <= 2 * norm rho ^ 2 :=
      mul_le_mul_of_nonneg_right hnum_le (sq_nonneg _)
    _ <= 2 * (1 + norm rho) ^ 2 :=
      mul_le_mul_of_nonneg_left hden_ge (by norm_num)

/-- The exact Bombieri-Lagarias source convergence hypothesis is
unconditionally instantiated by the full signed zeta multiset. -/
theorem summable_signedZetaBombieriLagariasSourceWeight :
    Summable (fun i : SignedZetaZeroMultiplicityIndex =>
      bombieriLagariasSourceWeight (signedZetaZeroValue i)) := by
  apply Summable.of_nonneg_of_le
    (fun i => bombieriLagariasSourceWeight_nonneg (signedZetaZeroValue i))
  · intro i
    have hnontrivial := signedZetaZeroValue_isNontrivialZetaZero i
    have hre_nonneg : 0 <= (signedZetaZeroValue i).re :=
      zetaZeroSubtype_re_nonneg_of_not_trivial
        ⟨signedZetaZeroValue i, hnontrivial.1⟩ hnontrivial.2.1
    exact bombieriLagariasSourceWeight_le_two_mul_norm_neg_inv_sq
      (signedZetaZeroValue_ne_zero i) hre_nonneg hnontrivial.re_lt_one.le
  · simpa [signedZetaBombieriLagariasIncrement] using
      summable_signedZetaBombieriLagariasIncrement_norm_sq.mul_left 2

/-- The normalized power-sum family over the full signed zeta multiset is
summable at every exponent. -/
theorem summable_signedZetaBombieriLagariasNormalizedSummand (n : Nat) :
    Summable (fun i : SignedZetaZeroMultiplicityIndex =>
      bombieriLagariasNormalizedSummand
        (signedZetaBombieriLagariasIncrement i) n) :=
  summable_bombieriLagariasNormalizedSummand
    signedZetaBombieriLagariasIncrement
    summable_signedZetaBombieriLagariasIncrement_abs_re
    summable_signedZetaBombieriLagariasIncrement_norm_sq n

/-- One positive branch is summable before pairing it with its conjugate. -/
theorem summable_positiveMultiplicityZetaLiRealSummand (n : Nat) :
    Summable (fun i : PositiveOrdinateZetaZeroMultiplicityIndex =>
      (zetaLiComplexSummand (i.1.1 : Complex) n).re) := by
  have hfull := summable_signedZetaBombieriLagariasNormalizedSummand n
  have hleft := hfull.comp_injective Sum.inl_injective
  simpa only [bombieriLagariasNormalizedSummand_signedZeta_eq,
    signedZetaZeroValue, Function.comp_def] using hleft

/- One positive multiplicity-expanded branch sums to the corresponding
multiplicity-weighted half coefficient. -/
set_option maxHeartbeats 800000 in
theorem tsum_positiveMultiplicityIndex_zetaLi_re_eq (n : Nat) :
    (∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
        (zetaLiComplexSummand (i.1.1 : Complex) n).re) =
      ∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaZeroMultiplicityReal rho.1 *
          (zetaLiComplexSummand (rho : Complex) n).re := by
  calc
    (∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
        (zetaLiComplexSummand (i.1.1 : Complex) n).re) =
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          ∑' _k : Fin (zetaZeroMultiplicity rho.1),
            (zetaLiComplexSummand (rho : Complex) n).re :=
      (summable_positiveMultiplicityZetaLiRealSummand n).tsum_sigma
    _ = ∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaZeroMultiplicityReal rho.1 *
          (zetaLiComplexSummand (rho : Complex) n).re := by
      apply tsum_congr
      intro rho
      rw [tsum_fintype]
      simp [zetaZeroMultiplicityReal, nsmul_eq_mul]

/- Splitting the signed multiset into its two ordinate signs gives two equal
positive multiplicity-expanded branch sums. -/
set_option maxHeartbeats 800000 in
theorem tsum_signedZetaBombieriLagariasNormalizedSummand_eq_two_branches
    (n : Nat) :
    (∑' i : SignedZetaZeroMultiplicityIndex,
        bombieriLagariasNormalizedSummand
          (signedZetaBombieriLagariasIncrement i) n) =
      (∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
          (zetaLiComplexSummand (i.1.1 : Complex) n).re) +
        ∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
          (zetaLiComplexSummand (i.1.1 : Complex) n).re := by
  have hbranch : Summable (fun i : PositiveOrdinateZetaZeroMultiplicityIndex =>
      (zetaLiComplexSummand (i.1.1 : Complex) n).re) := by
    exact summable_positiveMultiplicityZetaLiRealSummand n
  have hleft : Summable (fun i : PositiveOrdinateZetaZeroMultiplicityIndex =>
      bombieriLagariasNormalizedSummand
        (signedZetaBombieriLagariasIncrement (Sum.inl i)) n) := by
    simpa only [bombieriLagariasNormalizedSummand_signedZeta_eq,
      signedZetaZeroValue] using hbranch
  have hright : Summable (fun i : PositiveOrdinateZetaZeroMultiplicityIndex =>
      bombieriLagariasNormalizedSummand
        (signedZetaBombieriLagariasIncrement (Sum.inr i)) n) := by
    simpa only [bombieriLagariasNormalizedSummand_signedZeta_eq,
      signedZetaZeroValue, zetaLiComplexSummand_conj,
      Complex.conj_re] using hbranch
  rw [hleft.tsum_sum hright]
  have hleft_eq :
      (∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
          bombieriLagariasNormalizedSummand
            (signedZetaBombieriLagariasIncrement (Sum.inl i)) n) =
        ∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
          (zetaLiComplexSummand (i.1.1 : Complex) n).re := by
    apply tsum_congr
    intro i
    rfl
  have hright_eq :
      (∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
          bombieriLagariasNormalizedSummand
            (signedZetaBombieriLagariasIncrement (Sum.inr i)) n) =
        ∑' i : PositiveOrdinateZetaZeroMultiplicityIndex,
          (zetaLiComplexSummand (i.1.1 : Complex) n).re := by
    apply tsum_congr
    intro i
    simp only [bombieriLagariasNormalizedSummand_signedZeta_eq,
      signedZetaZeroValue, zetaLiComplexSummand_conj, Complex.conj_re]
  rw [hleft_eq, hright_eq]

/-- The M50 coefficient is exactly the normalized power sum over the full
signed, multiplicity-expanded zeta-zero multiset. -/
theorem fullZetaLiCoefficient_eq_signed_normalized_tsum (n : Nat) :
    fullZetaLiCoefficient n =
      ∑' i : SignedZetaZeroMultiplicityIndex,
        bombieriLagariasNormalizedSummand
          (signedZetaBombieriLagariasIncrement i) n := by
  rw [fullZetaLiCoefficient]
  rw [tsum_signedZetaBombieriLagariasNormalizedSummand_eq_two_branches,
    tsum_positiveMultiplicityIndex_zetaLi_re_eq]
  have hhalf : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        (zetaLiComplexSummand (rho : Complex) n).re) := by
    have hscaled :=
      (summable_multiplicityWeightedZetaLiRealSummand n).mul_left
        (1 / 2 : Real)
    exact hscaled.congr (fun rho => by
      simp [multiplicityWeightedZetaLiRealSummand]
      ring)
  rw [← hhalf.tsum_add hhalf]
  apply tsum_congr
  intro rho
  simp [multiplicityWeightedZetaLiRealSummand]
  ring

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
