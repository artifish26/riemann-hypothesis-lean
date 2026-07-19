import RiemannHypothesisProject.LiCriterion.BombieriLagariasSelection

/-!
# The source-shaped Bombieri-Lagarias implication

The index type in this module is the multiset: repeated indices encode
multiplicity.  The hypotheses expose the source convergence weight and the
omission of both `0` and `1`.  The proof converts that weight to the normalized
linear and quadratic summability inputs, applies the dominant-modulus theorem,
and then converts the closed-unit-disk condition for `1 - rho⁻¹` to a
half-plane statement.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Filter

noncomputable section

/-- The convergence weight in the Bombieri-Lagarias multiset hypothesis. -/
def bombieriLagariasSourceWeight (rho : Complex) : Real :=
  (1 + abs rho.re) / (1 + norm rho) ^ 2

/-- The Li power-sum term in the project normalization. -/
def bombieriLagariasLiSummand (rho : Complex) (n : Nat) : Real :=
  (1 - (1 - rho⁻¹) ^ n).re

theorem bombieriLagariasSourceWeight_nonneg (rho : Complex) :
    0 <= bombieriLagariasSourceWeight rho := by
  unfold bombieriLagariasSourceWeight
  positivity

/-- A point in the open unit disk has source weight at least `1 / 4`. -/
theorem one_fourth_le_bombieriLagariasSourceWeight_of_norm_lt_one
    {rho : Complex} (hrho : norm rho < 1) :
    (1 / 4 : Real) <= bombieriLagariasSourceWeight rho := by
  have hden_pos : 0 < (1 + norm rho) ^ 2 := by positivity
  have hden_le : (1 + norm rho) ^ 2 <= 4 := by
    nlinarith [norm_nonneg rho]
  unfold bombieriLagariasSourceWeight
  rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 4) hden_pos]
  nlinarith [abs_nonneg rho.re]

/-- Source-weight summability forces all but finitely many multiset members
outside the open unit disk. -/
theorem eventually_one_le_norm_of_bombieriLagariasSourceWeight_summable
    {iota : Type*} (rho : iota -> Complex)
    (hsource : Summable (fun i => bombieriLagariasSourceWeight (rho i))) :
    ∀ᶠ i in cofinite, 1 <= norm (rho i) := by
  have hsmall : ∀ᶠ i in cofinite,
      bombieriLagariasSourceWeight (rho i) < (1 / 4 : Real) :=
    hsource.tendsto_cofinite_zero.eventually_lt_const (by norm_num)
  filter_upwards [hsmall] with i hi
  by_contra hnorm
  have hlower :=
    one_fourth_le_bombieriLagariasSourceWeight_of_norm_lt_one
      (lt_of_not_ge hnorm)
  linarith

/-- Away from the origin, reciprocal norm square is controlled by four times
the denominator part of the source weight. -/
theorem norm_inv_sq_le_four_div_sourceDenominator
    {rho : Complex} (hrho_ne : rho ≠ 0) (hrho_norm : 1 <= norm rho) :
    norm rho⁻¹ ^ 2 <= 4 / (1 + norm rho) ^ 2 := by
  have hnorm_pos : 0 < norm rho := norm_pos_iff.mpr hrho_ne
  have hden_pos : 0 < (1 + norm rho) ^ 2 := by positivity
  rw [norm_inv, inv_pow]
  have hbound : 1 / norm rho ^ 2 <= 4 / (1 + norm rho) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hnorm_pos) hden_pos]
    nlinarith [sq_nonneg (norm rho - 1)]
  simpa only [one_div] using hbound

/-- The normalized quadratic input follows pointwise from the source weight
outside the unit disk. -/
theorem norm_neg_inv_sq_le_four_mul_bombieriLagariasSourceWeight
    {rho : Complex} (hrho_ne : rho ≠ 0) (hrho_norm : 1 <= norm rho) :
    norm (-rho⁻¹) ^ 2 <= 4 * bombieriLagariasSourceWeight rho := by
  have hinv := norm_inv_sq_le_four_div_sourceDenominator hrho_ne hrho_norm
  rw [norm_neg]
  exact hinv.trans (by
    unfold bombieriLagariasSourceWeight
    have hden_nonneg : 0 <= (1 + norm rho) ^ 2 := sq_nonneg _
    have hnum : 1 <= 1 + abs rho.re := by linarith [abs_nonneg rho.re]
    calc
      4 / (1 + norm rho) ^ 2 <=
          4 * ((1 + abs rho.re) / (1 + norm rho) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [div_eq_mul_inv]
        calc
          ((1 + norm rho) ^ 2)⁻¹ =
              1 * ((1 + norm rho) ^ 2)⁻¹ := by ring
          _ <= (1 + abs rho.re) * ((1 + norm rho) ^ 2)⁻¹ :=
            mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden_nonneg)
      _ = 4 * ((1 + abs rho.re) / (1 + norm rho) ^ 2) := rfl)

/-- The real linear input is controlled by the same source weight. -/
theorem abs_neg_inv_re_le_four_mul_bombieriLagariasSourceWeight
    {rho : Complex} (hrho_ne : rho ≠ 0) (hrho_norm : 1 <= norm rho) :
    abs (-rho⁻¹).re <= 4 * bombieriLagariasSourceWeight rho := by
  have hnormSq_pos : 0 < Complex.normSq rho :=
    Complex.normSq_pos.mpr hrho_ne
  have hidentity :
      abs (-rho⁻¹).re = abs rho.re * norm rho⁻¹ ^ 2 := by
    change abs (-(rho⁻¹).re) = _
    rw [abs_neg, Complex.inv_re, abs_div,
      abs_of_pos hnormSq_pos, Complex.sq_norm, Complex.normSq_inv]
    rw [div_eq_mul_inv]
  rw [hidentity]
  have hinv := norm_inv_sq_le_four_div_sourceDenominator hrho_ne hrho_norm
  calc
    abs rho.re * norm rho⁻¹ ^ 2 <=
        abs rho.re * (4 / (1 + norm rho) ^ 2) :=
      mul_le_mul_of_nonneg_left hinv (abs_nonneg _)
    _ <= (1 + abs rho.re) * (4 / (1 + norm rho) ^ 2) := by
      exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg rho.re])
        (by positivity)
    _ = 4 * bombieriLagariasSourceWeight rho := by
      unfold bombieriLagariasSourceWeight
      rw [div_eq_mul_inv]
      ring

/-- The source convergence hypothesis supplies normalized quadratic
summability. -/
theorem summable_norm_neg_inv_sq_of_bombieriLagariasSourceWeight
    {iota : Type*} (rho : iota -> Complex)
    (hzero : forall i, rho i ≠ 0)
    (hsource : Summable (fun i => bombieriLagariasSourceWeight (rho i))) :
    Summable (fun i => norm (-(rho i)⁻¹) ^ 2) := by
  have hmajor := hsource.mul_left 4
  apply Summable.of_norm_bounded_eventually hmajor
  filter_upwards
    [eventually_one_le_norm_of_bombieriLagariasSourceWeight_summable
      rho hsource] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_neg_inv_sq_le_four_mul_bombieriLagariasSourceWeight
    (hzero i) hi

/-- The source convergence hypothesis supplies absolute summability of the
normalized real linear terms. -/
theorem summable_abs_neg_inv_re_of_bombieriLagariasSourceWeight
    {iota : Type*} (rho : iota -> Complex)
    (hzero : forall i, rho i ≠ 0)
    (hsource : Summable (fun i => bombieriLagariasSourceWeight (rho i))) :
    Summable (fun i => abs (-(rho i)⁻¹).re) := by
  have hmajor := hsource.mul_left 4
  apply Summable.of_norm_bounded_eventually hmajor
  filter_upwards
    [eventually_one_le_norm_of_bombieriLagariasSourceWeight_summable
      rho hsource] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
  exact abs_neg_inv_re_le_four_mul_bombieriLagariasSourceWeight
    (hzero i) hi

/-- The unit-disk condition for `1 - rho⁻¹` is exactly the lower
half-plane condition needed by the project normalization. -/
theorem bombieriLagarias_one_half_le_re_of_ratio_norm_le_one
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

/-- The source-shaped Bombieri-Lagarias implication in the `1 - rho⁻¹`
normalization.  Repeated indices encode multiplicity. -/
theorem bombieriLagarias_lower_half_plane
    {iota : Type*} (rho : iota -> Complex)
    (hzero : forall i, rho i ≠ 0)
    (_hone : forall i, rho i ≠ 1)
    (hsource : Summable (fun i => bombieriLagariasSourceWeight (rho i)))
    (hnonneg : forall n : Nat, 0 < n ->
      0 <= ∑' i, bombieriLagariasLiSummand (rho i) n) :
    forall i, (1 / 2 : Real) <= (rho i).re := by
  have hratio := norm_one_add_le_one_of_bombieriLagarias_nonneg
    (fun i => -(rho i)⁻¹)
    (summable_abs_neg_inv_re_of_bombieriLagariasSourceWeight
      rho hzero hsource)
    (summable_norm_neg_inv_sq_of_bombieriLagariasSourceWeight
      rho hzero hsource)
    (fun n hn => by
      simpa [bombieriLagariasLiSummand,
        bombieriLagariasNormalizedSummand, sub_eq_add_neg] using
        hnonneg n hn)
  intro i
  apply bombieriLagarias_one_half_le_re_of_ratio_norm_le_one (hzero i)
  simpa [sub_eq_add_neg] using hratio i

/-- Functional reflection upgrades the one-half-plane implication to the
critical line. -/
theorem bombieriLagarias_critical_line_of_reflection
    {iota : Type*} (rho : iota -> Complex) (reflect : iota -> iota)
    (hreflect : forall i, rho (reflect i) = 1 - rho i)
    (hzero : forall i, rho i ≠ 0)
    (hone : forall i, rho i ≠ 1)
    (hsource : Summable (fun i => bombieriLagariasSourceWeight (rho i)))
    (hnonneg : forall n : Nat, 0 < n ->
      0 <= ∑' i, bombieriLagariasLiSummand (rho i) n) :
    forall i, (rho i).re = (1 / 2 : Real) := by
  have hlower := bombieriLagarias_lower_half_plane
    rho hzero hone hsource hnonneg
  intro i
  have hmirror := hlower (reflect i)
  rw [hreflect] at hmirror
  change (1 / 2 : Real) <= 1 - (rho i).re at hmirror
  exact le_antisymm (by nlinarith) (hlower i)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
