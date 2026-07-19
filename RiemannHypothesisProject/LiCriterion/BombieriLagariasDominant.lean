import RiemannHypothesisProject.LiCriterion.BombieriLagariasCore
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Dominant-modulus exclusion for Li power sums

The normalized input is a family `u` for which the Mobius ratios are `1 + u`.
Summability of the real linear terms and of `norm u ^ 2` is exactly what is
needed to control the conditionally convergent first-order contribution and
the absolutely convergent quadratic remainder.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Filter
open scoped Topology

noncomputable section

/-- The real power-sum term in normalized Bombieri-Lagarias coordinates. -/
def bombieriLagariasNormalizedSummand (u : Complex) (n : Nat) : Real :=
  (1 - (1 + u) ^ n).re

/-- The normalized Li power sum is summable from its linear-real and
quadratic inputs. -/
theorem summable_bombieriLagariasNormalizedSummand
    {iota : Type*} (u : iota -> Complex)
    (hlinear : Summable (fun i => abs (u i).re))
    (hquadratic : Summable (fun i => norm (u i) ^ 2))
    (n : Nat) :
    Summable (fun i => bombieriLagariasNormalizedSummand (u i) n) := by
  have hmajor : Summable (fun i =>
      (n : Real) * abs (u i).re +
        (n : Real) ^ 2 * (2 : Real) ^ n * norm (u i) ^ 2) :=
    (hlinear.mul_left (n : Real)).add
      (hquadratic.mul_left ((n : Real) ^ 2 * (2 : Real) ^ n))
  apply Summable.of_norm_bounded_eventually hmajor
  filter_upwards
    [hquadratic.tendsto_cofinite_zero.eventually_lt_const zero_lt_one]
      with i hi
  have hnorm_u : norm (u i) <= 1 := by
    have hnorm_nonneg : 0 <= norm (u i) := norm_nonneg _
    nlinarith [sq_nonneg (norm (u i) - 1)]
  have hnorm_ratio : norm (1 + u i) <= 2 := by
    calc
      norm (1 + u i) <= norm (1 : Complex) + norm (u i) := norm_add_le _ _
      _ <= 1 + 1 := add_le_add (by norm_num) hnorm_u
      _ = 2 := by norm_num
  rw [Real.norm_eq_abs]
  exact abs_one_sub_pow_re_le (u i) 2 (by norm_num) hnorm_ratio n

/-- Quantitative bound for the complement of a finite dominant shell. -/
theorem abs_tsum_bombieriLagariasNormalizedSummand_compl_le
    {iota : Type*} (u : iota -> Complex)
    (hlinear : Summable (fun i => abs (u i).re))
    (hquadratic : Summable (fun i => norm (u i) ^ 2))
    (s : Finset iota) (q : Real) (hq_one : 1 <= q)
    (hratio : forall i, i ∉ s -> norm (1 + u i) <= q)
    (n : Nat) :
    abs (∑' i : ↑(↑s : Set iota)ᶜ,
        bombieriLagariasNormalizedSummand (u i) n) <=
      (n : Real) * (∑' i : ↑(↑s : Set iota)ᶜ, abs (u i).re) +
        (n : Real) ^ 2 * q ^ n *
          (∑' i : ↑(↑s : Set iota)ᶜ, norm (u i) ^ 2) := by
  let term : ↑(↑s : Set iota)ᶜ -> Real := fun i =>
    bombieriLagariasNormalizedSummand (u i) n
  let linear : ↑(↑s : Set iota)ᶜ -> Real :=
    (fun i => abs (u i).re) ∘ Subtype.val
  let quadratic : ↑(↑s : Set iota)ᶜ -> Real :=
    (fun i => norm (u i) ^ 2) ∘ Subtype.val
  let majorant : ↑(↑s : Set iota)ᶜ -> Real := fun i =>
    (n : Real) * linear i + (n : Real) ^ 2 * q ^ n * quadratic i
  let hlinear_sub := hlinear.subtype (fun i => i ∈ (↑s : Set iota)ᶜ)
  let hquadratic_sub := hquadratic.subtype (fun i => i ∈ (↑s : Set iota)ᶜ)
  have hterm : Summable term :=
    (summable_bombieriLagariasNormalizedSummand u hlinear hquadratic n).subtype _
  have hmajorant : Summable majorant :=
    (hlinear_sub.mul_left (n : Real)).add
      (hquadratic_sub.mul_left ((n : Real) ^ 2 * q ^ n))
  have hterm_norm : Summable (fun i => norm (term i)) :=
    summable_norm_iff.mpr hterm
  have hpointwise : forall i, norm (term i) <= majorant i := by
    intro i
    change abs (bombieriLagariasNormalizedSummand (u i) n) <=
      (n : Real) * abs (u i).re +
        (n : Real) ^ 2 * q ^ n * norm (u i) ^ 2
    have hi_not : (i : iota) ∉ s := i.2
    exact abs_one_sub_pow_re_le (u i) q hq_one (hratio i hi_not) n
  calc
    abs (∑' i : ↑(↑s : Set iota)ᶜ,
        bombieriLagariasNormalizedSummand (u i) n) =
        norm (∑' i, term i) := by simp [term, Real.norm_eq_abs]
    _ <= ∑' i, norm (term i) := norm_tsum_le_tsum_norm hterm_norm
    _ <= ∑' i, majorant i :=
      hterm_norm.tsum_le_tsum hpointwise hmajorant
    _ = (n : Real) * (∑' i, linear i) +
        (n : Real) ^ 2 * q ^ n * (∑' i, quadratic i) := by
      change (∑' i, ((n : Real) * linear i +
          (n : Real) ^ 2 * q ^ n * quadratic i)) = _
      rw [Summable.tsum_add
          (hlinear_sub.mul_left (n : Real))
          (hquadratic_sub.mul_left ((n : Real) ^ 2 * q ^ n)),
        tsum_mul_left, tsum_mul_left]
    _ = (n : Real) * (∑' i : ↑(↑s : Set iota)ᶜ, abs (u i).re) +
        (n : Real) ^ 2 * q ^ n *
          (∑' i : ↑(↑s : Set iota)ᶜ, norm (u i) ^ 2) := by
      rfl

/-- A finite nonempty shell of ratios of common modulus `r > 1`, separated
from the remaining ratios by `q < r`, is incompatible with nonnegativity of
all normalized Li power sums. -/
theorem not_nonneg_bombieriLagariasNormalizedSummand_of_dominant_shell
    {iota : Type*} (u : iota -> Complex)
    (hlinear : Summable (fun i => abs (u i).re))
    (hquadratic : Summable (fun i => norm (u i) ^ 2))
    (s : Finset iota) (hs_nonempty : s.Nonempty)
    (r q : Real) (hr : 1 < r) (hq_one : 1 <= q) (hq_lt : q < r)
    (hshell : forall i, i ∈ s -> norm (1 + u i) = r)
    (hrest : forall i, i ∉ s -> norm (1 + u i) <= q) :
    Not (forall n : Nat, 0 < n ->
      0 <= ∑' i, bombieriLagariasNormalizedSummand (u i) n) := by
  intro hnonneg
  have hr_pos : 0 < r := zero_lt_one.trans hr
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  let z : s -> Circle := fun i =>
    ⟨((1 + u i) / (r : Real) : Complex), by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_div, hshell i i.2]
      norm_num [abs_of_pos hr_pos, hr_ne]⟩
  obtain ⟨exponent, hexponent, hpowers⟩ :=
    exists_tendsto_unitCircle_powers_one z
  have hr_inv_abs : abs r⁻¹ < 1 := by
    rw [abs_of_pos (inv_pos.mpr hr_pos)]
    exact inv_lt_one_of_one_lt₀ hr
  have hinv_pow : Tendsto (fun n : Nat => r⁻¹ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr_inv_abs
  have hinv_exponent :
      Tendsto (fun k => r⁻¹ ^ exponent k) atTop (nhds 0) :=
    hinv_pow.comp hexponent
  have hcircle_re (i : s) :
      Tendsto (fun k => ((z i ^ exponent k : Circle) : Complex).re)
        atTop (nhds 1) := by
    have hi_circle :
        Tendsto (fun k => z i ^ exponent k) atTop (nhds 1) :=
      hpowers.apply_nhds i
    have hi_complex :
        Tendsto (fun k => ((z i ^ exponent k : Circle) : Complex))
          atTop (nhds (1 : Complex)) :=
      by
        have hcoe : Continuous (fun x : Circle => (x : Complex)) :=
          continuous_subtype_val
        exact (hcoe.tendsto 1).comp hi_circle
    change Tendsto
      (Complex.re ∘ fun k => ((z i ^ exponent k : Circle) : Complex))
        atTop (nhds 1)
    exact (Complex.continuous_re.tendsto (1 : Complex)).comp hi_complex
  have hshell_limit :
      Tendsto (fun k => ∑ i : s,
          (r⁻¹ ^ exponent k -
            ((z i ^ exponent k : Circle) : Complex).re))
        atTop (nhds (-(s.card : Real))) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset s) (fun i _ =>
      hinv_exponent.sub (hcircle_re i))
    simpa using hsum
  have hshell_identity (k : Nat) :
      (∑ i : s,
          bombieriLagariasNormalizedSummand (u i) (exponent k)) /
          r ^ exponent k =
        ∑ i : s,
          (r⁻¹ ^ exponent k -
            ((z i ^ exponent k : Circle) : Complex).re) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [bombieriLagariasNormalizedSummand]
    change (1 - (1 + u i) ^ exponent k).re / r ^ exponent k =
      r⁻¹ ^ exponent k -
        ((((1 + u i) / (r : Real) : Complex) ^ exponent k).re)
    rw [div_pow]
    have hrealpow : ((r : Complex) ^ exponent k).re = r ^ exponent k := by
      rw [← Complex.ofReal_pow]
      rfl
    have himpow : ((r : Complex) ^ exponent k).im = 0 := by
      rw [← Complex.ofReal_pow]
      rfl
    have hnormsqpow :
        Complex.normSq ((r : Complex) ^ exponent k) =
          (r ^ exponent k) ^ 2 := by
      rw [Complex.normSq_apply, hrealpow, himpow]
      ring
    rw [Complex.div_re, hrealpow, himpow, hnormsqpow]
    simp only [mul_zero]
    rw [inv_pow]
    field_simp [pow_ne_zero _ hr_ne]
    change (1 - ((1 + u i) ^ exponent k).re) * r ^ exponent k = _
    ring
  have hshell_normalized_limit :
      Tendsto (fun k =>
          (∑ i : s,
            bombieriLagariasNormalizedSummand (u i) (exponent k)) /
            r ^ exponent k)
        atTop (nhds (-(s.card : Real))) := by
    exact hshell_limit.congr'
      (Eventually.of_forall fun k => (hshell_identity k).symm)
  let A : Real := ∑' i : ↑(↑s : Set iota)ᶜ, abs (u i).re
  let B : Real := ∑' i : ↑(↑s : Set iota)ᶜ, norm (u i) ^ 2
  have hA_nonneg : 0 <= A := tsum_nonneg fun _ => abs_nonneg _
  have hB_nonneg : 0 <= B := tsum_nonneg fun _ => sq_nonneg _
  have hq_div_abs : abs (q / r) < 1 := by
    rw [abs_of_nonneg (div_nonneg (zero_le_one.trans hq_one) hr_pos.le)]
    exact (div_lt_one hr_pos).mpr hq_lt
  have hfirst_base : Tendsto
      (fun n : Nat => A * ((n : Real) ^ 1 * r⁻¹ ^ n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 1 (r := r⁻¹) hr_inv_abs).tendsto_atTop_zero.const_mul A
  have hsecond_base : Tendsto
      (fun n : Nat => B * ((n : Real) ^ 2 * (q / r) ^ n)) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (summable_pow_mul_geometric_of_norm_lt_one
        (R := Real) 2 (r := q / r) hq_div_abs).tendsto_atTop_zero.const_mul B
  have hbound_base : Tendsto
      (fun n : Nat =>
        A * ((n : Real) ^ 1 * r⁻¹ ^ n) +
          B * ((n : Real) ^ 2 * (q / r) ^ n)) atTop (nhds 0) := by
    simpa using hfirst_base.add hsecond_base
  have htail_bound (n : Nat) :
      abs ((∑' i : ↑(↑s : Set iota)ᶜ,
          bombieriLagariasNormalizedSummand (u i) n) / r ^ n) <=
        A * ((n : Real) ^ 1 * r⁻¹ ^ n) +
          B * ((n : Real) ^ 2 * (q / r) ^ n) := by
    have hraw := abs_tsum_bombieriLagariasNormalizedSummand_compl_le
      u hlinear hquadratic s q hq_one hrest n
    rw [abs_div, abs_of_pos (pow_pos hr_pos n)]
    calc
      abs (∑' i : ↑(↑s : Set iota)ᶜ,
          bombieriLagariasNormalizedSummand (u i) n) / r ^ n <=
          ((n : Real) * A + (n : Real) ^ 2 * q ^ n * B) /
            r ^ n := div_le_div_of_nonneg_right hraw (pow_nonneg hr_pos.le n)
      _ = A * ((n : Real) ^ 1 * r⁻¹ ^ n) +
          B * ((n : Real) ^ 2 * (q / r) ^ n) := by
        rw [div_pow]
        rw [inv_pow]
        field_simp [hr_ne]
  have htail_abs_limit : Tendsto (fun k =>
      abs ((∑' i : ↑(↑s : Set iota)ᶜ,
          bombieriLagariasNormalizedSummand (u i) (exponent k)) /
        r ^ exponent k)) atTop (nhds 0) :=
    squeeze_zero (fun _ => abs_nonneg _)
      (fun k => htail_bound (exponent k)) (hbound_base.comp hexponent)
  have htail_limit : Tendsto (fun k =>
      (∑' i : ↑(↑s : Set iota)ᶜ,
          bombieriLagariasNormalizedSummand (u i) (exponent k)) /
        r ^ exponent k) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr htail_abs_limit
  have hfull_split (n : Nat) :
      (∑ i : s, bombieriLagariasNormalizedSummand (u i) n) +
          (∑' i : ↑(↑s : Set iota)ᶜ,
            bombieriLagariasNormalizedSummand (u i) n) =
        ∑' i, bombieriLagariasNormalizedSummand (u i) n := by
    have hsplit := (summable_bombieriLagariasNormalizedSummand
      u hlinear hquadratic n).sum_add_tsum_compl (s := s)
    rw [← Finset.sum_attach] at hsplit
    simpa using hsplit
  have hfull_normalized_limit : Tendsto (fun k =>
      (∑' i, bombieriLagariasNormalizedSummand (u i) (exponent k)) /
        r ^ exponent k) atTop (nhds (-(s.card : Real))) := by
    have hadd : Tendsto (fun k =>
        (∑ i : s,
          bombieriLagariasNormalizedSummand (u i) (exponent k)) /
            r ^ exponent k +
          (∑' i : ↑(↑s : Set iota)ᶜ,
            bombieriLagariasNormalizedSummand (u i) (exponent k)) /
              r ^ exponent k) atTop (nhds (-(s.card : Real))) := by
      simpa using hshell_normalized_limit.add htail_limit
    apply hadd.congr'
    filter_upwards with k
    rw [← add_div, hfull_split (exponent k)]
  have hlimit_nonneg : 0 <= -(s.card : Real) := by
    apply ge_of_tendsto hfull_normalized_limit
    filter_upwards [hexponent.eventually (eventually_gt_atTop 0)] with k hk
    exact div_nonneg (hnonneg (exponent k) hk) (pow_nonneg hr_pos.le _)
  have hcard_pos : 0 < (s.card : Real) := by
    exact_mod_cast s.card_pos.mpr hs_nonempty
  linarith

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
