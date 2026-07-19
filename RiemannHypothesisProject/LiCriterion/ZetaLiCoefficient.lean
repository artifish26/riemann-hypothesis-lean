import RiemannHypothesisProject.LiCriterion.StarConvergence
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiJensen
import RiemannHypothesisProject.RiemannWeilShiftedRadius.TrivialAxisGeometry
import Mathlib.Algebra.Ring.GeomSum

/-!
# Full multiplicity-aware zeta Li coefficients

The coefficient is formed from the full nontrivial zeta-zero multiset by
pairing each positive-ordinate zero with its conjugate and retaining analytic
multiplicity.  Pairing cancels the conditionally convergent reciprocal term;
the remaining summand is bounded by the unconditional multiplicity-weighted
inverse-square height series.  Canonical radial-star convergence then follows
from the exact positive-height windows.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate Filter

open scoped Topology

noncomputable section

/-- The complex Li summand attached to a nonzero complex number. -/
def zetaLiComplexSummand (rho : Complex) (n : Nat) : Complex :=
  1 - (1 - rho⁻¹) ^ n

/-- The conjugate-paired Li summand attached to one positive-ordinate zero. -/
def zetaLiPairedSummand
    (rho : PositiveOrdinateZetaZeroSubtype) (n : Nat) : Complex :=
  zetaLiComplexSummand (rho : Complex) n +
    zetaLiComplexSummand (conj (rho : Complex)) n

/-- A finite constant controlling the geometric-sum remainder at exponent
`n`. -/
def zetaLiGeometricRemainderConstant (n : Nat) : Real :=
  (Finset.range n).sum (fun j => (j : Real) * (2 : Real) ^ j)

/-- A power differs from `1` by at most a linear factor in `z - 1` on the
closed radius-two disk.  The deliberately loose finite constant keeps the
later Li estimate elementary. -/
theorem norm_pow_sub_one_le
    (z : Complex) (hz : ‖z‖ <= 2) (j : Nat) :
    ‖z ^ j - 1‖ <=
      (j : Real) * (2 : Real) ^ j * ‖z - 1‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hdecomp :
          z ^ (j + 1) - 1 = (z ^ j - 1) * z + (z - 1) := by
        rw [pow_succ]
        ring
      have hnorm :
          ‖(z ^ j - 1) * z‖ <=
            ((j : Real) * (2 : Real) ^ j * ‖z - 1‖) * 2 := by
        rw [Complex.norm_mul]
        exact mul_le_mul ih hz (norm_nonneg _) (by positivity)
      calc
        ‖z ^ (j + 1) - 1‖ =
            ‖(z ^ j - 1) * z + (z - 1)‖ := by rw [hdecomp]
        _ <= ‖(z ^ j - 1) * z‖ + ‖z - 1‖ := norm_add_le _ _
        _ <= ((j : Real) * (2 : Real) ^ j * ‖z - 1‖) * 2 +
            ‖z - 1‖ := add_le_add hnorm le_rfl
        _ <= ((j + 1 : Nat) : Real) * (2 : Real) ^ (j + 1) *
            ‖z - 1‖ := by
          have hpow : (0 : Real) <= (2 : Real) ^ j := by positivity
          have hpow_one : (1 : Real) <= (2 : Real) ^ j := by
            exact one_le_pow₀ (by norm_num)
          have hnorm_nonneg : (0 : Real) <= ‖z - 1‖ := norm_nonneg _
          rw [pow_succ]
          push_cast
          nlinarith

/-- The geometric sum at `1 - w` differs from `n` by a controlled multiple
of `‖w‖` whenever `‖w‖ <= 1`. -/
theorem norm_geometric_sum_sub_nat_le
    (w : Complex) (hw : ‖w‖ <= 1) (n : Nat) :
    ‖(Finset.range n).sum (fun j => (1 - w) ^ j) - (n : Complex)‖ <=
      zetaLiGeometricRemainderConstant n * ‖w‖ := by
  have hbase : ‖1 - w‖ <= 2 := by
    calc
      ‖1 - w‖ <= ‖(1 : Complex)‖ + ‖w‖ := norm_sub_le _ _
      _ = 1 + ‖w‖ := by norm_num
      _ <= 1 + 1 := add_le_add le_rfl hw
      _ = 2 := by norm_num
  have hrewrite :
      (Finset.range n).sum (fun j => (1 - w) ^ j) - (n : Complex) =
        (Finset.range n).sum (fun j => ((1 - w) ^ j - 1)) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hrewrite]
  calc
    ‖(Finset.range n).sum (fun j => ((1 - w) ^ j - 1))‖ <=
        (Finset.range n).sum (fun j => ‖(1 - w) ^ j - 1‖) :=
      norm_sum_le _ _
    _ <= (Finset.range n).sum
        (fun j => (j : Real) * (2 : Real) ^ j * ‖w‖) := by
      apply Finset.sum_le_sum
      intro j _hj
      have hj := norm_pow_sub_one_le (1 - w) hbase j
      simpa using hj
    _ = zetaLiGeometricRemainderConstant n * ‖w‖ := by
      rw [zetaLiGeometricRemainderConstant, Finset.sum_mul]

/-- The Li summand is a reciprocal times its finite geometric sum. -/
theorem zetaLiComplexSummand_eq_inv_mul_geometric_sum
    (rho : Complex) (n : Nat) :
    zetaLiComplexSummand rho n =
      rho⁻¹ * (Finset.range n).sum (fun j => (1 - rho⁻¹) ^ j) := by
  simpa [zetaLiComplexSummand] using
    (mul_neg_geom_sum (1 - rho⁻¹) n).symm

/-- Split the Li summand into its linear reciprocal term and a quadratic
remainder. -/
theorem zetaLiComplexSummand_eq_linear_add_remainder
    (rho : Complex) (n : Nat) :
    zetaLiComplexSummand rho n =
      (n : Complex) * rho⁻¹ +
        rho⁻¹ *
          ((Finset.range n).sum (fun j => (1 - rho⁻¹) ^ j) - (n : Complex)) := by
  rw [zetaLiComplexSummand_eq_inv_mul_geometric_sum]
  ring

/-- The nonlinear remainder is quadratic in the reciprocal on the unit disk. -/
theorem norm_zetaLi_remainder_le
    (w : Complex) (hw : ‖w‖ <= 1) (n : Nat) :
    ‖w * ((Finset.range n).sum (fun j => (1 - w) ^ j) - (n : Complex))‖ <=
      zetaLiGeometricRemainderConstant n * ‖w‖ ^ 2 := by
  rw [Complex.norm_mul]
  have hgeom := norm_geometric_sum_sub_nat_le w hw n
  calc
    ‖w‖ * ‖(Finset.range n).sum (fun j => (1 - w) ^ j) - (n : Complex)‖ <=
        ‖w‖ * (zetaLiGeometricRemainderConstant n * ‖w‖) :=
      mul_le_mul_of_nonneg_left hgeom (norm_nonneg w)
    _ = zetaLiGeometricRemainderConstant n * ‖w‖ ^ 2 := by ring

/-- Complex conjugation commutes with the Li summand. -/
theorem zetaLiComplexSummand_conj (rho : Complex) (n : Nat) :
    zetaLiComplexSummand (conj rho) n = conj (zetaLiComplexSummand rho n) := by
  simp [zetaLiComplexSummand]

/-- The paired summand is twice the real part of the positive summand and is
therefore real. -/
theorem zetaLiPairedSummand_eq_two_re
    (rho : PositiveOrdinateZetaZeroSubtype) (n : Nat) :
    zetaLiPairedSummand rho n =
      ((2 * (zetaLiComplexSummand (rho : Complex) n).re : Real) : Complex) := by
  rw [zetaLiPairedSummand, zetaLiComplexSummand_conj]
  apply Complex.ext
  · simp
    ring
  · simp

/-- In the critical strip, the conjugate pair of reciprocal terms has
quadratic size. -/
theorem norm_inv_add_conj_inv_le_two_mul_norm_inv_sq
    (rho : Complex) (hrho : Not (rho = 0))
    (hre_nonneg : 0 <= rho.re) (hre_le_one : rho.re <= 1) :
    ‖rho⁻¹ + conj rho⁻¹‖ <= 2 * ‖rho⁻¹‖ ^ 2 := by
  have hnormSq_pos : 0 < Complex.normSq rho :=
    Complex.normSq_pos.mpr hrho
  have heq :
      rho⁻¹ + conj rho⁻¹ =
        ((2 * (rho.re / Complex.normSq rho) : Real) : Complex) := by
    apply Complex.ext
    · simp [Complex.inv_re]
      ring
    · simp [Complex.inv_im]
      ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (mul_nonneg (by norm_num)
    (div_nonneg hre_nonneg hnormSq_pos.le))]
  rw [Complex.sq_norm, Complex.normSq_inv, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa using
    (mul_le_mul_of_nonneg_right hre_le_one (inv_nonneg.mpr hnormSq_pos.le))

/-- A convenient fixed-exponent constant for the paired Li estimate. -/
def zetaLiPairedBoundConstant (n : Nat) : Real :=
  2 * (n : Real) + 2 * zetaLiGeometricRemainderConstant n

/-- The fixed-exponent paired summand has inverse-square size once the
reciprocal lies in the unit disk. -/
theorem norm_zetaLiPairedSummand_le_inv_sq
    (rho : PositiveOrdinateZetaZeroSubtype) (n : Nat)
    (hw : ‖((rho : Complex)⁻¹)‖ <= 1) :
    ‖zetaLiPairedSummand rho n‖ <=
      zetaLiPairedBoundConstant n * ‖((rho : Complex)⁻¹)‖ ^ 2 := by
  let w : Complex := (rho : Complex)⁻¹
  let r : Complex :=
    w * ((Finset.range n).sum (fun j => (1 - w) ^ j) - (n : Complex))
  let rc : Complex :=
    conj w *
      ((Finset.range n).sum (fun j => (1 - conj w) ^ j) - (n : Complex))
  have hnotTrivial : Not (IsTrivialZetaZero (rho : Complex)) :=
    not_isTrivialZetaZero_of_im_ne_zero (ne_of_gt rho.2)
  have hre_nonneg : 0 <= (rho : Complex).re :=
    zetaZeroSubtype_re_nonneg_of_not_trivial rho.1 hnotTrivial
  have hre_le_one : (rho : Complex).re <= 1 :=
    (show IsZetaZero (rho : Complex) from rho.1.property).re_lt_one.le
  have hrho_ne : Not ((rho : Complex) = 0) := by
    intro h
    have : Complex.im (rho : Complex) = 0 := by rw [h]; simp
    exact (ne_of_gt rho.2) this
  have hlinear : ‖w + conj w‖ <= 2 * ‖w‖ ^ 2 := by
    simpa [w] using
      norm_inv_add_conj_inv_le_two_mul_norm_inv_sq
        (rho : Complex) hrho_ne hre_nonneg hre_le_one
  have hr : ‖r‖ <= zetaLiGeometricRemainderConstant n * ‖w‖ ^ 2 := by
    exact norm_zetaLi_remainder_le w hw n
  have hw_conj : ‖conj w‖ <= 1 := by
    rw [Complex.norm_conj]
    exact hw
  have hrc : ‖rc‖ <= zetaLiGeometricRemainderConstant n * ‖w‖ ^ 2 := by
    have h := norm_zetaLi_remainder_le (conj w) hw_conj n
    simpa [rc, Complex.norm_conj] using h
  have hdecomp :
      zetaLiPairedSummand rho n =
        (n : Complex) * (w + conj w) + (r + rc) := by
    rw [zetaLiPairedSummand]
    rw [zetaLiComplexSummand_eq_linear_add_remainder]
    rw [zetaLiComplexSummand_eq_linear_add_remainder]
    dsimp [w, r, rc]
    simp only [map_inv₀]
    ring
  rw [hdecomp]
  calc
    ‖(n : Complex) * (w + conj w) + (r + rc)‖ <=
        ‖(n : Complex) * (w + conj w)‖ + (‖r‖ + ‖rc‖) := by
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ <= (n : Real) * (2 * ‖w‖ ^ 2) +
        (zetaLiGeometricRemainderConstant n * ‖w‖ ^ 2 +
          zetaLiGeometricRemainderConstant n * ‖w‖ ^ 2) := by
      rw [Complex.norm_mul]
      norm_num
      exact add_le_add
        (mul_le_mul_of_nonneg_left hlinear (Nat.cast_nonneg n))
        (add_le_add hr hrc)
    _ = zetaLiPairedBoundConstant n * ‖w‖ ^ 2 := by
      rw [zetaLiPairedBoundConstant]
      ring

/-- Above height `1`, reciprocal norm square is bounded by the canonical
clamped inverse-square height. -/
theorem norm_inv_sq_le_clampedInverseSquare
    (rho : PositiveOrdinateZetaZeroSubtype)
    (hheight : 1 <= Complex.im (rho : Complex)) :
    ‖((rho : Complex)⁻¹)‖ ^ 2 <=
      (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹ := by
  have him_sq_pos : 0 < Complex.im (rho : Complex) ^ 2 :=
    sq_pos_of_pos rho.2
  have hdenom :
      Complex.im (rho : Complex) ^ 2 <= Complex.normSq (rho : Complex) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (Complex.re (rho : Complex))]
  have hinv := inv_anti₀ him_sq_pos hdenom
  rw [Complex.sq_norm, Complex.normSq_inv]
  simpa [positiveOrdinateZetaZeroClampedHeight, max_eq_right hheight] using hinv

/-- Cofinitely many positive-ordinate zeroes lie above height `1`. -/
theorem eventually_one_le_positiveOrdinateZetaZero_im :
    ∀ᶠ rho : PositiveOrdinateZetaZeroSubtype in cofinite,
      1 <= Complex.im (rho : Complex) := by
  filter_upwards
    [(canonicalPositiveOrdinateWindow 1).eventually_cofinite_notMem]
      with rho hrho
  by_contra hheight
  apply hrho
  rw [mem_canonicalPositiveOrdinateWindow_iff]
  exact le_of_not_ge hheight

/-- The multiplicity-weighted paired Li family. -/
def multiplicityWeightedZetaLiPairedSummand
    (n : Nat) (rho : PositiveOrdinateZetaZeroSubtype) : Complex :=
  (zetaZeroMultiplicity rho.1 : Complex) * zetaLiPairedSummand rho n

/-- The full multiplicity-aware paired Li family is unconditionally summable. -/
theorem summable_multiplicityWeightedZetaLiPairedSummand (n : Nat) :
    Summable (multiplicityWeightedZetaLiPairedSummand n) := by
  have hmajor : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaLiPairedBoundConstant n *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2)) :=
    Summable.mul_left (zetaLiPairedBoundConstant n)
      unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable
  apply Summable.of_norm_bounded_eventually hmajor
  filter_upwards [eventually_one_le_positiveOrdinateZetaZero_im] with rho hheight
  have hnorm_inv_le_one : ‖((rho : Complex)⁻¹)‖ <= 1 := by
    rw [norm_inv]
    apply inv_le_one_of_one_le₀
    exact hheight.trans
      ((le_abs_self (Complex.im (rho : Complex))).trans
        (Complex.abs_im_le_norm (rho : Complex)))
  have hpair := norm_zetaLiPairedSummand_le_inv_sq rho n hnorm_inv_le_one
  have hinv := norm_inv_sq_le_clampedInverseSquare rho hheight
  have hpair_clamped :
      ‖zetaLiPairedSummand rho n‖ <=
        zetaLiPairedBoundConstant n *
          (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹ :=
    hpair.trans
      (mul_le_mul_of_nonneg_left hinv (by
        unfold zetaLiPairedBoundConstant zetaLiGeometricRemainderConstant
        positivity))
  rw [multiplicityWeightedZetaLiPairedSummand, Complex.norm_mul]
  have hmult_nonneg :
      0 <= zetaZeroMultiplicityReal rho.1 :=
    (zetaZeroMultiplicityReal_pos rho.1).le
  rw [show ‖(zetaZeroMultiplicity rho.1 : Complex)‖ =
      zetaZeroMultiplicityReal rho.1 by
        simp [zetaZeroMultiplicityReal]]
  calc
    zetaZeroMultiplicityReal rho.1 * ‖zetaLiPairedSummand rho n‖ <=
        zetaZeroMultiplicityReal rho.1 *
          (zetaLiPairedBoundConstant n *
            (positiveOrdinateZetaZeroClampedHeight rho ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hpair_clamped hmult_nonneg
    _ = zetaLiPairedBoundConstant n *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by
      rw [div_eq_mul_inv]
      ring

/-- Every nontrivial zeta zero has nonzero ordinate.  This is the real-axis
cleanup that makes the positive/conjugate decomposition exhaustive. -/
theorem isNontrivialZetaZero_im_ne_zero
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    Not (Complex.im (rho : Complex) = 0) := by
  intro haxis
  have hz : IsZetaZero (rho : Complex) := rho.property
  have hre_lt_one : (rho : Complex).re < 1 := hz.re_lt_one
  by_cases hre_nonpos : (rho : Complex).re <= 0
  · exact hnotTrivial
      (isTrivialZetaZero_of_isZetaZero_of_im_eq_zero_of_re_nonpos
        hz haxis hre_nonpos)
  · exact
      openUnitIntervalRealAxisZetaZeroFree (rho : Complex) hz haxis
        (lt_of_not_ge hre_nonpos) hre_lt_one

/-- The signed multiplicity index exhausts every nontrivial zeta zero and
every unit of its analytic multiplicity. -/
theorem exists_signedZetaZeroMultiplicityIndex_value_eq
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex)))
    (k : Fin (zetaZeroMultiplicity rho)) :
    exists i : SignedZetaZeroMultiplicityIndex,
      signedZetaZeroValue i = (rho : Complex) := by
  have him_ne := isNontrivialZetaZero_im_ne_zero rho hnotTrivial
  rcases lt_or_gt_of_ne him_ne with him_neg | him_pos
  · let sigma : PositiveOrdinateZetaZeroSubtype :=
      ⟨⟨conj (rho : Complex),
          zetaZeroConjugationSymmetry (rho : Complex) rho.property⟩, by
        simpa using neg_pos.mpr him_neg⟩
    have hmult : zetaZeroMultiplicity sigma.1 = zetaZeroMultiplicity rho := by
      simpa [sigma] using zetaZeroMultiplicity_conj rho
    let j : Fin (zetaZeroMultiplicity sigma.1) := Fin.cast hmult.symm k
    refine ⟨Sum.inr ⟨sigma, j⟩, ?_⟩
    simp [signedZetaZeroValue, sigma]
  · let sigma : PositiveOrdinateZetaZeroSubtype := ⟨rho, him_pos⟩
    refine ⟨Sum.inl ⟨sigma, k⟩, ?_⟩
    rfl

/-- The real multiplicity-weighted contribution of one conjugate pair. -/
def multiplicityWeightedZetaLiRealSummand
    (n : Nat) (rho : PositiveOrdinateZetaZeroSubtype) : Real :=
  zetaZeroMultiplicityReal rho.1 *
    (2 * (zetaLiComplexSummand (rho : Complex) n).re)

/-- The complex paired summand is the real paired summand embedded in
`Complex`. -/
theorem multiplicityWeightedZetaLiPairedSummand_eq_ofReal
    (n : Nat) (rho : PositiveOrdinateZetaZeroSubtype) :
    multiplicityWeightedZetaLiPairedSummand n rho =
      (multiplicityWeightedZetaLiRealSummand n rho : Complex) := by
  rw [multiplicityWeightedZetaLiPairedSummand,
    multiplicityWeightedZetaLiRealSummand,
    zetaLiPairedSummand_eq_two_re]
  simp [zetaZeroMultiplicityReal]

/-- The real full Li family is summable. -/
theorem summable_multiplicityWeightedZetaLiRealSummand (n : Nat) :
    Summable (multiplicityWeightedZetaLiRealSummand n) := by
  rw [← Complex.summable_ofReal]
  simpa only [← multiplicityWeightedZetaLiPairedSummand_eq_ofReal] using
    summable_multiplicityWeightedZetaLiPairedSummand n

/-- The full multiplicity-aware zeta Li coefficient.  The sum runs over the
entire nontrivial zero multiset through canonical positive/conjugate pairing. -/
def fullZetaLiCoefficient (n : Nat) : Real :=
  ∑' rho : PositiveOrdinateZetaZeroSubtype,
    multiplicityWeightedZetaLiRealSummand n rho

/-- The equivalent complex coefficient before taking the checked real form. -/
def fullZetaLiCoefficientComplex (n : Nat) : Complex :=
  ∑' rho : PositiveOrdinateZetaZeroSubtype,
    multiplicityWeightedZetaLiPairedSummand n rho

/-- The complex full coefficient is exactly the real coefficient embedded in
`Complex`. -/
theorem fullZetaLiCoefficientComplex_eq_ofReal (n : Nat) :
    fullZetaLiCoefficientComplex n = (fullZetaLiCoefficient n : Complex) := by
  rw [fullZetaLiCoefficientComplex, fullZetaLiCoefficient]
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro rho
  exact multiplicityWeightedZetaLiPairedSummand_eq_ofReal n rho

/-- The full real Li coefficient is the canonical radial-star limit. -/
theorem fullZetaLiCoefficient_canonicalRadialStarConverges (n : Nat) :
    CanonicalRadialStarConverges
      (multiplicityWeightedZetaLiRealSummand n)
      (fullZetaLiCoefficient n) :=
  HasSum.canonicalRadialStarConverges
    (summable_multiplicityWeightedZetaLiRealSummand n).hasSum

/-- The equivalent complex paired coefficient has the same canonical radial
star convergence. -/
theorem fullZetaLiCoefficientComplex_canonicalRadialStarConverges (n : Nat) :
    CanonicalRadialStarConverges
      (multiplicityWeightedZetaLiPairedSummand n)
      (fullZetaLiCoefficientComplex n) :=
  HasSum.canonicalRadialStarConverges
    (summable_multiplicityWeightedZetaLiPairedSummand n).hasSum

/-- The finite signed multiplicity-expanded Li sum in the canonical radial
window. -/
def signedMultiplicityExpandedZetaLiRadialSum (n N : Nat) : Complex :=
  (canonicalPositiveOrdinateWindow (N : Real)).sum (fun rho =>
    Finset.univ.sum
        (fun _ : Fin (zetaZeroMultiplicity rho.1) =>
          zetaLiComplexSummand (rho : Complex) n) +
      Finset.univ.sum
        (fun _ : Fin (zetaZeroMultiplicity rho.1) =>
          zetaLiComplexSummand (conj (rho : Complex)) n))

/-- The literal signed multiplicity expansion agrees with the weighted paired
radial sum. -/
theorem signedMultiplicityExpandedZetaLiRadialSum_eq_weighted
    (n N : Nat) :
    signedMultiplicityExpandedZetaLiRadialSum n N =
      (canonicalPositiveOrdinateWindow (N : Real)).sum
        (multiplicityWeightedZetaLiPairedSummand n) := by
  unfold signedMultiplicityExpandedZetaLiRadialSum
  apply Finset.sum_congr rfl
  intro rho _hrho
  simp [multiplicityWeightedZetaLiPairedSummand, zetaLiPairedSummand]
  ring

/-- The literal signed multiplicity-expanded radial sums converge to the full
complex Li coefficient. -/
theorem signedMultiplicityExpandedZetaLiRadialSum_tendsto (n : Nat) :
    Tendsto (signedMultiplicityExpandedZetaLiRadialSum n) atTop
      (nhds (fullZetaLiCoefficientComplex n)) := by
  have hfun :
      signedMultiplicityExpandedZetaLiRadialSum n =
        fun N : Nat => (canonicalPositiveOrdinateWindow (N : Real)).sum
          (multiplicityWeightedZetaLiPairedSummand n) := by
    funext N
    exact signedMultiplicityExpandedZetaLiRadialSum_eq_weighted n N
  rw [hfun]
  exact fullZetaLiCoefficientComplex_canonicalRadialStarConverges n

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
