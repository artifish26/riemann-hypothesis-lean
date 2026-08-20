import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Exact rational matrix certificates for M100-DF6D4

This experimental module supplies the kernel-checked algebra used by the
DF6D4 endpoint-certificate lane.  A concrete certificate consists of a
rational Gram factor and rational entry enclosures for the analytic matrix.
After subtracting the Gram factor, exact rational arithmetic checks symmetric
row diagonal dominance of the residual.  The only theorem-specific input left
to a concrete endpoint module is a proof that every analytic entry lies in its
declared rational enclosure.

No floating-point or Arb computation is trusted by this module.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open scoped BigOperators

/-- A closed interval with rational endpoints. -/
structure RationalInterval where
  lower : Rat
  upper : Rat
deriving Inhabited

namespace RationalInterval

/-- A real number lies in a rational interval. -/
noncomputable def Contains (I : RationalInterval) (x : Real) : Prop :=
  (I.lower : Real) <= x ∧ x <= (I.upper : Real)

/-- The exact rational shift used after subtracting a Gram entry. -/
def shift (I : RationalInterval) (q : Rat) : RationalInterval where
  lower := I.lower - q
  upper := I.upper - q

/-- A rational upper bound for the absolute value of every member. -/
def absUpper (I : RationalInterval) : Rat :=
  max |I.lower| |I.upper|

theorem abs_le_absUpper
    {I : RationalInterval} {x : Real} (hx : I.Contains x) :
    |x| <= (I.absUpper : Real) := by
  unfold Contains absUpper at *
  rw [Rat.cast_max, Rat.cast_abs, Rat.cast_abs]
  exact abs_le_max_abs_abs hx.1 hx.2

theorem contains_shift_iff
    {I : RationalInterval} {q : Rat} {x : Real} :
    (I.shift q).Contains (x - (q : Real)) ↔ I.Contains x := by
  norm_num [Contains, shift]

end RationalInterval

/-- The off-diagonal absolute row sum of a real matrix. -/
noncomputable def matrixOffDiagonalAbsRowSum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) (i : n) : Real :=
  ∑ j ∈ Finset.univ.erase i, |A i j|

/-- Symmetric row diagonal dominance with nonnegative residual diagonal. -/
noncomputable def Matrix.IsSymmetricRowDiagonallyDominant
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) : Prop :=
  A.IsHermitian ∧ ∀ i, matrixOffDiagonalAbsRowSum A i <= A i i

private theorem neg_abs_mul_add_sq_le_two_mul
    (a x y : Real) :
    -(|a| * (x ^ 2 + y ^ 2)) <= 2 * x * a * y := by
  have hxy : 2 * |x| * |y| <= x ^ 2 + y ^ 2 := by
    simpa [sq_abs] using two_mul_le_add_sq |x| |y|
  have ha :
      |a| * (2 * |x| * |y|) <= |a| * (x ^ 2 + y ^ 2) :=
    mul_le_mul_of_nonneg_left hxy (abs_nonneg a)
  have habs : |2 * x * a * y| <= |a| * (x ^ 2 + y ^ 2) := by
    simpa [abs_mul, mul_assoc, mul_comm, mul_left_comm] using ha
  exact (neg_le_of_abs_le habs)

/-- A symmetric row-diagonally-dominant real matrix is positive semidefinite.
This is the exact residual checker used after a rational Gram factor has been
subtracted from an analytic endpoint matrix. -/
theorem Matrix.posSemidef_of_isSymmetricRowDiagonallyDominant
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real}
    (hA : Matrix.IsSymmetricRowDiagonallyDominant A) :
    A.PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA.1 ?_
  intro x
  have hsymm : ∀ i j, A i j = A j i := by
    intro i j
    simpa using (hA.1.apply j i)
  let diagonalPart : Real := ∑ i, A i i * x i ^ 2
  let rowBoundPart : Real :=
    ∑ i, matrixOffDiagonalAbsRowSum A i * x i ^ 2
  let offDiagonalPart : Real :=
    ∑ i, ∑ j ∈ Finset.univ.erase i, x i * A i j * x j
  have hquadratic :
      dotProduct (star x) (Matrix.mulVec A x) =
        diagonalPart + offDiagonalPart := by
    simp only [diagonalPart, offDiagonalPart, dotProduct, Matrix.mulVec,
      star_trivial, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := fun j => x i * (A i j * x j)) (Finset.mem_univ i)]
    ring
  have hrow : rowBoundPart <= diagonalPart := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (hA.2 i) (sq_nonneg (x i))
  have hswap :
      (∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * x j ^ 2) =
        ∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * x i ^ 2 := by
    calc
      (∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * x j ^ 2) =
          ∑ i, ∑ j, if j ≠ i then |A i j| * x j ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter]
      _ = ∑ j, ∑ i, if j ≠ i then |A i j| * x j ^ 2 else 0 :=
        Finset.sum_comm
      _ = ∑ j, ∑ i, if i ≠ j then |A j i| * x j ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        simp only [ne_comm (a := j) (b := i), hsymm i j]
      _ = ∑ j, ∑ i ∈ Finset.univ.erase j, |A j i| * x j ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.filter_ne' Finset.univ j, Finset.sum_filter]
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * x i ^ 2 := by
        rfl
  have hpairs :
      (∑ i, ∑ j ∈ Finset.univ.erase i,
          -(|A i j| * (x i ^ 2 + x j ^ 2))) <=
        ∑ i, ∑ j ∈ Finset.univ.erase i,
          2 * x i * A i j * x j := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact neg_abs_mul_add_sq_le_two_mul (A i j) (x i) (x j)
  have hpairs' : -2 * rowBoundPart <= 2 * offDiagonalPart := by
    have hfirst :
        (∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * x i ^ 2) =
          rowBoundPart := by
      simp only [rowBoundPart, matrixOffDiagonalAbsRowSum, Finset.sum_mul]
    have hsecond :
        (∑ i, ∑ j ∈ Finset.univ.erase i, |A i j| * x j ^ 2) =
          rowBoundPart := hswap.trans hfirst
    have hpairSum :
        (∑ i, ∑ j ∈ Finset.univ.erase i,
            -(|A i j| * (x i ^ 2 + x j ^ 2))) =
          -(rowBoundPart + rowBoundPart) := by
      simp_rw [mul_add, neg_add_rev]
      simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib,
        hfirst, hsecond]
    calc
      -2 * rowBoundPart = -(rowBoundPart + rowBoundPart) := by ring
      _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
          -(|A i j| * (x i ^ 2 + x j ^ 2)) := hpairSum.symm
      _ <= ∑ i, ∑ j ∈ Finset.univ.erase i,
          2 * x i * A i j * x j := hpairs
      _ = 2 * offDiagonalPart := by
        simp only [offDiagonalPart, Finset.mul_sum, mul_assoc]
  rw [hquadratic]
  linarith

/-- Rational data for a Gram-plus-diagonally-dominant certificate. -/
structure RationalMatrixCertificate (n : Nat) where
  entry : Matrix (Fin n) (Fin n) RationalInterval
  gramFactor : Matrix (Fin n) (Fin n) Rat

namespace RationalMatrixCertificate

/-- Row-major array data interpreted as a square matrix.  Concrete generated
certificates separately check the expected array length. -/
def matrixOfArray {α : Type*} [Inhabited α] {n : Nat}
    (data : Array α) : Matrix (Fin n) (Fin n) α :=
  fun i j => data[i.val * n + j.val]!

/-- The shape condition recorded by every generated certificate. -/
def HasExpectedLength {α : Type*} {n : Nat} (data : Array α) : Prop :=
  data.size = n * n

/-- The exact rational Gram entry subtracted from an analytic entry. -/
def gramEntry {n : Nat} (c : RationalMatrixCertificate n)
    (i j : Fin n) : Rat :=
  ∑ k, c.gramFactor k i * c.gramFactor k j

/-- The rational enclosure for the residual after Gram subtraction. -/
def residualEntry {n : Nat} (c : RationalMatrixCertificate n)
    (i j : Fin n) : RationalInterval :=
  (c.entry i j).shift (c.gramEntry i j)

/-- Exact rational validity condition checked for a concrete certificate. -/
def Valid {n : Nat} (c : RationalMatrixCertificate n) : Prop :=
  (∀ i j, (c.entry i j).lower <= (c.entry i j).upper) ∧
    ∀ i,
      ∑ j ∈ Finset.univ.erase i, (c.residualEntry i j).absUpper <=
        (c.residualEntry i i).lower

/-- Cast a rational Gram factor to the real matrix used by the theorem. -/
noncomputable def realGramFactor {n : Nat} (c : RationalMatrixCertificate n) :
    Matrix (Fin n) (Fin n) Real :=
  fun i j => (c.gramFactor i j : Real)

theorem realGramFactor_gram_apply {n : Nat}
    (c : RationalMatrixCertificate n) (i j : Fin n) :
    (Matrix.conjTranspose c.realGramFactor * c.realGramFactor) i j =
      (c.gramEntry i j : Real) := by
  simp [realGramFactor, gramEntry, Matrix.mul_apply]

/-- Soundness of a rational Gram/residual certificate.  The enclosure proof
is the sole bridge from the analytic endpoint matrix to the exact checker. -/
theorem posSemidef_of_valid_of_entry_enclosures
    {n : Nat} (c : RationalMatrixCertificate n)
    (M : Matrix (Fin n) (Fin n) Real)
    (hvalid : c.Valid)
    (hM : M.IsHermitian)
    (henclose : ∀ i j, (c.entry i j).Contains (M i j)) :
    M.PosSemidef := by
  let G : Matrix (Fin n) (Fin n) Real :=
    Matrix.conjTranspose c.realGramFactor * c.realGramFactor
  let R : Matrix (Fin n) (Fin n) Real := M - G
  have hG : G.PosSemidef := by
    dsimp [G]
    exact Matrix.posSemidef_conjTranspose_mul_self c.realGramFactor
  have hRherm : R.IsHermitian := by
    dsimp [R, G]
    exact hM.sub (Matrix.isHermitian_conjTranspose_mul_self _)
  have hRdom : ∀ i, matrixOffDiagonalAbsRowSum R i <= R i i := by
    intro i
    have hdiag :
        (c.residualEntry i i).Contains
          (M i i - (c.gramEntry i i : Real)) :=
      (RationalInterval.contains_shift_iff
        (I := c.entry i i) (q := c.gramEntry i i) (x := M i i)).2
        (henclose i i)
    have hoff : ∀ j ∈ Finset.univ.erase i,
        |R i j| <= ((c.residualEntry i j).absUpper : Real) := by
      intro j hj
      apply RationalInterval.abs_le_absUpper
      change (c.residualEntry i j).Contains (M i j - G i j)
      rw [show G i j = (c.gramEntry i j : Real) by
        dsimp [G]
        exact realGramFactor_gram_apply c i j]
      exact (RationalInterval.contains_shift_iff
        (I := c.entry i j) (q := c.gramEntry i j) (x := M i j)).2
        (henclose i j)
    calc
      matrixOffDiagonalAbsRowSum R i =
          ∑ j ∈ Finset.univ.erase i, |R i j| := rfl
      _ <= ∑ j ∈ Finset.univ.erase i,
          ((c.residualEntry i j).absUpper : Real) :=
        Finset.sum_le_sum fun j hj => hoff j hj
      _ <= ((c.residualEntry i i).lower : Real) := by
        exact_mod_cast hvalid.2 i
      _ <= R i i := by
        change ((c.residualEntry i i).lower : Real) <= M i i - G i i
        rw [show G i i = (c.gramEntry i i : Real) by
          dsimp [G]
          exact realGramFactor_gram_apply c i i]
        exact hdiag.1
  have hR : R.PosSemidef :=
    Matrix.posSemidef_of_isSymmetricRowDiagonallyDominant ⟨hRherm, hRdom⟩
  have hsum := hG.add hR
  simpa [R, G] using hsum

end RationalMatrixCertificate

end M100
end Experiments
end RiemannHypothesisProject
