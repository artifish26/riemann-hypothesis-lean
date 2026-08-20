import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFixedAssembly

/-!
# Complex-coordinate transfer for M100-DF6D5B1C

This module complexifies the four real symmetric matrices consumed by the
DF6D5 fixed-endpoint assembly.  It proves exact real/imaginary decompositions
for their Hermitian quadratics and transfers the checked endpoint, coupling,
and conditional block-coercivity bounds to complex coordinate vectors.

The cross term remains genuinely complex: its norm supplies the checked Schur
bound, while the complete block value uses its real part.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators ComplexConjugate

/-- Entrywise complexification of a real finite matrix. -/
def suzukiDF6D5ComplexifyMatrix {n : Nat}
    (M : Matrix (Fin n) (Fin n) Real) :
    Matrix (Fin n) (Fin n) Complex :=
  fun i j => (M i j : Complex)

/-- The squared Euclidean norm of a complex finite coordinate vector. -/
def suzukiDF6D5ComplexCoordinateNormSq {n : Nat}
    (z : Fin n → Complex) : Real :=
  ∑ i, ‖z i‖ ^ 2

/-- The real value of the Hermitian quadratic associated with a real matrix. -/
def suzukiDF6D5ComplexMatrixQuadratic {n : Nat}
    (M : Matrix (Fin n) (Fin n) Real) (z : Fin n → Complex) : Real :=
  (dotProduct (fun i => conj (z i))
    (Matrix.mulVec (suzukiDF6D5ComplexifyMatrix M) z)).re

/-- The complex block value used by the endpoint form identity. -/
def suzukiDF6D5ComplexBlockFormValue
    (low far : Real) (cross : Complex) : Real :=
  blockSchurFormValue low far cross.re

theorem suzukiDF6D5ComplexifyMatrix_isHermitian {n : Nat}
    {M : Matrix (Fin n) (Fin n) Real}
    (hM : ∀ i j, M i j = M j i) :
    (suzukiDF6D5ComplexifyMatrix M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [suzukiDF6D5ComplexifyMatrix, hM j i]

theorem suzukiDF6D5ComplexCoordinateNormSq_re_im {n : Nat}
    (z : Fin n → Complex) :
    suzukiDF6D5ComplexCoordinateNormSq z =
      suzukiDF6D5CoordinateNormSq (fun i => (z i).re) +
        suzukiDF6D5CoordinateNormSq (fun i => (z i).im) := by
  unfold suzukiDF6D5ComplexCoordinateNormSq
    suzukiDF6D5CoordinateNormSq
  calc
    ∑ i, ‖z i‖ ^ 2 = ∑ i, Complex.normSq (z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Complex.sq_norm (z i)
    _ = ∑ i, ((z i).re ^ 2 + (z i).im ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Complex.normSq_apply]
      ring
    _ = (∑ i, (z i).re ^ 2) + ∑ i, (z i).im ^ 2 :=
      Finset.sum_add_distrib

theorem suzukiDF6D5ComplexMatrixQuadratic_re_im {n : Nat}
    (M : Matrix (Fin n) (Fin n) Real) (z : Fin n → Complex) :
    suzukiDF6D5ComplexMatrixQuadratic M z =
      suzukiDF6D5MatrixQuadratic M (fun i => (z i).re) +
        suzukiDF6D5MatrixQuadratic M (fun i => (z i).im) := by
  simp [suzukiDF6D5ComplexMatrixQuadratic,
    suzukiDF6D5ComplexifyMatrix, suzukiDF6D5MatrixQuadratic,
    dotProduct, Matrix.mulVec, Complex.mul_re, Finset.mul_sum,
    Finset.sum_add_distrib]

theorem suzukiDF6D5ComplexCoordinateNormSq_nonneg {n : Nat}
    (z : Fin n → Complex) :
    0 ≤ suzukiDF6D5ComplexCoordinateNormSq z := by
  unfold suzukiDF6D5ComplexCoordinateNormSq
  positivity

/-! ## The four live Hermitian matrix consumers -/

def suzukiDF6D5EvenEndpointHermitianQuadratic
    (z : Fin 45 → Complex) : Real :=
  suzukiDF6D5ComplexMatrixQuadratic suzukiDF6D4EvenEndpointMatrix z

def suzukiDF6D5OddEndpointHermitianQuadratic
    (z : Fin 44 → Complex) : Real :=
  suzukiDF6D5ComplexMatrixQuadratic suzukiDF6D4OddEndpointMatrix z

def suzukiDF6D5EvenCouplingHermitianQuadratic
    (z : Fin 45 → Complex) : Real :=
  suzukiDF6D5ComplexMatrixQuadratic suzukiDF6D4EvenCouplingUpperMatrix z

def suzukiDF6D5OddCouplingHermitianQuadratic
    (z : Fin 44 → Complex) : Real :=
  suzukiDF6D5ComplexMatrixQuadratic suzukiDF6D4OddCouplingUpperMatrix z

theorem suzukiDF6D5EvenEndpointComplexMatrix_isHermitian :
    (suzukiDF6D5ComplexifyMatrix
      suzukiDF6D4EvenEndpointMatrix).IsHermitian :=
  suzukiDF6D5ComplexifyMatrix_isHermitian
    suzukiDF6D4EvenEndpointMatrix_symmetric

theorem suzukiDF6D5OddEndpointComplexMatrix_isHermitian :
    (suzukiDF6D5ComplexifyMatrix
      suzukiDF6D4OddEndpointMatrix).IsHermitian :=
  suzukiDF6D5ComplexifyMatrix_isHermitian
    suzukiDF6D4OddEndpointMatrix_symmetric

theorem suzukiDF6D5EvenCouplingComplexMatrix_isHermitian :
    (suzukiDF6D5ComplexifyMatrix
      suzukiDF6D4EvenCouplingUpperMatrix).IsHermitian :=
  suzukiDF6D5ComplexifyMatrix_isHermitian
    suzukiDF6D4EvenCouplingUpperMatrix_symmetric

theorem suzukiDF6D5OddCouplingComplexMatrix_isHermitian :
    (suzukiDF6D5ComplexifyMatrix
      suzukiDF6D4OddCouplingUpperMatrix).IsHermitian :=
  suzukiDF6D5ComplexifyMatrix_isHermitian
    suzukiDF6D4OddCouplingUpperMatrix_symmetric

/-! ## Checked endpoint and coupling transfers -/

theorem suzukiDF6D5EvenEndpointHermitianQuadratic_lower
    (z : Fin 45 → Complex) :
    (1 / 25000 : Real) * suzukiDF6D5ComplexCoordinateNormSq z ≤
      suzukiDF6D5EvenEndpointHermitianQuadratic z := by
  rw [suzukiDF6D5ComplexCoordinateNormSq_re_im]
  simp only [suzukiDF6D5EvenEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5EvenEndpointQuadratic_lower
    (fun i => (z i).re)
  have him := suzukiDF6D5EvenEndpointQuadratic_lower
    (fun i => (z i).im)
  linarith

theorem suzukiDF6D5OddEndpointHermitianQuadratic_lower
    (z : Fin 44 → Complex) :
    (1 / 200 : Real) * suzukiDF6D5ComplexCoordinateNormSq z ≤
      suzukiDF6D5OddEndpointHermitianQuadratic z := by
  rw [suzukiDF6D5ComplexCoordinateNormSq_re_im]
  simp only [suzukiDF6D5OddEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5OddEndpointQuadratic_lower
    (fun i => (z i).re)
  have him := suzukiDF6D5OddEndpointQuadratic_lower
    (fun i => (z i).im)
  linarith

theorem suzukiDF6D5OddEndpointHermitianQuadratic_upper
    (z : Fin 44 → Complex) :
    suzukiDF6D5OddEndpointHermitianQuadratic z ≤
      5 * suzukiDF6D5ComplexCoordinateNormSq z := by
  rw [suzukiDF6D5ComplexCoordinateNormSq_re_im]
  simp only [suzukiDF6D5OddEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5OddEndpointQuadratic_upper
    (fun i => (z i).re)
  have him := suzukiDF6D5OddEndpointQuadratic_upper
    (fun i => (z i).im)
  linarith

theorem suzukiDF6D5EvenCouplingHermitianQuadratic_le_ratio
    (z : Fin 45 → Complex) :
    (5 / 2 : Real) * suzukiDF6D5EvenCouplingHermitianQuadratic z ≤
      (1 / 20 : Real) * suzukiDF6D5EvenEndpointHermitianQuadratic z := by
  simp only [suzukiDF6D5EvenCouplingHermitianQuadratic,
    suzukiDF6D5EvenEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5EvenCouplingQuadratic_le_ratio
    (fun i => (z i).re)
  have him := suzukiDF6D5EvenCouplingQuadratic_le_ratio
    (fun i => (z i).im)
  linarith

theorem suzukiDF6D5OddCouplingHermitianQuadratic_le_ratio
    (z : Fin 44 → Complex) :
    (5 / 2 : Real) * suzukiDF6D5OddCouplingHermitianQuadratic z ≤
      (999 / 1000 : Real) *
        suzukiDF6D5OddEndpointHermitianQuadratic z := by
  simp only [suzukiDF6D5OddCouplingHermitianQuadratic,
    suzukiDF6D5OddEndpointHermitianQuadratic,
    suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5OddCouplingQuadratic_le_ratio
    (fun i => (z i).re)
  have him := suzukiDF6D5OddCouplingQuadratic_le_ratio
    (fun i => (z i).im)
  linarith

/-! ## Conditional complex coordinate-block coercivity -/

theorem suzukiDF6D5EvenComplexCoordinateBlock_coercive
    (z : Fin 45 → Complex) {farEnergy farNormSq : Real} {cross : Complex}
    (hfarNorm : 0 ≤ farNormSq)
    (hfar : 2 * farNormSq ≤ farEnergy)
    (hcross : ‖cross‖ ^ 2 ≤
      (5 / 2 : Real) *
        suzukiDF6D5EvenCouplingHermitianQuadratic z * farEnergy) :
    (1 / 400000 : Real) *
        (suzukiDF6D5ComplexCoordinateNormSq z + farNormSq) ≤
      suzukiDF6D5ComplexBlockFormValue
        (suzukiDF6D5EvenEndpointHermitianQuadratic z)
        farEnergy cross := by
  have hcoord := suzukiDF6D5ComplexCoordinateNormSq_nonneg z
  have hlowBound := suzukiDF6D5EvenEndpointHermitianQuadratic_lower z
  have hlow : 0 ≤ suzukiDF6D5EvenEndpointHermitianQuadratic z :=
    (mul_nonneg (by norm_num) hcoord).trans hlowBound
  have hfarNonneg : 0 ≤ farEnergy := by linarith
  have hratio := suzukiDF6D5EvenCouplingHermitianQuadratic_le_ratio z
  have hcrossReNorm : cross.re ^ 2 ≤ ‖cross‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg cross.im]
  have hschur : cross.re ^ 2 ≤
      (1 / 20 : Real) *
        suzukiDF6D5EvenEndpointHermitianQuadratic z * farEnergy := by
    exact (hcrossReNorm.trans hcross).trans
      (mul_le_mul_of_nonneg_right hratio hfarNonneg)
  have hblock := blockSchurFormValue_ge_even_reserve
    hlow hfarNonneg hschur
  unfold suzukiDF6D5ComplexBlockFormValue
  calc
    (1 / 400000 : Real) *
        (suzukiDF6D5ComplexCoordinateNormSq z + farNormSq) ≤
        (3 / 4 : Real) *
          (suzukiDF6D5EvenEndpointHermitianQuadratic z + farEnergy) := by
      nlinarith
    _ ≤ blockSchurFormValue
        (suzukiDF6D5EvenEndpointHermitianQuadratic z)
        farEnergy cross.re := hblock

theorem suzukiDF6D5OddComplexCoordinateBlock_coercive
    (z : Fin 44 → Complex) {farEnergy farNormSq : Real} {cross : Complex}
    (hfarNorm : 0 ≤ farNormSq)
    (hfar : 2 * farNormSq ≤ farEnergy)
    (hcross : ‖cross‖ ^ 2 ≤
      (5 / 2 : Real) *
        suzukiDF6D5OddCouplingHermitianQuadratic z * farEnergy) :
    (1 / 400000 : Real) *
        (suzukiDF6D5ComplexCoordinateNormSq z + farNormSq) ≤
      suzukiDF6D5ComplexBlockFormValue
        (suzukiDF6D5OddEndpointHermitianQuadratic z)
        farEnergy cross := by
  have hcoord := suzukiDF6D5ComplexCoordinateNormSq_nonneg z
  have hlowBound := suzukiDF6D5OddEndpointHermitianQuadratic_lower z
  have hlow : 0 ≤ suzukiDF6D5OddEndpointHermitianQuadratic z :=
    (mul_nonneg (by norm_num) hcoord).trans hlowBound
  have hfarNonneg : 0 ≤ farEnergy := by linarith
  have hratio := suzukiDF6D5OddCouplingHermitianQuadratic_le_ratio z
  have hcrossReNorm : cross.re ^ 2 ≤ ‖cross‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg cross.im]
  have hschur : cross.re ^ 2 ≤
      (999 / 1000 : Real) *
        suzukiDF6D5OddEndpointHermitianQuadratic z * farEnergy := by
    exact (hcrossReNorm.trans hcross).trans
      (mul_le_mul_of_nonneg_right hratio hfarNonneg)
  have hblock := blockSchurFormValue_ge_odd_reserve
    hlow hfarNonneg hschur
  unfold suzukiDF6D5ComplexBlockFormValue
  calc
    (1 / 400000 : Real) *
        (suzukiDF6D5ComplexCoordinateNormSq z + farNormSq) ≤
        (1 / 2000 : Real) *
          (suzukiDF6D5OddEndpointHermitianQuadratic z + farEnergy) := by
      nlinarith
    _ ≤ blockSchurFormValue
        (suzukiDF6D5OddEndpointHermitianQuadratic z)
        farEnergy cross.re := hblock

end

end RiemannHypothesisProject.Experiments.M100
