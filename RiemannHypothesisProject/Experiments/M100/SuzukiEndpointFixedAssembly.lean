import RiemannHypothesisProject.Experiments.M100.BlockSchurCoercivity
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCertificateEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage2Certificate
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointOddAdditiveCertificate

/-!
# Fixed-endpoint certificate-to-Schur assembly for M100-DF6D5

This module applies DF6A to the concrete endpoint matrices checked in DF6D4.
It derives the even `1 / 20` and odd `999 / 1000` Schur ratios, then obtains
the common `1 / 400000` bound on the explicit coordinate-block model.

The separate identification of these coordinates and far blocks with the
exact full closed Suzuki domain is intentionally not assumed here.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

def suzukiDF6D5CoordinateNormSq {n : Nat} (x : Fin n → Real) : Real :=
  ∑ i, x i ^ 2

def suzukiDF6D5MatrixQuadratic {n : Nat}
    (M : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) : Real :=
  dotProduct x (Matrix.mulVec M x)

theorem suzukiDF6D5MatrixQuadratic_sub {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) :
    suzukiDF6D5MatrixQuadratic (A - B) x =
      suzukiDF6D5MatrixQuadratic A x -
        suzukiDF6D5MatrixQuadratic B x := by
  simp [suzukiDF6D5MatrixQuadratic, Matrix.sub_mulVec, dotProduct_sub]

theorem suzukiDF6D5MatrixQuadratic_smul {n : Nat}
    (c : Real) (A : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) :
    suzukiDF6D5MatrixQuadratic (c • A) x =
      c * suzukiDF6D5MatrixQuadratic A x := by
  simp [suzukiDF6D5MatrixQuadratic, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul]

theorem suzukiDF6D5MatrixQuadratic_one {n : Nat}
    (x : Fin n → Real) :
    suzukiDF6D5MatrixQuadratic
        (1 : Matrix (Fin n) (Fin n) Real) x =
      suzukiDF6D5CoordinateNormSq x := by
  simp [suzukiDF6D5MatrixQuadratic, suzukiDF6D5CoordinateNormSq,
    Matrix.one_mulVec, dotProduct, pow_two]

theorem suzukiDF6D5CoordinateNormSq_nonneg {n : Nat}
    (x : Fin n → Real) :
    0 ≤ suzukiDF6D5CoordinateNormSq x := by
  unfold suzukiDF6D5CoordinateNormSq
  positivity

private theorem matrixQuadratic_nonneg_of_posSemidef {n : Nat}
    {M : Matrix (Fin n) (Fin n) Real} (hM : M.PosSemidef)
    (x : Fin n → Real) :
    0 ≤ suzukiDF6D5MatrixQuadratic M x := by
  have h := hM.dotProduct_mulVec_nonneg x
  simpa [suzukiDF6D5MatrixQuadratic, Pi.star_apply, star_trivial] using h

theorem suzukiDF6D4EvenLowerMatrix_eq :
    suzukiDF6D4EvenLowerMatrix =
      suzukiDF6D4EvenEndpointMatrix -
        (1 / 25000 : Real) •
          (1 : Matrix (Fin 45) (Fin 45) Real) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [suzukiDF6D4EvenLowerMatrix,
      suzukiDF6D4EvenEndpointMatrix]
  · have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    simp [suzukiDF6D4EvenLowerMatrix,
      suzukiDF6D4EvenEndpointMatrix, hij, hval]

theorem suzukiDF6D4OddLowerMatrix_eq :
    suzukiDF6D4OddLowerMatrix =
      suzukiDF6D4OddEndpointMatrix -
        (1 / 200 : Real) •
          (1 : Matrix (Fin 44) (Fin 44) Real) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [suzukiDF6D4OddLowerMatrix,
      suzukiDF6D4OddEndpointMatrix]
  · have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    simp [suzukiDF6D4OddLowerMatrix,
      suzukiDF6D4OddEndpointMatrix, hij, hval]

theorem suzukiDF6D4OddUpperMatrix_eq :
    suzukiDF6D4OddUpperMatrix =
      (5 : Real) • (1 : Matrix (Fin 44) (Fin 44) Real) -
        suzukiDF6D4OddEndpointMatrix := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [suzukiDF6D4OddUpperMatrix,
      suzukiDF6D4OddEndpointMatrix]
  · have hval : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
    simp [suzukiDF6D4OddUpperMatrix,
      suzukiDF6D4OddEndpointMatrix, hij, hval]

theorem suzukiDF6D5EvenEndpointQuadratic_lower
    (x : Fin 45 → Real) :
    (1 / 25000 : Real) * suzukiDF6D5CoordinateNormSq x ≤
      suzukiDF6D5MatrixQuadratic suzukiDF6D4EvenEndpointMatrix x := by
  have h := matrixQuadratic_nonneg_of_posSemidef
    suzukiDF6D4EvenLowerMatrix_posSemidef x
  rw [suzukiDF6D4EvenLowerMatrix_eq,
    suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_smul,
    suzukiDF6D5MatrixQuadratic_one] at h
  linarith

theorem suzukiDF6D5OddEndpointQuadratic_lower
    (x : Fin 44 → Real) :
    (1 / 200 : Real) * suzukiDF6D5CoordinateNormSq x ≤
      suzukiDF6D5MatrixQuadratic suzukiDF6D4OddEndpointMatrix x := by
  have h := matrixQuadratic_nonneg_of_posSemidef
    suzukiDF6D4OddLowerMatrix_posSemidef x
  rw [suzukiDF6D4OddLowerMatrix_eq,
    suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_smul,
    suzukiDF6D5MatrixQuadratic_one] at h
  linarith

theorem suzukiDF6D5OddEndpointQuadratic_upper
    (x : Fin 44 → Real) :
    suzukiDF6D5MatrixQuadratic suzukiDF6D4OddEndpointMatrix x ≤
      5 * suzukiDF6D5CoordinateNormSq x := by
  have h := matrixQuadratic_nonneg_of_posSemidef
    suzukiDF6D4OddUpperMatrix_posSemidef x
  rw [suzukiDF6D4OddUpperMatrix_eq,
    suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_smul,
    suzukiDF6D5MatrixQuadratic_one] at h
  linarith

theorem suzukiDF6D5EvenCouplingQuadratic_le_ratio
    (x : Fin 45 → Real) :
    (5 / 2 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenCouplingUpperMatrix x ≤
      (1 / 20 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenEndpointMatrix x := by
  have htarget := matrixQuadratic_nonneg_of_posSemidef
    suzukiDF6D4EvenResidualCertificateTargetMatrix_posSemidef x
  have hlow : 0 ≤ suzukiDF6D5MatrixQuadratic
      suzukiDF6D4EvenEndpointMatrix x := by
    have hnorm := suzukiDF6D5CoordinateNormSq_nonneg x
    exact (mul_nonneg (by norm_num) hnorm).trans
      (suzukiDF6D5EvenEndpointQuadratic_lower x)
  rw [suzukiDF6D4EvenResidualCertificateTargetMatrix,
    suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_smul] at htarget
  have hcoefficient :
      (5 / 2 : Real) *
          ((suzukiDF6D4EvenStrictComparisonCoefficient : Rat) : Real) ≤
        (1 / 20 : Real) := by
    norm_num [suzukiDF6D4EvenStrictComparisonCoefficient,
      suzukiDF6D4EvenComparisonCoefficient,
      suzukiDF6D4StrictReserve]
  calc
    (5 / 2 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenCouplingUpperMatrix x ≤
        (5 / 2 : Real) *
          (((suzukiDF6D4EvenStrictComparisonCoefficient : Rat) : Real) *
            suzukiDF6D5MatrixQuadratic
              suzukiDF6D4EvenEndpointMatrix x) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · norm_num
    _ = ((5 / 2 : Real) *
          ((suzukiDF6D4EvenStrictComparisonCoefficient : Rat) : Real)) *
          suzukiDF6D5MatrixQuadratic
            suzukiDF6D4EvenEndpointMatrix x := by ring
    _ ≤ (1 / 20 : Real) *
          suzukiDF6D5MatrixQuadratic
            suzukiDF6D4EvenEndpointMatrix x :=
      mul_le_mul_of_nonneg_right hcoefficient hlow

theorem suzukiDF6D5OddCouplingQuadratic_le_ratio
    (x : Fin 44 → Real) :
    (5 / 2 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddCouplingUpperMatrix x ≤
      (999 / 1000 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddEndpointMatrix x := by
  have htarget := matrixQuadratic_nonneg_of_posSemidef
    suzukiDF6D5OddAdditiveTargetMatrix_posSemidef x
  have hlow : 0 ≤ suzukiDF6D5MatrixQuadratic
      suzukiDF6D4OddEndpointMatrix x := by
    have hnorm := suzukiDF6D5CoordinateNormSq_nonneg x
    exact (mul_nonneg (by norm_num) hnorm).trans
      (suzukiDF6D5OddEndpointQuadratic_lower x)
  have hupper := suzukiDF6D5OddEndpointQuadratic_upper x
  rw [suzukiDF6D5OddAdditiveTargetMatrix,
    suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_smul,
    suzukiDF6D5MatrixQuadratic_one,
    suzukiDF6D4OddResidualCertificateTargetMatrix,
    suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_smul] at htarget
  have hreserve :
      (1 / 2500 : Real) *
          suzukiDF6D5MatrixQuadratic
            suzukiDF6D4OddEndpointMatrix x ≤
        (1 / 500 : Real) * suzukiDF6D5CoordinateNormSq x := by
    nlinarith
  have hcomparison :
      suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddCouplingUpperMatrix x ≤
        (((suzukiDF6D4OddStrictComparisonCoefficient : Rat) : Real) -
          (1 / 2500 : Real)) *
            suzukiDF6D5MatrixQuadratic
              suzukiDF6D4OddEndpointMatrix x := by
    norm_num [suzukiDF6D5OddAdditiveReserve] at htarget
    linarith
  have hcoefficient :
      (5 / 2 : Real) *
          (((suzukiDF6D4OddStrictComparisonCoefficient : Rat) : Real) -
            (1 / 2500 : Real)) ≤
        (999 / 1000 : Real) := by
    norm_num [suzukiDF6D4OddStrictComparisonCoefficient,
      suzukiDF6D4OddComparisonCoefficient,
      suzukiDF6D4StrictReserve]
  calc
    (5 / 2 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddCouplingUpperMatrix x ≤
        (5 / 2 : Real) *
          ((((suzukiDF6D4OddStrictComparisonCoefficient : Rat) : Real) -
            (1 / 2500 : Real)) *
              suzukiDF6D5MatrixQuadratic
                suzukiDF6D4OddEndpointMatrix x) :=
      mul_le_mul_of_nonneg_left hcomparison (by norm_num)
    _ = ((5 / 2 : Real) *
          (((suzukiDF6D4OddStrictComparisonCoefficient : Rat) : Real) -
            (1 / 2500 : Real))) *
          suzukiDF6D5MatrixQuadratic
            suzukiDF6D4OddEndpointMatrix x := by ring
    _ ≤ (999 / 1000 : Real) *
          suzukiDF6D5MatrixQuadratic
            suzukiDF6D4OddEndpointMatrix x :=
      mul_le_mul_of_nonneg_right hcoefficient hlow

theorem suzukiDF6D5EvenCoordinateBlock_coercive
    (x : Fin 45 → Real) {farEnergy farNormSq cross : Real}
    (hfarNorm : 0 ≤ farNormSq)
    (hfar : 2 * farNormSq ≤ farEnergy)
    (hcross : cross ^ 2 ≤
      (5 / 2 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenCouplingUpperMatrix x * farEnergy) :
    (1 / 400000 : Real) *
        (suzukiDF6D5CoordinateNormSq x + farNormSq) ≤
      blockSchurFormValue
        (suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenEndpointMatrix x)
        farEnergy cross := by
  have hcoord := suzukiDF6D5CoordinateNormSq_nonneg x
  have hlowBound := suzukiDF6D5EvenEndpointQuadratic_lower x
  have hlow : 0 ≤ suzukiDF6D5MatrixQuadratic
      suzukiDF6D4EvenEndpointMatrix x :=
    (mul_nonneg (by norm_num) hcoord).trans hlowBound
  have hfarNonneg : 0 ≤ farEnergy := by linarith
  have hratio := suzukiDF6D5EvenCouplingQuadratic_le_ratio x
  have hschur : cross ^ 2 ≤
      (1 / 20 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenEndpointMatrix x * farEnergy := by
    exact hcross.trans
      (mul_le_mul_of_nonneg_right hratio hfarNonneg)
  have hblock := blockSchurFormValue_ge_even_reserve
    hlow hfarNonneg hschur
  calc
    (1 / 400000 : Real) *
        (suzukiDF6D5CoordinateNormSq x + farNormSq) ≤
        (3 / 4 : Real) *
          (suzukiDF6D5MatrixQuadratic
              suzukiDF6D4EvenEndpointMatrix x + farEnergy) := by
      nlinarith
    _ ≤ blockSchurFormValue
        (suzukiDF6D5MatrixQuadratic
          suzukiDF6D4EvenEndpointMatrix x)
        farEnergy cross := hblock

theorem suzukiDF6D5OddCoordinateBlock_coercive
    (x : Fin 44 → Real) {farEnergy farNormSq cross : Real}
    (hfarNorm : 0 ≤ farNormSq)
    (hfar : 2 * farNormSq ≤ farEnergy)
    (hcross : cross ^ 2 ≤
      (5 / 2 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddCouplingUpperMatrix x * farEnergy) :
    (1 / 400000 : Real) *
        (suzukiDF6D5CoordinateNormSq x + farNormSq) ≤
      blockSchurFormValue
        (suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddEndpointMatrix x)
        farEnergy cross := by
  have hcoord := suzukiDF6D5CoordinateNormSq_nonneg x
  have hlowBound := suzukiDF6D5OddEndpointQuadratic_lower x
  have hlow : 0 ≤ suzukiDF6D5MatrixQuadratic
      suzukiDF6D4OddEndpointMatrix x :=
    (mul_nonneg (by norm_num) hcoord).trans hlowBound
  have hfarNonneg : 0 ≤ farEnergy := by linarith
  have hratio := suzukiDF6D5OddCouplingQuadratic_le_ratio x
  have hschur : cross ^ 2 ≤
      (999 / 1000 : Real) *
        suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddEndpointMatrix x * farEnergy := by
    exact hcross.trans
      (mul_le_mul_of_nonneg_right hratio hfarNonneg)
  have hblock := blockSchurFormValue_ge_odd_reserve
    hlow hfarNonneg hschur
  calc
    (1 / 400000 : Real) *
        (suzukiDF6D5CoordinateNormSq x + farNormSq) ≤
        (1 / 2000 : Real) *
          (suzukiDF6D5MatrixQuadratic
              suzukiDF6D4OddEndpointMatrix x + farEnergy) := by
      nlinarith
    _ ≤ blockSchurFormValue
        (suzukiDF6D5MatrixQuadratic
          suzukiDF6D4OddEndpointMatrix x)
        farEnergy cross := hblock

end

end RiemannHypothesisProject.Experiments.M100
