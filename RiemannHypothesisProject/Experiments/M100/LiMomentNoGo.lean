import Mathlib.Analysis.Matrix.PosDef
import RiemannHypothesisProject.LiCriterion.WeilPairing

/-!
# M100-X07 Li moment Hankel route filter

This experimental module isolates the first necessary Hankel inequality for a
positive moment representation.  It does not prove the numerical sign of the
actual zeta Li minor; that sign is audited separately by the X07 arithmetic
coefficient probe.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open ComplexCompactExhaustion
open scoped Matrix

noncomputable section

/-- The first two-by-two Hankel matrix of a proposed moment sequence. -/
def momentHankelTwo (moment : Nat → Real) : Matrix (Fin 2) (Fin 2) Real :=
  !![moment 0, moment 1; moment 1, moment 2]

/-- The first Hankel determinant is the log-convexity defect. -/
theorem momentHankelTwo_det (moment : Nat → Real) :
    (momentHankelTwo moment).det =
      moment 0 * moment 2 - moment 1 ^ 2 := by
  simp [momentHankelTwo, Matrix.det_fin_two]
  ring

/-- Positive semidefiniteness of the first Hankel matrix forces the first
log-convexity inequality required by every positive moment sequence. -/
theorem first_moment_logConvex_of_momentHankelTwo_posSemidef
    {moment : Nat → Real}
    (hPSD : (momentHankelTwo moment).PosSemidef) :
    moment 1 ^ 2 ≤ moment 0 * moment 2 := by
  have hdet : 0 ≤ (momentHankelTwo moment).det := hPSD.det_nonneg
  rw [momentHankelTwo_det] at hdet
  linarith

/-- A negative first Hankel determinant rules out positive semidefiniteness. -/
theorem momentHankelTwo_not_posSemidef_of_det_neg
    {moment : Nat → Real}
    (hneg : moment 0 * moment 2 - moment 1 ^ 2 < 0) :
    ¬ (momentHankelTwo moment).PosSemidef := by
  intro hPSD
  have hdet : 0 ≤ moment 0 * moment 2 - moment 1 ^ 2 := by
    rw [← momentHankelTwo_det]
    exact hPSD.det_nonneg
  linarith

/-- The raw moment candidate tested in X07: `m_k = lambda_(k+1)`. -/
def fullZetaLiMomentCandidate (k : Nat) : Real :=
  fullZetaLiCoefficient (k + 1)

/-- Any positive-Hankel realization of the raw candidate must satisfy the
explicit three-coefficient inequality tested numerically by X07. -/
theorem fullZetaLi_firstMomentMinor_nonneg_of_posSemidef
    (hPSD : (momentHankelTwo fullZetaLiMomentCandidate).PosSemidef) :
    fullZetaLiCoefficient 2 ^ 2 ≤
      fullZetaLiCoefficient 1 * fullZetaLiCoefficient 3 := by
  simpa [fullZetaLiMomentCandidate] using
    first_moment_logConvex_of_momentHankelTwo_posSemidef hPSD

/-- Geometric damping cannot repair the sign of the first Hankel determinant:
it only multiplies that determinant by a square. -/
def geometricMomentRescale
    (scale : Real) (moment : Nat → Real) (n : Nat) : Real :=
  scale ^ n * moment n

theorem momentHankelTwo_det_geometricMomentRescale
    (scale : Real) (moment : Nat → Real) :
    (momentHankelTwo (geometricMomentRescale scale moment)).det =
      scale ^ 2 * (momentHankelTwo moment).det := by
  rw [momentHankelTwo_det, momentHankelTwo_det]
  simp [geometricMomentRescale]
  ring

/-- Consequently every nonzero geometric rescaling retains a negative first
Hankel determinant. -/
theorem geometricMomentRescale_not_posSemidef_of_det_neg
    {scale : Real} {moment : Nat → Real}
    (hscale : scale ≠ 0)
    (hneg : moment 0 * moment 2 - moment 1 ^ 2 < 0) :
    ¬ (momentHankelTwo (geometricMomentRescale scale moment)).PosSemidef := by
  apply momentHankelTwo_not_posSemidef_of_det_neg
  rw [← momentHankelTwo_det,
    momentHankelTwo_det_geometricMomentRescale]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hscale) (by
    rwa [momentHankelTwo_det])

end

end M100
end Experiments
end RiemannHypothesisProject
