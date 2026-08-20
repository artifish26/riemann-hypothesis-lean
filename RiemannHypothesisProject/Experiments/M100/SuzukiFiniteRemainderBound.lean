import RiemannHypothesisProject.Experiments.M100.SuzukiLogFourierDomain
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.InnerProductSpace.Continuous

/-!
# M100-DF6D2 finite-radius remainder bounds

Suzuki's equation (2.5) expresses the complete smooth-core form as the local
logarithmic energy plus three bounded pieces: a scalar `L^2` term, finitely
many symmetric translation terms, and a smooth-kernel operator term. This
module proves the concrete `L^2` bounds for that operator-level decomposition.

The translation is the actual measure-preserving translation on global
`L^2(Real, Complex)`. The smooth-kernel term is accepted as its continuous
linear `L^2` operator; construction of that operator from Suzuki's `r''`
kernel is a separate analytic bridge.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Translation of a global `L^2` class by composition with `x -> x + t`. -/
def suzukiL2Translate (t : Real) (v : SuzukiL2) : SuzukiL2 :=
  Lp.compMeasurePreserving (fun x : Real => x + t)
    (measurePreserving_add_right (volume : Measure Real) t) v

/-- Translation bundled as a linear isometry on global `L²`. -/
def suzukiL2TranslateLI (t : Real) :
    SuzukiL2 →ₗᵢ[Complex] SuzukiL2 :=
  Lp.compMeasurePreservingₗᵢ Complex (fun x : Real ↦ x + t)
    (measurePreserving_add_right (volume : Measure Real) t)

/-- Translation bundled as a continuous linear map. -/
def suzukiL2TranslateCLM (t : Real) :
    SuzukiL2 →L[Complex] SuzukiL2 :=
  (suzukiL2TranslateLI t).toContinuousLinearMap

@[simp]
theorem suzukiL2TranslateCLM_apply (t : Real) (v : SuzukiL2) :
    suzukiL2TranslateCLM t v = suzukiL2Translate t v :=
  rfl

@[simp]
theorem suzukiL2Translate_norm (t : Real) (v : SuzukiL2) :
    norm (suzukiL2Translate t v) = norm v := by
  exact Lp.norm_compMeasurePreserving v
    (measurePreserving_add_right (volume : Measure Real) t)

/-- The complex translation correlation on global `L^2`. -/
def suzukiL2TranslationCorrelation (t : Real) (v : SuzukiL2) : Complex :=
  inner Complex (suzukiL2Translate t v) v

theorem suzukiL2TranslationCorrelation_norm_le
    (t : Real) (v : SuzukiL2) :
    norm (suzukiL2TranslationCorrelation t v) <= norm v ^ 2 := by
  calc
    norm (suzukiL2TranslationCorrelation t v) <=
        norm (suzukiL2Translate t v) * norm v :=
      norm_inner_le_norm _ _
    _ = norm v ^ 2 := by rw [suzukiL2Translate_norm]; ring

/-- The two conjugate translation integrals in Suzuki's equation (2.5), in
their global-`L^2` diagonal form. -/
def suzukiL2SymmetricTranslationDiagonal
    (t : Real) (v : SuzukiL2) : Real :=
  2 * (suzukiL2TranslationCorrelation t v).re

theorem suzukiL2SymmetricTranslationDiagonal_abs_le
    (t : Real) (v : SuzukiL2) :
    abs (suzukiL2SymmetricTranslationDiagonal t v) <=
      2 * norm v ^ 2 := by
  calc
    abs (suzukiL2SymmetricTranslationDiagonal t v) =
        2 * abs (suzukiL2TranslationCorrelation t v).re := by
      rw [suzukiL2SymmetricTranslationDiagonal, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    _ <= 2 * norm (suzukiL2TranslationCorrelation t v) :=
      mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm _) (by positivity)
    _ <= 2 * norm v ^ 2 :=
      mul_le_mul_of_nonneg_left
        (suzukiL2TranslationCorrelation_norm_le t v) (by positivity)

/-- A finite weighted sum of the symmetric translation diagonals. -/
def suzukiL2FiniteTranslationRemainder
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I -> Real) (v : SuzukiL2) : Real :=
  Finset.sum s (fun i =>
    coefficient i * suzukiL2SymmetricTranslationDiagonal (shift i) v)

theorem suzukiL2FiniteTranslationRemainder_abs_le
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I -> Real) (v : SuzukiL2) :
    abs (suzukiL2FiniteTranslationRemainder s coefficient shift v) <=
      (Finset.sum s (fun i => 2 * abs (coefficient i))) * norm v ^ 2 := by
  calc
    abs (suzukiL2FiniteTranslationRemainder s coefficient shift v) <=
        Finset.sum s (fun i =>
          abs (coefficient i *
            suzukiL2SymmetricTranslationDiagonal (shift i) v)) := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= Finset.sum s (fun i =>
        (2 * abs (coefficient i)) * norm v ^ 2) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have h := suzukiL2SymmetricTranslationDiagonal_abs_le
        (shift i) v
      nlinarith [abs_nonneg (coefficient i)]
    _ = (Finset.sum s (fun i => 2 * abs (coefficient i))) *
        norm v ^ 2 := by
      rw [Finset.sum_mul]

/-- The real diagonal associated with a bounded smooth-kernel operator. -/
def suzukiL2BoundedOperatorDiagonal
    (K : SuzukiL2 →L[Complex] SuzukiL2) (v : SuzukiL2) : Real :=
  (inner Complex (K v) v).re

theorem suzukiL2BoundedOperatorDiagonal_abs_le
    (K : SuzukiL2 →L[Complex] SuzukiL2) (v : SuzukiL2) :
    abs (suzukiL2BoundedOperatorDiagonal K v) <=
      norm K * norm v ^ 2 := by
  calc
    abs (suzukiL2BoundedOperatorDiagonal K v) <=
        norm (inner Complex (K v) v) :=
      Complex.abs_re_le_norm _
    _ <= norm (K v) * norm v := norm_inner_le_norm _ _
    _ <= (norm K * norm v) * norm v := by
      exact mul_le_mul_of_nonneg_right (K.le_opNorm v) (norm_nonneg v)
    _ = norm K * norm v ^ 2 := by ring

/-- Operator-level form of all bounded terms in Suzuki's equation (2.5). -/
def suzukiL2FiniteRadiusRemainder
    {I : Type*} [DecidableEq I] (s : Finset I)
    (scalar : Real) (coefficient shift : I -> Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2) (v : SuzukiL2) : Real :=
  scalar * norm v ^ 2 +
    suzukiL2FiniteTranslationRemainder s coefficient shift v +
    suzukiL2BoundedOperatorDiagonal K v

/-- Explicit ambient-`L^2` bound for the complete finite-radius remainder. -/
theorem suzukiL2FiniteRadiusRemainder_abs_le
    {I : Type*} [DecidableEq I] (s : Finset I)
    (scalar : Real) (coefficient shift : I -> Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2) (v : SuzukiL2) :
    abs (suzukiL2FiniteRadiusRemainder
        s scalar coefficient shift K v) <=
      (abs scalar +
        Finset.sum s (fun i => 2 * abs (coefficient i)) + norm K) *
        norm v ^ 2 := by
  have htranslation := suzukiL2FiniteTranslationRemainder_abs_le
    s coefficient shift v
  have hkernel := suzukiL2BoundedOperatorDiagonal_abs_le K v
  calc
    abs (suzukiL2FiniteRadiusRemainder
        s scalar coefficient shift K v) <=
        abs (scalar * norm v ^ 2) +
          abs (suzukiL2FiniteTranslationRemainder
            s coefficient shift v) +
          abs (suzukiL2BoundedOperatorDiagonal K v) := by
      unfold suzukiL2FiniteRadiusRemainder
      exact (abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ <= abs scalar * norm v ^ 2 +
          (Finset.sum s (fun i => 2 * abs (coefficient i))) *
            norm v ^ 2 +
          norm K * norm v ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg (norm v))]
      gcongr
    _ = (abs scalar +
          Finset.sum s (fun i => 2 * abs (coefficient i)) + norm K) *
          norm v ^ 2 := by ring

/-- Polarization of the symmetric translation term. Its diagonal real part
is the two-conjugate translation contribution in Suzuki's equation (2.5). -/
def suzukiL2SymmetricTranslationEnergy
    (t : Real) (u v : SuzukiL2) : Complex :=
  inner Complex (suzukiL2TranslateCLM t u) v +
    inner Complex u (suzukiL2TranslateCLM t v)

theorem suzukiL2SymmetricTranslationEnergy_jointContinuous (t : Real) :
    Continuous (Function.uncurry
      (suzukiL2SymmetricTranslationEnergy t)) := by
  unfold suzukiL2SymmetricTranslationEnergy Function.uncurry
  fun_prop

/-- Polarized finite translation remainder. -/
def suzukiL2FiniteTranslationEnergy
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u v : SuzukiL2) : Complex :=
  Finset.sum s (fun i ↦
    (coefficient i : Complex) *
      suzukiL2SymmetricTranslationEnergy (shift i) u v)

theorem suzukiL2FiniteTranslationEnergy_jointContinuous
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) :
    Continuous (Function.uncurry
      (suzukiL2FiniteTranslationEnergy s coefficient shift)) := by
  unfold suzukiL2FiniteTranslationEnergy Function.uncurry
  apply continuous_finsetSum
  intro i hi
  exact continuous_const.mul
    (suzukiL2SymmetricTranslationEnergy_jointContinuous (shift i))

/-- Polarized form associated with a bounded smooth-kernel operator. -/
def suzukiL2BoundedOperatorEnergy
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiL2) : Complex :=
  inner Complex (K u) v

theorem suzukiL2BoundedOperatorEnergy_jointContinuous
    (K : SuzukiL2 →L[Complex] SuzukiL2) :
    Continuous (Function.uncurry
      (suzukiL2BoundedOperatorEnergy K)) := by
  unfold suzukiL2BoundedOperatorEnergy Function.uncurry
  fun_prop

/-- Polarized operator-level form of all bounded terms in Suzuki's equation
(2.5). -/
def suzukiL2FiniteRadiusRemainderEnergy
    {I : Type*} [DecidableEq I] (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiL2) : Complex :=
  (scalar : Complex) * inner Complex u v +
    suzukiL2FiniteTranslationEnergy s coefficient shift u v +
    suzukiL2BoundedOperatorEnergy K u v

theorem suzukiL2FiniteRadiusRemainderEnergy_jointContinuous
    {I : Type*} [DecidableEq I] (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2) :
    Continuous (Function.uncurry
      (suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift K)) := by
  unfold suzukiL2FiniteRadiusRemainderEnergy Function.uncurry
  exact ((continuous_const.mul continuous_inner).add
    (suzukiL2FiniteTranslationEnergy_jointContinuous
      s coefficient shift)).add
    (suzukiL2BoundedOperatorEnergy_jointContinuous K)

theorem suzukiL2SymmetricTranslationEnergy_self_re
    (t : Real) (v : SuzukiL2) :
    (suzukiL2SymmetricTranslationEnergy t v v).re =
      suzukiL2SymmetricTranslationDiagonal t v := by
  unfold suzukiL2SymmetricTranslationEnergy
    suzukiL2SymmetricTranslationDiagonal
    suzukiL2TranslationCorrelation
  rw [Complex.add_re, suzukiL2TranslateCLM_apply]
  have hsym :
      (inner Complex v (suzukiL2Translate t v)).re =
        (inner Complex (suzukiL2Translate t v) v).re :=
    inner_re_symm (𝕜 := Complex) v (suzukiL2Translate t v)
  rw [hsym]
  ring

theorem suzukiL2FiniteTranslationEnergy_self_re
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (v : SuzukiL2) :
    (suzukiL2FiniteTranslationEnergy s coefficient shift v v).re =
      suzukiL2FiniteTranslationRemainder s coefficient shift v := by
  unfold suzukiL2FiniteTranslationEnergy
    suzukiL2FiniteTranslationRemainder
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero,
    suzukiL2SymmetricTranslationEnergy_self_re]

theorem suzukiL2FiniteRadiusRemainderEnergy_self_re
    {I : Type*} [DecidableEq I] (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2) (v : SuzukiL2) :
    (suzukiL2FiniteRadiusRemainderEnergy
      s scalar coefficient shift K v v).re =
        suzukiL2FiniteRadiusRemainder
          s scalar coefficient shift K v := by
  unfold suzukiL2FiniteRadiusRemainderEnergy
    suzukiL2FiniteRadiusRemainder
    suzukiL2BoundedOperatorEnergy
    suzukiL2BoundedOperatorDiagonal
  rw [Complex.add_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hself : (inner Complex v v).re = norm v ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) v
  rw [hself, suzukiL2FiniteTranslationEnergy_self_re]

end

end M100
end Experiments
end RiemannHypothesisProject
