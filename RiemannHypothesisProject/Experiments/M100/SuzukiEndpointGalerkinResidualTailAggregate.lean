import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailGeometricIntervals

/-!
# Aggregate analytic residual-tail matrices for M100-DF6D4

This module packages the checked order-`n^-11` coordinate envelopes as exact
diagonal Gram majorants, then combines them with the leading and structured
tail matrices using the two frozen Young splits.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Generic diagonal-envelope matrices -/

def suzukiDF6D4DiagonalEnvelopeMatrix {d : Nat}
    (coefficient : Real) (envelope : Fin d → Real) :
    Matrix (Fin d) (Fin d) Real :=
  fun i j => if i = j then coefficient * envelope i else 0

def suzukiDF6D4DiagonalEnvelopeEntryInterval {d : Nat}
    (coefficientInterval : RationalInterval)
    (envelopeInterval : Fin d → RationalInterval) (i j : Fin d) :
    RationalInterval :=
  if i = j then coefficientInterval.mulCentered (envelopeInterval i)
  else RationalInterval.point 0

theorem suzukiDF6D4DiagonalEnvelopeEntryInterval_contains
    {d : Nat} {coefficient : Real}
    {coefficientInterval : RationalInterval}
    {envelope : Fin d → Real}
    {envelopeInterval : Fin d → RationalInterval}
    (hcoefficient : coefficientInterval.Contains coefficient)
    (henvelope : ∀ i, (envelopeInterval i).Contains (envelope i))
    (i j : Fin d) :
    (suzukiDF6D4DiagonalEnvelopeEntryInterval
      coefficientInterval envelopeInterval i j).Contains
        (suzukiDF6D4DiagonalEnvelopeMatrix coefficient envelope i j) := by
  by_cases hij : i = j
  · subst j
    simp only [suzukiDF6D4DiagonalEnvelopeEntryInterval,
      suzukiDF6D4DiagonalEnvelopeMatrix, if_true]
    exact RationalInterval.contains_mulCentered hcoefficient (henvelope i)
  · simp only [suzukiDF6D4DiagonalEnvelopeEntryInterval,
      suzukiDF6D4DiagonalEnvelopeMatrix, hij, if_false]
    simpa using RationalInterval.contains_point (0 : Rat)

theorem suzukiDF6D4DiagonalEnvelopeMatrix_quadratic
    {d : Nat} (coefficient : Real) (envelope x : Fin d → Real) :
    dotProduct x
        (Matrix.mulVec
          (suzukiDF6D4DiagonalEnvelopeMatrix coefficient envelope) x) =
      coefficient * ∑ i, envelope i * (x i) ^ 2 := by
  unfold dotProduct Matrix.mulVec suzukiDF6D4DiagonalEnvelopeMatrix
  calc
    (∑ i, x i * ∑ j, (if i = j then coefficient * envelope i else 0) * x j) =
        ∑ i, coefficient * (envelope i * (x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp only [if_true]
        ring
      · intro j _ hji
        simp only [Ne.symm hji, if_false, zero_mul]
      · simp
    _ = coefficient * ∑ i, envelope i * (x i) ^ 2 := by
      rw [Finset.mul_sum]

/-! ## Frozen geometric-tail diagonal majorants -/

def suzukiDF6D4GeometricTailCoefficient {d : Nat}
    (envelope : Fin d → Real) : Real :=
  (∑ i, envelope i) * (1 / (21 * (600 : Real) ^ 21))

def suzukiDF6D4GeometricTailCoefficientInterval {d : Nat}
    (envelopeInterval : Fin d → RationalInterval) : RationalInterval :=
  RationalInterval.scale (1 / (21 * (600 : Rat) ^ 21))
    (RationalInterval.sum Finset.univ envelopeInterval)

theorem suzukiDF6D4GeometricTailCoefficientInterval_contains
    {d : Nat} (envelope : Fin d → Real)
    (envelopeInterval : Fin d → RationalInterval)
    (henvelope : ∀ i, (envelopeInterval i).Contains (envelope i)) :
    (suzukiDF6D4GeometricTailCoefficientInterval envelopeInterval).Contains
      (suzukiDF6D4GeometricTailCoefficient envelope) := by
  have hsum := RationalInterval.contains_sum
    (s := Finset.univ) (fun i _ => henvelope i)
  have h := RationalInterval.contains_scale
    (1 / (21 * (600 : Rat) ^ 21)) hsum
  unfold suzukiDF6D4GeometricTailCoefficientInterval
    suzukiDF6D4GeometricTailCoefficient
  convert h using 1 <;> norm_num <;> ring

def suzukiDF6D4EvenGeometricTailMatrix : Matrix (Fin 45) (Fin 45) Real :=
  suzukiDF6D4DiagonalEnvelopeMatrix
    (suzukiDF6D4GeometricTailCoefficient
      suzukiDF6D4EvenResidualGeometricEnvelope)
    suzukiDF6D4EvenResidualGeometricEnvelope

def suzukiDF6D4OddGeometricTailMatrix : Matrix (Fin 44) (Fin 44) Real :=
  suzukiDF6D4DiagonalEnvelopeMatrix
    (suzukiDF6D4GeometricTailCoefficient
      suzukiDF6D4OddResidualGeometricEnvelope)
    suzukiDF6D4OddResidualGeometricEnvelope

def suzukiDF6D4EvenGeometricTailEntryInterval
    (i j : Fin 45) : RationalInterval :=
  suzukiDF6D4DiagonalEnvelopeEntryInterval
    (suzukiDF6D4GeometricTailCoefficientInterval
      suzukiDF6D4EvenResidualGeometricEnvelopeInterval)
    suzukiDF6D4EvenResidualGeometricEnvelopeInterval i j

def suzukiDF6D4OddGeometricTailEntryInterval
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4DiagonalEnvelopeEntryInterval
    (suzukiDF6D4GeometricTailCoefficientInterval
      suzukiDF6D4OddResidualGeometricEnvelopeInterval)
    suzukiDF6D4OddResidualGeometricEnvelopeInterval i j

theorem suzukiDF6D4EvenGeometricTailEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenGeometricTailEntryInterval i j).Contains
      (suzukiDF6D4EvenGeometricTailMatrix i j) := by
  exact suzukiDF6D4DiagonalEnvelopeEntryInterval_contains
    (suzukiDF6D4GeometricTailCoefficientInterval_contains
      suzukiDF6D4EvenResidualGeometricEnvelope
      suzukiDF6D4EvenResidualGeometricEnvelopeInterval
      suzukiDF6D4EvenResidualGeometricEnvelopeInterval_contains)
    suzukiDF6D4EvenResidualGeometricEnvelopeInterval_contains i j

theorem suzukiDF6D4OddGeometricTailEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddGeometricTailEntryInterval i j).Contains
      (suzukiDF6D4OddGeometricTailMatrix i j) := by
  exact suzukiDF6D4DiagonalEnvelopeEntryInterval_contains
    (suzukiDF6D4GeometricTailCoefficientInterval_contains
      suzukiDF6D4OddResidualGeometricEnvelope
      suzukiDF6D4OddResidualGeometricEnvelopeInterval
      suzukiDF6D4OddResidualGeometricEnvelopeInterval_contains)
    suzukiDF6D4OddResidualGeometricEnvelopeInterval_contains i j

theorem suzukiDF6D4EvenGeometricTailMatrix_quadratic
    (x : Fin 45 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4EvenGeometricTailMatrix x) =
      (∑ i : Fin 45, suzukiDF6D4EvenResidualGeometricEnvelope i) *
          (1 / (21 * (600 : Real) ^ 21)) *
        ∑ i : Fin 45,
          suzukiDF6D4EvenResidualGeometricEnvelope i * (x i) ^ 2 := by
  exact suzukiDF6D4DiagonalEnvelopeMatrix_quadratic
    (suzukiDF6D4GeometricTailCoefficient
      suzukiDF6D4EvenResidualGeometricEnvelope)
    suzukiDF6D4EvenResidualGeometricEnvelope x

theorem suzukiDF6D4OddGeometricTailMatrix_quadratic
    (x : Fin 44 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4OddGeometricTailMatrix x) =
      (∑ i : Fin 44, suzukiDF6D4OddResidualGeometricEnvelope i) *
          (1 / (21 * (600 : Real) ^ 21)) *
        ∑ i : Fin 44,
          suzukiDF6D4OddResidualGeometricEnvelope i * (x i) ^ 2 := by
  exact suzukiDF6D4DiagonalEnvelopeMatrix_quadratic
    (suzukiDF6D4GeometricTailCoefficient
      suzukiDF6D4OddResidualGeometricEnvelope)
    suzukiDF6D4OddResidualGeometricEnvelope x

/-! ## Structured-tail sum matrices -/

def suzukiDF6D4EvenStructuredTailMatrix : Matrix (Fin 45) (Fin 45) Real :=
  (15 : Real) • ∑ index : Fin 15,
    suzukiDF6D4EvenStructuredTailContributionMatrix index

def suzukiDF6D4OddStructuredTailMatrix : Matrix (Fin 44) (Fin 44) Real :=
  (14 : Real) • ∑ index : Fin 14,
    suzukiDF6D4OddStructuredTailContributionMatrix index

def suzukiDF6D4EvenStructuredTailEntryInterval
    (i j : Fin 45) : RationalInterval :=
  RationalInterval.scale 15
    (RationalInterval.sum Finset.univ fun index : Fin 15 =>
      suzukiDF6D4EvenStructuredTailContributionEntryInterval index i j)

def suzukiDF6D4OddStructuredTailEntryInterval
    (i j : Fin 44) : RationalInterval :=
  RationalInterval.scale 14
    (RationalInterval.sum Finset.univ fun index : Fin 14 =>
      suzukiDF6D4OddStructuredTailContributionEntryInterval index i j)

theorem suzukiDF6D4EvenStructuredTailEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenStructuredTailEntryInterval i j).Contains
      (suzukiDF6D4EvenStructuredTailMatrix i j) := by
  unfold suzukiDF6D4EvenStructuredTailEntryInterval
    suzukiDF6D4EvenStructuredTailMatrix
  exact RationalInterval.contains_scale 15
    (RationalInterval.contains_sum fun index _ =>
      suzukiDF6D4EvenStructuredTailContributionEntryInterval_contains index i j)

theorem suzukiDF6D4OddStructuredTailEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddStructuredTailEntryInterval i j).Contains
      (suzukiDF6D4OddStructuredTailMatrix i j) := by
  unfold suzukiDF6D4OddStructuredTailEntryInterval
    suzukiDF6D4OddStructuredTailMatrix
  exact RationalInterval.contains_scale 14
    (RationalInterval.contains_sum fun index _ =>
      suzukiDF6D4OddStructuredTailContributionEntryInterval_contains index i j)

theorem suzukiDF6D4EvenStructuredTailMatrix_quadratic
    (x : Fin 45 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4EvenStructuredTailMatrix x) =
      15 * ∑ index : Fin 15,
        suzukiDF6D4EvenStructuredTailContributionBound index x := by
  unfold suzukiDF6D4EvenStructuredTailMatrix
  rw [Matrix.smul_mulVec, dotProduct_smul]
  simp only [Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul,
    suzukiDF6D4EvenStructuredTailContributionMatrix_quadratic]

theorem suzukiDF6D4OddStructuredTailMatrix_quadratic
    (x : Fin 44 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4OddStructuredTailMatrix x) =
      14 * ∑ index : Fin 14,
        suzukiDF6D4OddStructuredTailContributionBound index x := by
  unfold suzukiDF6D4OddStructuredTailMatrix
  rw [Matrix.smul_mulVec, dotProduct_smul]
  simp only [Matrix.sum_mulVec, dotProduct_sum, smul_eq_mul,
    suzukiDF6D4OddStructuredTailContributionMatrix_quadratic]

/-! ## Exact Young-weighted aggregate matrices -/

def suzukiDF6D4EvenResidualRemainderTailMatrix :
    Matrix (Fin 45) (Fin 45) Real :=
  (11 / 10 : Real) • suzukiDF6D4EvenStructuredTailMatrix +
    (11 : Real) • suzukiDF6D4EvenGeometricTailMatrix

def suzukiDF6D4OddResidualRemainderTailMatrix :
    Matrix (Fin 44) (Fin 44) Real :=
  (11 / 10 : Real) • suzukiDF6D4OddStructuredTailMatrix +
    (11 : Real) • suzukiDF6D4OddGeometricTailMatrix

def suzukiDF6D4EvenAnalyticTailMatrix : Matrix (Fin 45) (Fin 45) Real :=
  (21 / 20 : Real) • suzukiDF6D4EvenResidualTailMainMatrix +
    (21 : Real) • suzukiDF6D4EvenResidualRemainderTailMatrix

def suzukiDF6D4OddAnalyticTailMatrix : Matrix (Fin 44) (Fin 44) Real :=
  (21 / 20 : Real) • suzukiDF6D4OddResidualTailMainMatrix +
    (21 : Real) • suzukiDF6D4OddResidualRemainderTailMatrix

def suzukiDF6D4EvenResidualRemainderTailEntryInterval
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.scale (11 / 10 : Rat)
      (suzukiDF6D4EvenStructuredTailEntryInterval i j)).add
    (RationalInterval.scale 11
      (suzukiDF6D4EvenGeometricTailEntryInterval i j))

def suzukiDF6D4OddResidualRemainderTailEntryInterval
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.scale (11 / 10 : Rat)
      (suzukiDF6D4OddStructuredTailEntryInterval i j)).add
    (RationalInterval.scale 11
      (suzukiDF6D4OddGeometricTailEntryInterval i j))

def suzukiDF6D4EvenAnalyticTailEntryInterval
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.scale (21 / 20 : Rat)
      (suzukiDF6D4EvenResidualTailMainEntryInterval i j)).add
    (RationalInterval.scale 21
      (suzukiDF6D4EvenResidualRemainderTailEntryInterval i j))

def suzukiDF6D4OddAnalyticTailEntryInterval
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.scale (21 / 20 : Rat)
      (suzukiDF6D4OddResidualTailMainEntryInterval i j)).add
    (RationalInterval.scale 21
      (suzukiDF6D4OddResidualRemainderTailEntryInterval i j))

theorem suzukiDF6D4EvenResidualRemainderTailEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenResidualRemainderTailEntryInterval i j).Contains
      (suzukiDF6D4EvenResidualRemainderTailMatrix i j) := by
  unfold suzukiDF6D4EvenResidualRemainderTailEntryInterval
    suzukiDF6D4EvenResidualRemainderTailMatrix
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  convert RationalInterval.contains_add
    (RationalInterval.contains_scale (11 / 10 : Rat)
      (suzukiDF6D4EvenStructuredTailEntryInterval_contains i j))
    (RationalInterval.contains_scale 11
      (suzukiDF6D4EvenGeometricTailEntryInterval_contains i j)) using 1 <;>
    norm_num

theorem suzukiDF6D4OddResidualRemainderTailEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddResidualRemainderTailEntryInterval i j).Contains
      (suzukiDF6D4OddResidualRemainderTailMatrix i j) := by
  unfold suzukiDF6D4OddResidualRemainderTailEntryInterval
    suzukiDF6D4OddResidualRemainderTailMatrix
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  convert RationalInterval.contains_add
    (RationalInterval.contains_scale (11 / 10 : Rat)
      (suzukiDF6D4OddStructuredTailEntryInterval_contains i j))
    (RationalInterval.contains_scale 11
      (suzukiDF6D4OddGeometricTailEntryInterval_contains i j)) using 1 <;>
    norm_num

theorem suzukiDF6D4EvenAnalyticTailEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenAnalyticTailEntryInterval i j).Contains
      (suzukiDF6D4EvenAnalyticTailMatrix i j) := by
  unfold suzukiDF6D4EvenAnalyticTailEntryInterval
    suzukiDF6D4EvenAnalyticTailMatrix
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  convert RationalInterval.contains_add
    (RationalInterval.contains_scale (21 / 20 : Rat)
      (suzukiDF6D4EvenResidualTailMainEntryInterval_contains i j))
    (RationalInterval.contains_scale 21
      (suzukiDF6D4EvenResidualRemainderTailEntryInterval_contains i j)) using 1 <;>
    norm_num

theorem suzukiDF6D4OddAnalyticTailEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddAnalyticTailEntryInterval i j).Contains
      (suzukiDF6D4OddAnalyticTailMatrix i j) := by
  unfold suzukiDF6D4OddAnalyticTailEntryInterval
    suzukiDF6D4OddAnalyticTailMatrix
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  convert RationalInterval.contains_add
    (RationalInterval.contains_scale (21 / 20 : Rat)
      (suzukiDF6D4OddResidualTailMainEntryInterval_contains i j))
    (RationalInterval.contains_scale 21
      (suzukiDF6D4OddResidualRemainderTailEntryInterval_contains i j)) using 1 <;>
    norm_num

theorem suzukiDF6D4EvenResidualRemainderTailMatrix_quadratic
    (x : Fin 45 → Real) :
    dotProduct x
        (Matrix.mulVec suzukiDF6D4EvenResidualRemainderTailMatrix x) =
      (11 / 10 : Real) *
          (15 * ∑ index : Fin 15,
            suzukiDF6D4EvenStructuredTailContributionBound index x) +
        11 * ((∑ i : Fin 45, suzukiDF6D4EvenResidualGeometricEnvelope i) *
            (1 / (21 * (600 : Real) ^ 21)) *
          ∑ i : Fin 45,
            suzukiDF6D4EvenResidualGeometricEnvelope i * (x i) ^ 2) := by
  unfold suzukiDF6D4EvenResidualRemainderTailMatrix
  rw [Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul,
    suzukiDF6D4EvenStructuredTailMatrix_quadratic,
    suzukiDF6D4EvenGeometricTailMatrix_quadratic]
  simp only [smul_eq_mul]

theorem suzukiDF6D4OddResidualRemainderTailMatrix_quadratic
    (x : Fin 44 → Real) :
    dotProduct x
        (Matrix.mulVec suzukiDF6D4OddResidualRemainderTailMatrix x) =
      (11 / 10 : Real) *
          (14 * ∑ index : Fin 14,
            suzukiDF6D4OddStructuredTailContributionBound index x) +
        11 * ((∑ i : Fin 44, suzukiDF6D4OddResidualGeometricEnvelope i) *
            (1 / (21 * (600 : Real) ^ 21)) *
          ∑ i : Fin 44,
            suzukiDF6D4OddResidualGeometricEnvelope i * (x i) ^ 2) := by
  unfold suzukiDF6D4OddResidualRemainderTailMatrix
  rw [Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul,
    suzukiDF6D4OddStructuredTailMatrix_quadratic,
    suzukiDF6D4OddGeometricTailMatrix_quadratic]
  simp only [smul_eq_mul]

theorem suzukiDF6D4EvenAnalyticTailMatrix_quadratic
    (x : Fin 45 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4EvenAnalyticTailMatrix x) =
      (21 / 20 : Real) * suzukiDF6D4EvenResidualTailMainQuadratic x +
        21 * dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenResidualRemainderTailMatrix x) := by
  unfold suzukiDF6D4EvenAnalyticTailMatrix
  rw [Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul,
    suzukiDF6D4EvenResidualTailMainMatrix_quadratic]
  simp only [smul_eq_mul]

theorem suzukiDF6D4OddAnalyticTailMatrix_quadratic
    (x : Fin 44 → Real) :
    dotProduct x (Matrix.mulVec suzukiDF6D4OddAnalyticTailMatrix x) =
      (21 / 20 : Real) * suzukiDF6D4OddResidualTailMainQuadratic x +
        21 * dotProduct x
          (Matrix.mulVec suzukiDF6D4OddResidualRemainderTailMatrix x) := by
  unfold suzukiDF6D4OddAnalyticTailMatrix
  rw [Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul,
    suzukiDF6D4OddResidualTailMainMatrix_quadratic]
  simp only [smul_eq_mul]

/-! ## Matrix forms of the checked component tail bounds -/

theorem suzukiDF6D4EvenStructuredResidualTailQuadratic_le_matrix
    (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i) ^ 2) ≤
      dotProduct x (Matrix.mulVec suzukiDF6D4EvenStructuredTailMatrix x) := by
  rw [suzukiDF6D4EvenStructuredTailMatrix_quadratic]
  exact suzukiDF6D4EvenStructuredResidualTailQuadratic_le x

theorem suzukiDF6D4OddStructuredResidualTailQuadratic_le_matrix
    (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i) ^ 2) ≤
      dotProduct x (Matrix.mulVec suzukiDF6D4OddStructuredTailMatrix x) := by
  rw [suzukiDF6D4OddStructuredTailMatrix_quadratic]
  exact suzukiDF6D4OddStructuredResidualTailQuadratic_le x

theorem suzukiDF6D4EvenResidualGeometricTailQuadratic_le_matrix
    (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i, x i *
        suzukiDF6D4EvenResidualTailRemainder (601 + k) i) ^ 2) ≤
      dotProduct x (Matrix.mulVec suzukiDF6D4EvenGeometricTailMatrix x) := by
  rw [suzukiDF6D4EvenGeometricTailMatrix_quadratic]
  exact suzukiDF6D4EvenResidualGeometricTailQuadratic_le x

theorem suzukiDF6D4OddResidualGeometricTailQuadratic_le_matrix
    (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i, x i *
        suzukiDF6D4OddResidualTailRemainder (601 + k) i) ^ 2) ≤
      dotProduct x (Matrix.mulVec suzukiDF6D4OddGeometricTailMatrix x) := by
  rw [suzukiDF6D4OddGeometricTailMatrix_quadratic]
  exact suzukiDF6D4OddResidualGeometricTailQuadratic_le x

/-! ## Square-series summability bridges -/

theorem suzukiDF6D4TailYoung_summable
    (u v : Nat → Real)
    (hu : Summable fun k => (u k) ^ 2)
    (hv : Summable fun k => (v k) ^ 2) :
    Summable fun k => (u k + v k) ^ 2 := by
  have hmajor : Summable fun k =>
      (2 : Real) * (u k) ^ 2 + 2 * (v k) ^ 2 :=
    (hu.mul_left 2).add (hv.mul_left 2)
  exact hmajor.of_nonneg_of_le (fun k => sq_nonneg _)
    (fun k => by
      have h := suzukiDF6D4YoungSquare_le 1 (u k) (v k) (by norm_num)
      norm_num at h ⊢
      exact h)

theorem suzukiDF6D4TailQuadratic_summable_diagonalEnvelope
    {d : Nat} (r : Nat → Fin d → Real)
    (envelope : Fin d → Real) (weight : Nat → Real)
    (henvelope : ∀ i, 0 ≤ envelope i)
    (hweight : ∀ k, 0 ≤ weight k)
    (hr : ∀ k i, |r k i| ≤ envelope i * weight k)
    (hweightSummable : Summable fun k => (weight k) ^ 2)
    (x : Fin d → Real) :
    Summable fun k => (∑ i, x i * r k i) ^ 2 := by
  let envelopeSum : Real := ∑ i, envelope i
  let weightedSquare : Real := ∑ i, envelope i * (x i) ^ 2
  have hcauchy : (∑ i, envelope i * |x i|) ^ 2 ≤
      envelopeSum * weightedSquare := by
    simpa only [envelopeSum, weightedSquare] using
      suzukiDF6D4WeightedCauchy envelope x henvelope
  have hmode : ∀ k,
      (∑ i, x i * r k i) ^ 2 ≤
        (weight k) ^ 2 * (envelopeSum * weightedSquare) := by
    intro k
    have habs := suzukiDF6D4AbsDotProduct_le
      (r k) envelope x (weight k) (hr k)
    have hsumNonneg : 0 ≤ ∑ i, envelope i * |x i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (henvelope i) (abs_nonneg _)
    have hsquare : (∑ i, x i * r k i) ^ 2 ≤
        ((∑ i, envelope i * |x i|) * weight k) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg hsumNonneg (hweight k))).2 habs
    calc
      (∑ i, x i * r k i) ^ 2 ≤
          ((∑ i, envelope i * |x i|) * weight k) ^ 2 := hsquare
      _ = (∑ i, envelope i * |x i|) ^ 2 * (weight k) ^ 2 := by ring
      _ ≤ (envelopeSum * weightedSquare) * (weight k) ^ 2 :=
        mul_le_mul_of_nonneg_right hcauchy (sq_nonneg _)
      _ = (weight k) ^ 2 * (envelopeSum * weightedSquare) := by ring
  exact (hweightSummable.mul_right
      (envelopeSum * weightedSquare)).of_nonneg_of_le
    (fun k => sq_nonneg _) hmode

theorem suzukiDF6D4FrozenOrderElevenWeightSquare_summable :
    Summable fun k : Nat =>
      (1 / (((601 + k : Nat) : Real) ^ 11)) ^ 2 := by
  have h := suzukiDF6D4RankOneCoefficientTail_summable
    (d := 1)
    (fun k : Nat => 1 / (((601 + k : Nat) : Real) ^ 11))
    (fun _ : Fin 1 => (1 : Real)) (fun _ : Fin 1 => (1 : Real))
    1 11 (by norm_num) (by norm_num) (by
      intro k
      rw [abs_of_nonneg (by positivity)])
  simpa using h

theorem suzukiDF6D4EvenResidualGeometricTailQuadratic_summable
    (x : Fin 45 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i *
        suzukiDF6D4EvenResidualTailRemainder (601 + k) i) ^ 2 := by
  apply suzukiDF6D4TailQuadratic_summable_diagonalEnvelope
    (fun k i => suzukiDF6D4EvenResidualTailRemainder (601 + k) i)
    suzukiDF6D4EvenResidualGeometricEnvelope
    (fun k => 1 / (((601 + k : Nat) : Real) ^ 11))
  · exact suzukiDF6D4EvenResidualGeometricEnvelope_nonneg
  · intro k
    positivity
  · intro k i
    simpa only [div_eq_mul_inv, one_mul] using
      suzukiDF6D4EvenResidualTailRemainder_abs_le (601 + k) (by omega) i
  · exact suzukiDF6D4FrozenOrderElevenWeightSquare_summable

theorem suzukiDF6D4OddResidualGeometricTailQuadratic_summable
    (x : Fin 44 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i *
        suzukiDF6D4OddResidualTailRemainder (601 + k) i) ^ 2 := by
  apply suzukiDF6D4TailQuadratic_summable_diagonalEnvelope
    (fun k i => suzukiDF6D4OddResidualTailRemainder (601 + k) i)
    suzukiDF6D4OddResidualGeometricEnvelope
    (fun k => 1 / (((601 + k : Nat) : Real) ^ 11))
  · exact suzukiDF6D4OddResidualGeometricEnvelope_nonneg
  · intro k
    positivity
  · intro k i
    simpa only [div_eq_mul_inv, one_mul] using
      suzukiDF6D4OddResidualTailRemainder_abs_le (601 + k) (by omega) i
  · exact suzukiDF6D4FrozenOrderElevenWeightSquare_summable

theorem suzukiDF6D4_dot_fin_sum_sq_le
    {m d : Nat} (x : Fin d → Real) (vectors : Fin m → Fin d → Real) :
    (∑ i, x i * ∑ index, vectors index i) ^ 2 ≤
      (m : Real) * ∑ index, (∑ i, x i * vectors index i) ^ 2 := by
  have hdot :
      (∑ i, x i * ∑ index, vectors index i) =
        ∑ index, ∑ i, x i * vectors index i := by
    calc
      (∑ i, x i * ∑ index, vectors index i) =
          ∑ i, ∑ index, x i * vectors index i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ index, ∑ i, x i * vectors index i := Finset.sum_comm
  rw [hdot]
  simpa using
    (sq_sum_le_card_mul_sum_sq
      (s := Finset.univ)
      (f := fun index : Fin m => ∑ i, x i * vectors index i))

theorem suzukiDF6D4EvenStructuredResidualTailQuadratic_summable
    (x : Fin 45 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i) ^ 2 := by
  let term := fun index : Fin 15 => fun k : Nat =>
    (∑ i, x i *
      suzukiDF6D4EvenStructuredTailContribution index k i) ^ 2
  have hterm : ∀ index : Fin 15, Summable (term index) := fun index =>
    suzukiDF6D4EvenStructuredTailContribution_summable index x
  have hsum : Summable fun k : Nat => ∑ index : Fin 15, term index k := by
    simpa only [Finset.mem_univ, forall_const] using
      (summable_sum (s := Finset.univ) (fun index _ => hterm index))
  have hmajor : Summable fun k : Nat =>
      (15 : Real) * ∑ index : Fin 15, term index k := hsum.mul_left 15
  apply hmajor.of_nonneg_of_le (fun k => sq_nonneg _)
  intro k
  unfold suzukiDF6D4EvenStructuredResidualTail
  exact suzukiDF6D4_dot_fin_sum_sq_le x
    (fun index i => suzukiDF6D4EvenStructuredTailContribution index k i)

theorem suzukiDF6D4OddStructuredResidualTailQuadratic_summable
    (x : Fin 44 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i) ^ 2 := by
  let term := fun index : Fin 14 => fun k : Nat =>
    (∑ i, x i *
      suzukiDF6D4OddStructuredTailContribution index k i) ^ 2
  have hterm : ∀ index : Fin 14, Summable (term index) := fun index =>
    suzukiDF6D4OddStructuredTailContribution_summable index x
  have hsum : Summable fun k : Nat => ∑ index : Fin 14, term index k := by
    simpa only [Finset.mem_univ, forall_const] using
      (summable_sum (s := Finset.univ) (fun index _ => hterm index))
  have hmajor : Summable fun k : Nat =>
      (14 : Real) * ∑ index : Fin 14, term index k := hsum.mul_left 14
  apply hmajor.of_nonneg_of_le (fun k => sq_nonneg _)
  intro k
  unfold suzukiDF6D4OddStructuredResidualTail
  exact suzukiDF6D4_dot_fin_sum_sq_le x
    (fun index i => suzukiDF6D4OddStructuredTailContribution index k i)

theorem suzukiDF6D4EvenTailMainComparisonCoefficient_abs_le (k : Nat) :
    |suzukiDF6D4EvenTailMainComparisonCoefficient k| ≤
      (Real.pi⁻¹ * (Real.pi / 2)) / ((601 + k : Nat) : Real) := by
  have hdenom : 0 ≤ ((601 + k : Nat) : Real) := by positivity
  unfold suzukiDF6D4EvenTailMainComparisonCoefficient
  rw [abs_div, abs_mul, abs_mul, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos, abs_neg, abs_div,
    abs_of_pos Real.pi_pos, abs_of_nonneg hdenom]
  norm_num

theorem suzukiDF6D4EvenTailMainPrimeCoefficient_abs_le (k : Nat) :
    |suzukiDF6D4EvenTailMainPrimeCoefficient k| ≤
      (Real.pi⁻¹ * (Real.sqrt 2 * Real.log 2)) /
        ((601 + k : Nat) : Real) := by
  have htransform := suzukiDF6D4PrimeSineTransform_abs_le (601 + k)
  have hdenom : 0 ≤ ((601 + k : Nat) : Real) := by positivity
  unfold suzukiDF6D4EvenTailMainPrimeCoefficient
  rw [abs_div, abs_mul, abs_mul, suzukiDF6D4TailParity_real_abs,
    one_mul, abs_inv, abs_of_pos Real.pi_pos, abs_of_nonneg hdenom]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htransform
      (inv_nonneg.mpr Real.pi_pos.le)) hdenom

theorem suzukiDF6D4EvenResidualTailMainQuadratic_summable
    (x : Fin 45 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i * suzukiDF6D4EvenResidualTailMain (601 + k) i) ^ 2 := by
  let comparison := fun k : Nat =>
    (∑ i, x i * suzukiDF6D4EvenResidualTailTransformMoment 0 i) *
      suzukiDF6D4EvenTailMainComparisonCoefficient k
  let prime := fun k : Nat =>
    (∑ i, x i * suzukiDF6D4EvenTailTransformMoment 0
      (suzukiDF6D4EvenLowMode i)) *
      suzukiDF6D4EvenTailMainPrimeCoefficient k
  have hcomparison : Summable fun k => (comparison k) ^ 2 := by
    exact suzukiDF6D4RankOneCoefficientTail_summable
      suzukiDF6D4EvenTailMainComparisonCoefficient
      (suzukiDF6D4EvenResidualTailTransformMoment 0) x
      (Real.pi⁻¹ * (Real.pi / 2)) 1
      (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
        (div_nonneg Real.pi_pos.le (by norm_num)))
      (by norm_num) (fun k => by
        simpa using suzukiDF6D4EvenTailMainComparisonCoefficient_abs_le k)
  have hprime : Summable fun k => (prime k) ^ 2 := by
    exact suzukiDF6D4RankOneCoefficientTail_summable
      suzukiDF6D4EvenTailMainPrimeCoefficient
      (fun i => suzukiDF6D4EvenTailTransformMoment 0
        (suzukiDF6D4EvenLowMode i)) x
      (Real.pi⁻¹ * (Real.sqrt 2 * Real.log 2)) 1
      (mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
        (mul_nonneg (Real.sqrt_nonneg 2)
          (Real.log_nonneg (by norm_num))))
      (by norm_num) (fun k => by
        simpa using suzukiDF6D4EvenTailMainPrimeCoefficient_abs_le k)
  have hadd := suzukiDF6D4TailYoung_summable comparison prime
    hcomparison hprime
  refine hadd.congr fun k => ?_
  have hdot :
      (∑ i, x i * suzukiDF6D4EvenResidualTailMain (601 + k) i) =
        comparison k + prime k := by
    simp_rw [suzukiDF6D4EvenResidualTailMain_eq_contributions, mul_add]
    rw [Finset.sum_add_distrib]
    simp only [comparison, prime]
    congr 1 <;> rw [Finset.sum_mul] <;>
      apply Finset.sum_congr rfl <;> intro i _ <;> ring
  rw [hdot]

theorem suzukiDF6D4OddResidualTailMainQuadratic_summable
    (x : Fin 44 → Real) :
    Summable fun k : Nat =>
      (∑ i, x i * suzukiDF6D4OddResidualTailMain (601 + k) i) ^ 2 := by
  have h := suzukiDF6D4TailFixedRankOne_summable
    (suzukiDF6D4OddResidualTailFixedMoment 0) x 1 (by norm_num)
  refine h.congr fun k => ?_
  have hdot :
      (∑ i, x i * suzukiDF6D4OddResidualTailMain (601 + k) i) =
        (∑ i, x i * suzukiDF6D4OddResidualTailFixedMoment 0 i) *
          suzukiDF6D4TailFixedCoefficient 1 k := by
    simp_rw [suzukiDF6D4OddResidualTailMain_eq_contribution]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot]

/-! ## End-to-end Young assembly for the actual residual columns -/

theorem suzukiDF6D4EvenResidualRemainderTailMatrix_quadratic_linear
    (x : Fin 45 → Real) :
    dotProduct x
        (Matrix.mulVec suzukiDF6D4EvenResidualRemainderTailMatrix x) =
      (11 / 10 : Real) *
          dotProduct x (Matrix.mulVec suzukiDF6D4EvenStructuredTailMatrix x) +
        11 * dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenGeometricTailMatrix x) := by
  unfold suzukiDF6D4EvenResidualRemainderTailMatrix
  rw [Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]

theorem suzukiDF6D4OddResidualRemainderTailMatrix_quadratic_linear
    (x : Fin 44 → Real) :
    dotProduct x
        (Matrix.mulVec suzukiDF6D4OddResidualRemainderTailMatrix x) =
      (11 / 10 : Real) *
          dotProduct x (Matrix.mulVec suzukiDF6D4OddStructuredTailMatrix x) +
        11 * dotProduct x
          (Matrix.mulVec suzukiDF6D4OddGeometricTailMatrix x) := by
  unfold suzukiDF6D4OddResidualRemainderTailMatrix
  rw [Matrix.add_mulVec, dotProduct_add,
    Matrix.smul_mulVec, dotProduct_smul,
    Matrix.smul_mulVec, dotProduct_smul]
  simp only [smul_eq_mul]

theorem suzukiDF6D4EvenResidualTailQuadratic_le_analyticMatrix
    (x : Fin 45 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4EvenResidualColumn (601 + k) i) ^ 2) ≤
      dotProduct x (Matrix.mulVec suzukiDF6D4EvenAnalyticTailMatrix x) := by
  let main := fun k : Nat =>
    ∑ i, x i * suzukiDF6D4EvenResidualTailMain (601 + k) i
  let structured := fun k : Nat =>
    ∑ i, x i * suzukiDF6D4EvenStructuredResidualTail k i
  let geometric := fun k : Nat =>
    ∑ i, x i * suzukiDF6D4EvenResidualTailRemainder (601 + k) i
  have hcolumn : ∀ k : Nat,
      (∑ i, x i * suzukiDF6D4EvenResidualColumn (601 + k) i) =
        main k + (structured k + geometric k) := by
    intro k
    calc
      (∑ i, x i * suzukiDF6D4EvenResidualColumn (601 + k) i) =
          ∑ i, x i *
            (suzukiDF6D4EvenResidualTailPrefix (601 + k) i +
              suzukiDF6D4EvenResidualTailRemainder (601 + k) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [suzukiDF6D4EvenResidualColumn_eq_tailPrefix_add_remainder
          (601 + k) (by omega) i]
      _ = ∑ i, x i *
            ((suzukiDF6D4EvenResidualTailMain (601 + k) i +
                suzukiDF6D4EvenStructuredResidualTail k i) +
              suzukiDF6D4EvenResidualTailRemainder (601 + k) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [suzukiDF6D4EvenResidualTailPrefix_eq_main_add_structured k i]
      _ = main k + (structured k + geometric k) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        simp only [main, structured, geometric]
        ring
  have hmain : Summable fun k => (main k) ^ 2 := by
    simpa only [main] using
      suzukiDF6D4EvenResidualTailMainQuadratic_summable x
  have hstructured : Summable fun k => (structured k) ^ 2 := by
    simpa only [structured] using
      suzukiDF6D4EvenStructuredResidualTailQuadratic_summable x
  have hgeometric : Summable fun k => (geometric k) ^ 2 := by
    simpa only [geometric] using
      suzukiDF6D4EvenResidualGeometricTailQuadratic_summable x
  have hremainder : Summable fun k =>
      (structured k + geometric k) ^ 2 :=
    suzukiDF6D4TailYoung_summable structured geometric
      hstructured hgeometric
  have hstructuredBound :
      (∑' k : Nat, (structured k) ^ 2) ≤
        dotProduct x (Matrix.mulVec suzukiDF6D4EvenStructuredTailMatrix x) := by
    simpa only [structured] using
      suzukiDF6D4EvenStructuredResidualTailQuadratic_le_matrix x
  have hgeometricBound :
      (∑' k : Nat, (geometric k) ^ 2) ≤
        dotProduct x (Matrix.mulVec suzukiDF6D4EvenGeometricTailMatrix x) := by
    simpa only [geometric] using
      suzukiDF6D4EvenResidualGeometricTailQuadratic_le_matrix x
  have hremainderBound :
      (∑' k : Nat, (structured k + geometric k) ^ 2) ≤
        dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenResidualRemainderTailMatrix x) := by
    calc
      (∑' k : Nat, (structured k + geometric k) ^ 2) ≤
          (11 / 10 : Real) * (∑' k : Nat, (structured k) ^ 2) +
            11 * (∑' k : Nat, (geometric k) ^ 2) :=
        suzukiDF6D4TailYoungOneTenth_le structured geometric
          hstructured hgeometric
      _ ≤ (11 / 10 : Real) *
            dotProduct x
              (Matrix.mulVec suzukiDF6D4EvenStructuredTailMatrix x) +
          11 * dotProduct x
            (Matrix.mulVec suzukiDF6D4EvenGeometricTailMatrix x) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hstructuredBound (by norm_num))
          (mul_le_mul_of_nonneg_left hgeometricBound (by norm_num))
      _ = dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenResidualRemainderTailMatrix x) :=
        (suzukiDF6D4EvenResidualRemainderTailMatrix_quadratic_linear x).symm
  have hmainEq :
      (∑' k : Nat, (main k) ^ 2) =
        suzukiDF6D4EvenResidualTailMainQuadratic x := by
    simpa only [main] using suzukiDF6D4EvenResidualTailMainQuadratic_eq x
  calc
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4EvenResidualColumn (601 + k) i) ^ 2) =
        ∑' k : Nat, (main k + (structured k + geometric k)) ^ 2 :=
      tsum_congr fun k => by rw [hcolumn k]
    _ ≤ (21 / 20 : Real) * (∑' k : Nat, (main k) ^ 2) +
        21 * (∑' k : Nat, (structured k + geometric k) ^ 2) :=
      suzukiDF6D4TailYoungOneTwentieth_le main
        (fun k => structured k + geometric k) hmain hremainder
    _ ≤ (21 / 20 : Real) * suzukiDF6D4EvenResidualTailMainQuadratic x +
        21 * dotProduct x
          (Matrix.mulVec suzukiDF6D4EvenResidualRemainderTailMatrix x) := by
      rw [hmainEq]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hremainderBound
          (show (0 : Real) ≤ 21 by norm_num))
    _ = dotProduct x
        (Matrix.mulVec suzukiDF6D4EvenAnalyticTailMatrix x) :=
      (suzukiDF6D4EvenAnalyticTailMatrix_quadratic x).symm

theorem suzukiDF6D4OddResidualTailQuadratic_le_analyticMatrix
    (x : Fin 44 → Real) :
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4OddResidualColumn (601 + k) i) ^ 2) ≤
      dotProduct x (Matrix.mulVec suzukiDF6D4OddAnalyticTailMatrix x) := by
  let main := fun k : Nat =>
    ∑ i, x i * suzukiDF6D4OddResidualTailMain (601 + k) i
  let structured := fun k : Nat =>
    ∑ i, x i * suzukiDF6D4OddStructuredResidualTail k i
  let geometric := fun k : Nat =>
    ∑ i, x i * suzukiDF6D4OddResidualTailRemainder (601 + k) i
  have hcolumn : ∀ k : Nat,
      (∑ i, x i * suzukiDF6D4OddResidualColumn (601 + k) i) =
        main k + (structured k + geometric k) := by
    intro k
    calc
      (∑ i, x i * suzukiDF6D4OddResidualColumn (601 + k) i) =
          ∑ i, x i *
            (suzukiDF6D4OddResidualTailPrefix (601 + k) i +
              suzukiDF6D4OddResidualTailRemainder (601 + k) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [suzukiDF6D4OddResidualColumn_eq_tailPrefix_add_remainder
          (601 + k) (by omega) i]
      _ = ∑ i, x i *
            ((suzukiDF6D4OddResidualTailMain (601 + k) i +
                suzukiDF6D4OddStructuredResidualTail k i) +
              suzukiDF6D4OddResidualTailRemainder (601 + k) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [suzukiDF6D4OddResidualTailPrefix_eq_main_add_structured k i]
      _ = main k + (structured k + geometric k) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        simp only [main, structured, geometric]
        ring
  have hmain : Summable fun k => (main k) ^ 2 := by
    simpa only [main] using
      suzukiDF6D4OddResidualTailMainQuadratic_summable x
  have hstructured : Summable fun k => (structured k) ^ 2 := by
    simpa only [structured] using
      suzukiDF6D4OddStructuredResidualTailQuadratic_summable x
  have hgeometric : Summable fun k => (geometric k) ^ 2 := by
    simpa only [geometric] using
      suzukiDF6D4OddResidualGeometricTailQuadratic_summable x
  have hremainder : Summable fun k =>
      (structured k + geometric k) ^ 2 :=
    suzukiDF6D4TailYoung_summable structured geometric
      hstructured hgeometric
  have hstructuredBound :
      (∑' k : Nat, (structured k) ^ 2) ≤
        dotProduct x (Matrix.mulVec suzukiDF6D4OddStructuredTailMatrix x) := by
    simpa only [structured] using
      suzukiDF6D4OddStructuredResidualTailQuadratic_le_matrix x
  have hgeometricBound :
      (∑' k : Nat, (geometric k) ^ 2) ≤
        dotProduct x (Matrix.mulVec suzukiDF6D4OddGeometricTailMatrix x) := by
    simpa only [geometric] using
      suzukiDF6D4OddResidualGeometricTailQuadratic_le_matrix x
  have hremainderBound :
      (∑' k : Nat, (structured k + geometric k) ^ 2) ≤
        dotProduct x
          (Matrix.mulVec suzukiDF6D4OddResidualRemainderTailMatrix x) := by
    calc
      (∑' k : Nat, (structured k + geometric k) ^ 2) ≤
          (11 / 10 : Real) * (∑' k : Nat, (structured k) ^ 2) +
            11 * (∑' k : Nat, (geometric k) ^ 2) :=
        suzukiDF6D4TailYoungOneTenth_le structured geometric
          hstructured hgeometric
      _ ≤ (11 / 10 : Real) *
            dotProduct x
              (Matrix.mulVec suzukiDF6D4OddStructuredTailMatrix x) +
          11 * dotProduct x
            (Matrix.mulVec suzukiDF6D4OddGeometricTailMatrix x) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hstructuredBound (by norm_num))
          (mul_le_mul_of_nonneg_left hgeometricBound (by norm_num))
      _ = dotProduct x
          (Matrix.mulVec suzukiDF6D4OddResidualRemainderTailMatrix x) :=
        (suzukiDF6D4OddResidualRemainderTailMatrix_quadratic_linear x).symm
  have hmainEq :
      (∑' k : Nat, (main k) ^ 2) =
        suzukiDF6D4OddResidualTailMainQuadratic x := by
    simpa only [main] using suzukiDF6D4OddResidualTailMainQuadratic_eq x
  calc
    (∑' k : Nat,
      (∑ i, x i * suzukiDF6D4OddResidualColumn (601 + k) i) ^ 2) =
        ∑' k : Nat, (main k + (structured k + geometric k)) ^ 2 :=
      tsum_congr fun k => by rw [hcolumn k]
    _ ≤ (21 / 20 : Real) * (∑' k : Nat, (main k) ^ 2) +
        21 * (∑' k : Nat, (structured k + geometric k) ^ 2) :=
      suzukiDF6D4TailYoungOneTwentieth_le main
        (fun k => structured k + geometric k) hmain hremainder
    _ ≤ (21 / 20 : Real) * suzukiDF6D4OddResidualTailMainQuadratic x +
        21 * dotProduct x
          (Matrix.mulVec suzukiDF6D4OddResidualRemainderTailMatrix x) := by
      rw [hmainEq]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hremainderBound
          (show (0 : Real) ≤ 21 by norm_num))
    _ = dotProduct x
        (Matrix.mulVec suzukiDF6D4OddAnalyticTailMatrix x) :=
      (suzukiDF6D4OddAnalyticTailMatrix_quadratic x).symm

end

end RiemannHypothesisProject.Experiments.M100
