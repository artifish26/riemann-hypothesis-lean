import RiemannHypothesisProject.Experiments.M100.FixedGridIntervalArithmetic
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonTable

/-!
# Fixed-grid admission prototype for the even `(0,0)` target cell

This module exercises one complete certificate cell.  It uses the checked
frozen comparison-transform table, computes the solve and explicit-residual
columns once, proves that the resulting fixed-grid interval contains the live
real target entry, and checks inclusion in the generated certificate grid.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def suzukiDF6D4FixedGridDenominator : Nat :=
  1000000000000000000

theorem suzukiDF6D4FixedGridDenominator_pos :
    0 < suzukiDF6D4FixedGridDenominator := by
  norm_num [suzukiDF6D4FixedGridDenominator]

def suzukiDF6D4TabulatedComparisonEvenOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4TabulatedComparisonSineTransformInterval right).sub
        (suzukiDF6D4TabulatedComparisonSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4TabulatedComparisonSineTransformInterval left).add
        (suzukiDF6D4TabulatedComparisonSineTransformInterval right)))

def suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  (suzukiDF6D4EvenConvolutionPrefactorInterval left right).mulLeftNonneg
    (suzukiDF6D4TabulatedComparisonEvenOffDiagonalBracketInterval left right)

theorem suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
    (left right : Nat) (hleftPos : 0 < left) (hleftRight : left < right)
    (hright : right <= 602) :
    (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval left right).Contains
      (suzukiDF6D4ComparisonEvenOffDiagonal left right) := by
  have hRightTransform :=
    suzukiDF6D4TabulatedComparisonSineTransformInterval_contains right
      (by omega) hright
  have hLeftTransform :=
    suzukiDF6D4TabulatedComparisonSineTransformInterval_contains left
      (by omega) (by omega)
  have hDifference := RationalInterval.contains_sub hRightTransform hLeftTransform
  have hTotal := RationalInterval.contains_add hLeftTransform hRightTransform
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  have hBracket := RationalInterval.contains_add
    (RationalInterval.contains_scale differenceCoefficient hDifference)
    (RationalInterval.contains_scale totalCoefficient hTotal)
  have hProduct := RationalInterval.contains_mulLeftNonneg
    (suzukiDF6D4EvenConvolutionPrefactorInterval_lower_nonneg left right)
    (suzukiDF6D4EvenConvolutionPrefactorInterval_contains left right)
    hBracket
  unfold suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
    suzukiDF6D4TabulatedComparisonEvenOffDiagonalBracketInterval
    suzukiDF6D4ComparisonEvenOffDiagonal
  dsimp only [difference, differenceCoefficient, totalCoefficient] at hProduct ⊢
  exact hProduct

def suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval
    (i j : Fin 256) : RationalInterval :=
  if i = j then
    suzukiDF6D4TabulatedEvenComparisonDiagonalInterval
      (suzukiDF6D4GalerkinMode i)
  else if i.val < j.val then
    suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode i) (suzukiDF6D4GalerkinMode j)
  else
    suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode j) (suzukiDF6D4GalerkinMode i)

theorem suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains
    (i j : Fin 256) :
    (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval i j).Contains
      (suzukiDF6D4EvenComparisonGalerkinEntry i j) := by
  by_cases heq : i = j
  · subst j
    simp only [suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval,
      suzukiDF6D4EvenComparisonGalerkinEntry, if_pos]
    exact suzukiDF6D4TabulatedEvenComparisonDiagonalInterval_contains
      (suzukiDF6D4GalerkinMode i)
      (by simp [suzukiDF6D4GalerkinMode])
      (by have := i.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
  · by_cases hlt : i.val < j.val
    · simp only [suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval,
        suzukiDF6D4EvenComparisonGalerkinEntry, heq, hlt, if_false, if_true]
      exact suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4GalerkinMode])
        (by simp [suzukiDF6D4GalerkinMode]; omega)
        (by have := j.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
    · have hji : j.val < i.val := by
        have hne : i.val ≠ j.val := fun h => heq (Fin.ext h)
        omega
      simp only [suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval,
        suzukiDF6D4EvenComparisonGalerkinEntry, heq, hlt, if_false]
      exact suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4GalerkinMode])
        (by simp [suzukiDF6D4GalerkinMode]; omega)
        (by have := i.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)

def suzukiDF6D4EvenFixedGridSolveResidual
    (j : Fin 256) (i : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenCompleteCrossEntryInterval i j)).sub
    (FixedGridInterval.scaleFinSum
      (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
      (fun k : Fin 256 => FixedGridInterval.ofRationalInterval
        suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval j k)))

theorem suzukiDF6D4EvenFixedGridSolveResidual_contains
    (j : Fin 256) (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenFixedGridSolveResidual j i)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual j i) := by
  exact FixedGridInterval.contains_sub
    (FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i j))
    (by
      simpa only [mul_comm] using
        FixedGridInterval.contains_scaleFinSum
          (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
          (I := fun k : Fin 256 => FixedGridInterval.ofRationalInterval
            suzukiDF6D4FixedGridDenominator
            (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval j k))
          (x := fun k : Fin 256 =>
            suzukiDF6D4EvenComparisonGalerkinEntry j k)
          suzukiDF6D4FixedGridDenominator_pos
          (fun k => FixedGridInterval.contains_ofRationalInterval
            suzukiDF6D4FixedGridDenominator_pos
            (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains j k)))

def suzukiDF6D4EvenFixedGridResidualColumn
    (mode : Nat) (i : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FullEvenOffDiagonalInterval
        (suzukiDF6D4EvenLowMode i) mode)).sub
    (FixedGridInterval.scaleFinSum
      (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
      (fun k : Fin 256 => FixedGridInterval.ofRationalInterval
        suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) mode)))

theorem suzukiDF6D4EvenFixedGridResidualColumn_contains
    (mode : Nat) (hlower : 301 <= mode) (hupper : mode <= 602)
    (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenFixedGridResidualColumn mode i)).Contains
        (suzukiDF6D4EvenResidualColumn mode i) := by
  exact FixedGridInterval.contains_sub
    (FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains _ _
        (by simp [suzukiDF6D4EvenLowMode]; omega) hupper))
    (FixedGridInterval.contains_scaleFinSum
      (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
      (I := fun k : Fin 256 => FixedGridInterval.ofRationalInterval
        suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) mode))
      (x := fun k : Fin 256 =>
        suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) mode)
      suzukiDF6D4FixedGridDenominator_pos
      (fun k => FixedGridInterval.contains_ofRationalInterval
        suzukiDF6D4FixedGridDenominator_pos
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains _ _
          (by simp [suzukiDF6D4GalerkinMode])
          (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
          hupper)))

def suzukiDF6D4EvenFixedGridSolveColumn00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => suzukiDF6D4EvenFixedGridSolveResidual k 0

def suzukiDF6D4EvenFixedGridResidualColumn00 : Array FixedGridInterval :=
  Array.ofFn fun r : Fin 300 =>
    suzukiDF6D4EvenFixedGridResidualColumn (301 + r.val) 0

def suzukiDF6D4FixedGridArrayEntry {n : Nat}
    (data : Array FixedGridInterval) (i : Fin n) : FixedGridInterval :=
  data[i.val]!

theorem suzukiDF6D4EvenFixedGridSolveColumn00_entry
    (k : Fin 256) :
    suzukiDF6D4FixedGridArrayEntry
        suzukiDF6D4EvenFixedGridSolveColumn00 k =
      suzukiDF6D4EvenFixedGridSolveResidual k 0 := by
  simp [suzukiDF6D4FixedGridArrayEntry,
    suzukiDF6D4EvenFixedGridSolveColumn00, k.isLt]

theorem suzukiDF6D4EvenFixedGridResidualColumn00_entry
    (r : Fin 300) :
    suzukiDF6D4FixedGridArrayEntry
        suzukiDF6D4EvenFixedGridResidualColumn00 r =
      suzukiDF6D4EvenFixedGridResidualColumn (301 + r.val) 0 := by
  simp [suzukiDF6D4FixedGridArrayEntry,
    suzukiDF6D4EvenFixedGridResidualColumn00, r.isLt]

def suzukiDF6D4EvenFixedGridGalerkinBase00 : FixedGridInterval :=
  (FixedGridInterval.scaleFinSum
    (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k 0)
    (fun k : Fin 256 => FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenCompleteCrossEntryInterval 0 k))).add
  (FixedGridInterval.scaleFinSum
    (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k 0)
    (fun k : Fin 256 => suzukiDF6D4FixedGridArrayEntry
      suzukiDF6D4EvenFixedGridSolveColumn00 k))

theorem suzukiDF6D4EvenFixedGridGalerkinBase00_contains :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      suzukiDF6D4EvenFixedGridGalerkinBase00).Contains
        (suzukiDF6D4EvenGalerkinBaseEntry 0 0) := by
  have hcross := FixedGridInterval.contains_scaleFinSum
    (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k 0)
    (I := fun k : Fin 256 => FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenCompleteCrossEntryInterval 0 k))
    (x := fun k : Fin 256 => suzukiDF6D4EvenCompleteCrossEntry 0 k)
    suzukiDF6D4FixedGridDenominator_pos
    (fun k : Fin 256 => FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains 0 k))
  have hsolve := FixedGridInterval.contains_scaleFinSum
    (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k 0)
    (I := fun k : Fin 256 => suzukiDF6D4FixedGridArrayEntry
      suzukiDF6D4EvenFixedGridSolveColumn00 k)
    (x := fun k : Fin 256 => suzukiDF6D4EvenGalerkinSolveResidual k 0)
    suzukiDF6D4FixedGridDenominator_pos
    (fun k : Fin 256 => by
      rw [suzukiDF6D4EvenFixedGridSolveColumn00_entry]
      exact suzukiDF6D4EvenFixedGridSolveResidual_contains k 0)
  unfold suzukiDF6D4EvenFixedGridGalerkinBase00
  unfold suzukiDF6D4EvenGalerkinBaseEntry
  simpa only [Finset.sum_add_distrib, mul_comm] using
    FixedGridInterval.contains_add hcross hsolve

def suzukiDF6D4EvenFixedGridFiniteResidualGram00 : FixedGridInterval :=
  (FixedGridInterval.finSum fun k : Fin 256 =>
    FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridArrayEntry
        suzukiDF6D4EvenFixedGridSolveColumn00 k)
      (suzukiDF6D4FixedGridArrayEntry
        suzukiDF6D4EvenFixedGridSolveColumn00 k)).add
  (FixedGridInterval.finSum fun r : Fin 300 =>
    FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridArrayEntry
        suzukiDF6D4EvenFixedGridResidualColumn00 r)
      (suzukiDF6D4FixedGridArrayEntry
        suzukiDF6D4EvenFixedGridResidualColumn00 r))

theorem suzukiDF6D4EvenFixedGridFiniteResidualGram00_contains :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      suzukiDF6D4EvenFixedGridFiniteResidualGram00).Contains
        (suzukiDF6D4EvenFiniteResidualGramEntry 0 0) := by
  have hsolve := FixedGridInterval.contains_finSum
    (I := fun k : Fin 256 =>
      FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridArrayEntry
          suzukiDF6D4EvenFixedGridSolveColumn00 k)
        (suzukiDF6D4FixedGridArrayEntry
          suzukiDF6D4EvenFixedGridSolveColumn00 k))
    (x := fun k : Fin 256 =>
      suzukiDF6D4EvenGalerkinSolveResidual k 0 *
        suzukiDF6D4EvenGalerkinSolveResidual k 0)
    (fun k : Fin 256 => FixedGridInterval.contains_mulCentered
      suzukiDF6D4FixedGridDenominator_pos
      (by
        rw [suzukiDF6D4EvenFixedGridSolveColumn00_entry]
        exact suzukiDF6D4EvenFixedGridSolveResidual_contains k 0)
      (by
        rw [suzukiDF6D4EvenFixedGridSolveColumn00_entry]
        exact suzukiDF6D4EvenFixedGridSolveResidual_contains k 0))
  have hresidual := FixedGridInterval.contains_finSum
    (I := fun r : Fin 300 =>
      FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridArrayEntry
          suzukiDF6D4EvenFixedGridResidualColumn00 r)
        (suzukiDF6D4FixedGridArrayEntry
          suzukiDF6D4EvenFixedGridResidualColumn00 r))
    (x := fun r : Fin 300 =>
      suzukiDF6D4EvenResidualColumn (301 + r.val) 0 *
        suzukiDF6D4EvenResidualColumn (301 + r.val) 0)
    (fun r : Fin 300 => FixedGridInterval.contains_mulCentered
      suzukiDF6D4FixedGridDenominator_pos
      (by
        rw [suzukiDF6D4EvenFixedGridResidualColumn00_entry]
        exact suzukiDF6D4EvenFixedGridResidualColumn_contains
          (301 + r.val) (by omega) (by have := r.isLt; omega) 0)
      (by
        rw [suzukiDF6D4EvenFixedGridResidualColumn00_entry]
        exact suzukiDF6D4EvenFixedGridResidualColumn_contains
          (301 + r.val) (by omega) (by have := r.isLt; omega) 0))
  unfold suzukiDF6D4EvenFixedGridFiniteResidualGram00
  unfold suzukiDF6D4EvenFiniteResidualGramEntry
  exact FixedGridInterval.contains_add hsolve hresidual

def suzukiDF6D4EvenFixedGridCouplingUpper00 : FixedGridInterval :=
  (suzukiDF6D4EvenFixedGridGalerkinBase00.add
    (FixedGridInterval.scale (1 / 5)
      suzukiDF6D4EvenFixedGridFiniteResidualGram00)).add
    (FixedGridInterval.scale (1 / 5)
      (FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenAnalyticTailEntryInterval 0 0)))

theorem suzukiDF6D4EvenFixedGridCouplingUpper00_contains :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      suzukiDF6D4EvenFixedGridCouplingUpper00).Contains
        (suzukiDF6D4EvenCouplingUpperMatrix 0 0) := by
  have h := FixedGridInterval.contains_add
    (FixedGridInterval.contains_add
      suzukiDF6D4EvenFixedGridGalerkinBase00_contains
      (FixedGridInterval.contains_scale
        (q := (1 / 5 : Rat))
        suzukiDF6D4FixedGridDenominator_pos
        suzukiDF6D4EvenFixedGridFiniteResidualGram00_contains))
    (FixedGridInterval.contains_scale
      (q := (1 / 5 : Rat))
      suzukiDF6D4FixedGridDenominator_pos
      (FixedGridInterval.contains_ofRationalInterval
        suzukiDF6D4FixedGridDenominator_pos
        (suzukiDF6D4EvenAnalyticTailEntryInterval_contains 0 0)))
  unfold suzukiDF6D4EvenFixedGridCouplingUpper00
  unfold suzukiDF6D4EvenCouplingUpperMatrix
    suzukiDF6D4EvenGalerkinBaseMatrix
    suzukiDF6D4EvenFiniteResidualGramMatrix
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using h

def suzukiDF6D4EvenFixedGridResidualTarget00 : FixedGridInterval :=
  (FixedGridInterval.scale suzukiDF6D4EvenStrictComparisonCoefficient
    (FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenEndpointEntryInterval 0 0))).sub
    suzukiDF6D4EvenFixedGridCouplingUpper00

theorem suzukiDF6D4EvenFixedGridResidualTarget00_contains :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      suzukiDF6D4EvenFixedGridResidualTarget00).Contains
        (suzukiDF6D4EvenResidualCertificateTargetMatrix 0 0) := by
  have h := FixedGridInterval.contains_sub
    (FixedGridInterval.contains_scale
      (q := suzukiDF6D4EvenStrictComparisonCoefficient)
      suzukiDF6D4FixedGridDenominator_pos
      (FixedGridInterval.contains_ofRationalInterval
        suzukiDF6D4FixedGridDenominator_pos
        (suzukiDF6D4EvenEndpointEntryInterval_contains 0 0)))
    suzukiDF6D4EvenFixedGridCouplingUpper00_contains
  unfold suzukiDF6D4EvenFixedGridResidualTarget00
  unfold suzukiDF6D4EvenResidualCertificateTargetMatrix
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using h

theorem suzukiDF6D4EvenFixedGridResidualTarget00_admitted :
    (suzukiDF6D4EvenResidualTargetCertificate.entry 0 0).lower <=
        (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
          suzukiDF6D4EvenFixedGridResidualTarget00).lower /\
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        suzukiDF6D4EvenFixedGridResidualTarget00).upper <=
        (suzukiDF6D4EvenResidualTargetCertificate.entry 0 0).upper := by
  native_decide

theorem suzukiDF6D4EvenResidualTargetCertificateEntry00_contains :
    (suzukiDF6D4EvenResidualTargetCertificate.entry 0 0).Contains
      (suzukiDF6D4EvenResidualCertificateTargetMatrix 0 0) := by
  exact RationalInterval.contains_of_widen
    suzukiDF6D4EvenFixedGridResidualTarget00_admitted.1
    suzukiDF6D4EvenFixedGridResidualTarget00_admitted.2
    suzukiDF6D4EvenFixedGridResidualTarget00_contains

/-! ## Full even-parity cache and admission -/

def suzukiDF6D4EvenFixedGridSolveCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun k : Fin 256 =>
    Array.ofFn fun i : Fin 45 => suzukiDF6D4EvenFixedGridSolveResidual k i

def suzukiDF6D4EvenFixedGridResidualCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun r : Fin 300 =>
    Array.ofFn fun i : Fin 45 =>
      suzukiDF6D4EvenFixedGridResidualColumn (301 + r.val) i

def suzukiDF6D4FixedGridMatrixCacheEntry {rows columns : Nat}
    (data : Array (Array FixedGridInterval))
    (i : Fin rows) (j : Fin columns) : FixedGridInterval :=
  (data[i.val]!)[j.val]!

theorem suzukiDF6D4EvenFixedGridSolveCache_entry
    (k : Fin 256) (i : Fin 45) :
    suzukiDF6D4FixedGridMatrixCacheEntry
        suzukiDF6D4EvenFixedGridSolveCache k i =
      suzukiDF6D4EvenFixedGridSolveResidual k i := by
  simp [suzukiDF6D4FixedGridMatrixCacheEntry,
    suzukiDF6D4EvenFixedGridSolveCache, k.isLt, i.isLt]

theorem suzukiDF6D4EvenFixedGridResidualCache_entry
    (r : Fin 300) (i : Fin 45) :
    suzukiDF6D4FixedGridMatrixCacheEntry
        suzukiDF6D4EvenFixedGridResidualCache r i =
      suzukiDF6D4EvenFixedGridResidualColumn (301 + r.val) i := by
  simp [suzukiDF6D4FixedGridMatrixCacheEntry,
    suzukiDF6D4EvenFixedGridResidualCache, r.isLt, i.isLt]

def suzukiDF6D4EvenFixedGridGalerkinBase
    (i j : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.scaleFinSum
    (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k j)
    (fun k : Fin 256 => FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenCompleteCrossEntryInterval i k))).add
  (FixedGridInterval.scaleFinSum
    (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
    (fun k : Fin 256 => suzukiDF6D4FixedGridMatrixCacheEntry
      suzukiDF6D4EvenFixedGridSolveCache k j))

theorem suzukiDF6D4EvenFixedGridGalerkinBase_contains
    (i j : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenFixedGridGalerkinBase i j)).Contains
        (suzukiDF6D4EvenGalerkinBaseEntry i j) := by
  have hcross := FixedGridInterval.contains_scaleFinSum
    (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k j)
    (I := fun k : Fin 256 => FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenCompleteCrossEntryInterval i k))
    (x := fun k : Fin 256 => suzukiDF6D4EvenCompleteCrossEntry i k)
    suzukiDF6D4FixedGridDenominator_pos
    (fun k => FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i k))
  have hsolve := FixedGridInterval.contains_scaleFinSum
    (q := fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
    (I := fun k : Fin 256 => suzukiDF6D4FixedGridMatrixCacheEntry
      suzukiDF6D4EvenFixedGridSolveCache k j)
    (x := fun k : Fin 256 => suzukiDF6D4EvenGalerkinSolveResidual k j)
    suzukiDF6D4FixedGridDenominator_pos
    (fun k => by
      rw [suzukiDF6D4EvenFixedGridSolveCache_entry]
      exact suzukiDF6D4EvenFixedGridSolveResidual_contains k j)
  unfold suzukiDF6D4EvenFixedGridGalerkinBase
    suzukiDF6D4EvenGalerkinBaseEntry
  simpa only [Finset.sum_add_distrib, mul_comm] using
    FixedGridInterval.contains_add hcross hsolve

def suzukiDF6D4EvenFixedGridFiniteResidualGram
    (i j : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.finSum fun k : Fin 256 =>
    FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridMatrixCacheEntry
        suzukiDF6D4EvenFixedGridSolveCache k i)
      (suzukiDF6D4FixedGridMatrixCacheEntry
        suzukiDF6D4EvenFixedGridSolveCache k j)).add
  (FixedGridInterval.finSum fun r : Fin 300 =>
    FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridMatrixCacheEntry
        suzukiDF6D4EvenFixedGridResidualCache r i)
      (suzukiDF6D4FixedGridMatrixCacheEntry
        suzukiDF6D4EvenFixedGridResidualCache r j))

theorem suzukiDF6D4EvenFixedGridFiniteResidualGram_contains
    (i j : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenFixedGridFiniteResidualGram i j)).Contains
        (suzukiDF6D4EvenFiniteResidualGramEntry i j) := by
  have hsolve := FixedGridInterval.contains_finSum
    (I := fun k : Fin 256 =>
      FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridMatrixCacheEntry
          suzukiDF6D4EvenFixedGridSolveCache k i)
        (suzukiDF6D4FixedGridMatrixCacheEntry
          suzukiDF6D4EvenFixedGridSolveCache k j))
    (x := fun k : Fin 256 =>
      suzukiDF6D4EvenGalerkinSolveResidual k i *
        suzukiDF6D4EvenGalerkinSolveResidual k j)
    (fun k => FixedGridInterval.contains_mulCentered
      suzukiDF6D4FixedGridDenominator_pos
      (by rw [suzukiDF6D4EvenFixedGridSolveCache_entry]
          exact suzukiDF6D4EvenFixedGridSolveResidual_contains k i)
      (by rw [suzukiDF6D4EvenFixedGridSolveCache_entry]
          exact suzukiDF6D4EvenFixedGridSolveResidual_contains k j))
  have hresidual := FixedGridInterval.contains_finSum
    (I := fun r : Fin 300 =>
      FixedGridInterval.mulCentered suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridMatrixCacheEntry
          suzukiDF6D4EvenFixedGridResidualCache r i)
        (suzukiDF6D4FixedGridMatrixCacheEntry
          suzukiDF6D4EvenFixedGridResidualCache r j))
    (x := fun r : Fin 300 =>
      suzukiDF6D4EvenResidualColumn (301 + r.val) i *
        suzukiDF6D4EvenResidualColumn (301 + r.val) j)
    (fun r => FixedGridInterval.contains_mulCentered
      suzukiDF6D4FixedGridDenominator_pos
      (by rw [suzukiDF6D4EvenFixedGridResidualCache_entry]
          exact suzukiDF6D4EvenFixedGridResidualColumn_contains
            (301 + r.val) (by omega) (by have := r.isLt; omega) i)
      (by rw [suzukiDF6D4EvenFixedGridResidualCache_entry]
          exact suzukiDF6D4EvenFixedGridResidualColumn_contains
            (301 + r.val) (by omega) (by have := r.isLt; omega) j))
  unfold suzukiDF6D4EvenFixedGridFiniteResidualGram
    suzukiDF6D4EvenFiniteResidualGramEntry
  exact FixedGridInterval.contains_add hsolve hresidual

def suzukiDF6D4EvenFixedGridResidualTarget
    (i j : Fin 45) : FixedGridInterval :=
  (FixedGridInterval.scale suzukiDF6D4EvenStrictComparisonCoefficient
    (FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenEndpointEntryInterval i j))).sub
  (((suzukiDF6D4EvenFixedGridGalerkinBase i j).add
    (FixedGridInterval.scale (1 / 5)
      (suzukiDF6D4EvenFixedGridFiniteResidualGram i j))).add
    (FixedGridInterval.scale (1 / 5)
      (FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenAnalyticTailEntryInterval i j))))

theorem suzukiDF6D4EvenFixedGridResidualTarget_contains
    (i j : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4EvenFixedGridResidualTarget i j)).Contains
        (suzukiDF6D4EvenResidualCertificateTargetMatrix i j) := by
  have hcoupling := FixedGridInterval.contains_add
    (FixedGridInterval.contains_add
      (suzukiDF6D4EvenFixedGridGalerkinBase_contains i j)
      (FixedGridInterval.contains_scale (q := (1 / 5 : Rat))
        suzukiDF6D4FixedGridDenominator_pos
        (suzukiDF6D4EvenFixedGridFiniteResidualGram_contains i j)))
    (FixedGridInterval.contains_scale (q := (1 / 5 : Rat))
      suzukiDF6D4FixedGridDenominator_pos
      (FixedGridInterval.contains_ofRationalInterval
        suzukiDF6D4FixedGridDenominator_pos
        (suzukiDF6D4EvenAnalyticTailEntryInterval_contains i j)))
  have h := FixedGridInterval.contains_sub
    (FixedGridInterval.contains_scale
      (q := suzukiDF6D4EvenStrictComparisonCoefficient)
      suzukiDF6D4FixedGridDenominator_pos
      (FixedGridInterval.contains_ofRationalInterval
        suzukiDF6D4FixedGridDenominator_pos
        (suzukiDF6D4EvenEndpointEntryInterval_contains i j)))
    hcoupling
  unfold suzukiDF6D4EvenFixedGridResidualTarget
  unfold suzukiDF6D4EvenResidualCertificateTargetMatrix
    suzukiDF6D4EvenCouplingUpperMatrix
    suzukiDF6D4EvenGalerkinBaseMatrix
    suzukiDF6D4EvenFiniteResidualGramMatrix
  simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul] using h

end RiemannHypothesisProject.Experiments.M100
