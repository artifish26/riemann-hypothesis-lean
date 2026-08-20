import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard102Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard102Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard102EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard102EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 102 k) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard102EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 102 k)) at h
  exact h

def suzukiDF6D4FixedGridShard102EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard102EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard102EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard102EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard102EvenComparisonData)

theorem suzukiDF6D4FixedGridShard102EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard102EvenSolveData =
      suzukiDF6D4FixedGridShard102EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard102Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard102EvenSolveData =
    suzukiDF6D4FixedGridShard102EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard102EvenCross_eq_live :
    suzukiDF6D4FixedGridShard102EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 102) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard102EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 102)) at h
  exact h

theorem suzukiDF6D4FixedGridShard102EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard102EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 102 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 102 k) := by
    rw [suzukiDF6D4FixedGridShard102EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 102 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102EvenDotSoundness i
          suzukiDF6D4FixedGridShard102EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 102 k) := by
    simpa [suzukiDF6D4FixedGridShard102EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard102EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 102 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 102) := by
    rw [suzukiDF6D4FixedGridShard102EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 102)
  rw [suzukiDF6D4FixedGridShard102EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard102EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard102EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard102EvenDotSoundness i
            suzukiDF6D4FixedGridShard102EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard102EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard102OddComparison_eq_live :
    suzukiDF6D4FixedGridShard102OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 102 k) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard102OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 102 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard102OddCross_eq_live :
    suzukiDF6D4FixedGridShard102OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 102) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard102OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 102)) at h
  exact h

def suzukiDF6D4FixedGridShard102OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard102OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard102OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard102OddDotSoundness i.val
      suzukiDF6D4FixedGridShard102OddComparisonData)

theorem suzukiDF6D4FixedGridShard102OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard102OddSolveData =
      suzukiDF6D4FixedGridShard102OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard102Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard102OddSolveData =
    suzukiDF6D4FixedGridShard102OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard102OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard102OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 102 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 102 k) := by
    rw [suzukiDF6D4FixedGridShard102OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 102 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102OddDotSoundness i
          suzukiDF6D4FixedGridShard102OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 102 k) := by
    simpa [suzukiDF6D4FixedGridShard102OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard102OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 102 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 102) := by
    rw [suzukiDF6D4FixedGridShard102OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 102)
  rw [suzukiDF6D4FixedGridShard102OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard102OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard102OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard102OddDotSoundness i
            suzukiDF6D4FixedGridShard102OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard102OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard102EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard102EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 403) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard102EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 403)) at h
  exact h

theorem suzukiDF6D4FixedGridShard102EvenFull_eq_live :
    suzukiDF6D4FixedGridShard102EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 403) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard102EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 403)) at h
  exact h

def suzukiDF6D4FixedGridShard102EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard102EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard102EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard102EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard102EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard102EvenResidualData =
      suzukiDF6D4FixedGridShard102EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard102Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard102EvenResidualData =
    suzukiDF6D4FixedGridShard102EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard102EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard102EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 403 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 403) := by
    rw [suzukiDF6D4FixedGridShard102EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 403
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102EvenDotSoundness i
          suzukiDF6D4FixedGridShard102EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 403) := by
    simpa [suzukiDF6D4FixedGridShard102EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard102EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 403) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 403) := by
    rw [suzukiDF6D4FixedGridShard102EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 403
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard102EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard102EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard102EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard102EvenDotSoundness i
            suzukiDF6D4FixedGridShard102EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard102EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard102OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard102OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 403) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard102OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 403)) at h
  exact h

theorem suzukiDF6D4FixedGridShard102OddFull_eq_live :
    suzukiDF6D4FixedGridShard102OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 403) := by
  have h := suzukiDF6D4FixedGridShard102Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard102OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 403)) at h
  exact h

def suzukiDF6D4FixedGridShard102OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard102OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard102OddDotSoundness i.val
        suzukiDF6D4FixedGridShard102OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard102OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard102OddResidualData =
      suzukiDF6D4FixedGridShard102OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard102Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard102OddResidualData =
    suzukiDF6D4FixedGridShard102OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard102OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard102OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 403 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 403) := by
    rw [suzukiDF6D4FixedGridShard102OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 403
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102OddDotSoundness i
          suzukiDF6D4FixedGridShard102OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 403) := by
    simpa [suzukiDF6D4FixedGridShard102OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard102OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 403) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard102OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 403) := by
    rw [suzukiDF6D4FixedGridShard102OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 403
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard102OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard102OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard102OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard102OddDotSoundness i
            suzukiDF6D4FixedGridShard102OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard102OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
