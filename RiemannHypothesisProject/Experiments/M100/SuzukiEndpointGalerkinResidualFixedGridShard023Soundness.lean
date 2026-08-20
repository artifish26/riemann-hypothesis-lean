import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard023Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard023Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard023EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard023EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 23 k) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard023EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 23 k)) at h
  exact h

def suzukiDF6D4FixedGridShard023EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard023EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard023EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard023EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard023EvenComparisonData)

theorem suzukiDF6D4FixedGridShard023EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard023EvenSolveData =
      suzukiDF6D4FixedGridShard023EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard023Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard023EvenSolveData =
    suzukiDF6D4FixedGridShard023EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard023EvenCross_eq_live :
    suzukiDF6D4FixedGridShard023EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 23) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard023EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 23)) at h
  exact h

theorem suzukiDF6D4FixedGridShard023EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard023EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 23 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 23 k) := by
    rw [suzukiDF6D4FixedGridShard023EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 23 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023EvenDotSoundness i
          suzukiDF6D4FixedGridShard023EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 23 k) := by
    simpa [suzukiDF6D4FixedGridShard023EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard023EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 23 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 23) := by
    rw [suzukiDF6D4FixedGridShard023EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 23)
  rw [suzukiDF6D4FixedGridShard023EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard023EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard023EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard023EvenDotSoundness i
            suzukiDF6D4FixedGridShard023EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard023EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard023OddComparison_eq_live :
    suzukiDF6D4FixedGridShard023OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 23 k) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard023OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 23 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard023OddCross_eq_live :
    suzukiDF6D4FixedGridShard023OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 23) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard023OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 23)) at h
  exact h

def suzukiDF6D4FixedGridShard023OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard023OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard023OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard023OddDotSoundness i.val
      suzukiDF6D4FixedGridShard023OddComparisonData)

theorem suzukiDF6D4FixedGridShard023OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard023OddSolveData =
      suzukiDF6D4FixedGridShard023OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard023Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard023OddSolveData =
    suzukiDF6D4FixedGridShard023OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard023OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard023OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 23 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 23 k) := by
    rw [suzukiDF6D4FixedGridShard023OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 23 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023OddDotSoundness i
          suzukiDF6D4FixedGridShard023OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 23 k) := by
    simpa [suzukiDF6D4FixedGridShard023OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard023OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 23 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 23) := by
    rw [suzukiDF6D4FixedGridShard023OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 23)
  rw [suzukiDF6D4FixedGridShard023OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard023OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard023OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard023OddDotSoundness i
            suzukiDF6D4FixedGridShard023OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard023OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard023EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard023EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 324) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard023EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 324)) at h
  exact h

theorem suzukiDF6D4FixedGridShard023EvenFull_eq_live :
    suzukiDF6D4FixedGridShard023EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 324) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard023EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 324)) at h
  exact h

def suzukiDF6D4FixedGridShard023EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard023EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard023EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard023EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard023EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard023EvenResidualData =
      suzukiDF6D4FixedGridShard023EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard023Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard023EvenResidualData =
    suzukiDF6D4FixedGridShard023EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard023EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard023EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 324 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 324) := by
    rw [suzukiDF6D4FixedGridShard023EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 324
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023EvenDotSoundness i
          suzukiDF6D4FixedGridShard023EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 324) := by
    simpa [suzukiDF6D4FixedGridShard023EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard023EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 324) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 324) := by
    rw [suzukiDF6D4FixedGridShard023EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 324
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard023EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard023EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard023EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard023EvenDotSoundness i
            suzukiDF6D4FixedGridShard023EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard023EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard023OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard023OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 324) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard023OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 324)) at h
  exact h

theorem suzukiDF6D4FixedGridShard023OddFull_eq_live :
    suzukiDF6D4FixedGridShard023OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 324) := by
  have h := suzukiDF6D4FixedGridShard023Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard023OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 324)) at h
  exact h

def suzukiDF6D4FixedGridShard023OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard023OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard023OddDotSoundness i.val
        suzukiDF6D4FixedGridShard023OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard023OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard023OddResidualData =
      suzukiDF6D4FixedGridShard023OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard023Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard023OddResidualData =
    suzukiDF6D4FixedGridShard023OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard023OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard023OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 324 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 324) := by
    rw [suzukiDF6D4FixedGridShard023OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 324
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023OddDotSoundness i
          suzukiDF6D4FixedGridShard023OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 324) := by
    simpa [suzukiDF6D4FixedGridShard023OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard023OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 324) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard023OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 324) := by
    rw [suzukiDF6D4FixedGridShard023OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 324
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard023OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard023OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard023OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard023OddDotSoundness i
            suzukiDF6D4FixedGridShard023OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard023OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
