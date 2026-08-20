import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard094Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard094Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard094EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard094EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 94 k) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard094EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 94 k)) at h
  exact h

def suzukiDF6D4FixedGridShard094EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard094EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard094EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard094EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard094EvenComparisonData)

theorem suzukiDF6D4FixedGridShard094EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard094EvenSolveData =
      suzukiDF6D4FixedGridShard094EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard094Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard094EvenSolveData =
    suzukiDF6D4FixedGridShard094EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard094EvenCross_eq_live :
    suzukiDF6D4FixedGridShard094EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 94) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard094EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 94)) at h
  exact h

theorem suzukiDF6D4FixedGridShard094EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard094EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 94 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 94 k) := by
    rw [suzukiDF6D4FixedGridShard094EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 94 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094EvenDotSoundness i
          suzukiDF6D4FixedGridShard094EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 94 k) := by
    simpa [suzukiDF6D4FixedGridShard094EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard094EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 94 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 94) := by
    rw [suzukiDF6D4FixedGridShard094EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 94)
  rw [suzukiDF6D4FixedGridShard094EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard094EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard094EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard094EvenDotSoundness i
            suzukiDF6D4FixedGridShard094EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard094EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard094OddComparison_eq_live :
    suzukiDF6D4FixedGridShard094OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 94 k) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard094OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 94 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard094OddCross_eq_live :
    suzukiDF6D4FixedGridShard094OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 94) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard094OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 94)) at h
  exact h

def suzukiDF6D4FixedGridShard094OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard094OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard094OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard094OddDotSoundness i.val
      suzukiDF6D4FixedGridShard094OddComparisonData)

theorem suzukiDF6D4FixedGridShard094OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard094OddSolveData =
      suzukiDF6D4FixedGridShard094OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard094Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard094OddSolveData =
    suzukiDF6D4FixedGridShard094OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard094OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard094OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 94 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 94 k) := by
    rw [suzukiDF6D4FixedGridShard094OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 94 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094OddDotSoundness i
          suzukiDF6D4FixedGridShard094OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 94 k) := by
    simpa [suzukiDF6D4FixedGridShard094OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard094OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 94 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 94) := by
    rw [suzukiDF6D4FixedGridShard094OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 94)
  rw [suzukiDF6D4FixedGridShard094OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard094OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard094OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard094OddDotSoundness i
            suzukiDF6D4FixedGridShard094OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard094OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard094EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard094EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 395) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard094EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 395)) at h
  exact h

theorem suzukiDF6D4FixedGridShard094EvenFull_eq_live :
    suzukiDF6D4FixedGridShard094EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 395) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard094EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 395)) at h
  exact h

def suzukiDF6D4FixedGridShard094EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard094EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard094EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard094EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard094EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard094EvenResidualData =
      suzukiDF6D4FixedGridShard094EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard094Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard094EvenResidualData =
    suzukiDF6D4FixedGridShard094EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard094EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard094EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 395 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 395) := by
    rw [suzukiDF6D4FixedGridShard094EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 395
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094EvenDotSoundness i
          suzukiDF6D4FixedGridShard094EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 395) := by
    simpa [suzukiDF6D4FixedGridShard094EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard094EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 395) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 395) := by
    rw [suzukiDF6D4FixedGridShard094EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 395
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard094EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard094EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard094EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard094EvenDotSoundness i
            suzukiDF6D4FixedGridShard094EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard094EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard094OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard094OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 395) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard094OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 395)) at h
  exact h

theorem suzukiDF6D4FixedGridShard094OddFull_eq_live :
    suzukiDF6D4FixedGridShard094OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 395) := by
  have h := suzukiDF6D4FixedGridShard094Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard094OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 395)) at h
  exact h

def suzukiDF6D4FixedGridShard094OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard094OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard094OddDotSoundness i.val
        suzukiDF6D4FixedGridShard094OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard094OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard094OddResidualData =
      suzukiDF6D4FixedGridShard094OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard094Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard094OddResidualData =
    suzukiDF6D4FixedGridShard094OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard094OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard094OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 395 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 395) := by
    rw [suzukiDF6D4FixedGridShard094OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 395
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094OddDotSoundness i
          suzukiDF6D4FixedGridShard094OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 395) := by
    simpa [suzukiDF6D4FixedGridShard094OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard094OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 395) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard094OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 395) := by
    rw [suzukiDF6D4FixedGridShard094OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 395
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard094OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard094OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard094OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard094OddDotSoundness i
            suzukiDF6D4FixedGridShard094OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard094OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
