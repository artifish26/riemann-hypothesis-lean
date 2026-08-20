import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard018Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard018Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard018EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard018EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 18 k) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard018EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 18 k)) at h
  exact h

def suzukiDF6D4FixedGridShard018EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard018EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard018EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard018EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard018EvenComparisonData)

theorem suzukiDF6D4FixedGridShard018EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard018EvenSolveData =
      suzukiDF6D4FixedGridShard018EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard018Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard018EvenSolveData =
    suzukiDF6D4FixedGridShard018EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard018EvenCross_eq_live :
    suzukiDF6D4FixedGridShard018EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 18) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard018EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 18)) at h
  exact h

theorem suzukiDF6D4FixedGridShard018EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard018EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 18 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 18 k) := by
    rw [suzukiDF6D4FixedGridShard018EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 18 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018EvenDotSoundness i
          suzukiDF6D4FixedGridShard018EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 18 k) := by
    simpa [suzukiDF6D4FixedGridShard018EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard018EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 18 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 18) := by
    rw [suzukiDF6D4FixedGridShard018EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 18)
  rw [suzukiDF6D4FixedGridShard018EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard018EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard018EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard018EvenDotSoundness i
            suzukiDF6D4FixedGridShard018EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard018EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard018OddComparison_eq_live :
    suzukiDF6D4FixedGridShard018OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 18 k) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard018OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 18 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard018OddCross_eq_live :
    suzukiDF6D4FixedGridShard018OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 18) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard018OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 18)) at h
  exact h

def suzukiDF6D4FixedGridShard018OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard018OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard018OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard018OddDotSoundness i.val
      suzukiDF6D4FixedGridShard018OddComparisonData)

theorem suzukiDF6D4FixedGridShard018OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard018OddSolveData =
      suzukiDF6D4FixedGridShard018OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard018Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard018OddSolveData =
    suzukiDF6D4FixedGridShard018OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard018OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard018OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 18 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 18 k) := by
    rw [suzukiDF6D4FixedGridShard018OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 18 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018OddDotSoundness i
          suzukiDF6D4FixedGridShard018OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 18 k) := by
    simpa [suzukiDF6D4FixedGridShard018OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard018OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 18 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 18) := by
    rw [suzukiDF6D4FixedGridShard018OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 18)
  rw [suzukiDF6D4FixedGridShard018OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard018OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard018OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard018OddDotSoundness i
            suzukiDF6D4FixedGridShard018OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard018OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard018EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard018EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 319) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard018EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 319)) at h
  exact h

theorem suzukiDF6D4FixedGridShard018EvenFull_eq_live :
    suzukiDF6D4FixedGridShard018EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 319) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard018EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 319)) at h
  exact h

def suzukiDF6D4FixedGridShard018EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard018EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard018EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard018EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard018EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard018EvenResidualData =
      suzukiDF6D4FixedGridShard018EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard018Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard018EvenResidualData =
    suzukiDF6D4FixedGridShard018EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard018EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard018EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 319 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 319) := by
    rw [suzukiDF6D4FixedGridShard018EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 319
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018EvenDotSoundness i
          suzukiDF6D4FixedGridShard018EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 319) := by
    simpa [suzukiDF6D4FixedGridShard018EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard018EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 319) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 319) := by
    rw [suzukiDF6D4FixedGridShard018EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 319
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard018EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard018EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard018EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard018EvenDotSoundness i
            suzukiDF6D4FixedGridShard018EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard018EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard018OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard018OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 319) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard018OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 319)) at h
  exact h

theorem suzukiDF6D4FixedGridShard018OddFull_eq_live :
    suzukiDF6D4FixedGridShard018OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 319) := by
  have h := suzukiDF6D4FixedGridShard018Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard018OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 319)) at h
  exact h

def suzukiDF6D4FixedGridShard018OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard018OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard018OddDotSoundness i.val
        suzukiDF6D4FixedGridShard018OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard018OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard018OddResidualData =
      suzukiDF6D4FixedGridShard018OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard018Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard018OddResidualData =
    suzukiDF6D4FixedGridShard018OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard018OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard018OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 319 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 319) := by
    rw [suzukiDF6D4FixedGridShard018OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 319
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018OddDotSoundness i
          suzukiDF6D4FixedGridShard018OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 319) := by
    simpa [suzukiDF6D4FixedGridShard018OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard018OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 319) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard018OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 319) := by
    rw [suzukiDF6D4FixedGridShard018OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 319
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard018OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard018OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard018OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard018OddDotSoundness i
            suzukiDF6D4FixedGridShard018OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard018OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
