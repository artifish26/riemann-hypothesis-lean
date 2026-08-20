import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard075Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard075Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard075EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard075EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 75 k) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard075EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 75 k)) at h
  exact h

def suzukiDF6D4FixedGridShard075EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard075EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard075EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard075EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard075EvenComparisonData)

theorem suzukiDF6D4FixedGridShard075EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard075EvenSolveData =
      suzukiDF6D4FixedGridShard075EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard075Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard075EvenSolveData =
    suzukiDF6D4FixedGridShard075EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard075EvenCross_eq_live :
    suzukiDF6D4FixedGridShard075EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 75) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard075EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 75)) at h
  exact h

theorem suzukiDF6D4FixedGridShard075EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard075EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 75 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 75 k) := by
    rw [suzukiDF6D4FixedGridShard075EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 75 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075EvenDotSoundness i
          suzukiDF6D4FixedGridShard075EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 75 k) := by
    simpa [suzukiDF6D4FixedGridShard075EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard075EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 75 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 75) := by
    rw [suzukiDF6D4FixedGridShard075EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 75)
  rw [suzukiDF6D4FixedGridShard075EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard075EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard075EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard075EvenDotSoundness i
            suzukiDF6D4FixedGridShard075EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard075EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard075OddComparison_eq_live :
    suzukiDF6D4FixedGridShard075OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 75 k) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard075OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 75 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard075OddCross_eq_live :
    suzukiDF6D4FixedGridShard075OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 75) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard075OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 75)) at h
  exact h

def suzukiDF6D4FixedGridShard075OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard075OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard075OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard075OddDotSoundness i.val
      suzukiDF6D4FixedGridShard075OddComparisonData)

theorem suzukiDF6D4FixedGridShard075OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard075OddSolveData =
      suzukiDF6D4FixedGridShard075OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard075Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard075OddSolveData =
    suzukiDF6D4FixedGridShard075OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard075OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard075OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 75 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 75 k) := by
    rw [suzukiDF6D4FixedGridShard075OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 75 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075OddDotSoundness i
          suzukiDF6D4FixedGridShard075OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 75 k) := by
    simpa [suzukiDF6D4FixedGridShard075OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard075OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 75 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 75) := by
    rw [suzukiDF6D4FixedGridShard075OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 75)
  rw [suzukiDF6D4FixedGridShard075OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard075OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard075OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard075OddDotSoundness i
            suzukiDF6D4FixedGridShard075OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard075OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard075EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard075EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 376) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard075EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 376)) at h
  exact h

theorem suzukiDF6D4FixedGridShard075EvenFull_eq_live :
    suzukiDF6D4FixedGridShard075EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 376) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard075EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 376)) at h
  exact h

def suzukiDF6D4FixedGridShard075EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard075EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard075EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard075EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard075EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard075EvenResidualData =
      suzukiDF6D4FixedGridShard075EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard075Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard075EvenResidualData =
    suzukiDF6D4FixedGridShard075EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard075EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard075EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 376 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 376) := by
    rw [suzukiDF6D4FixedGridShard075EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 376
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075EvenDotSoundness i
          suzukiDF6D4FixedGridShard075EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 376) := by
    simpa [suzukiDF6D4FixedGridShard075EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard075EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 376) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 376) := by
    rw [suzukiDF6D4FixedGridShard075EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 376
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard075EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard075EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard075EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard075EvenDotSoundness i
            suzukiDF6D4FixedGridShard075EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard075EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard075OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard075OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 376) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard075OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 376)) at h
  exact h

theorem suzukiDF6D4FixedGridShard075OddFull_eq_live :
    suzukiDF6D4FixedGridShard075OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 376) := by
  have h := suzukiDF6D4FixedGridShard075Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard075OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 376)) at h
  exact h

def suzukiDF6D4FixedGridShard075OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard075OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard075OddDotSoundness i.val
        suzukiDF6D4FixedGridShard075OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard075OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard075OddResidualData =
      suzukiDF6D4FixedGridShard075OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard075Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard075OddResidualData =
    suzukiDF6D4FixedGridShard075OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard075OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard075OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 376 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 376) := by
    rw [suzukiDF6D4FixedGridShard075OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 376
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075OddDotSoundness i
          suzukiDF6D4FixedGridShard075OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 376) := by
    simpa [suzukiDF6D4FixedGridShard075OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard075OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 376) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard075OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 376) := by
    rw [suzukiDF6D4FixedGridShard075OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 376
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard075OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard075OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard075OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard075OddDotSoundness i
            suzukiDF6D4FixedGridShard075OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard075OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
