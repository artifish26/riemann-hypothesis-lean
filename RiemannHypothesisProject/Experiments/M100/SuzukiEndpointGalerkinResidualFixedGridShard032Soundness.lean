import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard032Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard032Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard032EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard032EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 32 k) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard032EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 32 k)) at h
  exact h

def suzukiDF6D4FixedGridShard032EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard032EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard032EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard032EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard032EvenComparisonData)

theorem suzukiDF6D4FixedGridShard032EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard032EvenSolveData =
      suzukiDF6D4FixedGridShard032EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard032Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard032EvenSolveData =
    suzukiDF6D4FixedGridShard032EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard032EvenCross_eq_live :
    suzukiDF6D4FixedGridShard032EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 32) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard032EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 32)) at h
  exact h

theorem suzukiDF6D4FixedGridShard032EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard032EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 32 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 32 k) := by
    rw [suzukiDF6D4FixedGridShard032EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 32 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032EvenDotSoundness i
          suzukiDF6D4FixedGridShard032EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 32 k) := by
    simpa [suzukiDF6D4FixedGridShard032EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard032EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 32 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 32) := by
    rw [suzukiDF6D4FixedGridShard032EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 32)
  rw [suzukiDF6D4FixedGridShard032EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard032EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard032EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard032EvenDotSoundness i
            suzukiDF6D4FixedGridShard032EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard032EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard032OddComparison_eq_live :
    suzukiDF6D4FixedGridShard032OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 32 k) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard032OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 32 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard032OddCross_eq_live :
    suzukiDF6D4FixedGridShard032OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 32) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard032OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 32)) at h
  exact h

def suzukiDF6D4FixedGridShard032OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard032OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard032OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard032OddDotSoundness i.val
      suzukiDF6D4FixedGridShard032OddComparisonData)

theorem suzukiDF6D4FixedGridShard032OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard032OddSolveData =
      suzukiDF6D4FixedGridShard032OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard032Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard032OddSolveData =
    suzukiDF6D4FixedGridShard032OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard032OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard032OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 32 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 32 k) := by
    rw [suzukiDF6D4FixedGridShard032OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 32 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032OddDotSoundness i
          suzukiDF6D4FixedGridShard032OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 32 k) := by
    simpa [suzukiDF6D4FixedGridShard032OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard032OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 32 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 32) := by
    rw [suzukiDF6D4FixedGridShard032OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 32)
  rw [suzukiDF6D4FixedGridShard032OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard032OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard032OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard032OddDotSoundness i
            suzukiDF6D4FixedGridShard032OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard032OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard032EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard032EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 333) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard032EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 333)) at h
  exact h

theorem suzukiDF6D4FixedGridShard032EvenFull_eq_live :
    suzukiDF6D4FixedGridShard032EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 333) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard032EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 333)) at h
  exact h

def suzukiDF6D4FixedGridShard032EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard032EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard032EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard032EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard032EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard032EvenResidualData =
      suzukiDF6D4FixedGridShard032EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard032Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard032EvenResidualData =
    suzukiDF6D4FixedGridShard032EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard032EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard032EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 333 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 333) := by
    rw [suzukiDF6D4FixedGridShard032EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 333
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032EvenDotSoundness i
          suzukiDF6D4FixedGridShard032EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 333) := by
    simpa [suzukiDF6D4FixedGridShard032EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard032EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 333) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 333) := by
    rw [suzukiDF6D4FixedGridShard032EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 333
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard032EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard032EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard032EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard032EvenDotSoundness i
            suzukiDF6D4FixedGridShard032EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard032EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard032OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard032OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 333) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard032OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 333)) at h
  exact h

theorem suzukiDF6D4FixedGridShard032OddFull_eq_live :
    suzukiDF6D4FixedGridShard032OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 333) := by
  have h := suzukiDF6D4FixedGridShard032Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard032OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 333)) at h
  exact h

def suzukiDF6D4FixedGridShard032OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard032OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard032OddDotSoundness i.val
        suzukiDF6D4FixedGridShard032OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard032OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard032OddResidualData =
      suzukiDF6D4FixedGridShard032OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard032Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard032OddResidualData =
    suzukiDF6D4FixedGridShard032OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard032OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard032OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 333 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 333) := by
    rw [suzukiDF6D4FixedGridShard032OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 333
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032OddDotSoundness i
          suzukiDF6D4FixedGridShard032OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 333) := by
    simpa [suzukiDF6D4FixedGridShard032OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard032OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 333) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard032OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 333) := by
    rw [suzukiDF6D4FixedGridShard032OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 333
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard032OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard032OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard032OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard032OddDotSoundness i
            suzukiDF6D4FixedGridShard032OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard032OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
