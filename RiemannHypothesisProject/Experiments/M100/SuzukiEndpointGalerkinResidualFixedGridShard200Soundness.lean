import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard200Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard200Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard200EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard200EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 200 k) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard200EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 200 k)) at h
  exact h

def suzukiDF6D4FixedGridShard200EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard200EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard200EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard200EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard200EvenComparisonData)

theorem suzukiDF6D4FixedGridShard200EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard200EvenSolveData =
      suzukiDF6D4FixedGridShard200EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard200Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard200EvenSolveData =
    suzukiDF6D4FixedGridShard200EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard200EvenCross_eq_live :
    suzukiDF6D4FixedGridShard200EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 200) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard200EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 200)) at h
  exact h

theorem suzukiDF6D4FixedGridShard200EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard200EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 200 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 200 k) := by
    rw [suzukiDF6D4FixedGridShard200EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 200 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200EvenDotSoundness i
          suzukiDF6D4FixedGridShard200EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 200 k) := by
    simpa [suzukiDF6D4FixedGridShard200EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard200EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 200 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 200) := by
    rw [suzukiDF6D4FixedGridShard200EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 200)
  rw [suzukiDF6D4FixedGridShard200EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard200EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard200EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard200EvenDotSoundness i
            suzukiDF6D4FixedGridShard200EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard200EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard200OddComparison_eq_live :
    suzukiDF6D4FixedGridShard200OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 200 k) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard200OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 200 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard200OddCross_eq_live :
    suzukiDF6D4FixedGridShard200OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 200) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard200OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 200)) at h
  exact h

def suzukiDF6D4FixedGridShard200OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard200OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard200OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard200OddDotSoundness i.val
      suzukiDF6D4FixedGridShard200OddComparisonData)

theorem suzukiDF6D4FixedGridShard200OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard200OddSolveData =
      suzukiDF6D4FixedGridShard200OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard200Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard200OddSolveData =
    suzukiDF6D4FixedGridShard200OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard200OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard200OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 200 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 200 k) := by
    rw [suzukiDF6D4FixedGridShard200OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 200 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200OddDotSoundness i
          suzukiDF6D4FixedGridShard200OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 200 k) := by
    simpa [suzukiDF6D4FixedGridShard200OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard200OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 200 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 200) := by
    rw [suzukiDF6D4FixedGridShard200OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 200)
  rw [suzukiDF6D4FixedGridShard200OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard200OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard200OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard200OddDotSoundness i
            suzukiDF6D4FixedGridShard200OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard200OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard200EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard200EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 501) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard200EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 501)) at h
  exact h

theorem suzukiDF6D4FixedGridShard200EvenFull_eq_live :
    suzukiDF6D4FixedGridShard200EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 501) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard200EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 501)) at h
  exact h

def suzukiDF6D4FixedGridShard200EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard200EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard200EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard200EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard200EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard200EvenResidualData =
      suzukiDF6D4FixedGridShard200EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard200Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard200EvenResidualData =
    suzukiDF6D4FixedGridShard200EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard200EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard200EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 501 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 501) := by
    rw [suzukiDF6D4FixedGridShard200EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 501
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200EvenDotSoundness i
          suzukiDF6D4FixedGridShard200EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 501) := by
    simpa [suzukiDF6D4FixedGridShard200EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard200EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 501) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 501) := by
    rw [suzukiDF6D4FixedGridShard200EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 501
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard200EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard200EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard200EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard200EvenDotSoundness i
            suzukiDF6D4FixedGridShard200EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard200EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard200OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard200OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 501) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard200OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 501)) at h
  exact h

theorem suzukiDF6D4FixedGridShard200OddFull_eq_live :
    suzukiDF6D4FixedGridShard200OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 501) := by
  have h := suzukiDF6D4FixedGridShard200Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard200OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 501)) at h
  exact h

def suzukiDF6D4FixedGridShard200OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard200OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard200OddDotSoundness i.val
        suzukiDF6D4FixedGridShard200OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard200OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard200OddResidualData =
      suzukiDF6D4FixedGridShard200OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard200Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard200OddResidualData =
    suzukiDF6D4FixedGridShard200OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard200OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard200OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 501 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 501) := by
    rw [suzukiDF6D4FixedGridShard200OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 501
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200OddDotSoundness i
          suzukiDF6D4FixedGridShard200OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 501) := by
    simpa [suzukiDF6D4FixedGridShard200OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard200OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 501) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard200OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 501) := by
    rw [suzukiDF6D4FixedGridShard200OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 501
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard200OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard200OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard200OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard200OddDotSoundness i
            suzukiDF6D4FixedGridShard200OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard200OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
