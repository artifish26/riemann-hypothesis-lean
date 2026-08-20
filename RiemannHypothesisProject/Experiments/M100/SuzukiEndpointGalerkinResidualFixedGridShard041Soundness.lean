import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard041Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard041Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard041EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard041EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 41 k) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard041EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 41 k)) at h
  exact h

def suzukiDF6D4FixedGridShard041EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard041EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard041EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard041EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard041EvenComparisonData)

theorem suzukiDF6D4FixedGridShard041EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard041EvenSolveData =
      suzukiDF6D4FixedGridShard041EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard041Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard041EvenSolveData =
    suzukiDF6D4FixedGridShard041EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard041EvenCross_eq_live :
    suzukiDF6D4FixedGridShard041EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 41) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard041EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 41)) at h
  exact h

theorem suzukiDF6D4FixedGridShard041EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard041EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 41 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 41 k) := by
    rw [suzukiDF6D4FixedGridShard041EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 41 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041EvenDotSoundness i
          suzukiDF6D4FixedGridShard041EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 41 k) := by
    simpa [suzukiDF6D4FixedGridShard041EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard041EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 41 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 41) := by
    rw [suzukiDF6D4FixedGridShard041EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 41)
  rw [suzukiDF6D4FixedGridShard041EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard041EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard041EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard041EvenDotSoundness i
            suzukiDF6D4FixedGridShard041EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard041EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard041OddComparison_eq_live :
    suzukiDF6D4FixedGridShard041OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 41 k) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard041OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 41 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard041OddCross_eq_live :
    suzukiDF6D4FixedGridShard041OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 41) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard041OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 41)) at h
  exact h

def suzukiDF6D4FixedGridShard041OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard041OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard041OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard041OddDotSoundness i.val
      suzukiDF6D4FixedGridShard041OddComparisonData)

theorem suzukiDF6D4FixedGridShard041OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard041OddSolveData =
      suzukiDF6D4FixedGridShard041OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard041Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard041OddSolveData =
    suzukiDF6D4FixedGridShard041OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard041OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard041OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 41 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 41 k) := by
    rw [suzukiDF6D4FixedGridShard041OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 41 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041OddDotSoundness i
          suzukiDF6D4FixedGridShard041OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 41 k) := by
    simpa [suzukiDF6D4FixedGridShard041OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard041OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 41 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 41) := by
    rw [suzukiDF6D4FixedGridShard041OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 41)
  rw [suzukiDF6D4FixedGridShard041OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard041OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard041OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard041OddDotSoundness i
            suzukiDF6D4FixedGridShard041OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard041OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard041EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard041EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 342) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard041EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 342)) at h
  exact h

theorem suzukiDF6D4FixedGridShard041EvenFull_eq_live :
    suzukiDF6D4FixedGridShard041EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 342) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard041EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 342)) at h
  exact h

def suzukiDF6D4FixedGridShard041EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard041EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard041EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard041EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard041EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard041EvenResidualData =
      suzukiDF6D4FixedGridShard041EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard041Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard041EvenResidualData =
    suzukiDF6D4FixedGridShard041EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard041EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard041EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 342 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 342) := by
    rw [suzukiDF6D4FixedGridShard041EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 342
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041EvenDotSoundness i
          suzukiDF6D4FixedGridShard041EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 342) := by
    simpa [suzukiDF6D4FixedGridShard041EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard041EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 342) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 342) := by
    rw [suzukiDF6D4FixedGridShard041EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 342
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard041EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard041EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard041EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard041EvenDotSoundness i
            suzukiDF6D4FixedGridShard041EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard041EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard041OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard041OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 342) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard041OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 342)) at h
  exact h

theorem suzukiDF6D4FixedGridShard041OddFull_eq_live :
    suzukiDF6D4FixedGridShard041OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 342) := by
  have h := suzukiDF6D4FixedGridShard041Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard041OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 342)) at h
  exact h

def suzukiDF6D4FixedGridShard041OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard041OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard041OddDotSoundness i.val
        suzukiDF6D4FixedGridShard041OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard041OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard041OddResidualData =
      suzukiDF6D4FixedGridShard041OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard041Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard041OddResidualData =
    suzukiDF6D4FixedGridShard041OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard041OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard041OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 342 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 342) := by
    rw [suzukiDF6D4FixedGridShard041OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 342
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041OddDotSoundness i
          suzukiDF6D4FixedGridShard041OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 342) := by
    simpa [suzukiDF6D4FixedGridShard041OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard041OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 342) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard041OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 342) := by
    rw [suzukiDF6D4FixedGridShard041OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 342
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard041OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard041OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard041OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard041OddDotSoundness i
            suzukiDF6D4FixedGridShard041OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard041OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
