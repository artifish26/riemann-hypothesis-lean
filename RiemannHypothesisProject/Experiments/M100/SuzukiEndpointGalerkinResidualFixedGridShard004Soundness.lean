import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard004Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard004Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard004EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard004EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 4 k) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard004EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 4 k)) at h
  exact h

def suzukiDF6D4FixedGridShard004EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard004EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard004EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard004EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard004EvenComparisonData)

theorem suzukiDF6D4FixedGridShard004EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard004EvenSolveData =
      suzukiDF6D4FixedGridShard004EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard004Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard004EvenSolveData =
    suzukiDF6D4FixedGridShard004EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard004EvenCross_eq_live :
    suzukiDF6D4FixedGridShard004EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 4) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard004EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 4)) at h
  exact h

theorem suzukiDF6D4FixedGridShard004EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard004EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 4 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 4 k) := by
    rw [suzukiDF6D4FixedGridShard004EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 4 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004EvenDotSoundness i
          suzukiDF6D4FixedGridShard004EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 4 k) := by
    simpa [suzukiDF6D4FixedGridShard004EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard004EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 4 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 4) := by
    rw [suzukiDF6D4FixedGridShard004EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 4)
  rw [suzukiDF6D4FixedGridShard004EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard004EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard004EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard004EvenDotSoundness i
            suzukiDF6D4FixedGridShard004EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard004EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard004OddComparison_eq_live :
    suzukiDF6D4FixedGridShard004OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 4 k) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard004OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 4 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard004OddCross_eq_live :
    suzukiDF6D4FixedGridShard004OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 4) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard004OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 4)) at h
  exact h

def suzukiDF6D4FixedGridShard004OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard004OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard004OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard004OddDotSoundness i.val
      suzukiDF6D4FixedGridShard004OddComparisonData)

theorem suzukiDF6D4FixedGridShard004OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard004OddSolveData =
      suzukiDF6D4FixedGridShard004OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard004Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard004OddSolveData =
    suzukiDF6D4FixedGridShard004OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard004OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard004OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 4 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 4 k) := by
    rw [suzukiDF6D4FixedGridShard004OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 4 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004OddDotSoundness i
          suzukiDF6D4FixedGridShard004OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 4 k) := by
    simpa [suzukiDF6D4FixedGridShard004OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard004OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 4 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 4) := by
    rw [suzukiDF6D4FixedGridShard004OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 4)
  rw [suzukiDF6D4FixedGridShard004OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard004OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard004OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard004OddDotSoundness i
            suzukiDF6D4FixedGridShard004OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard004OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard004EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard004EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 305) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard004EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 305)) at h
  exact h

theorem suzukiDF6D4FixedGridShard004EvenFull_eq_live :
    suzukiDF6D4FixedGridShard004EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 305) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard004EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 305)) at h
  exact h

def suzukiDF6D4FixedGridShard004EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard004EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard004EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard004EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard004EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard004EvenResidualData =
      suzukiDF6D4FixedGridShard004EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard004Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard004EvenResidualData =
    suzukiDF6D4FixedGridShard004EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard004EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard004EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 305 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 305) := by
    rw [suzukiDF6D4FixedGridShard004EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 305
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004EvenDotSoundness i
          suzukiDF6D4FixedGridShard004EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 305) := by
    simpa [suzukiDF6D4FixedGridShard004EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard004EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 305) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 305) := by
    rw [suzukiDF6D4FixedGridShard004EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 305
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard004EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard004EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard004EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard004EvenDotSoundness i
            suzukiDF6D4FixedGridShard004EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard004EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard004OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard004OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 305) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard004OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 305)) at h
  exact h

theorem suzukiDF6D4FixedGridShard004OddFull_eq_live :
    suzukiDF6D4FixedGridShard004OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 305) := by
  have h := suzukiDF6D4FixedGridShard004Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard004OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 305)) at h
  exact h

def suzukiDF6D4FixedGridShard004OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard004OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard004OddDotSoundness i.val
        suzukiDF6D4FixedGridShard004OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard004OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard004OddResidualData =
      suzukiDF6D4FixedGridShard004OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard004Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard004OddResidualData =
    suzukiDF6D4FixedGridShard004OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard004OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard004OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 305 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 305) := by
    rw [suzukiDF6D4FixedGridShard004OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 305
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004OddDotSoundness i
          suzukiDF6D4FixedGridShard004OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 305) := by
    simpa [suzukiDF6D4FixedGridShard004OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard004OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 305) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard004OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 305) := by
    rw [suzukiDF6D4FixedGridShard004OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 305
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard004OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard004OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard004OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard004OddDotSoundness i
            suzukiDF6D4FixedGridShard004OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard004OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
