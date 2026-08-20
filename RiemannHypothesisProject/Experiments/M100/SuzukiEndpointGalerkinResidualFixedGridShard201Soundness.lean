import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard201Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard201Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard201EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard201EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 201 k) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard201EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 201 k)) at h
  exact h

def suzukiDF6D4FixedGridShard201EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard201EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard201EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard201EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard201EvenComparisonData)

theorem suzukiDF6D4FixedGridShard201EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard201EvenSolveData =
      suzukiDF6D4FixedGridShard201EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard201Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard201EvenSolveData =
    suzukiDF6D4FixedGridShard201EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard201EvenCross_eq_live :
    suzukiDF6D4FixedGridShard201EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 201) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard201EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 201)) at h
  exact h

theorem suzukiDF6D4FixedGridShard201EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard201EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 201 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 201 k) := by
    rw [suzukiDF6D4FixedGridShard201EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 201 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201EvenDotSoundness i
          suzukiDF6D4FixedGridShard201EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 201 k) := by
    simpa [suzukiDF6D4FixedGridShard201EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard201EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 201 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 201) := by
    rw [suzukiDF6D4FixedGridShard201EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 201)
  rw [suzukiDF6D4FixedGridShard201EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard201EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard201EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard201EvenDotSoundness i
            suzukiDF6D4FixedGridShard201EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard201EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard201OddComparison_eq_live :
    suzukiDF6D4FixedGridShard201OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 201 k) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard201OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 201 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard201OddCross_eq_live :
    suzukiDF6D4FixedGridShard201OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 201) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard201OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 201)) at h
  exact h

def suzukiDF6D4FixedGridShard201OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard201OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard201OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard201OddDotSoundness i.val
      suzukiDF6D4FixedGridShard201OddComparisonData)

theorem suzukiDF6D4FixedGridShard201OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard201OddSolveData =
      suzukiDF6D4FixedGridShard201OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard201Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard201OddSolveData =
    suzukiDF6D4FixedGridShard201OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard201OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard201OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 201 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 201 k) := by
    rw [suzukiDF6D4FixedGridShard201OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 201 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201OddDotSoundness i
          suzukiDF6D4FixedGridShard201OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 201 k) := by
    simpa [suzukiDF6D4FixedGridShard201OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard201OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 201 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 201) := by
    rw [suzukiDF6D4FixedGridShard201OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 201)
  rw [suzukiDF6D4FixedGridShard201OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard201OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard201OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard201OddDotSoundness i
            suzukiDF6D4FixedGridShard201OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard201OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard201EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard201EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 502) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard201EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 502)) at h
  exact h

theorem suzukiDF6D4FixedGridShard201EvenFull_eq_live :
    suzukiDF6D4FixedGridShard201EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 502) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard201EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 502)) at h
  exact h

def suzukiDF6D4FixedGridShard201EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard201EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard201EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard201EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard201EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard201EvenResidualData =
      suzukiDF6D4FixedGridShard201EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard201Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard201EvenResidualData =
    suzukiDF6D4FixedGridShard201EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard201EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard201EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 502 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 502) := by
    rw [suzukiDF6D4FixedGridShard201EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 502
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201EvenDotSoundness i
          suzukiDF6D4FixedGridShard201EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 502) := by
    simpa [suzukiDF6D4FixedGridShard201EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard201EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 502) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 502) := by
    rw [suzukiDF6D4FixedGridShard201EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 502
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard201EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard201EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard201EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard201EvenDotSoundness i
            suzukiDF6D4FixedGridShard201EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard201EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard201OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard201OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 502) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard201OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 502)) at h
  exact h

theorem suzukiDF6D4FixedGridShard201OddFull_eq_live :
    suzukiDF6D4FixedGridShard201OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 502) := by
  have h := suzukiDF6D4FixedGridShard201Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard201OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 502)) at h
  exact h

def suzukiDF6D4FixedGridShard201OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard201OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard201OddDotSoundness i.val
        suzukiDF6D4FixedGridShard201OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard201OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard201OddResidualData =
      suzukiDF6D4FixedGridShard201OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard201Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard201OddResidualData =
    suzukiDF6D4FixedGridShard201OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard201OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard201OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 502 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 502) := by
    rw [suzukiDF6D4FixedGridShard201OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 502
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201OddDotSoundness i
          suzukiDF6D4FixedGridShard201OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 502) := by
    simpa [suzukiDF6D4FixedGridShard201OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard201OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 502) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard201OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 502) := by
    rw [suzukiDF6D4FixedGridShard201OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 502
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard201OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard201OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard201OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard201OddDotSoundness i
            suzukiDF6D4FixedGridShard201OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard201OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
