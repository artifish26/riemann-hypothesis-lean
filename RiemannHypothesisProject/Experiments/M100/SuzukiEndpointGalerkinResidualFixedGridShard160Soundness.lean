import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard160Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard160Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard160EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard160EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 160 k) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard160EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 160 k)) at h
  exact h

def suzukiDF6D4FixedGridShard160EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard160EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard160EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard160EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard160EvenComparisonData)

theorem suzukiDF6D4FixedGridShard160EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard160EvenSolveData =
      suzukiDF6D4FixedGridShard160EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard160Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard160EvenSolveData =
    suzukiDF6D4FixedGridShard160EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard160EvenCross_eq_live :
    suzukiDF6D4FixedGridShard160EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 160) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard160EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 160)) at h
  exact h

theorem suzukiDF6D4FixedGridShard160EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard160EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 160 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 160 k) := by
    rw [suzukiDF6D4FixedGridShard160EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 160 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160EvenDotSoundness i
          suzukiDF6D4FixedGridShard160EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 160 k) := by
    simpa [suzukiDF6D4FixedGridShard160EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard160EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 160 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 160) := by
    rw [suzukiDF6D4FixedGridShard160EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 160)
  rw [suzukiDF6D4FixedGridShard160EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard160EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard160EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard160EvenDotSoundness i
            suzukiDF6D4FixedGridShard160EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard160EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard160OddComparison_eq_live :
    suzukiDF6D4FixedGridShard160OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 160 k) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard160OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 160 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard160OddCross_eq_live :
    suzukiDF6D4FixedGridShard160OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 160) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard160OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 160)) at h
  exact h

def suzukiDF6D4FixedGridShard160OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard160OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard160OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard160OddDotSoundness i.val
      suzukiDF6D4FixedGridShard160OddComparisonData)

theorem suzukiDF6D4FixedGridShard160OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard160OddSolveData =
      suzukiDF6D4FixedGridShard160OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard160Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard160OddSolveData =
    suzukiDF6D4FixedGridShard160OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard160OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard160OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 160 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 160 k) := by
    rw [suzukiDF6D4FixedGridShard160OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 160 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160OddDotSoundness i
          suzukiDF6D4FixedGridShard160OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 160 k) := by
    simpa [suzukiDF6D4FixedGridShard160OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard160OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 160 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 160) := by
    rw [suzukiDF6D4FixedGridShard160OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 160)
  rw [suzukiDF6D4FixedGridShard160OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard160OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard160OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard160OddDotSoundness i
            suzukiDF6D4FixedGridShard160OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard160OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard160EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard160EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 461) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard160EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 461)) at h
  exact h

theorem suzukiDF6D4FixedGridShard160EvenFull_eq_live :
    suzukiDF6D4FixedGridShard160EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 461) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard160EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 461)) at h
  exact h

def suzukiDF6D4FixedGridShard160EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard160EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard160EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard160EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard160EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard160EvenResidualData =
      suzukiDF6D4FixedGridShard160EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard160Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard160EvenResidualData =
    suzukiDF6D4FixedGridShard160EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard160EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard160EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 461 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 461) := by
    rw [suzukiDF6D4FixedGridShard160EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 461
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160EvenDotSoundness i
          suzukiDF6D4FixedGridShard160EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 461) := by
    simpa [suzukiDF6D4FixedGridShard160EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard160EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 461) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 461) := by
    rw [suzukiDF6D4FixedGridShard160EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 461
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard160EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard160EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard160EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard160EvenDotSoundness i
            suzukiDF6D4FixedGridShard160EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard160EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard160OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard160OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 461) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard160OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 461)) at h
  exact h

theorem suzukiDF6D4FixedGridShard160OddFull_eq_live :
    suzukiDF6D4FixedGridShard160OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 461) := by
  have h := suzukiDF6D4FixedGridShard160Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard160OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 461)) at h
  exact h

def suzukiDF6D4FixedGridShard160OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard160OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard160OddDotSoundness i.val
        suzukiDF6D4FixedGridShard160OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard160OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard160OddResidualData =
      suzukiDF6D4FixedGridShard160OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard160Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard160OddResidualData =
    suzukiDF6D4FixedGridShard160OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard160OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard160OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 461 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 461) := by
    rw [suzukiDF6D4FixedGridShard160OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 461
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160OddDotSoundness i
          suzukiDF6D4FixedGridShard160OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 461) := by
    simpa [suzukiDF6D4FixedGridShard160OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard160OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 461) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard160OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 461) := by
    rw [suzukiDF6D4FixedGridShard160OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 461
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard160OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard160OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard160OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard160OddDotSoundness i
            suzukiDF6D4FixedGridShard160OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard160OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
