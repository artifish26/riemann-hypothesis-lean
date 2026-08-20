import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard046Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard046Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard046EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard046EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 46 k) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard046EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 46 k)) at h
  exact h

def suzukiDF6D4FixedGridShard046EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard046EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard046EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard046EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard046EvenComparisonData)

theorem suzukiDF6D4FixedGridShard046EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard046EvenSolveData =
      suzukiDF6D4FixedGridShard046EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard046Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard046EvenSolveData =
    suzukiDF6D4FixedGridShard046EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard046EvenCross_eq_live :
    suzukiDF6D4FixedGridShard046EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 46) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard046EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 46)) at h
  exact h

theorem suzukiDF6D4FixedGridShard046EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard046EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 46 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 46 k) := by
    rw [suzukiDF6D4FixedGridShard046EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 46 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046EvenDotSoundness i
          suzukiDF6D4FixedGridShard046EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 46 k) := by
    simpa [suzukiDF6D4FixedGridShard046EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard046EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 46 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 46) := by
    rw [suzukiDF6D4FixedGridShard046EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 46)
  rw [suzukiDF6D4FixedGridShard046EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard046EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard046EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard046EvenDotSoundness i
            suzukiDF6D4FixedGridShard046EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard046EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard046OddComparison_eq_live :
    suzukiDF6D4FixedGridShard046OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 46 k) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard046OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 46 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard046OddCross_eq_live :
    suzukiDF6D4FixedGridShard046OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 46) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard046OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 46)) at h
  exact h

def suzukiDF6D4FixedGridShard046OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard046OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard046OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard046OddDotSoundness i.val
      suzukiDF6D4FixedGridShard046OddComparisonData)

theorem suzukiDF6D4FixedGridShard046OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard046OddSolveData =
      suzukiDF6D4FixedGridShard046OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard046Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard046OddSolveData =
    suzukiDF6D4FixedGridShard046OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard046OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard046OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 46 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 46 k) := by
    rw [suzukiDF6D4FixedGridShard046OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 46 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046OddDotSoundness i
          suzukiDF6D4FixedGridShard046OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 46 k) := by
    simpa [suzukiDF6D4FixedGridShard046OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard046OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 46 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 46) := by
    rw [suzukiDF6D4FixedGridShard046OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 46)
  rw [suzukiDF6D4FixedGridShard046OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard046OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard046OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard046OddDotSoundness i
            suzukiDF6D4FixedGridShard046OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard046OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard046EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard046EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 347) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard046EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 347)) at h
  exact h

theorem suzukiDF6D4FixedGridShard046EvenFull_eq_live :
    suzukiDF6D4FixedGridShard046EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 347) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard046EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 347)) at h
  exact h

def suzukiDF6D4FixedGridShard046EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard046EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard046EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard046EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard046EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard046EvenResidualData =
      suzukiDF6D4FixedGridShard046EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard046Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard046EvenResidualData =
    suzukiDF6D4FixedGridShard046EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard046EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard046EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 347 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 347) := by
    rw [suzukiDF6D4FixedGridShard046EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 347
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046EvenDotSoundness i
          suzukiDF6D4FixedGridShard046EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 347) := by
    simpa [suzukiDF6D4FixedGridShard046EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard046EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 347) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 347) := by
    rw [suzukiDF6D4FixedGridShard046EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 347
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard046EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard046EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard046EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard046EvenDotSoundness i
            suzukiDF6D4FixedGridShard046EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard046EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard046OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard046OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 347) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard046OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 347)) at h
  exact h

theorem suzukiDF6D4FixedGridShard046OddFull_eq_live :
    suzukiDF6D4FixedGridShard046OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 347) := by
  have h := suzukiDF6D4FixedGridShard046Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard046OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 347)) at h
  exact h

def suzukiDF6D4FixedGridShard046OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard046OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard046OddDotSoundness i.val
        suzukiDF6D4FixedGridShard046OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard046OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard046OddResidualData =
      suzukiDF6D4FixedGridShard046OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard046Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard046OddResidualData =
    suzukiDF6D4FixedGridShard046OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard046OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard046OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 347 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 347) := by
    rw [suzukiDF6D4FixedGridShard046OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 347
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046OddDotSoundness i
          suzukiDF6D4FixedGridShard046OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 347) := by
    simpa [suzukiDF6D4FixedGridShard046OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard046OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 347) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard046OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 347) := by
    rw [suzukiDF6D4FixedGridShard046OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 347
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard046OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard046OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard046OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard046OddDotSoundness i
            suzukiDF6D4FixedGridShard046OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard046OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
