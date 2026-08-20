import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard168Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard168Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard168EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard168EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 168 k) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard168EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 168 k)) at h
  exact h

def suzukiDF6D4FixedGridShard168EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard168EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard168EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard168EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard168EvenComparisonData)

theorem suzukiDF6D4FixedGridShard168EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard168EvenSolveData =
      suzukiDF6D4FixedGridShard168EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard168Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard168EvenSolveData =
    suzukiDF6D4FixedGridShard168EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard168EvenCross_eq_live :
    suzukiDF6D4FixedGridShard168EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 168) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard168EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 168)) at h
  exact h

theorem suzukiDF6D4FixedGridShard168EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard168EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 168 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 168 k) := by
    rw [suzukiDF6D4FixedGridShard168EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 168 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168EvenDotSoundness i
          suzukiDF6D4FixedGridShard168EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 168 k) := by
    simpa [suzukiDF6D4FixedGridShard168EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard168EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 168 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 168) := by
    rw [suzukiDF6D4FixedGridShard168EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 168)
  rw [suzukiDF6D4FixedGridShard168EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard168EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard168EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard168EvenDotSoundness i
            suzukiDF6D4FixedGridShard168EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard168EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard168OddComparison_eq_live :
    suzukiDF6D4FixedGridShard168OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 168 k) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard168OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 168 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard168OddCross_eq_live :
    suzukiDF6D4FixedGridShard168OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 168) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard168OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 168)) at h
  exact h

def suzukiDF6D4FixedGridShard168OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard168OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard168OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard168OddDotSoundness i.val
      suzukiDF6D4FixedGridShard168OddComparisonData)

theorem suzukiDF6D4FixedGridShard168OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard168OddSolveData =
      suzukiDF6D4FixedGridShard168OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard168Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard168OddSolveData =
    suzukiDF6D4FixedGridShard168OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard168OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard168OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 168 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 168 k) := by
    rw [suzukiDF6D4FixedGridShard168OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 168 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168OddDotSoundness i
          suzukiDF6D4FixedGridShard168OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 168 k) := by
    simpa [suzukiDF6D4FixedGridShard168OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard168OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 168 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 168) := by
    rw [suzukiDF6D4FixedGridShard168OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 168)
  rw [suzukiDF6D4FixedGridShard168OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard168OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard168OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard168OddDotSoundness i
            suzukiDF6D4FixedGridShard168OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard168OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard168EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard168EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 469) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard168EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 469)) at h
  exact h

theorem suzukiDF6D4FixedGridShard168EvenFull_eq_live :
    suzukiDF6D4FixedGridShard168EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 469) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard168EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 469)) at h
  exact h

def suzukiDF6D4FixedGridShard168EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard168EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard168EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard168EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard168EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard168EvenResidualData =
      suzukiDF6D4FixedGridShard168EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard168Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard168EvenResidualData =
    suzukiDF6D4FixedGridShard168EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard168EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard168EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 469 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 469) := by
    rw [suzukiDF6D4FixedGridShard168EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 469
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168EvenDotSoundness i
          suzukiDF6D4FixedGridShard168EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 469) := by
    simpa [suzukiDF6D4FixedGridShard168EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard168EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 469) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 469) := by
    rw [suzukiDF6D4FixedGridShard168EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 469
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard168EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard168EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard168EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard168EvenDotSoundness i
            suzukiDF6D4FixedGridShard168EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard168EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard168OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard168OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 469) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard168OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 469)) at h
  exact h

theorem suzukiDF6D4FixedGridShard168OddFull_eq_live :
    suzukiDF6D4FixedGridShard168OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 469) := by
  have h := suzukiDF6D4FixedGridShard168Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard168OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 469)) at h
  exact h

def suzukiDF6D4FixedGridShard168OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard168OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard168OddDotSoundness i.val
        suzukiDF6D4FixedGridShard168OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard168OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard168OddResidualData =
      suzukiDF6D4FixedGridShard168OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard168Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard168OddResidualData =
    suzukiDF6D4FixedGridShard168OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard168OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard168OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 469 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 469) := by
    rw [suzukiDF6D4FixedGridShard168OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 469
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168OddDotSoundness i
          suzukiDF6D4FixedGridShard168OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 469) := by
    simpa [suzukiDF6D4FixedGridShard168OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard168OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 469) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard168OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 469) := by
    rw [suzukiDF6D4FixedGridShard168OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 469
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard168OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard168OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard168OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard168OddDotSoundness i
            suzukiDF6D4FixedGridShard168OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard168OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
