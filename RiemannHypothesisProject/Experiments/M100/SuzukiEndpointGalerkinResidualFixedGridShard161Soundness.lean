import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard161Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard161Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard161EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard161EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 161 k) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard161EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 161 k)) at h
  exact h

def suzukiDF6D4FixedGridShard161EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard161EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard161EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard161EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard161EvenComparisonData)

theorem suzukiDF6D4FixedGridShard161EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard161EvenSolveData =
      suzukiDF6D4FixedGridShard161EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard161Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard161EvenSolveData =
    suzukiDF6D4FixedGridShard161EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard161EvenCross_eq_live :
    suzukiDF6D4FixedGridShard161EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 161) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard161EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 161)) at h
  exact h

theorem suzukiDF6D4FixedGridShard161EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard161EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 161 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 161 k) := by
    rw [suzukiDF6D4FixedGridShard161EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 161 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161EvenDotSoundness i
          suzukiDF6D4FixedGridShard161EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 161 k) := by
    simpa [suzukiDF6D4FixedGridShard161EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard161EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 161 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 161) := by
    rw [suzukiDF6D4FixedGridShard161EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 161)
  rw [suzukiDF6D4FixedGridShard161EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard161EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard161EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard161EvenDotSoundness i
            suzukiDF6D4FixedGridShard161EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard161EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard161OddComparison_eq_live :
    suzukiDF6D4FixedGridShard161OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 161 k) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard161OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 161 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard161OddCross_eq_live :
    suzukiDF6D4FixedGridShard161OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 161) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard161OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 161)) at h
  exact h

def suzukiDF6D4FixedGridShard161OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard161OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard161OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard161OddDotSoundness i.val
      suzukiDF6D4FixedGridShard161OddComparisonData)

theorem suzukiDF6D4FixedGridShard161OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard161OddSolveData =
      suzukiDF6D4FixedGridShard161OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard161Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard161OddSolveData =
    suzukiDF6D4FixedGridShard161OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard161OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard161OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 161 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 161 k) := by
    rw [suzukiDF6D4FixedGridShard161OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 161 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161OddDotSoundness i
          suzukiDF6D4FixedGridShard161OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 161 k) := by
    simpa [suzukiDF6D4FixedGridShard161OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard161OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 161 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 161) := by
    rw [suzukiDF6D4FixedGridShard161OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 161)
  rw [suzukiDF6D4FixedGridShard161OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard161OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard161OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard161OddDotSoundness i
            suzukiDF6D4FixedGridShard161OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard161OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard161EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard161EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 462) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard161EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 462)) at h
  exact h

theorem suzukiDF6D4FixedGridShard161EvenFull_eq_live :
    suzukiDF6D4FixedGridShard161EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 462) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard161EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 462)) at h
  exact h

def suzukiDF6D4FixedGridShard161EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard161EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard161EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard161EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard161EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard161EvenResidualData =
      suzukiDF6D4FixedGridShard161EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard161Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard161EvenResidualData =
    suzukiDF6D4FixedGridShard161EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard161EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard161EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 462 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 462) := by
    rw [suzukiDF6D4FixedGridShard161EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 462
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161EvenDotSoundness i
          suzukiDF6D4FixedGridShard161EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 462) := by
    simpa [suzukiDF6D4FixedGridShard161EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard161EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 462) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 462) := by
    rw [suzukiDF6D4FixedGridShard161EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 462
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard161EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard161EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard161EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard161EvenDotSoundness i
            suzukiDF6D4FixedGridShard161EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard161EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard161OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard161OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 462) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard161OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 462)) at h
  exact h

theorem suzukiDF6D4FixedGridShard161OddFull_eq_live :
    suzukiDF6D4FixedGridShard161OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 462) := by
  have h := suzukiDF6D4FixedGridShard161Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard161OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 462)) at h
  exact h

def suzukiDF6D4FixedGridShard161OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard161OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard161OddDotSoundness i.val
        suzukiDF6D4FixedGridShard161OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard161OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard161OddResidualData =
      suzukiDF6D4FixedGridShard161OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard161Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard161OddResidualData =
    suzukiDF6D4FixedGridShard161OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard161OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard161OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 462 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 462) := by
    rw [suzukiDF6D4FixedGridShard161OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 462
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161OddDotSoundness i
          suzukiDF6D4FixedGridShard161OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 462) := by
    simpa [suzukiDF6D4FixedGridShard161OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard161OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 462) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard161OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 462) := by
    rw [suzukiDF6D4FixedGridShard161OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 462
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard161OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard161OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard161OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard161OddDotSoundness i
            suzukiDF6D4FixedGridShard161OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard161OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
