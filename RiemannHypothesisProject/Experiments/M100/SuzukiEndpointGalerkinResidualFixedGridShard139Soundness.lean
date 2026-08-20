import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard139Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard139Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard139EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard139EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 139 k) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard139EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 139 k)) at h
  exact h

def suzukiDF6D4FixedGridShard139EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard139EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard139EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard139EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard139EvenComparisonData)

theorem suzukiDF6D4FixedGridShard139EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard139EvenSolveData =
      suzukiDF6D4FixedGridShard139EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard139Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard139EvenSolveData =
    suzukiDF6D4FixedGridShard139EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard139EvenCross_eq_live :
    suzukiDF6D4FixedGridShard139EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 139) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard139EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 139)) at h
  exact h

theorem suzukiDF6D4FixedGridShard139EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard139EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 139 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 139 k) := by
    rw [suzukiDF6D4FixedGridShard139EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 139 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139EvenDotSoundness i
          suzukiDF6D4FixedGridShard139EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 139 k) := by
    simpa [suzukiDF6D4FixedGridShard139EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard139EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 139 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 139) := by
    rw [suzukiDF6D4FixedGridShard139EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 139)
  rw [suzukiDF6D4FixedGridShard139EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard139EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard139EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard139EvenDotSoundness i
            suzukiDF6D4FixedGridShard139EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard139EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard139OddComparison_eq_live :
    suzukiDF6D4FixedGridShard139OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 139 k) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard139OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 139 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard139OddCross_eq_live :
    suzukiDF6D4FixedGridShard139OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 139) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard139OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 139)) at h
  exact h

def suzukiDF6D4FixedGridShard139OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard139OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard139OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard139OddDotSoundness i.val
      suzukiDF6D4FixedGridShard139OddComparisonData)

theorem suzukiDF6D4FixedGridShard139OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard139OddSolveData =
      suzukiDF6D4FixedGridShard139OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard139Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard139OddSolveData =
    suzukiDF6D4FixedGridShard139OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard139OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard139OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 139 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 139 k) := by
    rw [suzukiDF6D4FixedGridShard139OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 139 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139OddDotSoundness i
          suzukiDF6D4FixedGridShard139OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 139 k) := by
    simpa [suzukiDF6D4FixedGridShard139OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard139OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 139 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 139) := by
    rw [suzukiDF6D4FixedGridShard139OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 139)
  rw [suzukiDF6D4FixedGridShard139OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard139OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard139OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard139OddDotSoundness i
            suzukiDF6D4FixedGridShard139OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard139OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard139EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard139EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 440) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard139EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 440)) at h
  exact h

theorem suzukiDF6D4FixedGridShard139EvenFull_eq_live :
    suzukiDF6D4FixedGridShard139EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 440) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard139EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 440)) at h
  exact h

def suzukiDF6D4FixedGridShard139EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard139EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard139EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard139EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard139EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard139EvenResidualData =
      suzukiDF6D4FixedGridShard139EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard139Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard139EvenResidualData =
    suzukiDF6D4FixedGridShard139EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard139EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard139EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 440 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 440) := by
    rw [suzukiDF6D4FixedGridShard139EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 440
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139EvenDotSoundness i
          suzukiDF6D4FixedGridShard139EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 440) := by
    simpa [suzukiDF6D4FixedGridShard139EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard139EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 440) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 440) := by
    rw [suzukiDF6D4FixedGridShard139EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 440
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard139EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard139EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard139EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard139EvenDotSoundness i
            suzukiDF6D4FixedGridShard139EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard139EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard139OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard139OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 440) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard139OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 440)) at h
  exact h

theorem suzukiDF6D4FixedGridShard139OddFull_eq_live :
    suzukiDF6D4FixedGridShard139OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 440) := by
  have h := suzukiDF6D4FixedGridShard139Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard139OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 440)) at h
  exact h

def suzukiDF6D4FixedGridShard139OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard139OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard139OddDotSoundness i.val
        suzukiDF6D4FixedGridShard139OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard139OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard139OddResidualData =
      suzukiDF6D4FixedGridShard139OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard139Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard139OddResidualData =
    suzukiDF6D4FixedGridShard139OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard139OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard139OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 440 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 440) := by
    rw [suzukiDF6D4FixedGridShard139OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 440
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139OddDotSoundness i
          suzukiDF6D4FixedGridShard139OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 440) := by
    simpa [suzukiDF6D4FixedGridShard139OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard139OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 440) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard139OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 440) := by
    rw [suzukiDF6D4FixedGridShard139OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 440
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard139OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard139OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard139OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard139OddDotSoundness i
            suzukiDF6D4FixedGridShard139OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard139OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
