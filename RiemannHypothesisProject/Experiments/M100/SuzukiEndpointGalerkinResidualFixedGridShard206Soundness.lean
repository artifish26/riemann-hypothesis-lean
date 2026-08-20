import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard206Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard206Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard206EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard206EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 206 k) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard206EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 206 k)) at h
  exact h

def suzukiDF6D4FixedGridShard206EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard206EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard206EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard206EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard206EvenComparisonData)

theorem suzukiDF6D4FixedGridShard206EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard206EvenSolveData =
      suzukiDF6D4FixedGridShard206EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard206Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard206EvenSolveData =
    suzukiDF6D4FixedGridShard206EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard206EvenCross_eq_live :
    suzukiDF6D4FixedGridShard206EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 206) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard206EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 206)) at h
  exact h

theorem suzukiDF6D4FixedGridShard206EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard206EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 206 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 206 k) := by
    rw [suzukiDF6D4FixedGridShard206EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 206 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206EvenDotSoundness i
          suzukiDF6D4FixedGridShard206EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 206 k) := by
    simpa [suzukiDF6D4FixedGridShard206EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard206EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 206 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 206) := by
    rw [suzukiDF6D4FixedGridShard206EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 206)
  rw [suzukiDF6D4FixedGridShard206EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard206EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard206EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard206EvenDotSoundness i
            suzukiDF6D4FixedGridShard206EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard206EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard206OddComparison_eq_live :
    suzukiDF6D4FixedGridShard206OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 206 k) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard206OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 206 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard206OddCross_eq_live :
    suzukiDF6D4FixedGridShard206OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 206) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard206OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 206)) at h
  exact h

def suzukiDF6D4FixedGridShard206OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard206OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard206OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard206OddDotSoundness i.val
      suzukiDF6D4FixedGridShard206OddComparisonData)

theorem suzukiDF6D4FixedGridShard206OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard206OddSolveData =
      suzukiDF6D4FixedGridShard206OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard206Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard206OddSolveData =
    suzukiDF6D4FixedGridShard206OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard206OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard206OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 206 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 206 k) := by
    rw [suzukiDF6D4FixedGridShard206OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 206 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206OddDotSoundness i
          suzukiDF6D4FixedGridShard206OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 206 k) := by
    simpa [suzukiDF6D4FixedGridShard206OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard206OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 206 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 206) := by
    rw [suzukiDF6D4FixedGridShard206OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 206)
  rw [suzukiDF6D4FixedGridShard206OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard206OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard206OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard206OddDotSoundness i
            suzukiDF6D4FixedGridShard206OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard206OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard206EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard206EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 507) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard206EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 507)) at h
  exact h

theorem suzukiDF6D4FixedGridShard206EvenFull_eq_live :
    suzukiDF6D4FixedGridShard206EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 507) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard206EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 507)) at h
  exact h

def suzukiDF6D4FixedGridShard206EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard206EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard206EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard206EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard206EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard206EvenResidualData =
      suzukiDF6D4FixedGridShard206EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard206Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard206EvenResidualData =
    suzukiDF6D4FixedGridShard206EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard206EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard206EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 507 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 507) := by
    rw [suzukiDF6D4FixedGridShard206EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 507
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206EvenDotSoundness i
          suzukiDF6D4FixedGridShard206EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 507) := by
    simpa [suzukiDF6D4FixedGridShard206EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard206EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 507) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 507) := by
    rw [suzukiDF6D4FixedGridShard206EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 507
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard206EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard206EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard206EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard206EvenDotSoundness i
            suzukiDF6D4FixedGridShard206EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard206EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard206OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard206OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 507) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard206OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 507)) at h
  exact h

theorem suzukiDF6D4FixedGridShard206OddFull_eq_live :
    suzukiDF6D4FixedGridShard206OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 507) := by
  have h := suzukiDF6D4FixedGridShard206Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard206OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 507)) at h
  exact h

def suzukiDF6D4FixedGridShard206OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard206OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard206OddDotSoundness i.val
        suzukiDF6D4FixedGridShard206OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard206OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard206OddResidualData =
      suzukiDF6D4FixedGridShard206OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard206Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard206OddResidualData =
    suzukiDF6D4FixedGridShard206OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard206OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard206OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 507 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 507) := by
    rw [suzukiDF6D4FixedGridShard206OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 507
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206OddDotSoundness i
          suzukiDF6D4FixedGridShard206OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 507) := by
    simpa [suzukiDF6D4FixedGridShard206OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard206OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 507) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard206OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 507) := by
    rw [suzukiDF6D4FixedGridShard206OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 507
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard206OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard206OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard206OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard206OddDotSoundness i
            suzukiDF6D4FixedGridShard206OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard206OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
