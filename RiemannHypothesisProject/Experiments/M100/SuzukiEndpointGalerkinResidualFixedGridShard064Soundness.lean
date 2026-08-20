import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard064Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard064Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard064EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard064EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 64 k) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard064EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 64 k)) at h
  exact h

def suzukiDF6D4FixedGridShard064EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard064EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard064EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard064EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard064EvenComparisonData)

theorem suzukiDF6D4FixedGridShard064EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard064EvenSolveData =
      suzukiDF6D4FixedGridShard064EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard064Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard064EvenSolveData =
    suzukiDF6D4FixedGridShard064EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard064EvenCross_eq_live :
    suzukiDF6D4FixedGridShard064EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 64) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard064EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 64)) at h
  exact h

theorem suzukiDF6D4FixedGridShard064EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard064EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 64 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 64 k) := by
    rw [suzukiDF6D4FixedGridShard064EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 64 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064EvenDotSoundness i
          suzukiDF6D4FixedGridShard064EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 64 k) := by
    simpa [suzukiDF6D4FixedGridShard064EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard064EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 64 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 64) := by
    rw [suzukiDF6D4FixedGridShard064EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 64)
  rw [suzukiDF6D4FixedGridShard064EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard064EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard064EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard064EvenDotSoundness i
            suzukiDF6D4FixedGridShard064EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard064EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard064OddComparison_eq_live :
    suzukiDF6D4FixedGridShard064OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 64 k) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard064OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 64 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard064OddCross_eq_live :
    suzukiDF6D4FixedGridShard064OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 64) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard064OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 64)) at h
  exact h

def suzukiDF6D4FixedGridShard064OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard064OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard064OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard064OddDotSoundness i.val
      suzukiDF6D4FixedGridShard064OddComparisonData)

theorem suzukiDF6D4FixedGridShard064OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard064OddSolveData =
      suzukiDF6D4FixedGridShard064OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard064Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard064OddSolveData =
    suzukiDF6D4FixedGridShard064OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard064OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard064OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 64 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 64 k) := by
    rw [suzukiDF6D4FixedGridShard064OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 64 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064OddDotSoundness i
          suzukiDF6D4FixedGridShard064OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 64 k) := by
    simpa [suzukiDF6D4FixedGridShard064OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard064OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 64 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 64) := by
    rw [suzukiDF6D4FixedGridShard064OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 64)
  rw [suzukiDF6D4FixedGridShard064OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard064OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard064OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard064OddDotSoundness i
            suzukiDF6D4FixedGridShard064OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard064OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard064EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard064EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 365) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard064EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 365)) at h
  exact h

theorem suzukiDF6D4FixedGridShard064EvenFull_eq_live :
    suzukiDF6D4FixedGridShard064EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 365) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard064EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 365)) at h
  exact h

def suzukiDF6D4FixedGridShard064EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard064EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard064EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard064EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard064EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard064EvenResidualData =
      suzukiDF6D4FixedGridShard064EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard064Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard064EvenResidualData =
    suzukiDF6D4FixedGridShard064EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard064EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard064EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 365 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 365) := by
    rw [suzukiDF6D4FixedGridShard064EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 365
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064EvenDotSoundness i
          suzukiDF6D4FixedGridShard064EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 365) := by
    simpa [suzukiDF6D4FixedGridShard064EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard064EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 365) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 365) := by
    rw [suzukiDF6D4FixedGridShard064EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 365
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard064EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard064EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard064EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard064EvenDotSoundness i
            suzukiDF6D4FixedGridShard064EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard064EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard064OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard064OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 365) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard064OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 365)) at h
  exact h

theorem suzukiDF6D4FixedGridShard064OddFull_eq_live :
    suzukiDF6D4FixedGridShard064OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 365) := by
  have h := suzukiDF6D4FixedGridShard064Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard064OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 365)) at h
  exact h

def suzukiDF6D4FixedGridShard064OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard064OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard064OddDotSoundness i.val
        suzukiDF6D4FixedGridShard064OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard064OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard064OddResidualData =
      suzukiDF6D4FixedGridShard064OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard064Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard064OddResidualData =
    suzukiDF6D4FixedGridShard064OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard064OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard064OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 365 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 365) := by
    rw [suzukiDF6D4FixedGridShard064OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 365
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064OddDotSoundness i
          suzukiDF6D4FixedGridShard064OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 365) := by
    simpa [suzukiDF6D4FixedGridShard064OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard064OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 365) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard064OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 365) := by
    rw [suzukiDF6D4FixedGridShard064OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 365
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard064OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard064OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard064OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard064OddDotSoundness i
            suzukiDF6D4FixedGridShard064OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard064OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
