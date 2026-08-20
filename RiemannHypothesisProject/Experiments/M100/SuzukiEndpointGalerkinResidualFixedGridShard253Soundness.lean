import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard253Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard253Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard253EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard253EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 253 k) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard253EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 253 k)) at h
  exact h

def suzukiDF6D4FixedGridShard253EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard253EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard253EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard253EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard253EvenComparisonData)

theorem suzukiDF6D4FixedGridShard253EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard253EvenSolveData =
      suzukiDF6D4FixedGridShard253EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard253Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard253EvenSolveData =
    suzukiDF6D4FixedGridShard253EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard253EvenCross_eq_live :
    suzukiDF6D4FixedGridShard253EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 253) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard253EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 253)) at h
  exact h

theorem suzukiDF6D4FixedGridShard253EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard253EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 253 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 253 k) := by
    rw [suzukiDF6D4FixedGridShard253EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 253 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253EvenDotSoundness i
          suzukiDF6D4FixedGridShard253EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 253 k) := by
    simpa [suzukiDF6D4FixedGridShard253EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard253EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 253 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 253) := by
    rw [suzukiDF6D4FixedGridShard253EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 253)
  rw [suzukiDF6D4FixedGridShard253EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard253EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard253EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard253EvenDotSoundness i
            suzukiDF6D4FixedGridShard253EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard253EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard253OddComparison_eq_live :
    suzukiDF6D4FixedGridShard253OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 253 k) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard253OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 253 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard253OddCross_eq_live :
    suzukiDF6D4FixedGridShard253OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 253) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard253OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 253)) at h
  exact h

def suzukiDF6D4FixedGridShard253OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard253OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard253OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard253OddDotSoundness i.val
      suzukiDF6D4FixedGridShard253OddComparisonData)

theorem suzukiDF6D4FixedGridShard253OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard253OddSolveData =
      suzukiDF6D4FixedGridShard253OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard253Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard253OddSolveData =
    suzukiDF6D4FixedGridShard253OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard253OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard253OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 253 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 253 k) := by
    rw [suzukiDF6D4FixedGridShard253OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 253 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253OddDotSoundness i
          suzukiDF6D4FixedGridShard253OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 253 k) := by
    simpa [suzukiDF6D4FixedGridShard253OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard253OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 253 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 253) := by
    rw [suzukiDF6D4FixedGridShard253OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 253)
  rw [suzukiDF6D4FixedGridShard253OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard253OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard253OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard253OddDotSoundness i
            suzukiDF6D4FixedGridShard253OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard253OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard253EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard253EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 554) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard253EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 554)) at h
  exact h

theorem suzukiDF6D4FixedGridShard253EvenFull_eq_live :
    suzukiDF6D4FixedGridShard253EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 554) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard253EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 554)) at h
  exact h

def suzukiDF6D4FixedGridShard253EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard253EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard253EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard253EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard253EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard253EvenResidualData =
      suzukiDF6D4FixedGridShard253EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard253Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard253EvenResidualData =
    suzukiDF6D4FixedGridShard253EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard253EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard253EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 554 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 554) := by
    rw [suzukiDF6D4FixedGridShard253EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 554
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253EvenDotSoundness i
          suzukiDF6D4FixedGridShard253EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 554) := by
    simpa [suzukiDF6D4FixedGridShard253EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard253EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 554) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 554) := by
    rw [suzukiDF6D4FixedGridShard253EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 554
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard253EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard253EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard253EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard253EvenDotSoundness i
            suzukiDF6D4FixedGridShard253EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard253EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard253OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard253OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 554) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard253OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 554)) at h
  exact h

theorem suzukiDF6D4FixedGridShard253OddFull_eq_live :
    suzukiDF6D4FixedGridShard253OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 554) := by
  have h := suzukiDF6D4FixedGridShard253Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard253OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 554)) at h
  exact h

def suzukiDF6D4FixedGridShard253OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard253OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard253OddDotSoundness i.val
        suzukiDF6D4FixedGridShard253OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard253OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard253OddResidualData =
      suzukiDF6D4FixedGridShard253OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard253Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard253OddResidualData =
    suzukiDF6D4FixedGridShard253OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard253OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard253OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 554 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 554) := by
    rw [suzukiDF6D4FixedGridShard253OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 554
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253OddDotSoundness i
          suzukiDF6D4FixedGridShard253OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 554) := by
    simpa [suzukiDF6D4FixedGridShard253OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard253OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 554) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard253OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 554) := by
    rw [suzukiDF6D4FixedGridShard253OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 554
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard253OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard253OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard253OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard253OddDotSoundness i
            suzukiDF6D4FixedGridShard253OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard253OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
