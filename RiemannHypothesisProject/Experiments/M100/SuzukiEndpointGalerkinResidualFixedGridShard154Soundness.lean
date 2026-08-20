import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard154Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard154Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard154EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard154EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 154 k) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard154EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 154 k)) at h
  exact h

def suzukiDF6D4FixedGridShard154EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard154EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard154EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard154EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard154EvenComparisonData)

theorem suzukiDF6D4FixedGridShard154EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard154EvenSolveData =
      suzukiDF6D4FixedGridShard154EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard154Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard154EvenSolveData =
    suzukiDF6D4FixedGridShard154EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard154EvenCross_eq_live :
    suzukiDF6D4FixedGridShard154EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 154) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard154EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 154)) at h
  exact h

theorem suzukiDF6D4FixedGridShard154EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard154EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 154 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 154 k) := by
    rw [suzukiDF6D4FixedGridShard154EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 154 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154EvenDotSoundness i
          suzukiDF6D4FixedGridShard154EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 154 k) := by
    simpa [suzukiDF6D4FixedGridShard154EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard154EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 154 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 154) := by
    rw [suzukiDF6D4FixedGridShard154EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 154)
  rw [suzukiDF6D4FixedGridShard154EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard154EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard154EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard154EvenDotSoundness i
            suzukiDF6D4FixedGridShard154EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard154EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard154OddComparison_eq_live :
    suzukiDF6D4FixedGridShard154OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 154 k) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard154OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 154 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard154OddCross_eq_live :
    suzukiDF6D4FixedGridShard154OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 154) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard154OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 154)) at h
  exact h

def suzukiDF6D4FixedGridShard154OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard154OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard154OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard154OddDotSoundness i.val
      suzukiDF6D4FixedGridShard154OddComparisonData)

theorem suzukiDF6D4FixedGridShard154OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard154OddSolveData =
      suzukiDF6D4FixedGridShard154OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard154Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard154OddSolveData =
    suzukiDF6D4FixedGridShard154OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard154OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard154OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 154 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 154 k) := by
    rw [suzukiDF6D4FixedGridShard154OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 154 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154OddDotSoundness i
          suzukiDF6D4FixedGridShard154OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 154 k) := by
    simpa [suzukiDF6D4FixedGridShard154OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard154OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 154 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 154) := by
    rw [suzukiDF6D4FixedGridShard154OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 154)
  rw [suzukiDF6D4FixedGridShard154OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard154OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard154OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard154OddDotSoundness i
            suzukiDF6D4FixedGridShard154OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard154OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard154EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard154EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 455) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard154EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 455)) at h
  exact h

theorem suzukiDF6D4FixedGridShard154EvenFull_eq_live :
    suzukiDF6D4FixedGridShard154EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 455) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard154EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 455)) at h
  exact h

def suzukiDF6D4FixedGridShard154EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard154EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard154EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard154EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard154EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard154EvenResidualData =
      suzukiDF6D4FixedGridShard154EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard154Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard154EvenResidualData =
    suzukiDF6D4FixedGridShard154EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard154EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard154EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 455 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 455) := by
    rw [suzukiDF6D4FixedGridShard154EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 455
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154EvenDotSoundness i
          suzukiDF6D4FixedGridShard154EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 455) := by
    simpa [suzukiDF6D4FixedGridShard154EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard154EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 455) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 455) := by
    rw [suzukiDF6D4FixedGridShard154EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 455
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard154EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard154EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard154EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard154EvenDotSoundness i
            suzukiDF6D4FixedGridShard154EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard154EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard154OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard154OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 455) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard154OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 455)) at h
  exact h

theorem suzukiDF6D4FixedGridShard154OddFull_eq_live :
    suzukiDF6D4FixedGridShard154OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 455) := by
  have h := suzukiDF6D4FixedGridShard154Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard154OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 455)) at h
  exact h

def suzukiDF6D4FixedGridShard154OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard154OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard154OddDotSoundness i.val
        suzukiDF6D4FixedGridShard154OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard154OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard154OddResidualData =
      suzukiDF6D4FixedGridShard154OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard154Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard154OddResidualData =
    suzukiDF6D4FixedGridShard154OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard154OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard154OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 455 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 455) := by
    rw [suzukiDF6D4FixedGridShard154OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 455
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154OddDotSoundness i
          suzukiDF6D4FixedGridShard154OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 455) := by
    simpa [suzukiDF6D4FixedGridShard154OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard154OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 455) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard154OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 455) := by
    rw [suzukiDF6D4FixedGridShard154OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 455
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard154OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard154OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard154OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard154OddDotSoundness i
            suzukiDF6D4FixedGridShard154OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard154OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
