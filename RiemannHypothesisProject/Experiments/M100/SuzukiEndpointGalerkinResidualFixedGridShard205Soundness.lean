import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard205Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard205Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard205EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard205EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 205 k) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard205EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 205 k)) at h
  exact h

def suzukiDF6D4FixedGridShard205EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard205EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard205EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard205EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard205EvenComparisonData)

theorem suzukiDF6D4FixedGridShard205EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard205EvenSolveData =
      suzukiDF6D4FixedGridShard205EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard205Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard205EvenSolveData =
    suzukiDF6D4FixedGridShard205EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard205EvenCross_eq_live :
    suzukiDF6D4FixedGridShard205EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 205) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard205EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 205)) at h
  exact h

theorem suzukiDF6D4FixedGridShard205EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard205EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 205 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 205 k) := by
    rw [suzukiDF6D4FixedGridShard205EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 205 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205EvenDotSoundness i
          suzukiDF6D4FixedGridShard205EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 205 k) := by
    simpa [suzukiDF6D4FixedGridShard205EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard205EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 205 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 205) := by
    rw [suzukiDF6D4FixedGridShard205EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 205)
  rw [suzukiDF6D4FixedGridShard205EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard205EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard205EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard205EvenDotSoundness i
            suzukiDF6D4FixedGridShard205EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard205EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard205OddComparison_eq_live :
    suzukiDF6D4FixedGridShard205OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 205 k) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard205OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 205 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard205OddCross_eq_live :
    suzukiDF6D4FixedGridShard205OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 205) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard205OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 205)) at h
  exact h

def suzukiDF6D4FixedGridShard205OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard205OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard205OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard205OddDotSoundness i.val
      suzukiDF6D4FixedGridShard205OddComparisonData)

theorem suzukiDF6D4FixedGridShard205OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard205OddSolveData =
      suzukiDF6D4FixedGridShard205OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard205Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard205OddSolveData =
    suzukiDF6D4FixedGridShard205OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard205OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard205OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 205 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 205 k) := by
    rw [suzukiDF6D4FixedGridShard205OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 205 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205OddDotSoundness i
          suzukiDF6D4FixedGridShard205OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 205 k) := by
    simpa [suzukiDF6D4FixedGridShard205OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard205OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 205 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 205) := by
    rw [suzukiDF6D4FixedGridShard205OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 205)
  rw [suzukiDF6D4FixedGridShard205OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard205OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard205OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard205OddDotSoundness i
            suzukiDF6D4FixedGridShard205OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard205OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard205EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard205EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 506) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard205EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 506)) at h
  exact h

theorem suzukiDF6D4FixedGridShard205EvenFull_eq_live :
    suzukiDF6D4FixedGridShard205EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 506) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard205EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 506)) at h
  exact h

def suzukiDF6D4FixedGridShard205EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard205EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard205EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard205EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard205EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard205EvenResidualData =
      suzukiDF6D4FixedGridShard205EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard205Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard205EvenResidualData =
    suzukiDF6D4FixedGridShard205EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard205EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard205EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 506 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 506) := by
    rw [suzukiDF6D4FixedGridShard205EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 506
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205EvenDotSoundness i
          suzukiDF6D4FixedGridShard205EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 506) := by
    simpa [suzukiDF6D4FixedGridShard205EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard205EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 506) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 506) := by
    rw [suzukiDF6D4FixedGridShard205EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 506
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard205EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard205EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard205EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard205EvenDotSoundness i
            suzukiDF6D4FixedGridShard205EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard205EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard205OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard205OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 506) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard205OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 506)) at h
  exact h

theorem suzukiDF6D4FixedGridShard205OddFull_eq_live :
    suzukiDF6D4FixedGridShard205OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 506) := by
  have h := suzukiDF6D4FixedGridShard205Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard205OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 506)) at h
  exact h

def suzukiDF6D4FixedGridShard205OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard205OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard205OddDotSoundness i.val
        suzukiDF6D4FixedGridShard205OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard205OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard205OddResidualData =
      suzukiDF6D4FixedGridShard205OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard205Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard205OddResidualData =
    suzukiDF6D4FixedGridShard205OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard205OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard205OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 506 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 506) := by
    rw [suzukiDF6D4FixedGridShard205OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 506
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205OddDotSoundness i
          suzukiDF6D4FixedGridShard205OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 506) := by
    simpa [suzukiDF6D4FixedGridShard205OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard205OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 506) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard205OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 506) := by
    rw [suzukiDF6D4FixedGridShard205OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 506
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard205OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard205OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard205OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard205OddDotSoundness i
            suzukiDF6D4FixedGridShard205OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard205OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
