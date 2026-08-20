import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard025Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard025Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard025EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard025EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 25 k) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard025EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 25 k)) at h
  exact h

def suzukiDF6D4FixedGridShard025EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard025EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard025EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard025EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard025EvenComparisonData)

theorem suzukiDF6D4FixedGridShard025EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard025EvenSolveData =
      suzukiDF6D4FixedGridShard025EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard025Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard025EvenSolveData =
    suzukiDF6D4FixedGridShard025EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard025EvenCross_eq_live :
    suzukiDF6D4FixedGridShard025EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 25) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard025EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 25)) at h
  exact h

theorem suzukiDF6D4FixedGridShard025EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard025EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 25 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 25 k) := by
    rw [suzukiDF6D4FixedGridShard025EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 25 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025EvenDotSoundness i
          suzukiDF6D4FixedGridShard025EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 25 k) := by
    simpa [suzukiDF6D4FixedGridShard025EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard025EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 25 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 25) := by
    rw [suzukiDF6D4FixedGridShard025EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 25)
  rw [suzukiDF6D4FixedGridShard025EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard025EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard025EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard025EvenDotSoundness i
            suzukiDF6D4FixedGridShard025EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard025EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard025OddComparison_eq_live :
    suzukiDF6D4FixedGridShard025OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 25 k) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard025OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 25 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard025OddCross_eq_live :
    suzukiDF6D4FixedGridShard025OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 25) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard025OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 25)) at h
  exact h

def suzukiDF6D4FixedGridShard025OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard025OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard025OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard025OddDotSoundness i.val
      suzukiDF6D4FixedGridShard025OddComparisonData)

theorem suzukiDF6D4FixedGridShard025OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard025OddSolveData =
      suzukiDF6D4FixedGridShard025OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard025Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard025OddSolveData =
    suzukiDF6D4FixedGridShard025OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard025OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard025OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 25 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 25 k) := by
    rw [suzukiDF6D4FixedGridShard025OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 25 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025OddDotSoundness i
          suzukiDF6D4FixedGridShard025OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 25 k) := by
    simpa [suzukiDF6D4FixedGridShard025OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard025OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 25 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 25) := by
    rw [suzukiDF6D4FixedGridShard025OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 25)
  rw [suzukiDF6D4FixedGridShard025OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard025OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard025OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard025OddDotSoundness i
            suzukiDF6D4FixedGridShard025OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard025OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard025EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard025EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 326) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard025EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 326)) at h
  exact h

theorem suzukiDF6D4FixedGridShard025EvenFull_eq_live :
    suzukiDF6D4FixedGridShard025EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 326) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard025EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 326)) at h
  exact h

def suzukiDF6D4FixedGridShard025EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard025EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard025EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard025EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard025EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard025EvenResidualData =
      suzukiDF6D4FixedGridShard025EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard025Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard025EvenResidualData =
    suzukiDF6D4FixedGridShard025EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard025EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard025EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 326 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 326) := by
    rw [suzukiDF6D4FixedGridShard025EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 326
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025EvenDotSoundness i
          suzukiDF6D4FixedGridShard025EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 326) := by
    simpa [suzukiDF6D4FixedGridShard025EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard025EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 326) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 326) := by
    rw [suzukiDF6D4FixedGridShard025EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 326
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard025EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard025EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard025EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard025EvenDotSoundness i
            suzukiDF6D4FixedGridShard025EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard025EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard025OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard025OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 326) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard025OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 326)) at h
  exact h

theorem suzukiDF6D4FixedGridShard025OddFull_eq_live :
    suzukiDF6D4FixedGridShard025OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 326) := by
  have h := suzukiDF6D4FixedGridShard025Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard025OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 326)) at h
  exact h

def suzukiDF6D4FixedGridShard025OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard025OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard025OddDotSoundness i.val
        suzukiDF6D4FixedGridShard025OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard025OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard025OddResidualData =
      suzukiDF6D4FixedGridShard025OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard025Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard025OddResidualData =
    suzukiDF6D4FixedGridShard025OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard025OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard025OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 326 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 326) := by
    rw [suzukiDF6D4FixedGridShard025OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 326
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025OddDotSoundness i
          suzukiDF6D4FixedGridShard025OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 326) := by
    simpa [suzukiDF6D4FixedGridShard025OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard025OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 326) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard025OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 326) := by
    rw [suzukiDF6D4FixedGridShard025OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 326
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard025OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard025OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard025OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard025OddDotSoundness i
            suzukiDF6D4FixedGridShard025OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard025OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
