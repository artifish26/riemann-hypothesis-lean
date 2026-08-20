import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard031Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard031Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard031EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard031EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 31 k) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard031EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 31 k)) at h
  exact h

def suzukiDF6D4FixedGridShard031EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard031EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard031EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard031EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard031EvenComparisonData)

theorem suzukiDF6D4FixedGridShard031EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard031EvenSolveData =
      suzukiDF6D4FixedGridShard031EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard031Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard031EvenSolveData =
    suzukiDF6D4FixedGridShard031EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard031EvenCross_eq_live :
    suzukiDF6D4FixedGridShard031EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 31) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard031EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 31)) at h
  exact h

theorem suzukiDF6D4FixedGridShard031EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard031EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 31 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 31 k) := by
    rw [suzukiDF6D4FixedGridShard031EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 31 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031EvenDotSoundness i
          suzukiDF6D4FixedGridShard031EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 31 k) := by
    simpa [suzukiDF6D4FixedGridShard031EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard031EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 31 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 31) := by
    rw [suzukiDF6D4FixedGridShard031EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 31)
  rw [suzukiDF6D4FixedGridShard031EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard031EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard031EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard031EvenDotSoundness i
            suzukiDF6D4FixedGridShard031EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard031EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard031OddComparison_eq_live :
    suzukiDF6D4FixedGridShard031OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 31 k) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard031OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 31 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard031OddCross_eq_live :
    suzukiDF6D4FixedGridShard031OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 31) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard031OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 31)) at h
  exact h

def suzukiDF6D4FixedGridShard031OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard031OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard031OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard031OddDotSoundness i.val
      suzukiDF6D4FixedGridShard031OddComparisonData)

theorem suzukiDF6D4FixedGridShard031OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard031OddSolveData =
      suzukiDF6D4FixedGridShard031OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard031Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard031OddSolveData =
    suzukiDF6D4FixedGridShard031OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard031OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard031OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 31 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 31 k) := by
    rw [suzukiDF6D4FixedGridShard031OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 31 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031OddDotSoundness i
          suzukiDF6D4FixedGridShard031OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 31 k) := by
    simpa [suzukiDF6D4FixedGridShard031OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard031OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 31 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 31) := by
    rw [suzukiDF6D4FixedGridShard031OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 31)
  rw [suzukiDF6D4FixedGridShard031OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard031OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard031OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard031OddDotSoundness i
            suzukiDF6D4FixedGridShard031OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard031OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard031EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard031EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 332) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard031EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 332)) at h
  exact h

theorem suzukiDF6D4FixedGridShard031EvenFull_eq_live :
    suzukiDF6D4FixedGridShard031EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 332) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard031EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 332)) at h
  exact h

def suzukiDF6D4FixedGridShard031EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard031EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard031EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard031EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard031EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard031EvenResidualData =
      suzukiDF6D4FixedGridShard031EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard031Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard031EvenResidualData =
    suzukiDF6D4FixedGridShard031EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard031EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard031EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 332 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 332) := by
    rw [suzukiDF6D4FixedGridShard031EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 332
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031EvenDotSoundness i
          suzukiDF6D4FixedGridShard031EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 332) := by
    simpa [suzukiDF6D4FixedGridShard031EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard031EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 332) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 332) := by
    rw [suzukiDF6D4FixedGridShard031EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 332
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard031EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard031EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard031EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard031EvenDotSoundness i
            suzukiDF6D4FixedGridShard031EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard031EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard031OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard031OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 332) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard031OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 332)) at h
  exact h

theorem suzukiDF6D4FixedGridShard031OddFull_eq_live :
    suzukiDF6D4FixedGridShard031OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 332) := by
  have h := suzukiDF6D4FixedGridShard031Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard031OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 332)) at h
  exact h

def suzukiDF6D4FixedGridShard031OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard031OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard031OddDotSoundness i.val
        suzukiDF6D4FixedGridShard031OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard031OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard031OddResidualData =
      suzukiDF6D4FixedGridShard031OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard031Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard031OddResidualData =
    suzukiDF6D4FixedGridShard031OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard031OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard031OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 332 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 332) := by
    rw [suzukiDF6D4FixedGridShard031OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 332
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031OddDotSoundness i
          suzukiDF6D4FixedGridShard031OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 332) := by
    simpa [suzukiDF6D4FixedGridShard031OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard031OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 332) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard031OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 332) := by
    rw [suzukiDF6D4FixedGridShard031OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 332
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard031OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard031OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard031OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard031OddDotSoundness i
            suzukiDF6D4FixedGridShard031OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard031OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
