import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard015Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard015Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard015EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard015EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 15 k) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard015EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 15 k)) at h
  exact h

def suzukiDF6D4FixedGridShard015EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard015EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard015EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard015EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard015EvenComparisonData)

theorem suzukiDF6D4FixedGridShard015EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard015EvenSolveData =
      suzukiDF6D4FixedGridShard015EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard015Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard015EvenSolveData =
    suzukiDF6D4FixedGridShard015EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard015EvenCross_eq_live :
    suzukiDF6D4FixedGridShard015EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 15) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard015EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 15)) at h
  exact h

theorem suzukiDF6D4FixedGridShard015EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard015EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 15 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 15 k) := by
    rw [suzukiDF6D4FixedGridShard015EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 15 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015EvenDotSoundness i
          suzukiDF6D4FixedGridShard015EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 15 k) := by
    simpa [suzukiDF6D4FixedGridShard015EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard015EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 15 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 15) := by
    rw [suzukiDF6D4FixedGridShard015EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 15)
  rw [suzukiDF6D4FixedGridShard015EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard015EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard015EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard015EvenDotSoundness i
            suzukiDF6D4FixedGridShard015EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard015EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard015OddComparison_eq_live :
    suzukiDF6D4FixedGridShard015OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 15 k) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard015OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 15 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard015OddCross_eq_live :
    suzukiDF6D4FixedGridShard015OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 15) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard015OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 15)) at h
  exact h

def suzukiDF6D4FixedGridShard015OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard015OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard015OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard015OddDotSoundness i.val
      suzukiDF6D4FixedGridShard015OddComparisonData)

theorem suzukiDF6D4FixedGridShard015OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard015OddSolveData =
      suzukiDF6D4FixedGridShard015OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard015Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard015OddSolveData =
    suzukiDF6D4FixedGridShard015OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard015OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard015OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 15 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 15 k) := by
    rw [suzukiDF6D4FixedGridShard015OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 15 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015OddDotSoundness i
          suzukiDF6D4FixedGridShard015OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 15 k) := by
    simpa [suzukiDF6D4FixedGridShard015OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard015OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 15 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 15) := by
    rw [suzukiDF6D4FixedGridShard015OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 15)
  rw [suzukiDF6D4FixedGridShard015OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard015OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard015OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard015OddDotSoundness i
            suzukiDF6D4FixedGridShard015OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard015OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard015EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard015EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 316) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard015EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 316)) at h
  exact h

theorem suzukiDF6D4FixedGridShard015EvenFull_eq_live :
    suzukiDF6D4FixedGridShard015EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 316) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard015EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 316)) at h
  exact h

def suzukiDF6D4FixedGridShard015EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard015EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard015EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard015EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard015EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard015EvenResidualData =
      suzukiDF6D4FixedGridShard015EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard015Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard015EvenResidualData =
    suzukiDF6D4FixedGridShard015EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard015EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard015EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 316 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 316) := by
    rw [suzukiDF6D4FixedGridShard015EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 316
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015EvenDotSoundness i
          suzukiDF6D4FixedGridShard015EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 316) := by
    simpa [suzukiDF6D4FixedGridShard015EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard015EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 316) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 316) := by
    rw [suzukiDF6D4FixedGridShard015EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 316
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard015EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard015EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard015EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard015EvenDotSoundness i
            suzukiDF6D4FixedGridShard015EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard015EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard015OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard015OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 316) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard015OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 316)) at h
  exact h

theorem suzukiDF6D4FixedGridShard015OddFull_eq_live :
    suzukiDF6D4FixedGridShard015OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 316) := by
  have h := suzukiDF6D4FixedGridShard015Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard015OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 316)) at h
  exact h

def suzukiDF6D4FixedGridShard015OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard015OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard015OddDotSoundness i.val
        suzukiDF6D4FixedGridShard015OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard015OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard015OddResidualData =
      suzukiDF6D4FixedGridShard015OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard015Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard015OddResidualData =
    suzukiDF6D4FixedGridShard015OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard015OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard015OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 316 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 316) := by
    rw [suzukiDF6D4FixedGridShard015OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 316
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015OddDotSoundness i
          suzukiDF6D4FixedGridShard015OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 316) := by
    simpa [suzukiDF6D4FixedGridShard015OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard015OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 316) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard015OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 316) := by
    rw [suzukiDF6D4FixedGridShard015OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 316
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard015OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard015OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard015OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard015OddDotSoundness i
            suzukiDF6D4FixedGridShard015OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard015OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
