import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard097Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard097Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard097EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard097EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 97 k) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard097EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 97 k)) at h
  exact h

def suzukiDF6D4FixedGridShard097EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard097EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard097EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard097EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard097EvenComparisonData)

theorem suzukiDF6D4FixedGridShard097EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard097EvenSolveData =
      suzukiDF6D4FixedGridShard097EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard097Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard097EvenSolveData =
    suzukiDF6D4FixedGridShard097EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard097EvenCross_eq_live :
    suzukiDF6D4FixedGridShard097EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 97) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard097EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 97)) at h
  exact h

theorem suzukiDF6D4FixedGridShard097EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard097EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 97 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 97 k) := by
    rw [suzukiDF6D4FixedGridShard097EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 97 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097EvenDotSoundness i
          suzukiDF6D4FixedGridShard097EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 97 k) := by
    simpa [suzukiDF6D4FixedGridShard097EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard097EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 97 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 97) := by
    rw [suzukiDF6D4FixedGridShard097EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 97)
  rw [suzukiDF6D4FixedGridShard097EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard097EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard097EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard097EvenDotSoundness i
            suzukiDF6D4FixedGridShard097EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard097EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard097OddComparison_eq_live :
    suzukiDF6D4FixedGridShard097OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 97 k) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard097OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 97 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard097OddCross_eq_live :
    suzukiDF6D4FixedGridShard097OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 97) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard097OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 97)) at h
  exact h

def suzukiDF6D4FixedGridShard097OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard097OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard097OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard097OddDotSoundness i.val
      suzukiDF6D4FixedGridShard097OddComparisonData)

theorem suzukiDF6D4FixedGridShard097OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard097OddSolveData =
      suzukiDF6D4FixedGridShard097OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard097Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard097OddSolveData =
    suzukiDF6D4FixedGridShard097OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard097OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard097OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 97 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 97 k) := by
    rw [suzukiDF6D4FixedGridShard097OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 97 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097OddDotSoundness i
          suzukiDF6D4FixedGridShard097OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 97 k) := by
    simpa [suzukiDF6D4FixedGridShard097OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard097OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 97 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 97) := by
    rw [suzukiDF6D4FixedGridShard097OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 97)
  rw [suzukiDF6D4FixedGridShard097OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard097OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard097OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard097OddDotSoundness i
            suzukiDF6D4FixedGridShard097OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard097OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard097EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard097EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 398) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard097EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 398)) at h
  exact h

theorem suzukiDF6D4FixedGridShard097EvenFull_eq_live :
    suzukiDF6D4FixedGridShard097EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 398) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard097EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 398)) at h
  exact h

def suzukiDF6D4FixedGridShard097EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard097EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard097EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard097EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard097EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard097EvenResidualData =
      suzukiDF6D4FixedGridShard097EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard097Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard097EvenResidualData =
    suzukiDF6D4FixedGridShard097EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard097EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard097EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 398 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 398) := by
    rw [suzukiDF6D4FixedGridShard097EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 398
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097EvenDotSoundness i
          suzukiDF6D4FixedGridShard097EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 398) := by
    simpa [suzukiDF6D4FixedGridShard097EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard097EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 398) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 398) := by
    rw [suzukiDF6D4FixedGridShard097EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 398
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard097EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard097EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard097EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard097EvenDotSoundness i
            suzukiDF6D4FixedGridShard097EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard097EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard097OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard097OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 398) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard097OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 398)) at h
  exact h

theorem suzukiDF6D4FixedGridShard097OddFull_eq_live :
    suzukiDF6D4FixedGridShard097OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 398) := by
  have h := suzukiDF6D4FixedGridShard097Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard097OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 398)) at h
  exact h

def suzukiDF6D4FixedGridShard097OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard097OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard097OddDotSoundness i.val
        suzukiDF6D4FixedGridShard097OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard097OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard097OddResidualData =
      suzukiDF6D4FixedGridShard097OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard097Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard097OddResidualData =
    suzukiDF6D4FixedGridShard097OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard097OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard097OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 398 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 398) := by
    rw [suzukiDF6D4FixedGridShard097OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 398
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097OddDotSoundness i
          suzukiDF6D4FixedGridShard097OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 398) := by
    simpa [suzukiDF6D4FixedGridShard097OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard097OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 398) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard097OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 398) := by
    rw [suzukiDF6D4FixedGridShard097OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 398
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard097OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard097OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard097OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard097OddDotSoundness i
            suzukiDF6D4FixedGridShard097OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard097OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
