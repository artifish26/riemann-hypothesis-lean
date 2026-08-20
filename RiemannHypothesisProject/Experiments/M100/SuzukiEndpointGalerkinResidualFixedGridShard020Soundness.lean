import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard020Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard020Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard020EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard020EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 20 k) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard020EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 20 k)) at h
  exact h

def suzukiDF6D4FixedGridShard020EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard020EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard020EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard020EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard020EvenComparisonData)

theorem suzukiDF6D4FixedGridShard020EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard020EvenSolveData =
      suzukiDF6D4FixedGridShard020EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard020Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard020EvenSolveData =
    suzukiDF6D4FixedGridShard020EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard020EvenCross_eq_live :
    suzukiDF6D4FixedGridShard020EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 20) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard020EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 20)) at h
  exact h

theorem suzukiDF6D4FixedGridShard020EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard020EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 20 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 20 k) := by
    rw [suzukiDF6D4FixedGridShard020EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 20 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020EvenDotSoundness i
          suzukiDF6D4FixedGridShard020EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 20 k) := by
    simpa [suzukiDF6D4FixedGridShard020EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard020EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 20 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 20) := by
    rw [suzukiDF6D4FixedGridShard020EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 20)
  rw [suzukiDF6D4FixedGridShard020EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard020EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard020EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard020EvenDotSoundness i
            suzukiDF6D4FixedGridShard020EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard020EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard020OddComparison_eq_live :
    suzukiDF6D4FixedGridShard020OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 20 k) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard020OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 20 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard020OddCross_eq_live :
    suzukiDF6D4FixedGridShard020OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 20) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard020OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 20)) at h
  exact h

def suzukiDF6D4FixedGridShard020OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard020OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard020OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard020OddDotSoundness i.val
      suzukiDF6D4FixedGridShard020OddComparisonData)

theorem suzukiDF6D4FixedGridShard020OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard020OddSolveData =
      suzukiDF6D4FixedGridShard020OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard020Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard020OddSolveData =
    suzukiDF6D4FixedGridShard020OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard020OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard020OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 20 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 20 k) := by
    rw [suzukiDF6D4FixedGridShard020OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 20 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020OddDotSoundness i
          suzukiDF6D4FixedGridShard020OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 20 k) := by
    simpa [suzukiDF6D4FixedGridShard020OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard020OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 20 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 20) := by
    rw [suzukiDF6D4FixedGridShard020OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 20)
  rw [suzukiDF6D4FixedGridShard020OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard020OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard020OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard020OddDotSoundness i
            suzukiDF6D4FixedGridShard020OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard020OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard020EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard020EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 321) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard020EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 321)) at h
  exact h

theorem suzukiDF6D4FixedGridShard020EvenFull_eq_live :
    suzukiDF6D4FixedGridShard020EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 321) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard020EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 321)) at h
  exact h

def suzukiDF6D4FixedGridShard020EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard020EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard020EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard020EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard020EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard020EvenResidualData =
      suzukiDF6D4FixedGridShard020EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard020Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard020EvenResidualData =
    suzukiDF6D4FixedGridShard020EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard020EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard020EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 321 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 321) := by
    rw [suzukiDF6D4FixedGridShard020EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 321
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020EvenDotSoundness i
          suzukiDF6D4FixedGridShard020EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 321) := by
    simpa [suzukiDF6D4FixedGridShard020EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard020EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 321) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 321) := by
    rw [suzukiDF6D4FixedGridShard020EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 321
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard020EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard020EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard020EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard020EvenDotSoundness i
            suzukiDF6D4FixedGridShard020EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard020EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard020OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard020OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 321) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard020OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 321)) at h
  exact h

theorem suzukiDF6D4FixedGridShard020OddFull_eq_live :
    suzukiDF6D4FixedGridShard020OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 321) := by
  have h := suzukiDF6D4FixedGridShard020Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard020OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 321)) at h
  exact h

def suzukiDF6D4FixedGridShard020OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard020OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard020OddDotSoundness i.val
        suzukiDF6D4FixedGridShard020OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard020OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard020OddResidualData =
      suzukiDF6D4FixedGridShard020OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard020Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard020OddResidualData =
    suzukiDF6D4FixedGridShard020OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard020OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard020OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 321 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 321) := by
    rw [suzukiDF6D4FixedGridShard020OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 321
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020OddDotSoundness i
          suzukiDF6D4FixedGridShard020OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 321) := by
    simpa [suzukiDF6D4FixedGridShard020OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard020OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 321) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard020OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 321) := by
    rw [suzukiDF6D4FixedGridShard020OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 321
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard020OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard020OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard020OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard020OddDotSoundness i
            suzukiDF6D4FixedGridShard020OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard020OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
