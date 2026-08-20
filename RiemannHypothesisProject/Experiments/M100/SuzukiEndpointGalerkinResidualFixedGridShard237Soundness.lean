import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard237Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard237Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard237EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard237EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 237 k) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard237EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 237 k)) at h
  exact h

def suzukiDF6D4FixedGridShard237EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard237EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard237EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard237EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard237EvenComparisonData)

theorem suzukiDF6D4FixedGridShard237EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard237EvenSolveData =
      suzukiDF6D4FixedGridShard237EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard237Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard237EvenSolveData =
    suzukiDF6D4FixedGridShard237EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard237EvenCross_eq_live :
    suzukiDF6D4FixedGridShard237EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 237) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard237EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 237)) at h
  exact h

theorem suzukiDF6D4FixedGridShard237EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard237EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 237 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 237 k) := by
    rw [suzukiDF6D4FixedGridShard237EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 237 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237EvenDotSoundness i
          suzukiDF6D4FixedGridShard237EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 237 k) := by
    simpa [suzukiDF6D4FixedGridShard237EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard237EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 237 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 237) := by
    rw [suzukiDF6D4FixedGridShard237EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 237)
  rw [suzukiDF6D4FixedGridShard237EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard237EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard237EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard237EvenDotSoundness i
            suzukiDF6D4FixedGridShard237EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard237EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard237OddComparison_eq_live :
    suzukiDF6D4FixedGridShard237OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 237 k) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard237OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 237 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard237OddCross_eq_live :
    suzukiDF6D4FixedGridShard237OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 237) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard237OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 237)) at h
  exact h

def suzukiDF6D4FixedGridShard237OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard237OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard237OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard237OddDotSoundness i.val
      suzukiDF6D4FixedGridShard237OddComparisonData)

theorem suzukiDF6D4FixedGridShard237OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard237OddSolveData =
      suzukiDF6D4FixedGridShard237OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard237Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard237OddSolveData =
    suzukiDF6D4FixedGridShard237OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard237OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard237OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 237 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 237 k) := by
    rw [suzukiDF6D4FixedGridShard237OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 237 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237OddDotSoundness i
          suzukiDF6D4FixedGridShard237OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 237 k) := by
    simpa [suzukiDF6D4FixedGridShard237OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard237OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 237 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 237) := by
    rw [suzukiDF6D4FixedGridShard237OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 237)
  rw [suzukiDF6D4FixedGridShard237OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard237OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard237OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard237OddDotSoundness i
            suzukiDF6D4FixedGridShard237OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard237OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard237EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard237EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 538) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard237EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 538)) at h
  exact h

theorem suzukiDF6D4FixedGridShard237EvenFull_eq_live :
    suzukiDF6D4FixedGridShard237EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 538) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard237EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 538)) at h
  exact h

def suzukiDF6D4FixedGridShard237EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard237EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard237EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard237EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard237EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard237EvenResidualData =
      suzukiDF6D4FixedGridShard237EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard237Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard237EvenResidualData =
    suzukiDF6D4FixedGridShard237EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard237EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard237EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 538 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 538) := by
    rw [suzukiDF6D4FixedGridShard237EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 538
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237EvenDotSoundness i
          suzukiDF6D4FixedGridShard237EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 538) := by
    simpa [suzukiDF6D4FixedGridShard237EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard237EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 538) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 538) := by
    rw [suzukiDF6D4FixedGridShard237EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 538
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard237EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard237EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard237EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard237EvenDotSoundness i
            suzukiDF6D4FixedGridShard237EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard237EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard237OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard237OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 538) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard237OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 538)) at h
  exact h

theorem suzukiDF6D4FixedGridShard237OddFull_eq_live :
    suzukiDF6D4FixedGridShard237OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 538) := by
  have h := suzukiDF6D4FixedGridShard237Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard237OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 538)) at h
  exact h

def suzukiDF6D4FixedGridShard237OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard237OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard237OddDotSoundness i.val
        suzukiDF6D4FixedGridShard237OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard237OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard237OddResidualData =
      suzukiDF6D4FixedGridShard237OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard237Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard237OddResidualData =
    suzukiDF6D4FixedGridShard237OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard237OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard237OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 538 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 538) := by
    rw [suzukiDF6D4FixedGridShard237OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 538
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237OddDotSoundness i
          suzukiDF6D4FixedGridShard237OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 538) := by
    simpa [suzukiDF6D4FixedGridShard237OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard237OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 538) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard237OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 538) := by
    rw [suzukiDF6D4FixedGridShard237OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 538
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard237OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard237OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard237OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard237OddDotSoundness i
            suzukiDF6D4FixedGridShard237OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard237OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
