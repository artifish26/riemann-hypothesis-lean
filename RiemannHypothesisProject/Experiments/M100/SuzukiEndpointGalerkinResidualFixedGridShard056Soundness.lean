import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard056Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard056Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard056EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard056EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 56 k) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard056EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 56 k)) at h
  exact h

def suzukiDF6D4FixedGridShard056EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard056EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard056EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard056EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard056EvenComparisonData)

theorem suzukiDF6D4FixedGridShard056EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard056EvenSolveData =
      suzukiDF6D4FixedGridShard056EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard056Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard056EvenSolveData =
    suzukiDF6D4FixedGridShard056EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard056EvenCross_eq_live :
    suzukiDF6D4FixedGridShard056EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 56) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard056EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 56)) at h
  exact h

theorem suzukiDF6D4FixedGridShard056EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard056EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 56 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 56 k) := by
    rw [suzukiDF6D4FixedGridShard056EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 56 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056EvenDotSoundness i
          suzukiDF6D4FixedGridShard056EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 56 k) := by
    simpa [suzukiDF6D4FixedGridShard056EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard056EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 56 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 56) := by
    rw [suzukiDF6D4FixedGridShard056EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 56)
  rw [suzukiDF6D4FixedGridShard056EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard056EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard056EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard056EvenDotSoundness i
            suzukiDF6D4FixedGridShard056EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard056EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard056OddComparison_eq_live :
    suzukiDF6D4FixedGridShard056OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 56 k) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard056OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 56 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard056OddCross_eq_live :
    suzukiDF6D4FixedGridShard056OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 56) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard056OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 56)) at h
  exact h

def suzukiDF6D4FixedGridShard056OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard056OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard056OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard056OddDotSoundness i.val
      suzukiDF6D4FixedGridShard056OddComparisonData)

theorem suzukiDF6D4FixedGridShard056OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard056OddSolveData =
      suzukiDF6D4FixedGridShard056OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard056Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard056OddSolveData =
    suzukiDF6D4FixedGridShard056OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard056OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard056OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 56 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 56 k) := by
    rw [suzukiDF6D4FixedGridShard056OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 56 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056OddDotSoundness i
          suzukiDF6D4FixedGridShard056OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 56 k) := by
    simpa [suzukiDF6D4FixedGridShard056OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard056OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 56 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 56) := by
    rw [suzukiDF6D4FixedGridShard056OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 56)
  rw [suzukiDF6D4FixedGridShard056OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard056OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard056OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard056OddDotSoundness i
            suzukiDF6D4FixedGridShard056OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard056OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard056EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard056EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 357) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard056EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 357)) at h
  exact h

theorem suzukiDF6D4FixedGridShard056EvenFull_eq_live :
    suzukiDF6D4FixedGridShard056EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 357) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard056EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 357)) at h
  exact h

def suzukiDF6D4FixedGridShard056EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard056EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard056EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard056EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard056EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard056EvenResidualData =
      suzukiDF6D4FixedGridShard056EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard056Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard056EvenResidualData =
    suzukiDF6D4FixedGridShard056EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard056EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard056EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 357 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 357) := by
    rw [suzukiDF6D4FixedGridShard056EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 357
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056EvenDotSoundness i
          suzukiDF6D4FixedGridShard056EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 357) := by
    simpa [suzukiDF6D4FixedGridShard056EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard056EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 357) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 357) := by
    rw [suzukiDF6D4FixedGridShard056EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 357
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard056EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard056EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard056EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard056EvenDotSoundness i
            suzukiDF6D4FixedGridShard056EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard056EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard056OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard056OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 357) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard056OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 357)) at h
  exact h

theorem suzukiDF6D4FixedGridShard056OddFull_eq_live :
    suzukiDF6D4FixedGridShard056OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 357) := by
  have h := suzukiDF6D4FixedGridShard056Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard056OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 357)) at h
  exact h

def suzukiDF6D4FixedGridShard056OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard056OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard056OddDotSoundness i.val
        suzukiDF6D4FixedGridShard056OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard056OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard056OddResidualData =
      suzukiDF6D4FixedGridShard056OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard056Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard056OddResidualData =
    suzukiDF6D4FixedGridShard056OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard056OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard056OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 357 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 357) := by
    rw [suzukiDF6D4FixedGridShard056OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 357
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056OddDotSoundness i
          suzukiDF6D4FixedGridShard056OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 357) := by
    simpa [suzukiDF6D4FixedGridShard056OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard056OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 357) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard056OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 357) := by
    rw [suzukiDF6D4FixedGridShard056OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 357
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard056OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard056OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard056OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard056OddDotSoundness i
            suzukiDF6D4FixedGridShard056OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard056OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
