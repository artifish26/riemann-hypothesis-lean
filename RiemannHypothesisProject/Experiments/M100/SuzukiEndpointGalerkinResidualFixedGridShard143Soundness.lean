import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard143Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard143Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard143EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard143EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 143 k) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard143EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 143 k)) at h
  exact h

def suzukiDF6D4FixedGridShard143EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard143EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard143EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard143EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard143EvenComparisonData)

theorem suzukiDF6D4FixedGridShard143EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard143EvenSolveData =
      suzukiDF6D4FixedGridShard143EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard143Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard143EvenSolveData =
    suzukiDF6D4FixedGridShard143EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard143EvenCross_eq_live :
    suzukiDF6D4FixedGridShard143EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 143) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard143EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 143)) at h
  exact h

theorem suzukiDF6D4FixedGridShard143EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard143EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 143 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 143 k) := by
    rw [suzukiDF6D4FixedGridShard143EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 143 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143EvenDotSoundness i
          suzukiDF6D4FixedGridShard143EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 143 k) := by
    simpa [suzukiDF6D4FixedGridShard143EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard143EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 143 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 143) := by
    rw [suzukiDF6D4FixedGridShard143EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 143)
  rw [suzukiDF6D4FixedGridShard143EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard143EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard143EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard143EvenDotSoundness i
            suzukiDF6D4FixedGridShard143EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard143EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard143OddComparison_eq_live :
    suzukiDF6D4FixedGridShard143OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 143 k) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard143OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 143 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard143OddCross_eq_live :
    suzukiDF6D4FixedGridShard143OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 143) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard143OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 143)) at h
  exact h

def suzukiDF6D4FixedGridShard143OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard143OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard143OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard143OddDotSoundness i.val
      suzukiDF6D4FixedGridShard143OddComparisonData)

theorem suzukiDF6D4FixedGridShard143OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard143OddSolveData =
      suzukiDF6D4FixedGridShard143OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard143Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard143OddSolveData =
    suzukiDF6D4FixedGridShard143OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard143OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard143OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 143 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 143 k) := by
    rw [suzukiDF6D4FixedGridShard143OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 143 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143OddDotSoundness i
          suzukiDF6D4FixedGridShard143OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 143 k) := by
    simpa [suzukiDF6D4FixedGridShard143OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard143OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 143 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 143) := by
    rw [suzukiDF6D4FixedGridShard143OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 143)
  rw [suzukiDF6D4FixedGridShard143OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard143OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard143OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard143OddDotSoundness i
            suzukiDF6D4FixedGridShard143OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard143OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard143EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard143EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 444) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard143EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 444)) at h
  exact h

theorem suzukiDF6D4FixedGridShard143EvenFull_eq_live :
    suzukiDF6D4FixedGridShard143EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 444) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard143EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 444)) at h
  exact h

def suzukiDF6D4FixedGridShard143EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard143EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard143EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard143EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard143EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard143EvenResidualData =
      suzukiDF6D4FixedGridShard143EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard143Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard143EvenResidualData =
    suzukiDF6D4FixedGridShard143EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard143EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard143EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 444 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 444) := by
    rw [suzukiDF6D4FixedGridShard143EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 444
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143EvenDotSoundness i
          suzukiDF6D4FixedGridShard143EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 444) := by
    simpa [suzukiDF6D4FixedGridShard143EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard143EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 444) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 444) := by
    rw [suzukiDF6D4FixedGridShard143EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 444
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard143EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard143EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard143EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard143EvenDotSoundness i
            suzukiDF6D4FixedGridShard143EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard143EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard143OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard143OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 444) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard143OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 444)) at h
  exact h

theorem suzukiDF6D4FixedGridShard143OddFull_eq_live :
    suzukiDF6D4FixedGridShard143OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 444) := by
  have h := suzukiDF6D4FixedGridShard143Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard143OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 444)) at h
  exact h

def suzukiDF6D4FixedGridShard143OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard143OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard143OddDotSoundness i.val
        suzukiDF6D4FixedGridShard143OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard143OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard143OddResidualData =
      suzukiDF6D4FixedGridShard143OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard143Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard143OddResidualData =
    suzukiDF6D4FixedGridShard143OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard143OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard143OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 444 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 444) := by
    rw [suzukiDF6D4FixedGridShard143OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 444
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143OddDotSoundness i
          suzukiDF6D4FixedGridShard143OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 444) := by
    simpa [suzukiDF6D4FixedGridShard143OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard143OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 444) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard143OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 444) := by
    rw [suzukiDF6D4FixedGridShard143OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 444
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard143OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard143OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard143OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard143OddDotSoundness i
            suzukiDF6D4FixedGridShard143OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard143OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
