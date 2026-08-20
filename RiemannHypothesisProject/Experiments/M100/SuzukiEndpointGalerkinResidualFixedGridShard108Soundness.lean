import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard108Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard108Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard108EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard108EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 108 k) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard108EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 108 k)) at h
  exact h

def suzukiDF6D4FixedGridShard108EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard108EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard108EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard108EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard108EvenComparisonData)

theorem suzukiDF6D4FixedGridShard108EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard108EvenSolveData =
      suzukiDF6D4FixedGridShard108EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard108Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard108EvenSolveData =
    suzukiDF6D4FixedGridShard108EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard108EvenCross_eq_live :
    suzukiDF6D4FixedGridShard108EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 108) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard108EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 108)) at h
  exact h

theorem suzukiDF6D4FixedGridShard108EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard108EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 108 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 108 k) := by
    rw [suzukiDF6D4FixedGridShard108EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 108 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108EvenDotSoundness i
          suzukiDF6D4FixedGridShard108EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 108 k) := by
    simpa [suzukiDF6D4FixedGridShard108EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard108EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 108 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 108) := by
    rw [suzukiDF6D4FixedGridShard108EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 108)
  rw [suzukiDF6D4FixedGridShard108EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard108EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard108EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard108EvenDotSoundness i
            suzukiDF6D4FixedGridShard108EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard108EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard108OddComparison_eq_live :
    suzukiDF6D4FixedGridShard108OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 108 k) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard108OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 108 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard108OddCross_eq_live :
    suzukiDF6D4FixedGridShard108OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 108) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard108OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 108)) at h
  exact h

def suzukiDF6D4FixedGridShard108OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard108OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard108OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard108OddDotSoundness i.val
      suzukiDF6D4FixedGridShard108OddComparisonData)

theorem suzukiDF6D4FixedGridShard108OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard108OddSolveData =
      suzukiDF6D4FixedGridShard108OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard108Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard108OddSolveData =
    suzukiDF6D4FixedGridShard108OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard108OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard108OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 108 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 108 k) := by
    rw [suzukiDF6D4FixedGridShard108OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 108 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108OddDotSoundness i
          suzukiDF6D4FixedGridShard108OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 108 k) := by
    simpa [suzukiDF6D4FixedGridShard108OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard108OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 108 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 108) := by
    rw [suzukiDF6D4FixedGridShard108OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 108)
  rw [suzukiDF6D4FixedGridShard108OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard108OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard108OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard108OddDotSoundness i
            suzukiDF6D4FixedGridShard108OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard108OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard108EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard108EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 409) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard108EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 409)) at h
  exact h

theorem suzukiDF6D4FixedGridShard108EvenFull_eq_live :
    suzukiDF6D4FixedGridShard108EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 409) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard108EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 409)) at h
  exact h

def suzukiDF6D4FixedGridShard108EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard108EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard108EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard108EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard108EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard108EvenResidualData =
      suzukiDF6D4FixedGridShard108EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard108Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard108EvenResidualData =
    suzukiDF6D4FixedGridShard108EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard108EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard108EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 409 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 409) := by
    rw [suzukiDF6D4FixedGridShard108EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 409
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108EvenDotSoundness i
          suzukiDF6D4FixedGridShard108EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 409) := by
    simpa [suzukiDF6D4FixedGridShard108EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard108EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 409) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 409) := by
    rw [suzukiDF6D4FixedGridShard108EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 409
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard108EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard108EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard108EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard108EvenDotSoundness i
            suzukiDF6D4FixedGridShard108EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard108EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard108OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard108OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 409) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard108OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 409)) at h
  exact h

theorem suzukiDF6D4FixedGridShard108OddFull_eq_live :
    suzukiDF6D4FixedGridShard108OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 409) := by
  have h := suzukiDF6D4FixedGridShard108Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard108OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 409)) at h
  exact h

def suzukiDF6D4FixedGridShard108OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard108OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard108OddDotSoundness i.val
        suzukiDF6D4FixedGridShard108OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard108OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard108OddResidualData =
      suzukiDF6D4FixedGridShard108OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard108Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard108OddResidualData =
    suzukiDF6D4FixedGridShard108OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard108OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard108OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 409 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 409) := by
    rw [suzukiDF6D4FixedGridShard108OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 409
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108OddDotSoundness i
          suzukiDF6D4FixedGridShard108OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 409) := by
    simpa [suzukiDF6D4FixedGridShard108OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard108OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 409) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard108OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 409) := by
    rw [suzukiDF6D4FixedGridShard108OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 409
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard108OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard108OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard108OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard108OddDotSoundness i
            suzukiDF6D4FixedGridShard108OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard108OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
