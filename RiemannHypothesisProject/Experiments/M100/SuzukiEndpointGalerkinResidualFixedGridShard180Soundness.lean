import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard180Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard180Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard180EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard180EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 180 k) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard180EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 180 k)) at h
  exact h

def suzukiDF6D4FixedGridShard180EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard180EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard180EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard180EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard180EvenComparisonData)

theorem suzukiDF6D4FixedGridShard180EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard180EvenSolveData =
      suzukiDF6D4FixedGridShard180EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard180Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard180EvenSolveData =
    suzukiDF6D4FixedGridShard180EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard180EvenCross_eq_live :
    suzukiDF6D4FixedGridShard180EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 180) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard180EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 180)) at h
  exact h

theorem suzukiDF6D4FixedGridShard180EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard180EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 180 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 180 k) := by
    rw [suzukiDF6D4FixedGridShard180EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 180 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180EvenDotSoundness i
          suzukiDF6D4FixedGridShard180EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 180 k) := by
    simpa [suzukiDF6D4FixedGridShard180EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard180EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 180 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 180) := by
    rw [suzukiDF6D4FixedGridShard180EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 180)
  rw [suzukiDF6D4FixedGridShard180EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard180EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard180EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard180EvenDotSoundness i
            suzukiDF6D4FixedGridShard180EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard180EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard180OddComparison_eq_live :
    suzukiDF6D4FixedGridShard180OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 180 k) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard180OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 180 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard180OddCross_eq_live :
    suzukiDF6D4FixedGridShard180OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 180) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard180OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 180)) at h
  exact h

def suzukiDF6D4FixedGridShard180OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard180OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard180OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard180OddDotSoundness i.val
      suzukiDF6D4FixedGridShard180OddComparisonData)

theorem suzukiDF6D4FixedGridShard180OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard180OddSolveData =
      suzukiDF6D4FixedGridShard180OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard180Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard180OddSolveData =
    suzukiDF6D4FixedGridShard180OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard180OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard180OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 180 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 180 k) := by
    rw [suzukiDF6D4FixedGridShard180OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 180 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180OddDotSoundness i
          suzukiDF6D4FixedGridShard180OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 180 k) := by
    simpa [suzukiDF6D4FixedGridShard180OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard180OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 180 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 180) := by
    rw [suzukiDF6D4FixedGridShard180OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 180)
  rw [suzukiDF6D4FixedGridShard180OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard180OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard180OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard180OddDotSoundness i
            suzukiDF6D4FixedGridShard180OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard180OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard180EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard180EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 481) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard180EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 481)) at h
  exact h

theorem suzukiDF6D4FixedGridShard180EvenFull_eq_live :
    suzukiDF6D4FixedGridShard180EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 481) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard180EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 481)) at h
  exact h

def suzukiDF6D4FixedGridShard180EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard180EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard180EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard180EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard180EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard180EvenResidualData =
      suzukiDF6D4FixedGridShard180EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard180Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard180EvenResidualData =
    suzukiDF6D4FixedGridShard180EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard180EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard180EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 481 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 481) := by
    rw [suzukiDF6D4FixedGridShard180EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 481
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180EvenDotSoundness i
          suzukiDF6D4FixedGridShard180EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 481) := by
    simpa [suzukiDF6D4FixedGridShard180EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard180EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 481) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 481) := by
    rw [suzukiDF6D4FixedGridShard180EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 481
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard180EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard180EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard180EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard180EvenDotSoundness i
            suzukiDF6D4FixedGridShard180EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard180EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard180OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard180OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 481) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard180OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 481)) at h
  exact h

theorem suzukiDF6D4FixedGridShard180OddFull_eq_live :
    suzukiDF6D4FixedGridShard180OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 481) := by
  have h := suzukiDF6D4FixedGridShard180Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard180OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 481)) at h
  exact h

def suzukiDF6D4FixedGridShard180OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard180OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard180OddDotSoundness i.val
        suzukiDF6D4FixedGridShard180OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard180OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard180OddResidualData =
      suzukiDF6D4FixedGridShard180OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard180Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard180OddResidualData =
    suzukiDF6D4FixedGridShard180OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard180OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard180OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 481 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 481) := by
    rw [suzukiDF6D4FixedGridShard180OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 481
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180OddDotSoundness i
          suzukiDF6D4FixedGridShard180OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 481) := by
    simpa [suzukiDF6D4FixedGridShard180OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard180OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 481) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard180OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 481) := by
    rw [suzukiDF6D4FixedGridShard180OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 481
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard180OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard180OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard180OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard180OddDotSoundness i
            suzukiDF6D4FixedGridShard180OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard180OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
