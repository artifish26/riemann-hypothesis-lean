import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard194Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard194Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard194EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard194EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 194 k) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard194EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 194 k)) at h
  exact h

def suzukiDF6D4FixedGridShard194EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard194EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard194EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard194EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard194EvenComparisonData)

theorem suzukiDF6D4FixedGridShard194EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard194EvenSolveData =
      suzukiDF6D4FixedGridShard194EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard194Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard194EvenSolveData =
    suzukiDF6D4FixedGridShard194EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard194EvenCross_eq_live :
    suzukiDF6D4FixedGridShard194EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 194) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard194EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 194)) at h
  exact h

theorem suzukiDF6D4FixedGridShard194EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard194EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 194 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 194 k) := by
    rw [suzukiDF6D4FixedGridShard194EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 194 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194EvenDotSoundness i
          suzukiDF6D4FixedGridShard194EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 194 k) := by
    simpa [suzukiDF6D4FixedGridShard194EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard194EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 194 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 194) := by
    rw [suzukiDF6D4FixedGridShard194EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 194)
  rw [suzukiDF6D4FixedGridShard194EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard194EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard194EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard194EvenDotSoundness i
            suzukiDF6D4FixedGridShard194EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard194EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard194OddComparison_eq_live :
    suzukiDF6D4FixedGridShard194OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 194 k) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard194OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 194 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard194OddCross_eq_live :
    suzukiDF6D4FixedGridShard194OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 194) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard194OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 194)) at h
  exact h

def suzukiDF6D4FixedGridShard194OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard194OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard194OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard194OddDotSoundness i.val
      suzukiDF6D4FixedGridShard194OddComparisonData)

theorem suzukiDF6D4FixedGridShard194OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard194OddSolveData =
      suzukiDF6D4FixedGridShard194OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard194Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard194OddSolveData =
    suzukiDF6D4FixedGridShard194OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard194OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard194OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 194 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 194 k) := by
    rw [suzukiDF6D4FixedGridShard194OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 194 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194OddDotSoundness i
          suzukiDF6D4FixedGridShard194OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 194 k) := by
    simpa [suzukiDF6D4FixedGridShard194OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard194OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 194 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 194) := by
    rw [suzukiDF6D4FixedGridShard194OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 194)
  rw [suzukiDF6D4FixedGridShard194OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard194OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard194OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard194OddDotSoundness i
            suzukiDF6D4FixedGridShard194OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard194OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard194EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard194EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 495) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard194EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 495)) at h
  exact h

theorem suzukiDF6D4FixedGridShard194EvenFull_eq_live :
    suzukiDF6D4FixedGridShard194EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 495) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard194EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 495)) at h
  exact h

def suzukiDF6D4FixedGridShard194EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard194EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard194EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard194EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard194EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard194EvenResidualData =
      suzukiDF6D4FixedGridShard194EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard194Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard194EvenResidualData =
    suzukiDF6D4FixedGridShard194EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard194EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard194EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 495 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 495) := by
    rw [suzukiDF6D4FixedGridShard194EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 495
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194EvenDotSoundness i
          suzukiDF6D4FixedGridShard194EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 495) := by
    simpa [suzukiDF6D4FixedGridShard194EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard194EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 495) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 495) := by
    rw [suzukiDF6D4FixedGridShard194EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 495
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard194EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard194EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard194EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard194EvenDotSoundness i
            suzukiDF6D4FixedGridShard194EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard194EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard194OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard194OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 495) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard194OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 495)) at h
  exact h

theorem suzukiDF6D4FixedGridShard194OddFull_eq_live :
    suzukiDF6D4FixedGridShard194OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 495) := by
  have h := suzukiDF6D4FixedGridShard194Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard194OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 495)) at h
  exact h

def suzukiDF6D4FixedGridShard194OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard194OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard194OddDotSoundness i.val
        suzukiDF6D4FixedGridShard194OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard194OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard194OddResidualData =
      suzukiDF6D4FixedGridShard194OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard194Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard194OddResidualData =
    suzukiDF6D4FixedGridShard194OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard194OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard194OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 495 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 495) := by
    rw [suzukiDF6D4FixedGridShard194OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 495
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194OddDotSoundness i
          suzukiDF6D4FixedGridShard194OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 495) := by
    simpa [suzukiDF6D4FixedGridShard194OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard194OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 495) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard194OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 495) := by
    rw [suzukiDF6D4FixedGridShard194OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 495
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard194OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard194OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard194OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard194OddDotSoundness i
            suzukiDF6D4FixedGridShard194OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard194OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
