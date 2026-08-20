import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard175Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard175Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard175EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard175EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 175 k) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard175EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 175 k)) at h
  exact h

def suzukiDF6D4FixedGridShard175EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard175EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard175EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard175EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard175EvenComparisonData)

theorem suzukiDF6D4FixedGridShard175EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard175EvenSolveData =
      suzukiDF6D4FixedGridShard175EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard175Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard175EvenSolveData =
    suzukiDF6D4FixedGridShard175EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard175EvenCross_eq_live :
    suzukiDF6D4FixedGridShard175EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 175) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard175EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 175)) at h
  exact h

theorem suzukiDF6D4FixedGridShard175EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard175EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 175 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 175 k) := by
    rw [suzukiDF6D4FixedGridShard175EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 175 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175EvenDotSoundness i
          suzukiDF6D4FixedGridShard175EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 175 k) := by
    simpa [suzukiDF6D4FixedGridShard175EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard175EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 175 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 175) := by
    rw [suzukiDF6D4FixedGridShard175EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 175)
  rw [suzukiDF6D4FixedGridShard175EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard175EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard175EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard175EvenDotSoundness i
            suzukiDF6D4FixedGridShard175EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard175EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard175OddComparison_eq_live :
    suzukiDF6D4FixedGridShard175OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 175 k) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard175OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 175 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard175OddCross_eq_live :
    suzukiDF6D4FixedGridShard175OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 175) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard175OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 175)) at h
  exact h

def suzukiDF6D4FixedGridShard175OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard175OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard175OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard175OddDotSoundness i.val
      suzukiDF6D4FixedGridShard175OddComparisonData)

theorem suzukiDF6D4FixedGridShard175OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard175OddSolveData =
      suzukiDF6D4FixedGridShard175OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard175Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard175OddSolveData =
    suzukiDF6D4FixedGridShard175OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard175OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard175OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 175 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 175 k) := by
    rw [suzukiDF6D4FixedGridShard175OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 175 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175OddDotSoundness i
          suzukiDF6D4FixedGridShard175OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 175 k) := by
    simpa [suzukiDF6D4FixedGridShard175OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard175OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 175 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 175) := by
    rw [suzukiDF6D4FixedGridShard175OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 175)
  rw [suzukiDF6D4FixedGridShard175OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard175OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard175OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard175OddDotSoundness i
            suzukiDF6D4FixedGridShard175OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard175OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard175EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard175EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 476) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard175EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 476)) at h
  exact h

theorem suzukiDF6D4FixedGridShard175EvenFull_eq_live :
    suzukiDF6D4FixedGridShard175EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 476) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard175EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 476)) at h
  exact h

def suzukiDF6D4FixedGridShard175EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard175EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard175EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard175EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard175EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard175EvenResidualData =
      suzukiDF6D4FixedGridShard175EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard175Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard175EvenResidualData =
    suzukiDF6D4FixedGridShard175EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard175EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard175EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 476 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 476) := by
    rw [suzukiDF6D4FixedGridShard175EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 476
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175EvenDotSoundness i
          suzukiDF6D4FixedGridShard175EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 476) := by
    simpa [suzukiDF6D4FixedGridShard175EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard175EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 476) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 476) := by
    rw [suzukiDF6D4FixedGridShard175EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 476
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard175EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard175EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard175EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard175EvenDotSoundness i
            suzukiDF6D4FixedGridShard175EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard175EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard175OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard175OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 476) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard175OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 476)) at h
  exact h

theorem suzukiDF6D4FixedGridShard175OddFull_eq_live :
    suzukiDF6D4FixedGridShard175OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 476) := by
  have h := suzukiDF6D4FixedGridShard175Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard175OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 476)) at h
  exact h

def suzukiDF6D4FixedGridShard175OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard175OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard175OddDotSoundness i.val
        suzukiDF6D4FixedGridShard175OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard175OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard175OddResidualData =
      suzukiDF6D4FixedGridShard175OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard175Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard175OddResidualData =
    suzukiDF6D4FixedGridShard175OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard175OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard175OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 476 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 476) := by
    rw [suzukiDF6D4FixedGridShard175OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 476
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175OddDotSoundness i
          suzukiDF6D4FixedGridShard175OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 476) := by
    simpa [suzukiDF6D4FixedGridShard175OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard175OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 476) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard175OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 476) := by
    rw [suzukiDF6D4FixedGridShard175OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 476
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard175OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard175OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard175OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard175OddDotSoundness i
            suzukiDF6D4FixedGridShard175OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard175OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
