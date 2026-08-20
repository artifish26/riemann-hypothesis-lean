import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard219Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard219Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard219EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard219EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 219 k) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard219EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 219 k)) at h
  exact h

def suzukiDF6D4FixedGridShard219EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard219EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard219EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard219EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard219EvenComparisonData)

theorem suzukiDF6D4FixedGridShard219EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard219EvenSolveData =
      suzukiDF6D4FixedGridShard219EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard219Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard219EvenSolveData =
    suzukiDF6D4FixedGridShard219EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard219EvenCross_eq_live :
    suzukiDF6D4FixedGridShard219EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 219) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard219EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 219)) at h
  exact h

theorem suzukiDF6D4FixedGridShard219EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard219EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 219 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 219 k) := by
    rw [suzukiDF6D4FixedGridShard219EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 219 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219EvenDotSoundness i
          suzukiDF6D4FixedGridShard219EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 219 k) := by
    simpa [suzukiDF6D4FixedGridShard219EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard219EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 219 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 219) := by
    rw [suzukiDF6D4FixedGridShard219EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 219)
  rw [suzukiDF6D4FixedGridShard219EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard219EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard219EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard219EvenDotSoundness i
            suzukiDF6D4FixedGridShard219EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard219EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard219OddComparison_eq_live :
    suzukiDF6D4FixedGridShard219OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 219 k) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard219OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 219 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard219OddCross_eq_live :
    suzukiDF6D4FixedGridShard219OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 219) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard219OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 219)) at h
  exact h

def suzukiDF6D4FixedGridShard219OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard219OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard219OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard219OddDotSoundness i.val
      suzukiDF6D4FixedGridShard219OddComparisonData)

theorem suzukiDF6D4FixedGridShard219OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard219OddSolveData =
      suzukiDF6D4FixedGridShard219OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard219Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard219OddSolveData =
    suzukiDF6D4FixedGridShard219OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard219OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard219OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 219 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 219 k) := by
    rw [suzukiDF6D4FixedGridShard219OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 219 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219OddDotSoundness i
          suzukiDF6D4FixedGridShard219OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 219 k) := by
    simpa [suzukiDF6D4FixedGridShard219OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard219OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 219 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 219) := by
    rw [suzukiDF6D4FixedGridShard219OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 219)
  rw [suzukiDF6D4FixedGridShard219OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard219OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard219OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard219OddDotSoundness i
            suzukiDF6D4FixedGridShard219OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard219OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard219EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard219EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 520) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard219EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 520)) at h
  exact h

theorem suzukiDF6D4FixedGridShard219EvenFull_eq_live :
    suzukiDF6D4FixedGridShard219EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 520) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard219EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 520)) at h
  exact h

def suzukiDF6D4FixedGridShard219EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard219EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard219EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard219EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard219EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard219EvenResidualData =
      suzukiDF6D4FixedGridShard219EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard219Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard219EvenResidualData =
    suzukiDF6D4FixedGridShard219EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard219EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard219EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 520 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 520) := by
    rw [suzukiDF6D4FixedGridShard219EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 520
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219EvenDotSoundness i
          suzukiDF6D4FixedGridShard219EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 520) := by
    simpa [suzukiDF6D4FixedGridShard219EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard219EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 520) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 520) := by
    rw [suzukiDF6D4FixedGridShard219EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 520
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard219EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard219EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard219EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard219EvenDotSoundness i
            suzukiDF6D4FixedGridShard219EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard219EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard219OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard219OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 520) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard219OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 520)) at h
  exact h

theorem suzukiDF6D4FixedGridShard219OddFull_eq_live :
    suzukiDF6D4FixedGridShard219OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 520) := by
  have h := suzukiDF6D4FixedGridShard219Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard219OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 520)) at h
  exact h

def suzukiDF6D4FixedGridShard219OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard219OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard219OddDotSoundness i.val
        suzukiDF6D4FixedGridShard219OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard219OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard219OddResidualData =
      suzukiDF6D4FixedGridShard219OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard219Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard219OddResidualData =
    suzukiDF6D4FixedGridShard219OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard219OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard219OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 520 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 520) := by
    rw [suzukiDF6D4FixedGridShard219OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 520
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219OddDotSoundness i
          suzukiDF6D4FixedGridShard219OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 520) := by
    simpa [suzukiDF6D4FixedGridShard219OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard219OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 520) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard219OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 520) := by
    rw [suzukiDF6D4FixedGridShard219OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 520
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard219OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard219OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard219OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard219OddDotSoundness i
            suzukiDF6D4FixedGridShard219OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard219OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
