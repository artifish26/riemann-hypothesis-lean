import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard059Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard059Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard059EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard059EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 59 k) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard059EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 59 k)) at h
  exact h

def suzukiDF6D4FixedGridShard059EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard059EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard059EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard059EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard059EvenComparisonData)

theorem suzukiDF6D4FixedGridShard059EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard059EvenSolveData =
      suzukiDF6D4FixedGridShard059EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard059Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard059EvenSolveData =
    suzukiDF6D4FixedGridShard059EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard059EvenCross_eq_live :
    suzukiDF6D4FixedGridShard059EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 59) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard059EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 59)) at h
  exact h

theorem suzukiDF6D4FixedGridShard059EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard059EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 59 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 59 k) := by
    rw [suzukiDF6D4FixedGridShard059EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 59 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059EvenDotSoundness i
          suzukiDF6D4FixedGridShard059EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 59 k) := by
    simpa [suzukiDF6D4FixedGridShard059EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard059EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 59 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 59) := by
    rw [suzukiDF6D4FixedGridShard059EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 59)
  rw [suzukiDF6D4FixedGridShard059EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard059EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard059EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard059EvenDotSoundness i
            suzukiDF6D4FixedGridShard059EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard059EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard059OddComparison_eq_live :
    suzukiDF6D4FixedGridShard059OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 59 k) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard059OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 59 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard059OddCross_eq_live :
    suzukiDF6D4FixedGridShard059OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 59) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard059OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 59)) at h
  exact h

def suzukiDF6D4FixedGridShard059OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard059OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard059OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard059OddDotSoundness i.val
      suzukiDF6D4FixedGridShard059OddComparisonData)

theorem suzukiDF6D4FixedGridShard059OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard059OddSolveData =
      suzukiDF6D4FixedGridShard059OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard059Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard059OddSolveData =
    suzukiDF6D4FixedGridShard059OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard059OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard059OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 59 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 59 k) := by
    rw [suzukiDF6D4FixedGridShard059OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 59 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059OddDotSoundness i
          suzukiDF6D4FixedGridShard059OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 59 k) := by
    simpa [suzukiDF6D4FixedGridShard059OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard059OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 59 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 59) := by
    rw [suzukiDF6D4FixedGridShard059OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 59)
  rw [suzukiDF6D4FixedGridShard059OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard059OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard059OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard059OddDotSoundness i
            suzukiDF6D4FixedGridShard059OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard059OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard059EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard059EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 360) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard059EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 360)) at h
  exact h

theorem suzukiDF6D4FixedGridShard059EvenFull_eq_live :
    suzukiDF6D4FixedGridShard059EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 360) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard059EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 360)) at h
  exact h

def suzukiDF6D4FixedGridShard059EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard059EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard059EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard059EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard059EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard059EvenResidualData =
      suzukiDF6D4FixedGridShard059EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard059Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard059EvenResidualData =
    suzukiDF6D4FixedGridShard059EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard059EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard059EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 360 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 360) := by
    rw [suzukiDF6D4FixedGridShard059EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 360
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059EvenDotSoundness i
          suzukiDF6D4FixedGridShard059EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 360) := by
    simpa [suzukiDF6D4FixedGridShard059EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard059EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 360) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 360) := by
    rw [suzukiDF6D4FixedGridShard059EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 360
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard059EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard059EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard059EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard059EvenDotSoundness i
            suzukiDF6D4FixedGridShard059EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard059EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard059OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard059OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 360) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard059OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 360)) at h
  exact h

theorem suzukiDF6D4FixedGridShard059OddFull_eq_live :
    suzukiDF6D4FixedGridShard059OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 360) := by
  have h := suzukiDF6D4FixedGridShard059Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard059OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 360)) at h
  exact h

def suzukiDF6D4FixedGridShard059OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard059OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard059OddDotSoundness i.val
        suzukiDF6D4FixedGridShard059OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard059OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard059OddResidualData =
      suzukiDF6D4FixedGridShard059OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard059Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard059OddResidualData =
    suzukiDF6D4FixedGridShard059OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard059OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard059OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 360 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 360) := by
    rw [suzukiDF6D4FixedGridShard059OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 360
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059OddDotSoundness i
          suzukiDF6D4FixedGridShard059OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 360) := by
    simpa [suzukiDF6D4FixedGridShard059OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard059OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 360) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard059OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 360) := by
    rw [suzukiDF6D4FixedGridShard059OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 360
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard059OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard059OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard059OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard059OddDotSoundness i
            suzukiDF6D4FixedGridShard059OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard059OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
