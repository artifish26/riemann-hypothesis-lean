import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard088Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard088Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard088EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard088EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 88 k) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard088EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 88 k)) at h
  exact h

def suzukiDF6D4FixedGridShard088EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard088EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard088EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard088EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard088EvenComparisonData)

theorem suzukiDF6D4FixedGridShard088EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard088EvenSolveData =
      suzukiDF6D4FixedGridShard088EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard088Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard088EvenSolveData =
    suzukiDF6D4FixedGridShard088EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard088EvenCross_eq_live :
    suzukiDF6D4FixedGridShard088EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 88) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard088EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 88)) at h
  exact h

theorem suzukiDF6D4FixedGridShard088EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard088EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 88 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 88 k) := by
    rw [suzukiDF6D4FixedGridShard088EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 88 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088EvenDotSoundness i
          suzukiDF6D4FixedGridShard088EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 88 k) := by
    simpa [suzukiDF6D4FixedGridShard088EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard088EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 88 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 88) := by
    rw [suzukiDF6D4FixedGridShard088EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 88)
  rw [suzukiDF6D4FixedGridShard088EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard088EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard088EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard088EvenDotSoundness i
            suzukiDF6D4FixedGridShard088EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard088EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard088OddComparison_eq_live :
    suzukiDF6D4FixedGridShard088OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 88 k) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard088OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 88 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard088OddCross_eq_live :
    suzukiDF6D4FixedGridShard088OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 88) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard088OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 88)) at h
  exact h

def suzukiDF6D4FixedGridShard088OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard088OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard088OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard088OddDotSoundness i.val
      suzukiDF6D4FixedGridShard088OddComparisonData)

theorem suzukiDF6D4FixedGridShard088OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard088OddSolveData =
      suzukiDF6D4FixedGridShard088OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard088Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard088OddSolveData =
    suzukiDF6D4FixedGridShard088OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard088OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard088OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 88 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 88 k) := by
    rw [suzukiDF6D4FixedGridShard088OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 88 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088OddDotSoundness i
          suzukiDF6D4FixedGridShard088OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 88 k) := by
    simpa [suzukiDF6D4FixedGridShard088OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard088OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 88 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 88) := by
    rw [suzukiDF6D4FixedGridShard088OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 88)
  rw [suzukiDF6D4FixedGridShard088OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard088OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard088OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard088OddDotSoundness i
            suzukiDF6D4FixedGridShard088OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard088OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard088EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard088EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 389) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard088EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 389)) at h
  exact h

theorem suzukiDF6D4FixedGridShard088EvenFull_eq_live :
    suzukiDF6D4FixedGridShard088EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 389) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard088EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 389)) at h
  exact h

def suzukiDF6D4FixedGridShard088EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard088EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard088EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard088EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard088EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard088EvenResidualData =
      suzukiDF6D4FixedGridShard088EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard088Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard088EvenResidualData =
    suzukiDF6D4FixedGridShard088EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard088EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard088EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 389 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 389) := by
    rw [suzukiDF6D4FixedGridShard088EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 389
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088EvenDotSoundness i
          suzukiDF6D4FixedGridShard088EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 389) := by
    simpa [suzukiDF6D4FixedGridShard088EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard088EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 389) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 389) := by
    rw [suzukiDF6D4FixedGridShard088EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 389
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard088EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard088EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard088EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard088EvenDotSoundness i
            suzukiDF6D4FixedGridShard088EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard088EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard088OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard088OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 389) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard088OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 389)) at h
  exact h

theorem suzukiDF6D4FixedGridShard088OddFull_eq_live :
    suzukiDF6D4FixedGridShard088OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 389) := by
  have h := suzukiDF6D4FixedGridShard088Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard088OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 389)) at h
  exact h

def suzukiDF6D4FixedGridShard088OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard088OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard088OddDotSoundness i.val
        suzukiDF6D4FixedGridShard088OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard088OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard088OddResidualData =
      suzukiDF6D4FixedGridShard088OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard088Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard088OddResidualData =
    suzukiDF6D4FixedGridShard088OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard088OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard088OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 389 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 389) := by
    rw [suzukiDF6D4FixedGridShard088OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 389
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088OddDotSoundness i
          suzukiDF6D4FixedGridShard088OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 389) := by
    simpa [suzukiDF6D4FixedGridShard088OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard088OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 389) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard088OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 389) := by
    rw [suzukiDF6D4FixedGridShard088OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 389
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard088OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard088OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard088OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard088OddDotSoundness i
            suzukiDF6D4FixedGridShard088OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard088OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
