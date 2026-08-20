import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard049Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard049Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard049EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard049EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 49 k) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard049EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 49 k)) at h
  exact h

def suzukiDF6D4FixedGridShard049EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard049EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard049EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard049EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard049EvenComparisonData)

theorem suzukiDF6D4FixedGridShard049EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard049EvenSolveData =
      suzukiDF6D4FixedGridShard049EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard049Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard049EvenSolveData =
    suzukiDF6D4FixedGridShard049EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard049EvenCross_eq_live :
    suzukiDF6D4FixedGridShard049EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 49) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard049EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 49)) at h
  exact h

theorem suzukiDF6D4FixedGridShard049EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard049EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 49 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 49 k) := by
    rw [suzukiDF6D4FixedGridShard049EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 49 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049EvenDotSoundness i
          suzukiDF6D4FixedGridShard049EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 49 k) := by
    simpa [suzukiDF6D4FixedGridShard049EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard049EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 49 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 49) := by
    rw [suzukiDF6D4FixedGridShard049EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 49)
  rw [suzukiDF6D4FixedGridShard049EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard049EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard049EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard049EvenDotSoundness i
            suzukiDF6D4FixedGridShard049EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard049EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard049OddComparison_eq_live :
    suzukiDF6D4FixedGridShard049OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 49 k) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard049OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 49 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard049OddCross_eq_live :
    suzukiDF6D4FixedGridShard049OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 49) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard049OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 49)) at h
  exact h

def suzukiDF6D4FixedGridShard049OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard049OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard049OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard049OddDotSoundness i.val
      suzukiDF6D4FixedGridShard049OddComparisonData)

theorem suzukiDF6D4FixedGridShard049OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard049OddSolveData =
      suzukiDF6D4FixedGridShard049OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard049Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard049OddSolveData =
    suzukiDF6D4FixedGridShard049OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard049OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard049OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 49 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 49 k) := by
    rw [suzukiDF6D4FixedGridShard049OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 49 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049OddDotSoundness i
          suzukiDF6D4FixedGridShard049OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 49 k) := by
    simpa [suzukiDF6D4FixedGridShard049OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard049OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 49 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 49) := by
    rw [suzukiDF6D4FixedGridShard049OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 49)
  rw [suzukiDF6D4FixedGridShard049OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard049OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard049OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard049OddDotSoundness i
            suzukiDF6D4FixedGridShard049OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard049OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard049EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard049EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 350) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard049EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 350)) at h
  exact h

theorem suzukiDF6D4FixedGridShard049EvenFull_eq_live :
    suzukiDF6D4FixedGridShard049EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 350) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard049EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 350)) at h
  exact h

def suzukiDF6D4FixedGridShard049EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard049EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard049EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard049EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard049EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard049EvenResidualData =
      suzukiDF6D4FixedGridShard049EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard049Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard049EvenResidualData =
    suzukiDF6D4FixedGridShard049EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard049EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard049EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 350 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 350) := by
    rw [suzukiDF6D4FixedGridShard049EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 350
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049EvenDotSoundness i
          suzukiDF6D4FixedGridShard049EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 350) := by
    simpa [suzukiDF6D4FixedGridShard049EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard049EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 350) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 350) := by
    rw [suzukiDF6D4FixedGridShard049EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 350
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard049EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard049EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard049EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard049EvenDotSoundness i
            suzukiDF6D4FixedGridShard049EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard049EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard049OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard049OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 350) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard049OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 350)) at h
  exact h

theorem suzukiDF6D4FixedGridShard049OddFull_eq_live :
    suzukiDF6D4FixedGridShard049OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 350) := by
  have h := suzukiDF6D4FixedGridShard049Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard049OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 350)) at h
  exact h

def suzukiDF6D4FixedGridShard049OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard049OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard049OddDotSoundness i.val
        suzukiDF6D4FixedGridShard049OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard049OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard049OddResidualData =
      suzukiDF6D4FixedGridShard049OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard049Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard049OddResidualData =
    suzukiDF6D4FixedGridShard049OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard049OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard049OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 350 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 350) := by
    rw [suzukiDF6D4FixedGridShard049OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 350
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049OddDotSoundness i
          suzukiDF6D4FixedGridShard049OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 350) := by
    simpa [suzukiDF6D4FixedGridShard049OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard049OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 350) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard049OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 350) := by
    rw [suzukiDF6D4FixedGridShard049OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 350
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard049OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard049OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard049OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard049OddDotSoundness i
            suzukiDF6D4FixedGridShard049OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard049OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
