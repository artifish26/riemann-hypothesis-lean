import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard039Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard039Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard039EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard039EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 39 k) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard039EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 39 k)) at h
  exact h

def suzukiDF6D4FixedGridShard039EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard039EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard039EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard039EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard039EvenComparisonData)

theorem suzukiDF6D4FixedGridShard039EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard039EvenSolveData =
      suzukiDF6D4FixedGridShard039EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard039Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard039EvenSolveData =
    suzukiDF6D4FixedGridShard039EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard039EvenCross_eq_live :
    suzukiDF6D4FixedGridShard039EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 39) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard039EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 39)) at h
  exact h

theorem suzukiDF6D4FixedGridShard039EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard039EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 39 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 39 k) := by
    rw [suzukiDF6D4FixedGridShard039EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 39 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039EvenDotSoundness i
          suzukiDF6D4FixedGridShard039EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 39 k) := by
    simpa [suzukiDF6D4FixedGridShard039EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard039EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 39 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 39) := by
    rw [suzukiDF6D4FixedGridShard039EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 39)
  rw [suzukiDF6D4FixedGridShard039EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard039EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard039EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard039EvenDotSoundness i
            suzukiDF6D4FixedGridShard039EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard039EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard039OddComparison_eq_live :
    suzukiDF6D4FixedGridShard039OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 39 k) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard039OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 39 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard039OddCross_eq_live :
    suzukiDF6D4FixedGridShard039OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 39) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard039OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 39)) at h
  exact h

def suzukiDF6D4FixedGridShard039OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard039OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard039OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard039OddDotSoundness i.val
      suzukiDF6D4FixedGridShard039OddComparisonData)

theorem suzukiDF6D4FixedGridShard039OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard039OddSolveData =
      suzukiDF6D4FixedGridShard039OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard039Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard039OddSolveData =
    suzukiDF6D4FixedGridShard039OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard039OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard039OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 39 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 39 k) := by
    rw [suzukiDF6D4FixedGridShard039OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 39 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039OddDotSoundness i
          suzukiDF6D4FixedGridShard039OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 39 k) := by
    simpa [suzukiDF6D4FixedGridShard039OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard039OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 39 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 39) := by
    rw [suzukiDF6D4FixedGridShard039OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 39)
  rw [suzukiDF6D4FixedGridShard039OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard039OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard039OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard039OddDotSoundness i
            suzukiDF6D4FixedGridShard039OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard039OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard039EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard039EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 340) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard039EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 340)) at h
  exact h

theorem suzukiDF6D4FixedGridShard039EvenFull_eq_live :
    suzukiDF6D4FixedGridShard039EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 340) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard039EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 340)) at h
  exact h

def suzukiDF6D4FixedGridShard039EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard039EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard039EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard039EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard039EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard039EvenResidualData =
      suzukiDF6D4FixedGridShard039EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard039Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard039EvenResidualData =
    suzukiDF6D4FixedGridShard039EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard039EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard039EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 340 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 340) := by
    rw [suzukiDF6D4FixedGridShard039EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 340
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039EvenDotSoundness i
          suzukiDF6D4FixedGridShard039EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 340) := by
    simpa [suzukiDF6D4FixedGridShard039EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard039EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 340) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 340) := by
    rw [suzukiDF6D4FixedGridShard039EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 340
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard039EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard039EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard039EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard039EvenDotSoundness i
            suzukiDF6D4FixedGridShard039EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard039EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard039OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard039OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 340) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard039OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 340)) at h
  exact h

theorem suzukiDF6D4FixedGridShard039OddFull_eq_live :
    suzukiDF6D4FixedGridShard039OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 340) := by
  have h := suzukiDF6D4FixedGridShard039Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard039OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 340)) at h
  exact h

def suzukiDF6D4FixedGridShard039OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard039OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard039OddDotSoundness i.val
        suzukiDF6D4FixedGridShard039OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard039OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard039OddResidualData =
      suzukiDF6D4FixedGridShard039OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard039Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard039OddResidualData =
    suzukiDF6D4FixedGridShard039OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard039OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard039OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 340 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 340) := by
    rw [suzukiDF6D4FixedGridShard039OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 340
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039OddDotSoundness i
          suzukiDF6D4FixedGridShard039OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 340) := by
    simpa [suzukiDF6D4FixedGridShard039OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard039OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 340) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard039OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 340) := by
    rw [suzukiDF6D4FixedGridShard039OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 340
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard039OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard039OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard039OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard039OddDotSoundness i
            suzukiDF6D4FixedGridShard039OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard039OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
