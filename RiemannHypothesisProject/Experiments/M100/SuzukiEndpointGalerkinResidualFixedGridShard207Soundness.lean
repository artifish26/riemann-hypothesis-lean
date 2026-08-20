import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard207Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard207Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard207EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard207EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 207 k) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard207EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 207 k)) at h
  exact h

def suzukiDF6D4FixedGridShard207EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard207EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard207EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard207EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard207EvenComparisonData)

theorem suzukiDF6D4FixedGridShard207EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard207EvenSolveData =
      suzukiDF6D4FixedGridShard207EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard207Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard207EvenSolveData =
    suzukiDF6D4FixedGridShard207EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard207EvenCross_eq_live :
    suzukiDF6D4FixedGridShard207EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 207) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard207EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 207)) at h
  exact h

theorem suzukiDF6D4FixedGridShard207EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard207EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 207 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 207 k) := by
    rw [suzukiDF6D4FixedGridShard207EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 207 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207EvenDotSoundness i
          suzukiDF6D4FixedGridShard207EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 207 k) := by
    simpa [suzukiDF6D4FixedGridShard207EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard207EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 207 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 207) := by
    rw [suzukiDF6D4FixedGridShard207EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 207)
  rw [suzukiDF6D4FixedGridShard207EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard207EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard207EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard207EvenDotSoundness i
            suzukiDF6D4FixedGridShard207EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard207EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard207OddComparison_eq_live :
    suzukiDF6D4FixedGridShard207OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 207 k) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard207OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 207 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard207OddCross_eq_live :
    suzukiDF6D4FixedGridShard207OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 207) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard207OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 207)) at h
  exact h

def suzukiDF6D4FixedGridShard207OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard207OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard207OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard207OddDotSoundness i.val
      suzukiDF6D4FixedGridShard207OddComparisonData)

theorem suzukiDF6D4FixedGridShard207OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard207OddSolveData =
      suzukiDF6D4FixedGridShard207OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard207Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard207OddSolveData =
    suzukiDF6D4FixedGridShard207OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard207OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard207OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 207 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 207 k) := by
    rw [suzukiDF6D4FixedGridShard207OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 207 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207OddDotSoundness i
          suzukiDF6D4FixedGridShard207OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 207 k) := by
    simpa [suzukiDF6D4FixedGridShard207OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard207OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 207 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 207) := by
    rw [suzukiDF6D4FixedGridShard207OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 207)
  rw [suzukiDF6D4FixedGridShard207OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard207OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard207OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard207OddDotSoundness i
            suzukiDF6D4FixedGridShard207OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard207OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard207EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard207EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 508) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard207EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 508)) at h
  exact h

theorem suzukiDF6D4FixedGridShard207EvenFull_eq_live :
    suzukiDF6D4FixedGridShard207EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 508) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard207EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 508)) at h
  exact h

def suzukiDF6D4FixedGridShard207EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard207EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard207EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard207EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard207EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard207EvenResidualData =
      suzukiDF6D4FixedGridShard207EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard207Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard207EvenResidualData =
    suzukiDF6D4FixedGridShard207EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard207EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard207EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 508 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 508) := by
    rw [suzukiDF6D4FixedGridShard207EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 508
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207EvenDotSoundness i
          suzukiDF6D4FixedGridShard207EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 508) := by
    simpa [suzukiDF6D4FixedGridShard207EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard207EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 508) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 508) := by
    rw [suzukiDF6D4FixedGridShard207EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 508
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard207EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard207EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard207EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard207EvenDotSoundness i
            suzukiDF6D4FixedGridShard207EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard207EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard207OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard207OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 508) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard207OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 508)) at h
  exact h

theorem suzukiDF6D4FixedGridShard207OddFull_eq_live :
    suzukiDF6D4FixedGridShard207OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 508) := by
  have h := suzukiDF6D4FixedGridShard207Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard207OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 508)) at h
  exact h

def suzukiDF6D4FixedGridShard207OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard207OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard207OddDotSoundness i.val
        suzukiDF6D4FixedGridShard207OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard207OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard207OddResidualData =
      suzukiDF6D4FixedGridShard207OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard207Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard207OddResidualData =
    suzukiDF6D4FixedGridShard207OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard207OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard207OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 508 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 508) := by
    rw [suzukiDF6D4FixedGridShard207OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 508
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207OddDotSoundness i
          suzukiDF6D4FixedGridShard207OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 508) := by
    simpa [suzukiDF6D4FixedGridShard207OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard207OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 508) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard207OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 508) := by
    rw [suzukiDF6D4FixedGridShard207OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 508
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard207OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard207OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard207OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard207OddDotSoundness i
            suzukiDF6D4FixedGridShard207OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard207OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
