import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard003Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard003Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard003EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard003EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 3 k) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard003EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 3 k)) at h
  exact h

def suzukiDF6D4FixedGridShard003EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard003EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard003EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard003EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard003EvenComparisonData)

theorem suzukiDF6D4FixedGridShard003EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard003EvenSolveData =
      suzukiDF6D4FixedGridShard003EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard003Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard003EvenSolveData =
    suzukiDF6D4FixedGridShard003EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard003EvenCross_eq_live :
    suzukiDF6D4FixedGridShard003EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 3) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard003EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 3)) at h
  exact h

theorem suzukiDF6D4FixedGridShard003EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard003EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 3 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 3 k) := by
    rw [suzukiDF6D4FixedGridShard003EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 3 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003EvenDotSoundness i
          suzukiDF6D4FixedGridShard003EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 3 k) := by
    simpa [suzukiDF6D4FixedGridShard003EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard003EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 3 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 3) := by
    rw [suzukiDF6D4FixedGridShard003EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 3)
  rw [suzukiDF6D4FixedGridShard003EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard003EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard003EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard003EvenDotSoundness i
            suzukiDF6D4FixedGridShard003EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard003EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard003OddComparison_eq_live :
    suzukiDF6D4FixedGridShard003OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 3 k) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard003OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 3 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard003OddCross_eq_live :
    suzukiDF6D4FixedGridShard003OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 3) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard003OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 3)) at h
  exact h

def suzukiDF6D4FixedGridShard003OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard003OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard003OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard003OddDotSoundness i.val
      suzukiDF6D4FixedGridShard003OddComparisonData)

theorem suzukiDF6D4FixedGridShard003OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard003OddSolveData =
      suzukiDF6D4FixedGridShard003OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard003Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard003OddSolveData =
    suzukiDF6D4FixedGridShard003OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard003OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard003OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 3 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 3 k) := by
    rw [suzukiDF6D4FixedGridShard003OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 3 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003OddDotSoundness i
          suzukiDF6D4FixedGridShard003OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 3 k) := by
    simpa [suzukiDF6D4FixedGridShard003OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard003OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 3 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 3) := by
    rw [suzukiDF6D4FixedGridShard003OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 3)
  rw [suzukiDF6D4FixedGridShard003OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard003OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard003OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard003OddDotSoundness i
            suzukiDF6D4FixedGridShard003OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard003OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard003EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard003EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 304) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard003EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 304)) at h
  exact h

theorem suzukiDF6D4FixedGridShard003EvenFull_eq_live :
    suzukiDF6D4FixedGridShard003EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 304) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard003EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 304)) at h
  exact h

def suzukiDF6D4FixedGridShard003EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard003EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard003EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard003EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard003EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard003EvenResidualData =
      suzukiDF6D4FixedGridShard003EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard003Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard003EvenResidualData =
    suzukiDF6D4FixedGridShard003EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard003EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard003EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 304 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 304) := by
    rw [suzukiDF6D4FixedGridShard003EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 304
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003EvenDotSoundness i
          suzukiDF6D4FixedGridShard003EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 304) := by
    simpa [suzukiDF6D4FixedGridShard003EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard003EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 304) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 304) := by
    rw [suzukiDF6D4FixedGridShard003EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 304
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard003EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard003EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard003EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard003EvenDotSoundness i
            suzukiDF6D4FixedGridShard003EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard003EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard003OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard003OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 304) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard003OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 304)) at h
  exact h

theorem suzukiDF6D4FixedGridShard003OddFull_eq_live :
    suzukiDF6D4FixedGridShard003OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 304) := by
  have h := suzukiDF6D4FixedGridShard003Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard003OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 304)) at h
  exact h

def suzukiDF6D4FixedGridShard003OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard003OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard003OddDotSoundness i.val
        suzukiDF6D4FixedGridShard003OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard003OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard003OddResidualData =
      suzukiDF6D4FixedGridShard003OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard003Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard003OddResidualData =
    suzukiDF6D4FixedGridShard003OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard003OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard003OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 304 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 304) := by
    rw [suzukiDF6D4FixedGridShard003OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 304
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003OddDotSoundness i
          suzukiDF6D4FixedGridShard003OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 304) := by
    simpa [suzukiDF6D4FixedGridShard003OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard003OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 304) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard003OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 304) := by
    rw [suzukiDF6D4FixedGridShard003OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 304
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard003OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard003OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard003OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard003OddDotSoundness i
            suzukiDF6D4FixedGridShard003OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard003OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
