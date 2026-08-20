import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard013Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard013Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard013EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard013EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 13 k) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard013EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 13 k)) at h
  exact h

def suzukiDF6D4FixedGridShard013EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard013EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard013EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard013EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard013EvenComparisonData)

theorem suzukiDF6D4FixedGridShard013EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard013EvenSolveData =
      suzukiDF6D4FixedGridShard013EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard013Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard013EvenSolveData =
    suzukiDF6D4FixedGridShard013EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard013EvenCross_eq_live :
    suzukiDF6D4FixedGridShard013EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 13) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard013EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 13)) at h
  exact h

theorem suzukiDF6D4FixedGridShard013EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard013EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 13 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 13 k) := by
    rw [suzukiDF6D4FixedGridShard013EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 13 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013EvenDotSoundness i
          suzukiDF6D4FixedGridShard013EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 13 k) := by
    simpa [suzukiDF6D4FixedGridShard013EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard013EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 13 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 13) := by
    rw [suzukiDF6D4FixedGridShard013EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 13)
  rw [suzukiDF6D4FixedGridShard013EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard013EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard013EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard013EvenDotSoundness i
            suzukiDF6D4FixedGridShard013EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard013EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard013OddComparison_eq_live :
    suzukiDF6D4FixedGridShard013OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 13 k) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard013OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 13 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard013OddCross_eq_live :
    suzukiDF6D4FixedGridShard013OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 13) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard013OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 13)) at h
  exact h

def suzukiDF6D4FixedGridShard013OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard013OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard013OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard013OddDotSoundness i.val
      suzukiDF6D4FixedGridShard013OddComparisonData)

theorem suzukiDF6D4FixedGridShard013OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard013OddSolveData =
      suzukiDF6D4FixedGridShard013OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard013Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard013OddSolveData =
    suzukiDF6D4FixedGridShard013OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard013OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard013OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 13 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 13 k) := by
    rw [suzukiDF6D4FixedGridShard013OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 13 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013OddDotSoundness i
          suzukiDF6D4FixedGridShard013OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 13 k) := by
    simpa [suzukiDF6D4FixedGridShard013OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard013OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 13 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 13) := by
    rw [suzukiDF6D4FixedGridShard013OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 13)
  rw [suzukiDF6D4FixedGridShard013OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard013OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard013OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard013OddDotSoundness i
            suzukiDF6D4FixedGridShard013OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard013OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard013EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard013EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 314) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard013EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 314)) at h
  exact h

theorem suzukiDF6D4FixedGridShard013EvenFull_eq_live :
    suzukiDF6D4FixedGridShard013EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 314) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard013EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 314)) at h
  exact h

def suzukiDF6D4FixedGridShard013EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard013EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard013EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard013EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard013EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard013EvenResidualData =
      suzukiDF6D4FixedGridShard013EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard013Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard013EvenResidualData =
    suzukiDF6D4FixedGridShard013EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard013EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard013EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 314 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 314) := by
    rw [suzukiDF6D4FixedGridShard013EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 314
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013EvenDotSoundness i
          suzukiDF6D4FixedGridShard013EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 314) := by
    simpa [suzukiDF6D4FixedGridShard013EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard013EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 314) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 314) := by
    rw [suzukiDF6D4FixedGridShard013EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 314
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard013EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard013EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard013EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard013EvenDotSoundness i
            suzukiDF6D4FixedGridShard013EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard013EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard013OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard013OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 314) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard013OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 314)) at h
  exact h

theorem suzukiDF6D4FixedGridShard013OddFull_eq_live :
    suzukiDF6D4FixedGridShard013OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 314) := by
  have h := suzukiDF6D4FixedGridShard013Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard013OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 314)) at h
  exact h

def suzukiDF6D4FixedGridShard013OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard013OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard013OddDotSoundness i.val
        suzukiDF6D4FixedGridShard013OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard013OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard013OddResidualData =
      suzukiDF6D4FixedGridShard013OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard013Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard013OddResidualData =
    suzukiDF6D4FixedGridShard013OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard013OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard013OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 314 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 314) := by
    rw [suzukiDF6D4FixedGridShard013OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 314
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013OddDotSoundness i
          suzukiDF6D4FixedGridShard013OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 314) := by
    simpa [suzukiDF6D4FixedGridShard013OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard013OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 314) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard013OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 314) := by
    rw [suzukiDF6D4FixedGridShard013OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 314
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard013OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard013OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard013OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard013OddDotSoundness i
            suzukiDF6D4FixedGridShard013OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard013OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
