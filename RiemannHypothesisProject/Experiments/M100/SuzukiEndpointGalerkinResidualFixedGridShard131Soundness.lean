import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard131Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard131Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard131EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard131EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 131 k) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard131EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 131 k)) at h
  exact h

def suzukiDF6D4FixedGridShard131EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard131EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard131EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard131EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard131EvenComparisonData)

theorem suzukiDF6D4FixedGridShard131EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard131EvenSolveData =
      suzukiDF6D4FixedGridShard131EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard131Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard131EvenSolveData =
    suzukiDF6D4FixedGridShard131EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard131EvenCross_eq_live :
    suzukiDF6D4FixedGridShard131EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 131) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard131EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 131)) at h
  exact h

theorem suzukiDF6D4FixedGridShard131EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard131EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 131 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 131 k) := by
    rw [suzukiDF6D4FixedGridShard131EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 131 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131EvenDotSoundness i
          suzukiDF6D4FixedGridShard131EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 131 k) := by
    simpa [suzukiDF6D4FixedGridShard131EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard131EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 131 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 131) := by
    rw [suzukiDF6D4FixedGridShard131EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 131)
  rw [suzukiDF6D4FixedGridShard131EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard131EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard131EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard131EvenDotSoundness i
            suzukiDF6D4FixedGridShard131EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard131EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard131OddComparison_eq_live :
    suzukiDF6D4FixedGridShard131OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 131 k) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard131OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 131 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard131OddCross_eq_live :
    suzukiDF6D4FixedGridShard131OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 131) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard131OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 131)) at h
  exact h

def suzukiDF6D4FixedGridShard131OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard131OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard131OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard131OddDotSoundness i.val
      suzukiDF6D4FixedGridShard131OddComparisonData)

theorem suzukiDF6D4FixedGridShard131OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard131OddSolveData =
      suzukiDF6D4FixedGridShard131OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard131Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard131OddSolveData =
    suzukiDF6D4FixedGridShard131OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard131OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard131OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 131 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 131 k) := by
    rw [suzukiDF6D4FixedGridShard131OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 131 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131OddDotSoundness i
          suzukiDF6D4FixedGridShard131OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 131 k) := by
    simpa [suzukiDF6D4FixedGridShard131OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard131OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 131 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 131) := by
    rw [suzukiDF6D4FixedGridShard131OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 131)
  rw [suzukiDF6D4FixedGridShard131OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard131OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard131OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard131OddDotSoundness i
            suzukiDF6D4FixedGridShard131OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard131OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard131EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard131EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 432) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard131EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 432)) at h
  exact h

theorem suzukiDF6D4FixedGridShard131EvenFull_eq_live :
    suzukiDF6D4FixedGridShard131EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 432) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard131EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 432)) at h
  exact h

def suzukiDF6D4FixedGridShard131EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard131EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard131EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard131EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard131EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard131EvenResidualData =
      suzukiDF6D4FixedGridShard131EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard131Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard131EvenResidualData =
    suzukiDF6D4FixedGridShard131EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard131EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard131EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 432 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 432) := by
    rw [suzukiDF6D4FixedGridShard131EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 432
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131EvenDotSoundness i
          suzukiDF6D4FixedGridShard131EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 432) := by
    simpa [suzukiDF6D4FixedGridShard131EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard131EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 432) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 432) := by
    rw [suzukiDF6D4FixedGridShard131EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 432
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard131EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard131EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard131EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard131EvenDotSoundness i
            suzukiDF6D4FixedGridShard131EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard131EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard131OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard131OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 432) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard131OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 432)) at h
  exact h

theorem suzukiDF6D4FixedGridShard131OddFull_eq_live :
    suzukiDF6D4FixedGridShard131OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 432) := by
  have h := suzukiDF6D4FixedGridShard131Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard131OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 432)) at h
  exact h

def suzukiDF6D4FixedGridShard131OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard131OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard131OddDotSoundness i.val
        suzukiDF6D4FixedGridShard131OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard131OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard131OddResidualData =
      suzukiDF6D4FixedGridShard131OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard131Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard131OddResidualData =
    suzukiDF6D4FixedGridShard131OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard131OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard131OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 432 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 432) := by
    rw [suzukiDF6D4FixedGridShard131OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 432
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131OddDotSoundness i
          suzukiDF6D4FixedGridShard131OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 432) := by
    simpa [suzukiDF6D4FixedGridShard131OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard131OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 432) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard131OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 432) := by
    rw [suzukiDF6D4FixedGridShard131OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 432
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard131OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard131OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard131OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard131OddDotSoundness i
            suzukiDF6D4FixedGridShard131OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard131OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
