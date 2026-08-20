import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard121Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard121Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard121EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard121EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 121 k) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard121EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 121 k)) at h
  exact h

def suzukiDF6D4FixedGridShard121EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard121EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard121EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard121EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard121EvenComparisonData)

theorem suzukiDF6D4FixedGridShard121EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard121EvenSolveData =
      suzukiDF6D4FixedGridShard121EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard121Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard121EvenSolveData =
    suzukiDF6D4FixedGridShard121EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard121EvenCross_eq_live :
    suzukiDF6D4FixedGridShard121EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 121) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard121EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 121)) at h
  exact h

theorem suzukiDF6D4FixedGridShard121EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard121EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 121 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 121 k) := by
    rw [suzukiDF6D4FixedGridShard121EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 121 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121EvenDotSoundness i
          suzukiDF6D4FixedGridShard121EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 121 k) := by
    simpa [suzukiDF6D4FixedGridShard121EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard121EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 121 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 121) := by
    rw [suzukiDF6D4FixedGridShard121EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 121)
  rw [suzukiDF6D4FixedGridShard121EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard121EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard121EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard121EvenDotSoundness i
            suzukiDF6D4FixedGridShard121EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard121EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard121OddComparison_eq_live :
    suzukiDF6D4FixedGridShard121OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 121 k) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard121OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 121 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard121OddCross_eq_live :
    suzukiDF6D4FixedGridShard121OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 121) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard121OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 121)) at h
  exact h

def suzukiDF6D4FixedGridShard121OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard121OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard121OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard121OddDotSoundness i.val
      suzukiDF6D4FixedGridShard121OddComparisonData)

theorem suzukiDF6D4FixedGridShard121OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard121OddSolveData =
      suzukiDF6D4FixedGridShard121OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard121Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard121OddSolveData =
    suzukiDF6D4FixedGridShard121OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard121OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard121OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 121 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 121 k) := by
    rw [suzukiDF6D4FixedGridShard121OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 121 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121OddDotSoundness i
          suzukiDF6D4FixedGridShard121OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 121 k) := by
    simpa [suzukiDF6D4FixedGridShard121OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard121OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 121 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 121) := by
    rw [suzukiDF6D4FixedGridShard121OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 121)
  rw [suzukiDF6D4FixedGridShard121OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard121OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard121OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard121OddDotSoundness i
            suzukiDF6D4FixedGridShard121OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard121OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard121EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard121EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 422) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard121EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 422)) at h
  exact h

theorem suzukiDF6D4FixedGridShard121EvenFull_eq_live :
    suzukiDF6D4FixedGridShard121EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 422) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard121EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 422)) at h
  exact h

def suzukiDF6D4FixedGridShard121EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard121EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard121EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard121EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard121EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard121EvenResidualData =
      suzukiDF6D4FixedGridShard121EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard121Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard121EvenResidualData =
    suzukiDF6D4FixedGridShard121EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard121EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard121EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 422 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 422) := by
    rw [suzukiDF6D4FixedGridShard121EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 422
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121EvenDotSoundness i
          suzukiDF6D4FixedGridShard121EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 422) := by
    simpa [suzukiDF6D4FixedGridShard121EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard121EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 422) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 422) := by
    rw [suzukiDF6D4FixedGridShard121EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 422
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard121EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard121EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard121EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard121EvenDotSoundness i
            suzukiDF6D4FixedGridShard121EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard121EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard121OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard121OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 422) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard121OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 422)) at h
  exact h

theorem suzukiDF6D4FixedGridShard121OddFull_eq_live :
    suzukiDF6D4FixedGridShard121OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 422) := by
  have h := suzukiDF6D4FixedGridShard121Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard121OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 422)) at h
  exact h

def suzukiDF6D4FixedGridShard121OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard121OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard121OddDotSoundness i.val
        suzukiDF6D4FixedGridShard121OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard121OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard121OddResidualData =
      suzukiDF6D4FixedGridShard121OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard121Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard121OddResidualData =
    suzukiDF6D4FixedGridShard121OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard121OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard121OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 422 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 422) := by
    rw [suzukiDF6D4FixedGridShard121OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 422
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121OddDotSoundness i
          suzukiDF6D4FixedGridShard121OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 422) := by
    simpa [suzukiDF6D4FixedGridShard121OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard121OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 422) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard121OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 422) := by
    rw [suzukiDF6D4FixedGridShard121OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 422
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard121OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard121OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard121OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard121OddDotSoundness i
            suzukiDF6D4FixedGridShard121OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard121OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
