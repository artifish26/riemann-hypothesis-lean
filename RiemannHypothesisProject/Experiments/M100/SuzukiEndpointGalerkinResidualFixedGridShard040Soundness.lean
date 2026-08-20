import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard040Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard040Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard040EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard040EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 40 k) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard040EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 40 k)) at h
  exact h

def suzukiDF6D4FixedGridShard040EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard040EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard040EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard040EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard040EvenComparisonData)

theorem suzukiDF6D4FixedGridShard040EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard040EvenSolveData =
      suzukiDF6D4FixedGridShard040EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard040Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard040EvenSolveData =
    suzukiDF6D4FixedGridShard040EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard040EvenCross_eq_live :
    suzukiDF6D4FixedGridShard040EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 40) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard040EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 40)) at h
  exact h

theorem suzukiDF6D4FixedGridShard040EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard040EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 40 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 40 k) := by
    rw [suzukiDF6D4FixedGridShard040EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 40 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040EvenDotSoundness i
          suzukiDF6D4FixedGridShard040EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 40 k) := by
    simpa [suzukiDF6D4FixedGridShard040EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard040EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 40 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 40) := by
    rw [suzukiDF6D4FixedGridShard040EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 40)
  rw [suzukiDF6D4FixedGridShard040EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard040EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard040EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard040EvenDotSoundness i
            suzukiDF6D4FixedGridShard040EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard040EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard040OddComparison_eq_live :
    suzukiDF6D4FixedGridShard040OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 40 k) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard040OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 40 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard040OddCross_eq_live :
    suzukiDF6D4FixedGridShard040OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 40) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard040OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 40)) at h
  exact h

def suzukiDF6D4FixedGridShard040OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard040OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard040OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard040OddDotSoundness i.val
      suzukiDF6D4FixedGridShard040OddComparisonData)

theorem suzukiDF6D4FixedGridShard040OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard040OddSolveData =
      suzukiDF6D4FixedGridShard040OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard040Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard040OddSolveData =
    suzukiDF6D4FixedGridShard040OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard040OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard040OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 40 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 40 k) := by
    rw [suzukiDF6D4FixedGridShard040OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 40 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040OddDotSoundness i
          suzukiDF6D4FixedGridShard040OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 40 k) := by
    simpa [suzukiDF6D4FixedGridShard040OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard040OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 40 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 40) := by
    rw [suzukiDF6D4FixedGridShard040OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 40)
  rw [suzukiDF6D4FixedGridShard040OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard040OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard040OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard040OddDotSoundness i
            suzukiDF6D4FixedGridShard040OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard040OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard040EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard040EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 341) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard040EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 341)) at h
  exact h

theorem suzukiDF6D4FixedGridShard040EvenFull_eq_live :
    suzukiDF6D4FixedGridShard040EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 341) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard040EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 341)) at h
  exact h

def suzukiDF6D4FixedGridShard040EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard040EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard040EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard040EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard040EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard040EvenResidualData =
      suzukiDF6D4FixedGridShard040EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard040Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard040EvenResidualData =
    suzukiDF6D4FixedGridShard040EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard040EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard040EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 341 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 341) := by
    rw [suzukiDF6D4FixedGridShard040EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 341
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040EvenDotSoundness i
          suzukiDF6D4FixedGridShard040EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 341) := by
    simpa [suzukiDF6D4FixedGridShard040EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard040EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 341) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 341) := by
    rw [suzukiDF6D4FixedGridShard040EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 341
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard040EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard040EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard040EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard040EvenDotSoundness i
            suzukiDF6D4FixedGridShard040EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard040EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard040OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard040OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 341) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard040OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 341)) at h
  exact h

theorem suzukiDF6D4FixedGridShard040OddFull_eq_live :
    suzukiDF6D4FixedGridShard040OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 341) := by
  have h := suzukiDF6D4FixedGridShard040Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard040OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 341)) at h
  exact h

def suzukiDF6D4FixedGridShard040OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard040OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard040OddDotSoundness i.val
        suzukiDF6D4FixedGridShard040OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard040OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard040OddResidualData =
      suzukiDF6D4FixedGridShard040OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard040Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard040OddResidualData =
    suzukiDF6D4FixedGridShard040OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard040OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard040OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 341 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 341) := by
    rw [suzukiDF6D4FixedGridShard040OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 341
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040OddDotSoundness i
          suzukiDF6D4FixedGridShard040OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 341) := by
    simpa [suzukiDF6D4FixedGridShard040OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard040OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 341) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard040OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 341) := by
    rw [suzukiDF6D4FixedGridShard040OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 341
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard040OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard040OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard040OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard040OddDotSoundness i
            suzukiDF6D4FixedGridShard040OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard040OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
