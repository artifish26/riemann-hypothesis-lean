import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard243Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard243Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard243EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard243EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 243 k) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard243EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 243 k)) at h
  exact h

def suzukiDF6D4FixedGridShard243EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard243EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard243EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard243EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard243EvenComparisonData)

theorem suzukiDF6D4FixedGridShard243EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard243EvenSolveData =
      suzukiDF6D4FixedGridShard243EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard243Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard243EvenSolveData =
    suzukiDF6D4FixedGridShard243EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard243EvenCross_eq_live :
    suzukiDF6D4FixedGridShard243EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 243) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard243EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 243)) at h
  exact h

theorem suzukiDF6D4FixedGridShard243EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard243EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 243 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 243 k) := by
    rw [suzukiDF6D4FixedGridShard243EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 243 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243EvenDotSoundness i
          suzukiDF6D4FixedGridShard243EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 243 k) := by
    simpa [suzukiDF6D4FixedGridShard243EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard243EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 243 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 243) := by
    rw [suzukiDF6D4FixedGridShard243EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 243)
  rw [suzukiDF6D4FixedGridShard243EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard243EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard243EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard243EvenDotSoundness i
            suzukiDF6D4FixedGridShard243EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard243EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard243OddComparison_eq_live :
    suzukiDF6D4FixedGridShard243OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 243 k) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard243OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 243 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard243OddCross_eq_live :
    suzukiDF6D4FixedGridShard243OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 243) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard243OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 243)) at h
  exact h

def suzukiDF6D4FixedGridShard243OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard243OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard243OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard243OddDotSoundness i.val
      suzukiDF6D4FixedGridShard243OddComparisonData)

theorem suzukiDF6D4FixedGridShard243OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard243OddSolveData =
      suzukiDF6D4FixedGridShard243OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard243Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard243OddSolveData =
    suzukiDF6D4FixedGridShard243OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard243OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard243OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 243 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 243 k) := by
    rw [suzukiDF6D4FixedGridShard243OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 243 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243OddDotSoundness i
          suzukiDF6D4FixedGridShard243OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 243 k) := by
    simpa [suzukiDF6D4FixedGridShard243OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard243OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 243 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 243) := by
    rw [suzukiDF6D4FixedGridShard243OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 243)
  rw [suzukiDF6D4FixedGridShard243OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard243OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard243OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard243OddDotSoundness i
            suzukiDF6D4FixedGridShard243OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard243OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard243EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard243EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 544) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard243EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 544)) at h
  exact h

theorem suzukiDF6D4FixedGridShard243EvenFull_eq_live :
    suzukiDF6D4FixedGridShard243EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 544) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard243EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 544)) at h
  exact h

def suzukiDF6D4FixedGridShard243EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard243EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard243EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard243EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard243EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard243EvenResidualData =
      suzukiDF6D4FixedGridShard243EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard243Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard243EvenResidualData =
    suzukiDF6D4FixedGridShard243EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard243EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard243EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 544 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 544) := by
    rw [suzukiDF6D4FixedGridShard243EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 544
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243EvenDotSoundness i
          suzukiDF6D4FixedGridShard243EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 544) := by
    simpa [suzukiDF6D4FixedGridShard243EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard243EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 544) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 544) := by
    rw [suzukiDF6D4FixedGridShard243EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 544
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard243EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard243EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard243EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard243EvenDotSoundness i
            suzukiDF6D4FixedGridShard243EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard243EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard243OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard243OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 544) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard243OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 544)) at h
  exact h

theorem suzukiDF6D4FixedGridShard243OddFull_eq_live :
    suzukiDF6D4FixedGridShard243OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 544) := by
  have h := suzukiDF6D4FixedGridShard243Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard243OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 544)) at h
  exact h

def suzukiDF6D4FixedGridShard243OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard243OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard243OddDotSoundness i.val
        suzukiDF6D4FixedGridShard243OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard243OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard243OddResidualData =
      suzukiDF6D4FixedGridShard243OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard243Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard243OddResidualData =
    suzukiDF6D4FixedGridShard243OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard243OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard243OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 544 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 544) := by
    rw [suzukiDF6D4FixedGridShard243OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 544
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243OddDotSoundness i
          suzukiDF6D4FixedGridShard243OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 544) := by
    simpa [suzukiDF6D4FixedGridShard243OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard243OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 544) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard243OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 544) := by
    rw [suzukiDF6D4FixedGridShard243OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 544
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard243OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard243OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard243OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard243OddDotSoundness i
            suzukiDF6D4FixedGridShard243OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard243OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
