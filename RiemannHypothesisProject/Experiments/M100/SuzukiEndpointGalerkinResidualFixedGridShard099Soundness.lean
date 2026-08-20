import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard099Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard099Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard099EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard099EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 99 k) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard099EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 99 k)) at h
  exact h

def suzukiDF6D4FixedGridShard099EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard099EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard099EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard099EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard099EvenComparisonData)

theorem suzukiDF6D4FixedGridShard099EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard099EvenSolveData =
      suzukiDF6D4FixedGridShard099EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard099Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard099EvenSolveData =
    suzukiDF6D4FixedGridShard099EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard099EvenCross_eq_live :
    suzukiDF6D4FixedGridShard099EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 99) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard099EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 99)) at h
  exact h

theorem suzukiDF6D4FixedGridShard099EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard099EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 99 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 99 k) := by
    rw [suzukiDF6D4FixedGridShard099EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 99 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099EvenDotSoundness i
          suzukiDF6D4FixedGridShard099EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 99 k) := by
    simpa [suzukiDF6D4FixedGridShard099EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard099EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 99 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 99) := by
    rw [suzukiDF6D4FixedGridShard099EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 99)
  rw [suzukiDF6D4FixedGridShard099EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard099EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard099EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard099EvenDotSoundness i
            suzukiDF6D4FixedGridShard099EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard099EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard099OddComparison_eq_live :
    suzukiDF6D4FixedGridShard099OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 99 k) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard099OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 99 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard099OddCross_eq_live :
    suzukiDF6D4FixedGridShard099OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 99) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard099OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 99)) at h
  exact h

def suzukiDF6D4FixedGridShard099OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard099OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard099OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard099OddDotSoundness i.val
      suzukiDF6D4FixedGridShard099OddComparisonData)

theorem suzukiDF6D4FixedGridShard099OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard099OddSolveData =
      suzukiDF6D4FixedGridShard099OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard099Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard099OddSolveData =
    suzukiDF6D4FixedGridShard099OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard099OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard099OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 99 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 99 k) := by
    rw [suzukiDF6D4FixedGridShard099OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 99 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099OddDotSoundness i
          suzukiDF6D4FixedGridShard099OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 99 k) := by
    simpa [suzukiDF6D4FixedGridShard099OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard099OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 99 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 99) := by
    rw [suzukiDF6D4FixedGridShard099OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 99)
  rw [suzukiDF6D4FixedGridShard099OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard099OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard099OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard099OddDotSoundness i
            suzukiDF6D4FixedGridShard099OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard099OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard099EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard099EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 400) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard099EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 400)) at h
  exact h

theorem suzukiDF6D4FixedGridShard099EvenFull_eq_live :
    suzukiDF6D4FixedGridShard099EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 400) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard099EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 400)) at h
  exact h

def suzukiDF6D4FixedGridShard099EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard099EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard099EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard099EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard099EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard099EvenResidualData =
      suzukiDF6D4FixedGridShard099EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard099Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard099EvenResidualData =
    suzukiDF6D4FixedGridShard099EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard099EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard099EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 400 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 400) := by
    rw [suzukiDF6D4FixedGridShard099EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 400
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099EvenDotSoundness i
          suzukiDF6D4FixedGridShard099EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 400) := by
    simpa [suzukiDF6D4FixedGridShard099EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard099EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 400) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 400) := by
    rw [suzukiDF6D4FixedGridShard099EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 400
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard099EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard099EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard099EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard099EvenDotSoundness i
            suzukiDF6D4FixedGridShard099EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard099EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard099OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard099OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 400) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard099OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 400)) at h
  exact h

theorem suzukiDF6D4FixedGridShard099OddFull_eq_live :
    suzukiDF6D4FixedGridShard099OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 400) := by
  have h := suzukiDF6D4FixedGridShard099Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard099OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 400)) at h
  exact h

def suzukiDF6D4FixedGridShard099OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard099OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard099OddDotSoundness i.val
        suzukiDF6D4FixedGridShard099OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard099OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard099OddResidualData =
      suzukiDF6D4FixedGridShard099OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard099Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard099OddResidualData =
    suzukiDF6D4FixedGridShard099OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard099OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard099OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 400 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 400) := by
    rw [suzukiDF6D4FixedGridShard099OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 400
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099OddDotSoundness i
          suzukiDF6D4FixedGridShard099OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 400) := by
    simpa [suzukiDF6D4FixedGridShard099OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard099OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 400) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard099OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 400) := by
    rw [suzukiDF6D4FixedGridShard099OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 400
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard099OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard099OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard099OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard099OddDotSoundness i
            suzukiDF6D4FixedGridShard099OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard099OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
