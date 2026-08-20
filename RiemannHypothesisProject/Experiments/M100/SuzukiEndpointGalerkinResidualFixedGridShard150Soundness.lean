import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard150Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard150Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard150EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard150EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 150 k) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard150EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 150 k)) at h
  exact h

def suzukiDF6D4FixedGridShard150EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard150EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard150EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard150EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard150EvenComparisonData)

theorem suzukiDF6D4FixedGridShard150EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard150EvenSolveData =
      suzukiDF6D4FixedGridShard150EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard150Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard150EvenSolveData =
    suzukiDF6D4FixedGridShard150EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard150EvenCross_eq_live :
    suzukiDF6D4FixedGridShard150EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 150) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard150EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 150)) at h
  exact h

theorem suzukiDF6D4FixedGridShard150EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard150EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 150 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 150 k) := by
    rw [suzukiDF6D4FixedGridShard150EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 150 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150EvenDotSoundness i
          suzukiDF6D4FixedGridShard150EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 150 k) := by
    simpa [suzukiDF6D4FixedGridShard150EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard150EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 150 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 150) := by
    rw [suzukiDF6D4FixedGridShard150EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 150)
  rw [suzukiDF6D4FixedGridShard150EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard150EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard150EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard150EvenDotSoundness i
            suzukiDF6D4FixedGridShard150EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard150EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard150OddComparison_eq_live :
    suzukiDF6D4FixedGridShard150OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 150 k) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard150OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 150 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard150OddCross_eq_live :
    suzukiDF6D4FixedGridShard150OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 150) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard150OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 150)) at h
  exact h

def suzukiDF6D4FixedGridShard150OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard150OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard150OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard150OddDotSoundness i.val
      suzukiDF6D4FixedGridShard150OddComparisonData)

theorem suzukiDF6D4FixedGridShard150OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard150OddSolveData =
      suzukiDF6D4FixedGridShard150OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard150Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard150OddSolveData =
    suzukiDF6D4FixedGridShard150OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard150OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard150OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 150 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 150 k) := by
    rw [suzukiDF6D4FixedGridShard150OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 150 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150OddDotSoundness i
          suzukiDF6D4FixedGridShard150OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 150 k) := by
    simpa [suzukiDF6D4FixedGridShard150OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard150OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 150 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 150) := by
    rw [suzukiDF6D4FixedGridShard150OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 150)
  rw [suzukiDF6D4FixedGridShard150OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard150OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard150OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard150OddDotSoundness i
            suzukiDF6D4FixedGridShard150OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard150OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard150EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard150EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 451) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard150EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 451)) at h
  exact h

theorem suzukiDF6D4FixedGridShard150EvenFull_eq_live :
    suzukiDF6D4FixedGridShard150EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 451) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard150EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 451)) at h
  exact h

def suzukiDF6D4FixedGridShard150EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard150EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard150EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard150EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard150EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard150EvenResidualData =
      suzukiDF6D4FixedGridShard150EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard150Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard150EvenResidualData =
    suzukiDF6D4FixedGridShard150EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard150EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard150EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 451 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 451) := by
    rw [suzukiDF6D4FixedGridShard150EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 451
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150EvenDotSoundness i
          suzukiDF6D4FixedGridShard150EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 451) := by
    simpa [suzukiDF6D4FixedGridShard150EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard150EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 451) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 451) := by
    rw [suzukiDF6D4FixedGridShard150EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 451
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard150EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard150EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard150EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard150EvenDotSoundness i
            suzukiDF6D4FixedGridShard150EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard150EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard150OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard150OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 451) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard150OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 451)) at h
  exact h

theorem suzukiDF6D4FixedGridShard150OddFull_eq_live :
    suzukiDF6D4FixedGridShard150OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 451) := by
  have h := suzukiDF6D4FixedGridShard150Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard150OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 451)) at h
  exact h

def suzukiDF6D4FixedGridShard150OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard150OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard150OddDotSoundness i.val
        suzukiDF6D4FixedGridShard150OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard150OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard150OddResidualData =
      suzukiDF6D4FixedGridShard150OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard150Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard150OddResidualData =
    suzukiDF6D4FixedGridShard150OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard150OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard150OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 451 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 451) := by
    rw [suzukiDF6D4FixedGridShard150OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 451
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150OddDotSoundness i
          suzukiDF6D4FixedGridShard150OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 451) := by
    simpa [suzukiDF6D4FixedGridShard150OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard150OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 451) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard150OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 451) := by
    rw [suzukiDF6D4FixedGridShard150OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 451
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard150OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard150OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard150OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard150OddDotSoundness i
            suzukiDF6D4FixedGridShard150OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard150OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
