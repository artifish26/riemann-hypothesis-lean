import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard082Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard082Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard082EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard082EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 82 k) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard082EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 82 k)) at h
  exact h

def suzukiDF6D4FixedGridShard082EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard082EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard082EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard082EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard082EvenComparisonData)

theorem suzukiDF6D4FixedGridShard082EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard082EvenSolveData =
      suzukiDF6D4FixedGridShard082EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard082Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard082EvenSolveData =
    suzukiDF6D4FixedGridShard082EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard082EvenCross_eq_live :
    suzukiDF6D4FixedGridShard082EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 82) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard082EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 82)) at h
  exact h

theorem suzukiDF6D4FixedGridShard082EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard082EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 82 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 82 k) := by
    rw [suzukiDF6D4FixedGridShard082EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 82 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082EvenDotSoundness i
          suzukiDF6D4FixedGridShard082EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 82 k) := by
    simpa [suzukiDF6D4FixedGridShard082EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard082EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 82 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 82) := by
    rw [suzukiDF6D4FixedGridShard082EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 82)
  rw [suzukiDF6D4FixedGridShard082EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard082EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard082EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard082EvenDotSoundness i
            suzukiDF6D4FixedGridShard082EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard082EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard082OddComparison_eq_live :
    suzukiDF6D4FixedGridShard082OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 82 k) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard082OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 82 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard082OddCross_eq_live :
    suzukiDF6D4FixedGridShard082OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 82) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard082OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 82)) at h
  exact h

def suzukiDF6D4FixedGridShard082OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard082OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard082OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard082OddDotSoundness i.val
      suzukiDF6D4FixedGridShard082OddComparisonData)

theorem suzukiDF6D4FixedGridShard082OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard082OddSolveData =
      suzukiDF6D4FixedGridShard082OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard082Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard082OddSolveData =
    suzukiDF6D4FixedGridShard082OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard082OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard082OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 82 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 82 k) := by
    rw [suzukiDF6D4FixedGridShard082OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 82 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082OddDotSoundness i
          suzukiDF6D4FixedGridShard082OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 82 k) := by
    simpa [suzukiDF6D4FixedGridShard082OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard082OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 82 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 82) := by
    rw [suzukiDF6D4FixedGridShard082OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 82)
  rw [suzukiDF6D4FixedGridShard082OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard082OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard082OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard082OddDotSoundness i
            suzukiDF6D4FixedGridShard082OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard082OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard082EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard082EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 383) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard082EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 383)) at h
  exact h

theorem suzukiDF6D4FixedGridShard082EvenFull_eq_live :
    suzukiDF6D4FixedGridShard082EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 383) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard082EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 383)) at h
  exact h

def suzukiDF6D4FixedGridShard082EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard082EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard082EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard082EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard082EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard082EvenResidualData =
      suzukiDF6D4FixedGridShard082EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard082Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard082EvenResidualData =
    suzukiDF6D4FixedGridShard082EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard082EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard082EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 383 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 383) := by
    rw [suzukiDF6D4FixedGridShard082EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 383
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082EvenDotSoundness i
          suzukiDF6D4FixedGridShard082EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 383) := by
    simpa [suzukiDF6D4FixedGridShard082EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard082EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 383) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 383) := by
    rw [suzukiDF6D4FixedGridShard082EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 383
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard082EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard082EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard082EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard082EvenDotSoundness i
            suzukiDF6D4FixedGridShard082EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard082EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard082OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard082OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 383) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard082OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 383)) at h
  exact h

theorem suzukiDF6D4FixedGridShard082OddFull_eq_live :
    suzukiDF6D4FixedGridShard082OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 383) := by
  have h := suzukiDF6D4FixedGridShard082Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard082OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 383)) at h
  exact h

def suzukiDF6D4FixedGridShard082OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard082OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard082OddDotSoundness i.val
        suzukiDF6D4FixedGridShard082OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard082OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard082OddResidualData =
      suzukiDF6D4FixedGridShard082OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard082Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard082OddResidualData =
    suzukiDF6D4FixedGridShard082OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard082OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard082OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 383 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 383) := by
    rw [suzukiDF6D4FixedGridShard082OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 383
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082OddDotSoundness i
          suzukiDF6D4FixedGridShard082OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 383) := by
    simpa [suzukiDF6D4FixedGridShard082OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard082OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 383) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard082OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 383) := by
    rw [suzukiDF6D4FixedGridShard082OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 383
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard082OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard082OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard082OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard082OddDotSoundness i
            suzukiDF6D4FixedGridShard082OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard082OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
