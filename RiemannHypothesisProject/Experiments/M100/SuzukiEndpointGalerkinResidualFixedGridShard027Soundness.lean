import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard027Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard027Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard027EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard027EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 27 k) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard027EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 27 k)) at h
  exact h

def suzukiDF6D4FixedGridShard027EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard027EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard027EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard027EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard027EvenComparisonData)

theorem suzukiDF6D4FixedGridShard027EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard027EvenSolveData =
      suzukiDF6D4FixedGridShard027EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard027Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard027EvenSolveData =
    suzukiDF6D4FixedGridShard027EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard027EvenCross_eq_live :
    suzukiDF6D4FixedGridShard027EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 27) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard027EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 27)) at h
  exact h

theorem suzukiDF6D4FixedGridShard027EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard027EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 27 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 27 k) := by
    rw [suzukiDF6D4FixedGridShard027EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 27 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027EvenDotSoundness i
          suzukiDF6D4FixedGridShard027EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 27 k) := by
    simpa [suzukiDF6D4FixedGridShard027EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard027EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 27 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 27) := by
    rw [suzukiDF6D4FixedGridShard027EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 27)
  rw [suzukiDF6D4FixedGridShard027EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard027EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard027EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard027EvenDotSoundness i
            suzukiDF6D4FixedGridShard027EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard027EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard027OddComparison_eq_live :
    suzukiDF6D4FixedGridShard027OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 27 k) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard027OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 27 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard027OddCross_eq_live :
    suzukiDF6D4FixedGridShard027OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 27) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard027OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 27)) at h
  exact h

def suzukiDF6D4FixedGridShard027OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard027OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard027OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard027OddDotSoundness i.val
      suzukiDF6D4FixedGridShard027OddComparisonData)

theorem suzukiDF6D4FixedGridShard027OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard027OddSolveData =
      suzukiDF6D4FixedGridShard027OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard027Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard027OddSolveData =
    suzukiDF6D4FixedGridShard027OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard027OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard027OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 27 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 27 k) := by
    rw [suzukiDF6D4FixedGridShard027OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 27 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027OddDotSoundness i
          suzukiDF6D4FixedGridShard027OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 27 k) := by
    simpa [suzukiDF6D4FixedGridShard027OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard027OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 27 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 27) := by
    rw [suzukiDF6D4FixedGridShard027OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 27)
  rw [suzukiDF6D4FixedGridShard027OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard027OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard027OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard027OddDotSoundness i
            suzukiDF6D4FixedGridShard027OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard027OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard027EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard027EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 328) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard027EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 328)) at h
  exact h

theorem suzukiDF6D4FixedGridShard027EvenFull_eq_live :
    suzukiDF6D4FixedGridShard027EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 328) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard027EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 328)) at h
  exact h

def suzukiDF6D4FixedGridShard027EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard027EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard027EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard027EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard027EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard027EvenResidualData =
      suzukiDF6D4FixedGridShard027EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard027Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard027EvenResidualData =
    suzukiDF6D4FixedGridShard027EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard027EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard027EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 328 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 328) := by
    rw [suzukiDF6D4FixedGridShard027EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 328
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027EvenDotSoundness i
          suzukiDF6D4FixedGridShard027EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 328) := by
    simpa [suzukiDF6D4FixedGridShard027EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard027EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 328) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 328) := by
    rw [suzukiDF6D4FixedGridShard027EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 328
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard027EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard027EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard027EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard027EvenDotSoundness i
            suzukiDF6D4FixedGridShard027EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard027EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard027OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard027OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 328) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard027OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 328)) at h
  exact h

theorem suzukiDF6D4FixedGridShard027OddFull_eq_live :
    suzukiDF6D4FixedGridShard027OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 328) := by
  have h := suzukiDF6D4FixedGridShard027Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard027OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 328)) at h
  exact h

def suzukiDF6D4FixedGridShard027OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard027OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard027OddDotSoundness i.val
        suzukiDF6D4FixedGridShard027OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard027OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard027OddResidualData =
      suzukiDF6D4FixedGridShard027OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard027Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard027OddResidualData =
    suzukiDF6D4FixedGridShard027OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard027OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard027OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 328 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 328) := by
    rw [suzukiDF6D4FixedGridShard027OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 328
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027OddDotSoundness i
          suzukiDF6D4FixedGridShard027OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 328) := by
    simpa [suzukiDF6D4FixedGridShard027OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard027OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 328) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard027OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 328) := by
    rw [suzukiDF6D4FixedGridShard027OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 328
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard027OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard027OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard027OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard027OddDotSoundness i
            suzukiDF6D4FixedGridShard027OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard027OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
