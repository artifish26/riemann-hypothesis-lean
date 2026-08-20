import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard078Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard078Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard078EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard078EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 78 k) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard078EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 78 k)) at h
  exact h

def suzukiDF6D4FixedGridShard078EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard078EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard078EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard078EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard078EvenComparisonData)

theorem suzukiDF6D4FixedGridShard078EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard078EvenSolveData =
      suzukiDF6D4FixedGridShard078EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard078Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard078EvenSolveData =
    suzukiDF6D4FixedGridShard078EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard078EvenCross_eq_live :
    suzukiDF6D4FixedGridShard078EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 78) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard078EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 78)) at h
  exact h

theorem suzukiDF6D4FixedGridShard078EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard078EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 78 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 78 k) := by
    rw [suzukiDF6D4FixedGridShard078EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 78 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078EvenDotSoundness i
          suzukiDF6D4FixedGridShard078EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 78 k) := by
    simpa [suzukiDF6D4FixedGridShard078EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard078EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 78 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 78) := by
    rw [suzukiDF6D4FixedGridShard078EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 78)
  rw [suzukiDF6D4FixedGridShard078EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard078EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard078EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard078EvenDotSoundness i
            suzukiDF6D4FixedGridShard078EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard078EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard078OddComparison_eq_live :
    suzukiDF6D4FixedGridShard078OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 78 k) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard078OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 78 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard078OddCross_eq_live :
    suzukiDF6D4FixedGridShard078OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 78) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard078OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 78)) at h
  exact h

def suzukiDF6D4FixedGridShard078OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard078OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard078OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard078OddDotSoundness i.val
      suzukiDF6D4FixedGridShard078OddComparisonData)

theorem suzukiDF6D4FixedGridShard078OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard078OddSolveData =
      suzukiDF6D4FixedGridShard078OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard078Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard078OddSolveData =
    suzukiDF6D4FixedGridShard078OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard078OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard078OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 78 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 78 k) := by
    rw [suzukiDF6D4FixedGridShard078OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 78 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078OddDotSoundness i
          suzukiDF6D4FixedGridShard078OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 78 k) := by
    simpa [suzukiDF6D4FixedGridShard078OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard078OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 78 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 78) := by
    rw [suzukiDF6D4FixedGridShard078OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 78)
  rw [suzukiDF6D4FixedGridShard078OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard078OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard078OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard078OddDotSoundness i
            suzukiDF6D4FixedGridShard078OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard078OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard078EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard078EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 379) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard078EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 379)) at h
  exact h

theorem suzukiDF6D4FixedGridShard078EvenFull_eq_live :
    suzukiDF6D4FixedGridShard078EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 379) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard078EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 379)) at h
  exact h

def suzukiDF6D4FixedGridShard078EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard078EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard078EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard078EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard078EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard078EvenResidualData =
      suzukiDF6D4FixedGridShard078EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard078Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard078EvenResidualData =
    suzukiDF6D4FixedGridShard078EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard078EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard078EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 379 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 379) := by
    rw [suzukiDF6D4FixedGridShard078EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 379
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078EvenDotSoundness i
          suzukiDF6D4FixedGridShard078EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 379) := by
    simpa [suzukiDF6D4FixedGridShard078EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard078EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 379) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 379) := by
    rw [suzukiDF6D4FixedGridShard078EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 379
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard078EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard078EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard078EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard078EvenDotSoundness i
            suzukiDF6D4FixedGridShard078EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard078EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard078OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard078OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 379) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard078OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 379)) at h
  exact h

theorem suzukiDF6D4FixedGridShard078OddFull_eq_live :
    suzukiDF6D4FixedGridShard078OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 379) := by
  have h := suzukiDF6D4FixedGridShard078Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard078OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 379)) at h
  exact h

def suzukiDF6D4FixedGridShard078OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard078OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard078OddDotSoundness i.val
        suzukiDF6D4FixedGridShard078OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard078OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard078OddResidualData =
      suzukiDF6D4FixedGridShard078OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard078Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard078OddResidualData =
    suzukiDF6D4FixedGridShard078OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard078OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard078OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 379 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 379) := by
    rw [suzukiDF6D4FixedGridShard078OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 379
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078OddDotSoundness i
          suzukiDF6D4FixedGridShard078OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 379) := by
    simpa [suzukiDF6D4FixedGridShard078OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard078OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 379) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard078OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 379) := by
    rw [suzukiDF6D4FixedGridShard078OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 379
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard078OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard078OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard078OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard078OddDotSoundness i
            suzukiDF6D4FixedGridShard078OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard078OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
