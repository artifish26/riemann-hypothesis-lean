import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard044Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard044Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard044EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard044EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 44 k) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard044EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 44 k)) at h
  exact h

def suzukiDF6D4FixedGridShard044EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard044EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard044EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard044EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard044EvenComparisonData)

theorem suzukiDF6D4FixedGridShard044EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard044EvenSolveData =
      suzukiDF6D4FixedGridShard044EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard044Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard044EvenSolveData =
    suzukiDF6D4FixedGridShard044EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard044EvenCross_eq_live :
    suzukiDF6D4FixedGridShard044EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 44) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard044EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 44)) at h
  exact h

theorem suzukiDF6D4FixedGridShard044EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard044EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 44 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 44 k) := by
    rw [suzukiDF6D4FixedGridShard044EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 44 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044EvenDotSoundness i
          suzukiDF6D4FixedGridShard044EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 44 k) := by
    simpa [suzukiDF6D4FixedGridShard044EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard044EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 44 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 44) := by
    rw [suzukiDF6D4FixedGridShard044EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 44)
  rw [suzukiDF6D4FixedGridShard044EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard044EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard044EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard044EvenDotSoundness i
            suzukiDF6D4FixedGridShard044EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard044EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard044OddComparison_eq_live :
    suzukiDF6D4FixedGridShard044OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 44 k) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard044OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 44 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard044OddCross_eq_live :
    suzukiDF6D4FixedGridShard044OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 44) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard044OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 44)) at h
  exact h

def suzukiDF6D4FixedGridShard044OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard044OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard044OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard044OddDotSoundness i.val
      suzukiDF6D4FixedGridShard044OddComparisonData)

theorem suzukiDF6D4FixedGridShard044OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard044OddSolveData =
      suzukiDF6D4FixedGridShard044OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard044Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard044OddSolveData =
    suzukiDF6D4FixedGridShard044OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard044OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard044OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 44 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 44 k) := by
    rw [suzukiDF6D4FixedGridShard044OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 44 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044OddDotSoundness i
          suzukiDF6D4FixedGridShard044OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 44 k) := by
    simpa [suzukiDF6D4FixedGridShard044OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard044OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 44 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 44) := by
    rw [suzukiDF6D4FixedGridShard044OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 44)
  rw [suzukiDF6D4FixedGridShard044OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard044OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard044OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard044OddDotSoundness i
            suzukiDF6D4FixedGridShard044OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard044OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard044EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard044EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 345) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard044EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 345)) at h
  exact h

theorem suzukiDF6D4FixedGridShard044EvenFull_eq_live :
    suzukiDF6D4FixedGridShard044EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 345) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard044EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 345)) at h
  exact h

def suzukiDF6D4FixedGridShard044EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard044EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard044EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard044EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard044EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard044EvenResidualData =
      suzukiDF6D4FixedGridShard044EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard044Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard044EvenResidualData =
    suzukiDF6D4FixedGridShard044EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard044EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard044EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 345 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 345) := by
    rw [suzukiDF6D4FixedGridShard044EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 345
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044EvenDotSoundness i
          suzukiDF6D4FixedGridShard044EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 345) := by
    simpa [suzukiDF6D4FixedGridShard044EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard044EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 345) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 345) := by
    rw [suzukiDF6D4FixedGridShard044EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 345
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard044EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard044EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard044EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard044EvenDotSoundness i
            suzukiDF6D4FixedGridShard044EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard044EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard044OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard044OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 345) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard044OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 345)) at h
  exact h

theorem suzukiDF6D4FixedGridShard044OddFull_eq_live :
    suzukiDF6D4FixedGridShard044OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 345) := by
  have h := suzukiDF6D4FixedGridShard044Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard044OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 345)) at h
  exact h

def suzukiDF6D4FixedGridShard044OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard044OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard044OddDotSoundness i.val
        suzukiDF6D4FixedGridShard044OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard044OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard044OddResidualData =
      suzukiDF6D4FixedGridShard044OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard044Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard044OddResidualData =
    suzukiDF6D4FixedGridShard044OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard044OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard044OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 345 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 345) := by
    rw [suzukiDF6D4FixedGridShard044OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 345
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044OddDotSoundness i
          suzukiDF6D4FixedGridShard044OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 345) := by
    simpa [suzukiDF6D4FixedGridShard044OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard044OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 345) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard044OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 345) := by
    rw [suzukiDF6D4FixedGridShard044OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 345
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard044OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard044OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard044OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard044OddDotSoundness i
            suzukiDF6D4FixedGridShard044OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard044OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
