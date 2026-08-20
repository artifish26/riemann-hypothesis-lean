import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard138Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard138Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard138EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard138EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 138 k) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard138EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 138 k)) at h
  exact h

def suzukiDF6D4FixedGridShard138EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard138EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard138EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard138EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard138EvenComparisonData)

theorem suzukiDF6D4FixedGridShard138EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard138EvenSolveData =
      suzukiDF6D4FixedGridShard138EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard138Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard138EvenSolveData =
    suzukiDF6D4FixedGridShard138EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard138EvenCross_eq_live :
    suzukiDF6D4FixedGridShard138EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 138) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard138EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 138)) at h
  exact h

theorem suzukiDF6D4FixedGridShard138EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard138EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 138 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 138 k) := by
    rw [suzukiDF6D4FixedGridShard138EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 138 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138EvenDotSoundness i
          suzukiDF6D4FixedGridShard138EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 138 k) := by
    simpa [suzukiDF6D4FixedGridShard138EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard138EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 138 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 138) := by
    rw [suzukiDF6D4FixedGridShard138EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 138)
  rw [suzukiDF6D4FixedGridShard138EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard138EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard138EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard138EvenDotSoundness i
            suzukiDF6D4FixedGridShard138EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard138EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard138OddComparison_eq_live :
    suzukiDF6D4FixedGridShard138OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 138 k) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard138OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 138 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard138OddCross_eq_live :
    suzukiDF6D4FixedGridShard138OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 138) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard138OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 138)) at h
  exact h

def suzukiDF6D4FixedGridShard138OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard138OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard138OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard138OddDotSoundness i.val
      suzukiDF6D4FixedGridShard138OddComparisonData)

theorem suzukiDF6D4FixedGridShard138OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard138OddSolveData =
      suzukiDF6D4FixedGridShard138OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard138Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard138OddSolveData =
    suzukiDF6D4FixedGridShard138OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard138OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard138OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 138 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 138 k) := by
    rw [suzukiDF6D4FixedGridShard138OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 138 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138OddDotSoundness i
          suzukiDF6D4FixedGridShard138OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 138 k) := by
    simpa [suzukiDF6D4FixedGridShard138OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard138OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 138 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 138) := by
    rw [suzukiDF6D4FixedGridShard138OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 138)
  rw [suzukiDF6D4FixedGridShard138OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard138OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard138OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard138OddDotSoundness i
            suzukiDF6D4FixedGridShard138OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard138OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard138EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard138EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 439) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard138EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 439)) at h
  exact h

theorem suzukiDF6D4FixedGridShard138EvenFull_eq_live :
    suzukiDF6D4FixedGridShard138EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 439) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard138EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 439)) at h
  exact h

def suzukiDF6D4FixedGridShard138EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard138EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard138EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard138EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard138EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard138EvenResidualData =
      suzukiDF6D4FixedGridShard138EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard138Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard138EvenResidualData =
    suzukiDF6D4FixedGridShard138EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard138EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard138EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 439 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 439) := by
    rw [suzukiDF6D4FixedGridShard138EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 439
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138EvenDotSoundness i
          suzukiDF6D4FixedGridShard138EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 439) := by
    simpa [suzukiDF6D4FixedGridShard138EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard138EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 439) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 439) := by
    rw [suzukiDF6D4FixedGridShard138EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 439
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard138EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard138EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard138EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard138EvenDotSoundness i
            suzukiDF6D4FixedGridShard138EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard138EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard138OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard138OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 439) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard138OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 439)) at h
  exact h

theorem suzukiDF6D4FixedGridShard138OddFull_eq_live :
    suzukiDF6D4FixedGridShard138OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 439) := by
  have h := suzukiDF6D4FixedGridShard138Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard138OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 439)) at h
  exact h

def suzukiDF6D4FixedGridShard138OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard138OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard138OddDotSoundness i.val
        suzukiDF6D4FixedGridShard138OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard138OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard138OddResidualData =
      suzukiDF6D4FixedGridShard138OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard138Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard138OddResidualData =
    suzukiDF6D4FixedGridShard138OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard138OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard138OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 439 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 439) := by
    rw [suzukiDF6D4FixedGridShard138OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 439
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138OddDotSoundness i
          suzukiDF6D4FixedGridShard138OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 439) := by
    simpa [suzukiDF6D4FixedGridShard138OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard138OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 439) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard138OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 439) := by
    rw [suzukiDF6D4FixedGridShard138OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 439
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard138OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard138OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard138OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard138OddDotSoundness i
            suzukiDF6D4FixedGridShard138OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard138OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
