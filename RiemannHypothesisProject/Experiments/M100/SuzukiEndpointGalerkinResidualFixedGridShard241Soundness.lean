import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard241Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard241Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard241EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard241EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 241 k) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard241EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 241 k)) at h
  exact h

def suzukiDF6D4FixedGridShard241EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard241EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard241EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard241EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard241EvenComparisonData)

theorem suzukiDF6D4FixedGridShard241EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard241EvenSolveData =
      suzukiDF6D4FixedGridShard241EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard241Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard241EvenSolveData =
    suzukiDF6D4FixedGridShard241EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard241EvenCross_eq_live :
    suzukiDF6D4FixedGridShard241EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 241) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard241EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 241)) at h
  exact h

theorem suzukiDF6D4FixedGridShard241EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard241EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 241 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 241 k) := by
    rw [suzukiDF6D4FixedGridShard241EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 241 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241EvenDotSoundness i
          suzukiDF6D4FixedGridShard241EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 241 k) := by
    simpa [suzukiDF6D4FixedGridShard241EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard241EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 241 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 241) := by
    rw [suzukiDF6D4FixedGridShard241EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 241)
  rw [suzukiDF6D4FixedGridShard241EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard241EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard241EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard241EvenDotSoundness i
            suzukiDF6D4FixedGridShard241EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard241EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard241OddComparison_eq_live :
    suzukiDF6D4FixedGridShard241OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 241 k) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard241OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 241 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard241OddCross_eq_live :
    suzukiDF6D4FixedGridShard241OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 241) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard241OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 241)) at h
  exact h

def suzukiDF6D4FixedGridShard241OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard241OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard241OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard241OddDotSoundness i.val
      suzukiDF6D4FixedGridShard241OddComparisonData)

theorem suzukiDF6D4FixedGridShard241OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard241OddSolveData =
      suzukiDF6D4FixedGridShard241OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard241Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard241OddSolveData =
    suzukiDF6D4FixedGridShard241OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard241OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard241OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 241 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 241 k) := by
    rw [suzukiDF6D4FixedGridShard241OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 241 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241OddDotSoundness i
          suzukiDF6D4FixedGridShard241OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 241 k) := by
    simpa [suzukiDF6D4FixedGridShard241OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard241OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 241 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 241) := by
    rw [suzukiDF6D4FixedGridShard241OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 241)
  rw [suzukiDF6D4FixedGridShard241OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard241OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard241OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard241OddDotSoundness i
            suzukiDF6D4FixedGridShard241OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard241OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard241EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard241EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 542) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard241EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 542)) at h
  exact h

theorem suzukiDF6D4FixedGridShard241EvenFull_eq_live :
    suzukiDF6D4FixedGridShard241EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 542) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard241EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 542)) at h
  exact h

def suzukiDF6D4FixedGridShard241EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard241EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard241EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard241EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard241EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard241EvenResidualData =
      suzukiDF6D4FixedGridShard241EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard241Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard241EvenResidualData =
    suzukiDF6D4FixedGridShard241EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard241EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard241EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 542 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 542) := by
    rw [suzukiDF6D4FixedGridShard241EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 542
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241EvenDotSoundness i
          suzukiDF6D4FixedGridShard241EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 542) := by
    simpa [suzukiDF6D4FixedGridShard241EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard241EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 542) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 542) := by
    rw [suzukiDF6D4FixedGridShard241EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 542
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard241EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard241EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard241EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard241EvenDotSoundness i
            suzukiDF6D4FixedGridShard241EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard241EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard241OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard241OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 542) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard241OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 542)) at h
  exact h

theorem suzukiDF6D4FixedGridShard241OddFull_eq_live :
    suzukiDF6D4FixedGridShard241OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 542) := by
  have h := suzukiDF6D4FixedGridShard241Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard241OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 542)) at h
  exact h

def suzukiDF6D4FixedGridShard241OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard241OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard241OddDotSoundness i.val
        suzukiDF6D4FixedGridShard241OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard241OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard241OddResidualData =
      suzukiDF6D4FixedGridShard241OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard241Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard241OddResidualData =
    suzukiDF6D4FixedGridShard241OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard241OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard241OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 542 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 542) := by
    rw [suzukiDF6D4FixedGridShard241OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 542
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241OddDotSoundness i
          suzukiDF6D4FixedGridShard241OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 542) := by
    simpa [suzukiDF6D4FixedGridShard241OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard241OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 542) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard241OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 542) := by
    rw [suzukiDF6D4FixedGridShard241OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 542
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard241OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard241OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard241OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard241OddDotSoundness i
            suzukiDF6D4FixedGridShard241OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard241OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
