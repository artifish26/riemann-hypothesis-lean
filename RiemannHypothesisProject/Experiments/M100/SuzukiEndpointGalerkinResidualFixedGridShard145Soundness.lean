import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard145Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard145Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard145EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard145EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 145 k) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard145EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 145 k)) at h
  exact h

def suzukiDF6D4FixedGridShard145EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard145EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard145EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard145EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard145EvenComparisonData)

theorem suzukiDF6D4FixedGridShard145EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard145EvenSolveData =
      suzukiDF6D4FixedGridShard145EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard145Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard145EvenSolveData =
    suzukiDF6D4FixedGridShard145EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard145EvenCross_eq_live :
    suzukiDF6D4FixedGridShard145EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 145) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard145EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 145)) at h
  exact h

theorem suzukiDF6D4FixedGridShard145EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard145EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 145 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 145 k) := by
    rw [suzukiDF6D4FixedGridShard145EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 145 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145EvenDotSoundness i
          suzukiDF6D4FixedGridShard145EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 145 k) := by
    simpa [suzukiDF6D4FixedGridShard145EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard145EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 145 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 145) := by
    rw [suzukiDF6D4FixedGridShard145EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 145)
  rw [suzukiDF6D4FixedGridShard145EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard145EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard145EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard145EvenDotSoundness i
            suzukiDF6D4FixedGridShard145EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard145EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard145OddComparison_eq_live :
    suzukiDF6D4FixedGridShard145OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 145 k) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard145OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 145 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard145OddCross_eq_live :
    suzukiDF6D4FixedGridShard145OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 145) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard145OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 145)) at h
  exact h

def suzukiDF6D4FixedGridShard145OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard145OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard145OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard145OddDotSoundness i.val
      suzukiDF6D4FixedGridShard145OddComparisonData)

theorem suzukiDF6D4FixedGridShard145OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard145OddSolveData =
      suzukiDF6D4FixedGridShard145OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard145Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard145OddSolveData =
    suzukiDF6D4FixedGridShard145OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard145OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard145OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 145 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 145 k) := by
    rw [suzukiDF6D4FixedGridShard145OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 145 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145OddDotSoundness i
          suzukiDF6D4FixedGridShard145OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 145 k) := by
    simpa [suzukiDF6D4FixedGridShard145OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard145OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 145 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 145) := by
    rw [suzukiDF6D4FixedGridShard145OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 145)
  rw [suzukiDF6D4FixedGridShard145OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard145OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard145OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard145OddDotSoundness i
            suzukiDF6D4FixedGridShard145OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard145OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard145EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard145EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 446) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard145EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 446)) at h
  exact h

theorem suzukiDF6D4FixedGridShard145EvenFull_eq_live :
    suzukiDF6D4FixedGridShard145EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 446) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard145EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 446)) at h
  exact h

def suzukiDF6D4FixedGridShard145EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard145EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard145EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard145EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard145EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard145EvenResidualData =
      suzukiDF6D4FixedGridShard145EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard145Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard145EvenResidualData =
    suzukiDF6D4FixedGridShard145EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard145EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard145EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 446 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 446) := by
    rw [suzukiDF6D4FixedGridShard145EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 446
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145EvenDotSoundness i
          suzukiDF6D4FixedGridShard145EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 446) := by
    simpa [suzukiDF6D4FixedGridShard145EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard145EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 446) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 446) := by
    rw [suzukiDF6D4FixedGridShard145EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 446
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard145EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard145EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard145EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard145EvenDotSoundness i
            suzukiDF6D4FixedGridShard145EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard145EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard145OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard145OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 446) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard145OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 446)) at h
  exact h

theorem suzukiDF6D4FixedGridShard145OddFull_eq_live :
    suzukiDF6D4FixedGridShard145OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 446) := by
  have h := suzukiDF6D4FixedGridShard145Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard145OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 446)) at h
  exact h

def suzukiDF6D4FixedGridShard145OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard145OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard145OddDotSoundness i.val
        suzukiDF6D4FixedGridShard145OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard145OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard145OddResidualData =
      suzukiDF6D4FixedGridShard145OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard145Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard145OddResidualData =
    suzukiDF6D4FixedGridShard145OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard145OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard145OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 446 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 446) := by
    rw [suzukiDF6D4FixedGridShard145OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 446
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145OddDotSoundness i
          suzukiDF6D4FixedGridShard145OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 446) := by
    simpa [suzukiDF6D4FixedGridShard145OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard145OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 446) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard145OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 446) := by
    rw [suzukiDF6D4FixedGridShard145OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 446
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard145OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard145OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard145OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard145OddDotSoundness i
            suzukiDF6D4FixedGridShard145OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard145OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
