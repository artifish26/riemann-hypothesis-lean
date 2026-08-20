import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard229Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard229Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard229EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard229EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 229 k) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard229EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 229 k)) at h
  exact h

def suzukiDF6D4FixedGridShard229EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard229EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard229EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard229EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard229EvenComparisonData)

theorem suzukiDF6D4FixedGridShard229EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard229EvenSolveData =
      suzukiDF6D4FixedGridShard229EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard229Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard229EvenSolveData =
    suzukiDF6D4FixedGridShard229EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard229EvenCross_eq_live :
    suzukiDF6D4FixedGridShard229EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 229) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard229EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 229)) at h
  exact h

theorem suzukiDF6D4FixedGridShard229EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard229EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 229 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 229 k) := by
    rw [suzukiDF6D4FixedGridShard229EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 229 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229EvenDotSoundness i
          suzukiDF6D4FixedGridShard229EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 229 k) := by
    simpa [suzukiDF6D4FixedGridShard229EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard229EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 229 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 229) := by
    rw [suzukiDF6D4FixedGridShard229EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 229)
  rw [suzukiDF6D4FixedGridShard229EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard229EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard229EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard229EvenDotSoundness i
            suzukiDF6D4FixedGridShard229EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard229EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard229OddComparison_eq_live :
    suzukiDF6D4FixedGridShard229OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 229 k) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard229OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 229 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard229OddCross_eq_live :
    suzukiDF6D4FixedGridShard229OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 229) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard229OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 229)) at h
  exact h

def suzukiDF6D4FixedGridShard229OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard229OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard229OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard229OddDotSoundness i.val
      suzukiDF6D4FixedGridShard229OddComparisonData)

theorem suzukiDF6D4FixedGridShard229OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard229OddSolveData =
      suzukiDF6D4FixedGridShard229OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard229Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard229OddSolveData =
    suzukiDF6D4FixedGridShard229OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard229OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard229OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 229 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 229 k) := by
    rw [suzukiDF6D4FixedGridShard229OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 229 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229OddDotSoundness i
          suzukiDF6D4FixedGridShard229OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 229 k) := by
    simpa [suzukiDF6D4FixedGridShard229OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard229OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 229 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 229) := by
    rw [suzukiDF6D4FixedGridShard229OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 229)
  rw [suzukiDF6D4FixedGridShard229OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard229OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard229OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard229OddDotSoundness i
            suzukiDF6D4FixedGridShard229OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard229OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard229EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard229EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 530) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard229EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 530)) at h
  exact h

theorem suzukiDF6D4FixedGridShard229EvenFull_eq_live :
    suzukiDF6D4FixedGridShard229EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 530) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard229EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 530)) at h
  exact h

def suzukiDF6D4FixedGridShard229EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard229EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard229EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard229EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard229EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard229EvenResidualData =
      suzukiDF6D4FixedGridShard229EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard229Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard229EvenResidualData =
    suzukiDF6D4FixedGridShard229EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard229EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard229EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 530 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 530) := by
    rw [suzukiDF6D4FixedGridShard229EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 530
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229EvenDotSoundness i
          suzukiDF6D4FixedGridShard229EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 530) := by
    simpa [suzukiDF6D4FixedGridShard229EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard229EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 530) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 530) := by
    rw [suzukiDF6D4FixedGridShard229EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 530
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard229EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard229EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard229EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard229EvenDotSoundness i
            suzukiDF6D4FixedGridShard229EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard229EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard229OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard229OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 530) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard229OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 530)) at h
  exact h

theorem suzukiDF6D4FixedGridShard229OddFull_eq_live :
    suzukiDF6D4FixedGridShard229OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 530) := by
  have h := suzukiDF6D4FixedGridShard229Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard229OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 530)) at h
  exact h

def suzukiDF6D4FixedGridShard229OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard229OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard229OddDotSoundness i.val
        suzukiDF6D4FixedGridShard229OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard229OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard229OddResidualData =
      suzukiDF6D4FixedGridShard229OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard229Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard229OddResidualData =
    suzukiDF6D4FixedGridShard229OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard229OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard229OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 530 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 530) := by
    rw [suzukiDF6D4FixedGridShard229OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 530
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229OddDotSoundness i
          suzukiDF6D4FixedGridShard229OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 530) := by
    simpa [suzukiDF6D4FixedGridShard229OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard229OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 530) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard229OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 530) := by
    rw [suzukiDF6D4FixedGridShard229OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 530
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard229OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard229OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard229OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard229OddDotSoundness i
            suzukiDF6D4FixedGridShard229OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard229OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
