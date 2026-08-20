import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard063Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard063Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard063EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard063EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 63 k) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard063EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 63 k)) at h
  exact h

def suzukiDF6D4FixedGridShard063EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard063EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard063EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard063EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard063EvenComparisonData)

theorem suzukiDF6D4FixedGridShard063EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard063EvenSolveData =
      suzukiDF6D4FixedGridShard063EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard063Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard063EvenSolveData =
    suzukiDF6D4FixedGridShard063EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard063EvenCross_eq_live :
    suzukiDF6D4FixedGridShard063EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 63) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard063EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 63)) at h
  exact h

theorem suzukiDF6D4FixedGridShard063EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard063EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 63 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 63 k) := by
    rw [suzukiDF6D4FixedGridShard063EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 63 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063EvenDotSoundness i
          suzukiDF6D4FixedGridShard063EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 63 k) := by
    simpa [suzukiDF6D4FixedGridShard063EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard063EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 63 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 63) := by
    rw [suzukiDF6D4FixedGridShard063EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 63)
  rw [suzukiDF6D4FixedGridShard063EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard063EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard063EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard063EvenDotSoundness i
            suzukiDF6D4FixedGridShard063EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard063EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard063OddComparison_eq_live :
    suzukiDF6D4FixedGridShard063OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 63 k) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard063OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 63 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard063OddCross_eq_live :
    suzukiDF6D4FixedGridShard063OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 63) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard063OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 63)) at h
  exact h

def suzukiDF6D4FixedGridShard063OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard063OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard063OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard063OddDotSoundness i.val
      suzukiDF6D4FixedGridShard063OddComparisonData)

theorem suzukiDF6D4FixedGridShard063OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard063OddSolveData =
      suzukiDF6D4FixedGridShard063OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard063Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard063OddSolveData =
    suzukiDF6D4FixedGridShard063OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard063OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard063OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 63 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 63 k) := by
    rw [suzukiDF6D4FixedGridShard063OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 63 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063OddDotSoundness i
          suzukiDF6D4FixedGridShard063OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 63 k) := by
    simpa [suzukiDF6D4FixedGridShard063OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard063OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 63 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 63) := by
    rw [suzukiDF6D4FixedGridShard063OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 63)
  rw [suzukiDF6D4FixedGridShard063OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard063OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard063OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard063OddDotSoundness i
            suzukiDF6D4FixedGridShard063OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard063OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard063EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard063EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 364) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard063EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 364)) at h
  exact h

theorem suzukiDF6D4FixedGridShard063EvenFull_eq_live :
    suzukiDF6D4FixedGridShard063EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 364) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard063EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 364)) at h
  exact h

def suzukiDF6D4FixedGridShard063EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard063EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard063EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard063EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard063EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard063EvenResidualData =
      suzukiDF6D4FixedGridShard063EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard063Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard063EvenResidualData =
    suzukiDF6D4FixedGridShard063EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard063EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard063EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 364 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 364) := by
    rw [suzukiDF6D4FixedGridShard063EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 364
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063EvenDotSoundness i
          suzukiDF6D4FixedGridShard063EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 364) := by
    simpa [suzukiDF6D4FixedGridShard063EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard063EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 364) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 364) := by
    rw [suzukiDF6D4FixedGridShard063EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 364
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard063EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard063EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard063EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard063EvenDotSoundness i
            suzukiDF6D4FixedGridShard063EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard063EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard063OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard063OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 364) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard063OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 364)) at h
  exact h

theorem suzukiDF6D4FixedGridShard063OddFull_eq_live :
    suzukiDF6D4FixedGridShard063OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 364) := by
  have h := suzukiDF6D4FixedGridShard063Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard063OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 364)) at h
  exact h

def suzukiDF6D4FixedGridShard063OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard063OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard063OddDotSoundness i.val
        suzukiDF6D4FixedGridShard063OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard063OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard063OddResidualData =
      suzukiDF6D4FixedGridShard063OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard063Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard063OddResidualData =
    suzukiDF6D4FixedGridShard063OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard063OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard063OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 364 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 364) := by
    rw [suzukiDF6D4FixedGridShard063OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 364
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063OddDotSoundness i
          suzukiDF6D4FixedGridShard063OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 364) := by
    simpa [suzukiDF6D4FixedGridShard063OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard063OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 364) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard063OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 364) := by
    rw [suzukiDF6D4FixedGridShard063OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 364
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard063OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard063OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard063OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard063OddDotSoundness i
            suzukiDF6D4FixedGridShard063OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard063OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
