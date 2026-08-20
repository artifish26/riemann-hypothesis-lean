import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard198Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard198Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard198EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard198EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 198 k) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard198EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 198 k)) at h
  exact h

def suzukiDF6D4FixedGridShard198EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard198EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard198EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard198EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard198EvenComparisonData)

theorem suzukiDF6D4FixedGridShard198EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard198EvenSolveData =
      suzukiDF6D4FixedGridShard198EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard198Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard198EvenSolveData =
    suzukiDF6D4FixedGridShard198EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard198EvenCross_eq_live :
    suzukiDF6D4FixedGridShard198EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 198) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard198EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 198)) at h
  exact h

theorem suzukiDF6D4FixedGridShard198EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard198EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 198 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 198 k) := by
    rw [suzukiDF6D4FixedGridShard198EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 198 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198EvenDotSoundness i
          suzukiDF6D4FixedGridShard198EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 198 k) := by
    simpa [suzukiDF6D4FixedGridShard198EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard198EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 198 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 198) := by
    rw [suzukiDF6D4FixedGridShard198EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 198)
  rw [suzukiDF6D4FixedGridShard198EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard198EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard198EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard198EvenDotSoundness i
            suzukiDF6D4FixedGridShard198EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard198EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard198OddComparison_eq_live :
    suzukiDF6D4FixedGridShard198OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 198 k) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard198OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 198 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard198OddCross_eq_live :
    suzukiDF6D4FixedGridShard198OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 198) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard198OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 198)) at h
  exact h

def suzukiDF6D4FixedGridShard198OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard198OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard198OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard198OddDotSoundness i.val
      suzukiDF6D4FixedGridShard198OddComparisonData)

theorem suzukiDF6D4FixedGridShard198OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard198OddSolveData =
      suzukiDF6D4FixedGridShard198OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard198Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard198OddSolveData =
    suzukiDF6D4FixedGridShard198OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard198OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard198OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 198 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 198 k) := by
    rw [suzukiDF6D4FixedGridShard198OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 198 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198OddDotSoundness i
          suzukiDF6D4FixedGridShard198OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 198 k) := by
    simpa [suzukiDF6D4FixedGridShard198OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard198OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 198 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 198) := by
    rw [suzukiDF6D4FixedGridShard198OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 198)
  rw [suzukiDF6D4FixedGridShard198OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard198OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard198OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard198OddDotSoundness i
            suzukiDF6D4FixedGridShard198OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard198OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard198EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard198EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 499) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard198EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 499)) at h
  exact h

theorem suzukiDF6D4FixedGridShard198EvenFull_eq_live :
    suzukiDF6D4FixedGridShard198EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 499) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard198EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 499)) at h
  exact h

def suzukiDF6D4FixedGridShard198EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard198EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard198EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard198EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard198EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard198EvenResidualData =
      suzukiDF6D4FixedGridShard198EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard198Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard198EvenResidualData =
    suzukiDF6D4FixedGridShard198EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard198EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard198EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 499 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 499) := by
    rw [suzukiDF6D4FixedGridShard198EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 499
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198EvenDotSoundness i
          suzukiDF6D4FixedGridShard198EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 499) := by
    simpa [suzukiDF6D4FixedGridShard198EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard198EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 499) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 499) := by
    rw [suzukiDF6D4FixedGridShard198EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 499
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard198EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard198EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard198EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard198EvenDotSoundness i
            suzukiDF6D4FixedGridShard198EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard198EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard198OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard198OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 499) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard198OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 499)) at h
  exact h

theorem suzukiDF6D4FixedGridShard198OddFull_eq_live :
    suzukiDF6D4FixedGridShard198OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 499) := by
  have h := suzukiDF6D4FixedGridShard198Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard198OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 499)) at h
  exact h

def suzukiDF6D4FixedGridShard198OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard198OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard198OddDotSoundness i.val
        suzukiDF6D4FixedGridShard198OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard198OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard198OddResidualData =
      suzukiDF6D4FixedGridShard198OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard198Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard198OddResidualData =
    suzukiDF6D4FixedGridShard198OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard198OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard198OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 499 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 499) := by
    rw [suzukiDF6D4FixedGridShard198OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 499
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198OddDotSoundness i
          suzukiDF6D4FixedGridShard198OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 499) := by
    simpa [suzukiDF6D4FixedGridShard198OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard198OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 499) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard198OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 499) := by
    rw [suzukiDF6D4FixedGridShard198OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 499
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard198OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard198OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard198OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard198OddDotSoundness i
            suzukiDF6D4FixedGridShard198OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard198OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
