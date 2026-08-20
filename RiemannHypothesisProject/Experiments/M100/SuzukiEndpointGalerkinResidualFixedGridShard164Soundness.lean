import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard164Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard164Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard164EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard164EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 164 k) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard164EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 164 k)) at h
  exact h

def suzukiDF6D4FixedGridShard164EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard164EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard164EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard164EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard164EvenComparisonData)

theorem suzukiDF6D4FixedGridShard164EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard164EvenSolveData =
      suzukiDF6D4FixedGridShard164EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard164Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard164EvenSolveData =
    suzukiDF6D4FixedGridShard164EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard164EvenCross_eq_live :
    suzukiDF6D4FixedGridShard164EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 164) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard164EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 164)) at h
  exact h

theorem suzukiDF6D4FixedGridShard164EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard164EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 164 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 164 k) := by
    rw [suzukiDF6D4FixedGridShard164EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 164 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164EvenDotSoundness i
          suzukiDF6D4FixedGridShard164EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 164 k) := by
    simpa [suzukiDF6D4FixedGridShard164EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard164EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 164 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 164) := by
    rw [suzukiDF6D4FixedGridShard164EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 164)
  rw [suzukiDF6D4FixedGridShard164EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard164EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard164EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard164EvenDotSoundness i
            suzukiDF6D4FixedGridShard164EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard164EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard164OddComparison_eq_live :
    suzukiDF6D4FixedGridShard164OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 164 k) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard164OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 164 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard164OddCross_eq_live :
    suzukiDF6D4FixedGridShard164OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 164) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard164OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 164)) at h
  exact h

def suzukiDF6D4FixedGridShard164OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard164OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard164OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard164OddDotSoundness i.val
      suzukiDF6D4FixedGridShard164OddComparisonData)

theorem suzukiDF6D4FixedGridShard164OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard164OddSolveData =
      suzukiDF6D4FixedGridShard164OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard164Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard164OddSolveData =
    suzukiDF6D4FixedGridShard164OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard164OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard164OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 164 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 164 k) := by
    rw [suzukiDF6D4FixedGridShard164OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 164 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164OddDotSoundness i
          suzukiDF6D4FixedGridShard164OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 164 k) := by
    simpa [suzukiDF6D4FixedGridShard164OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard164OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 164 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 164) := by
    rw [suzukiDF6D4FixedGridShard164OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 164)
  rw [suzukiDF6D4FixedGridShard164OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard164OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard164OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard164OddDotSoundness i
            suzukiDF6D4FixedGridShard164OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard164OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard164EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard164EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 465) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard164EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 465)) at h
  exact h

theorem suzukiDF6D4FixedGridShard164EvenFull_eq_live :
    suzukiDF6D4FixedGridShard164EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 465) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard164EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 465)) at h
  exact h

def suzukiDF6D4FixedGridShard164EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard164EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard164EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard164EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard164EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard164EvenResidualData =
      suzukiDF6D4FixedGridShard164EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard164Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard164EvenResidualData =
    suzukiDF6D4FixedGridShard164EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard164EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard164EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 465 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 465) := by
    rw [suzukiDF6D4FixedGridShard164EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 465
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164EvenDotSoundness i
          suzukiDF6D4FixedGridShard164EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 465) := by
    simpa [suzukiDF6D4FixedGridShard164EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard164EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 465) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 465) := by
    rw [suzukiDF6D4FixedGridShard164EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 465
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard164EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard164EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard164EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard164EvenDotSoundness i
            suzukiDF6D4FixedGridShard164EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard164EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard164OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard164OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 465) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard164OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 465)) at h
  exact h

theorem suzukiDF6D4FixedGridShard164OddFull_eq_live :
    suzukiDF6D4FixedGridShard164OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 465) := by
  have h := suzukiDF6D4FixedGridShard164Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard164OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 465)) at h
  exact h

def suzukiDF6D4FixedGridShard164OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard164OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard164OddDotSoundness i.val
        suzukiDF6D4FixedGridShard164OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard164OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard164OddResidualData =
      suzukiDF6D4FixedGridShard164OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard164Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard164OddResidualData =
    suzukiDF6D4FixedGridShard164OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard164OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard164OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 465 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 465) := by
    rw [suzukiDF6D4FixedGridShard164OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 465
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164OddDotSoundness i
          suzukiDF6D4FixedGridShard164OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 465) := by
    simpa [suzukiDF6D4FixedGridShard164OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard164OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 465) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard164OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 465) := by
    rw [suzukiDF6D4FixedGridShard164OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 465
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard164OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard164OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard164OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard164OddDotSoundness i
            suzukiDF6D4FixedGridShard164OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard164OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
