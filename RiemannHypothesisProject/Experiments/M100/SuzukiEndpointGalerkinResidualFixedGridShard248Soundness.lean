import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard248Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard248Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard248EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard248EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 248 k) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard248EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 248 k)) at h
  exact h

def suzukiDF6D4FixedGridShard248EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard248EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard248EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard248EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard248EvenComparisonData)

theorem suzukiDF6D4FixedGridShard248EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard248EvenSolveData =
      suzukiDF6D4FixedGridShard248EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard248Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard248EvenSolveData =
    suzukiDF6D4FixedGridShard248EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard248EvenCross_eq_live :
    suzukiDF6D4FixedGridShard248EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 248) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard248EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 248)) at h
  exact h

theorem suzukiDF6D4FixedGridShard248EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard248EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 248 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 248 k) := by
    rw [suzukiDF6D4FixedGridShard248EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 248 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248EvenDotSoundness i
          suzukiDF6D4FixedGridShard248EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 248 k) := by
    simpa [suzukiDF6D4FixedGridShard248EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard248EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 248 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 248) := by
    rw [suzukiDF6D4FixedGridShard248EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 248)
  rw [suzukiDF6D4FixedGridShard248EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard248EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard248EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard248EvenDotSoundness i
            suzukiDF6D4FixedGridShard248EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard248EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard248OddComparison_eq_live :
    suzukiDF6D4FixedGridShard248OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 248 k) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard248OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 248 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard248OddCross_eq_live :
    suzukiDF6D4FixedGridShard248OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 248) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard248OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 248)) at h
  exact h

def suzukiDF6D4FixedGridShard248OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard248OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard248OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard248OddDotSoundness i.val
      suzukiDF6D4FixedGridShard248OddComparisonData)

theorem suzukiDF6D4FixedGridShard248OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard248OddSolveData =
      suzukiDF6D4FixedGridShard248OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard248Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard248OddSolveData =
    suzukiDF6D4FixedGridShard248OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard248OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard248OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 248 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 248 k) := by
    rw [suzukiDF6D4FixedGridShard248OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 248 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248OddDotSoundness i
          suzukiDF6D4FixedGridShard248OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 248 k) := by
    simpa [suzukiDF6D4FixedGridShard248OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard248OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 248 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 248) := by
    rw [suzukiDF6D4FixedGridShard248OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 248)
  rw [suzukiDF6D4FixedGridShard248OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard248OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard248OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard248OddDotSoundness i
            suzukiDF6D4FixedGridShard248OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard248OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard248EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard248EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 549) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard248EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 549)) at h
  exact h

theorem suzukiDF6D4FixedGridShard248EvenFull_eq_live :
    suzukiDF6D4FixedGridShard248EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 549) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard248EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 549)) at h
  exact h

def suzukiDF6D4FixedGridShard248EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard248EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard248EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard248EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard248EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard248EvenResidualData =
      suzukiDF6D4FixedGridShard248EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard248Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard248EvenResidualData =
    suzukiDF6D4FixedGridShard248EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard248EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard248EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 549 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 549) := by
    rw [suzukiDF6D4FixedGridShard248EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 549
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248EvenDotSoundness i
          suzukiDF6D4FixedGridShard248EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 549) := by
    simpa [suzukiDF6D4FixedGridShard248EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard248EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 549) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 549) := by
    rw [suzukiDF6D4FixedGridShard248EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 549
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard248EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard248EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard248EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard248EvenDotSoundness i
            suzukiDF6D4FixedGridShard248EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard248EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard248OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard248OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 549) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard248OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 549)) at h
  exact h

theorem suzukiDF6D4FixedGridShard248OddFull_eq_live :
    suzukiDF6D4FixedGridShard248OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 549) := by
  have h := suzukiDF6D4FixedGridShard248Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard248OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 549)) at h
  exact h

def suzukiDF6D4FixedGridShard248OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard248OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard248OddDotSoundness i.val
        suzukiDF6D4FixedGridShard248OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard248OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard248OddResidualData =
      suzukiDF6D4FixedGridShard248OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard248Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard248OddResidualData =
    suzukiDF6D4FixedGridShard248OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard248OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard248OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 549 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 549) := by
    rw [suzukiDF6D4FixedGridShard248OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 549
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248OddDotSoundness i
          suzukiDF6D4FixedGridShard248OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 549) := by
    simpa [suzukiDF6D4FixedGridShard248OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard248OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 549) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard248OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 549) := by
    rw [suzukiDF6D4FixedGridShard248OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 549
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard248OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard248OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard248OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard248OddDotSoundness i
            suzukiDF6D4FixedGridShard248OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard248OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
