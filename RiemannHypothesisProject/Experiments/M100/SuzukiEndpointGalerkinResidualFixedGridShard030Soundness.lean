import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard030Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard030Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard030EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard030EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 30 k) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard030EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 30 k)) at h
  exact h

def suzukiDF6D4FixedGridShard030EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard030EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard030EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard030EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard030EvenComparisonData)

theorem suzukiDF6D4FixedGridShard030EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard030EvenSolveData =
      suzukiDF6D4FixedGridShard030EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard030Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard030EvenSolveData =
    suzukiDF6D4FixedGridShard030EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard030EvenCross_eq_live :
    suzukiDF6D4FixedGridShard030EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 30) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard030EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 30)) at h
  exact h

theorem suzukiDF6D4FixedGridShard030EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard030EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 30 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 30 k) := by
    rw [suzukiDF6D4FixedGridShard030EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 30 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030EvenDotSoundness i
          suzukiDF6D4FixedGridShard030EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 30 k) := by
    simpa [suzukiDF6D4FixedGridShard030EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard030EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 30 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 30) := by
    rw [suzukiDF6D4FixedGridShard030EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 30)
  rw [suzukiDF6D4FixedGridShard030EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard030EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard030EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard030EvenDotSoundness i
            suzukiDF6D4FixedGridShard030EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard030EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard030OddComparison_eq_live :
    suzukiDF6D4FixedGridShard030OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 30 k) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard030OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 30 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard030OddCross_eq_live :
    suzukiDF6D4FixedGridShard030OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 30) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard030OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 30)) at h
  exact h

def suzukiDF6D4FixedGridShard030OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard030OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard030OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard030OddDotSoundness i.val
      suzukiDF6D4FixedGridShard030OddComparisonData)

theorem suzukiDF6D4FixedGridShard030OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard030OddSolveData =
      suzukiDF6D4FixedGridShard030OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard030Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard030OddSolveData =
    suzukiDF6D4FixedGridShard030OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard030OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard030OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 30 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 30 k) := by
    rw [suzukiDF6D4FixedGridShard030OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 30 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030OddDotSoundness i
          suzukiDF6D4FixedGridShard030OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 30 k) := by
    simpa [suzukiDF6D4FixedGridShard030OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard030OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 30 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 30) := by
    rw [suzukiDF6D4FixedGridShard030OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 30)
  rw [suzukiDF6D4FixedGridShard030OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard030OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard030OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard030OddDotSoundness i
            suzukiDF6D4FixedGridShard030OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard030OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard030EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard030EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 331) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard030EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 331)) at h
  exact h

theorem suzukiDF6D4FixedGridShard030EvenFull_eq_live :
    suzukiDF6D4FixedGridShard030EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 331) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard030EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 331)) at h
  exact h

def suzukiDF6D4FixedGridShard030EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard030EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard030EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard030EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard030EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard030EvenResidualData =
      suzukiDF6D4FixedGridShard030EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard030Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard030EvenResidualData =
    suzukiDF6D4FixedGridShard030EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard030EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard030EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 331 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 331) := by
    rw [suzukiDF6D4FixedGridShard030EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 331
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030EvenDotSoundness i
          suzukiDF6D4FixedGridShard030EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 331) := by
    simpa [suzukiDF6D4FixedGridShard030EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard030EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 331) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 331) := by
    rw [suzukiDF6D4FixedGridShard030EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 331
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard030EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard030EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard030EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard030EvenDotSoundness i
            suzukiDF6D4FixedGridShard030EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard030EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard030OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard030OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 331) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard030OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 331)) at h
  exact h

theorem suzukiDF6D4FixedGridShard030OddFull_eq_live :
    suzukiDF6D4FixedGridShard030OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 331) := by
  have h := suzukiDF6D4FixedGridShard030Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard030OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 331)) at h
  exact h

def suzukiDF6D4FixedGridShard030OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard030OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard030OddDotSoundness i.val
        suzukiDF6D4FixedGridShard030OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard030OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard030OddResidualData =
      suzukiDF6D4FixedGridShard030OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard030Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard030OddResidualData =
    suzukiDF6D4FixedGridShard030OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard030OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard030OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 331 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 331) := by
    rw [suzukiDF6D4FixedGridShard030OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 331
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030OddDotSoundness i
          suzukiDF6D4FixedGridShard030OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 331) := by
    simpa [suzukiDF6D4FixedGridShard030OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard030OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 331) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard030OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 331) := by
    rw [suzukiDF6D4FixedGridShard030OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 331
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard030OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard030OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard030OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard030OddDotSoundness i
            suzukiDF6D4FixedGridShard030OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard030OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
