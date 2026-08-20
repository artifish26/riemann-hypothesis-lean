import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard235Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard235Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard235EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard235EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 235 k) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard235EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 235 k)) at h
  exact h

def suzukiDF6D4FixedGridShard235EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard235EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard235EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard235EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard235EvenComparisonData)

theorem suzukiDF6D4FixedGridShard235EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard235EvenSolveData =
      suzukiDF6D4FixedGridShard235EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard235Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard235EvenSolveData =
    suzukiDF6D4FixedGridShard235EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard235EvenCross_eq_live :
    suzukiDF6D4FixedGridShard235EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 235) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard235EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 235)) at h
  exact h

theorem suzukiDF6D4FixedGridShard235EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard235EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 235 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 235 k) := by
    rw [suzukiDF6D4FixedGridShard235EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 235 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235EvenDotSoundness i
          suzukiDF6D4FixedGridShard235EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 235 k) := by
    simpa [suzukiDF6D4FixedGridShard235EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard235EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 235 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 235) := by
    rw [suzukiDF6D4FixedGridShard235EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 235)
  rw [suzukiDF6D4FixedGridShard235EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard235EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard235EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard235EvenDotSoundness i
            suzukiDF6D4FixedGridShard235EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard235EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard235OddComparison_eq_live :
    suzukiDF6D4FixedGridShard235OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 235 k) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard235OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 235 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard235OddCross_eq_live :
    suzukiDF6D4FixedGridShard235OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 235) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard235OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 235)) at h
  exact h

def suzukiDF6D4FixedGridShard235OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard235OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard235OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard235OddDotSoundness i.val
      suzukiDF6D4FixedGridShard235OddComparisonData)

theorem suzukiDF6D4FixedGridShard235OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard235OddSolveData =
      suzukiDF6D4FixedGridShard235OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard235Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard235OddSolveData =
    suzukiDF6D4FixedGridShard235OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard235OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard235OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 235 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 235 k) := by
    rw [suzukiDF6D4FixedGridShard235OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 235 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235OddDotSoundness i
          suzukiDF6D4FixedGridShard235OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 235 k) := by
    simpa [suzukiDF6D4FixedGridShard235OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard235OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 235 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 235) := by
    rw [suzukiDF6D4FixedGridShard235OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 235)
  rw [suzukiDF6D4FixedGridShard235OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard235OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard235OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard235OddDotSoundness i
            suzukiDF6D4FixedGridShard235OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard235OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard235EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard235EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 536) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard235EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 536)) at h
  exact h

theorem suzukiDF6D4FixedGridShard235EvenFull_eq_live :
    suzukiDF6D4FixedGridShard235EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 536) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard235EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 536)) at h
  exact h

def suzukiDF6D4FixedGridShard235EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard235EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard235EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard235EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard235EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard235EvenResidualData =
      suzukiDF6D4FixedGridShard235EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard235Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard235EvenResidualData =
    suzukiDF6D4FixedGridShard235EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard235EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard235EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 536 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 536) := by
    rw [suzukiDF6D4FixedGridShard235EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 536
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235EvenDotSoundness i
          suzukiDF6D4FixedGridShard235EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 536) := by
    simpa [suzukiDF6D4FixedGridShard235EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard235EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 536) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 536) := by
    rw [suzukiDF6D4FixedGridShard235EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 536
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard235EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard235EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard235EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard235EvenDotSoundness i
            suzukiDF6D4FixedGridShard235EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard235EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard235OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard235OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 536) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard235OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 536)) at h
  exact h

theorem suzukiDF6D4FixedGridShard235OddFull_eq_live :
    suzukiDF6D4FixedGridShard235OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 536) := by
  have h := suzukiDF6D4FixedGridShard235Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard235OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 536)) at h
  exact h

def suzukiDF6D4FixedGridShard235OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard235OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard235OddDotSoundness i.val
        suzukiDF6D4FixedGridShard235OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard235OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard235OddResidualData =
      suzukiDF6D4FixedGridShard235OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard235Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard235OddResidualData =
    suzukiDF6D4FixedGridShard235OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard235OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard235OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 536 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 536) := by
    rw [suzukiDF6D4FixedGridShard235OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 536
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235OddDotSoundness i
          suzukiDF6D4FixedGridShard235OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 536) := by
    simpa [suzukiDF6D4FixedGridShard235OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard235OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 536) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard235OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 536) := by
    rw [suzukiDF6D4FixedGridShard235OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 536
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard235OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard235OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard235OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard235OddDotSoundness i
            suzukiDF6D4FixedGridShard235OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard235OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
