import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard125Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard125Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard125EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard125EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 125 k) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard125EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 125 k)) at h
  exact h

def suzukiDF6D4FixedGridShard125EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard125EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard125EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard125EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard125EvenComparisonData)

theorem suzukiDF6D4FixedGridShard125EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard125EvenSolveData =
      suzukiDF6D4FixedGridShard125EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard125Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard125EvenSolveData =
    suzukiDF6D4FixedGridShard125EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard125EvenCross_eq_live :
    suzukiDF6D4FixedGridShard125EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 125) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard125EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 125)) at h
  exact h

theorem suzukiDF6D4FixedGridShard125EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard125EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 125 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 125 k) := by
    rw [suzukiDF6D4FixedGridShard125EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 125 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125EvenDotSoundness i
          suzukiDF6D4FixedGridShard125EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 125 k) := by
    simpa [suzukiDF6D4FixedGridShard125EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard125EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 125 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 125) := by
    rw [suzukiDF6D4FixedGridShard125EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 125)
  rw [suzukiDF6D4FixedGridShard125EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard125EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard125EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard125EvenDotSoundness i
            suzukiDF6D4FixedGridShard125EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard125EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard125OddComparison_eq_live :
    suzukiDF6D4FixedGridShard125OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 125 k) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard125OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 125 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard125OddCross_eq_live :
    suzukiDF6D4FixedGridShard125OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 125) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard125OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 125)) at h
  exact h

def suzukiDF6D4FixedGridShard125OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard125OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard125OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard125OddDotSoundness i.val
      suzukiDF6D4FixedGridShard125OddComparisonData)

theorem suzukiDF6D4FixedGridShard125OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard125OddSolveData =
      suzukiDF6D4FixedGridShard125OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard125Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard125OddSolveData =
    suzukiDF6D4FixedGridShard125OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard125OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard125OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 125 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 125 k) := by
    rw [suzukiDF6D4FixedGridShard125OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 125 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125OddDotSoundness i
          suzukiDF6D4FixedGridShard125OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 125 k) := by
    simpa [suzukiDF6D4FixedGridShard125OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard125OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 125 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 125) := by
    rw [suzukiDF6D4FixedGridShard125OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 125)
  rw [suzukiDF6D4FixedGridShard125OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard125OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard125OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard125OddDotSoundness i
            suzukiDF6D4FixedGridShard125OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard125OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard125EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard125EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 426) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard125EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 426)) at h
  exact h

theorem suzukiDF6D4FixedGridShard125EvenFull_eq_live :
    suzukiDF6D4FixedGridShard125EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 426) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard125EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 426)) at h
  exact h

def suzukiDF6D4FixedGridShard125EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard125EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard125EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard125EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard125EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard125EvenResidualData =
      suzukiDF6D4FixedGridShard125EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard125Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard125EvenResidualData =
    suzukiDF6D4FixedGridShard125EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard125EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard125EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 426 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 426) := by
    rw [suzukiDF6D4FixedGridShard125EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 426
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125EvenDotSoundness i
          suzukiDF6D4FixedGridShard125EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 426) := by
    simpa [suzukiDF6D4FixedGridShard125EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard125EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 426) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 426) := by
    rw [suzukiDF6D4FixedGridShard125EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 426
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard125EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard125EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard125EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard125EvenDotSoundness i
            suzukiDF6D4FixedGridShard125EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard125EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard125OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard125OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 426) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard125OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 426)) at h
  exact h

theorem suzukiDF6D4FixedGridShard125OddFull_eq_live :
    suzukiDF6D4FixedGridShard125OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 426) := by
  have h := suzukiDF6D4FixedGridShard125Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard125OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 426)) at h
  exact h

def suzukiDF6D4FixedGridShard125OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard125OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard125OddDotSoundness i.val
        suzukiDF6D4FixedGridShard125OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard125OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard125OddResidualData =
      suzukiDF6D4FixedGridShard125OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard125Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard125OddResidualData =
    suzukiDF6D4FixedGridShard125OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard125OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard125OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 426 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 426) := by
    rw [suzukiDF6D4FixedGridShard125OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 426
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125OddDotSoundness i
          suzukiDF6D4FixedGridShard125OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 426) := by
    simpa [suzukiDF6D4FixedGridShard125OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard125OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 426) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard125OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 426) := by
    rw [suzukiDF6D4FixedGridShard125OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 426
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard125OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard125OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard125OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard125OddDotSoundness i
            suzukiDF6D4FixedGridShard125OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard125OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
