import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard255Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard255Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard255EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard255EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 255 k) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard255EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 255 k)) at h
  exact h

def suzukiDF6D4FixedGridShard255EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard255EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard255EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard255EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard255EvenComparisonData)

theorem suzukiDF6D4FixedGridShard255EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard255EvenSolveData =
      suzukiDF6D4FixedGridShard255EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard255Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard255EvenSolveData =
    suzukiDF6D4FixedGridShard255EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard255EvenCross_eq_live :
    suzukiDF6D4FixedGridShard255EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 255) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard255EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 255)) at h
  exact h

theorem suzukiDF6D4FixedGridShard255EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard255EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 255 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 255 k) := by
    rw [suzukiDF6D4FixedGridShard255EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 255 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255EvenDotSoundness i
          suzukiDF6D4FixedGridShard255EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 255 k) := by
    simpa [suzukiDF6D4FixedGridShard255EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard255EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 255 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 255) := by
    rw [suzukiDF6D4FixedGridShard255EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 255)
  rw [suzukiDF6D4FixedGridShard255EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard255EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard255EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard255EvenDotSoundness i
            suzukiDF6D4FixedGridShard255EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard255EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard255OddComparison_eq_live :
    suzukiDF6D4FixedGridShard255OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 255 k) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard255OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 255 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard255OddCross_eq_live :
    suzukiDF6D4FixedGridShard255OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 255) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard255OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 255)) at h
  exact h

def suzukiDF6D4FixedGridShard255OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard255OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard255OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard255OddDotSoundness i.val
      suzukiDF6D4FixedGridShard255OddComparisonData)

theorem suzukiDF6D4FixedGridShard255OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard255OddSolveData =
      suzukiDF6D4FixedGridShard255OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard255Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard255OddSolveData =
    suzukiDF6D4FixedGridShard255OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard255OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard255OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 255 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 255 k) := by
    rw [suzukiDF6D4FixedGridShard255OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 255 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255OddDotSoundness i
          suzukiDF6D4FixedGridShard255OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 255 k) := by
    simpa [suzukiDF6D4FixedGridShard255OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard255OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 255 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 255) := by
    rw [suzukiDF6D4FixedGridShard255OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 255)
  rw [suzukiDF6D4FixedGridShard255OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard255OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard255OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard255OddDotSoundness i
            suzukiDF6D4FixedGridShard255OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard255OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard255EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard255EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 556) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard255EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 556)) at h
  exact h

theorem suzukiDF6D4FixedGridShard255EvenFull_eq_live :
    suzukiDF6D4FixedGridShard255EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 556) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard255EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 556)) at h
  exact h

def suzukiDF6D4FixedGridShard255EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard255EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard255EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard255EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard255EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard255EvenResidualData =
      suzukiDF6D4FixedGridShard255EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard255Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard255EvenResidualData =
    suzukiDF6D4FixedGridShard255EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard255EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard255EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 556 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 556) := by
    rw [suzukiDF6D4FixedGridShard255EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 556
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255EvenDotSoundness i
          suzukiDF6D4FixedGridShard255EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 556) := by
    simpa [suzukiDF6D4FixedGridShard255EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard255EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 556) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 556) := by
    rw [suzukiDF6D4FixedGridShard255EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 556
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard255EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard255EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard255EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard255EvenDotSoundness i
            suzukiDF6D4FixedGridShard255EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard255EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard255OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard255OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 556) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard255OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 556)) at h
  exact h

theorem suzukiDF6D4FixedGridShard255OddFull_eq_live :
    suzukiDF6D4FixedGridShard255OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 556) := by
  have h := suzukiDF6D4FixedGridShard255Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard255OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 556)) at h
  exact h

def suzukiDF6D4FixedGridShard255OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard255OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard255OddDotSoundness i.val
        suzukiDF6D4FixedGridShard255OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard255OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard255OddResidualData =
      suzukiDF6D4FixedGridShard255OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard255Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard255OddResidualData =
    suzukiDF6D4FixedGridShard255OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard255OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard255OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 556 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 556) := by
    rw [suzukiDF6D4FixedGridShard255OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 556
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255OddDotSoundness i
          suzukiDF6D4FixedGridShard255OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 556) := by
    simpa [suzukiDF6D4FixedGridShard255OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard255OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 556) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard255OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 556) := by
    rw [suzukiDF6D4FixedGridShard255OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 556
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard255OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard255OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard255OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard255OddDotSoundness i
            suzukiDF6D4FixedGridShard255OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard255OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
