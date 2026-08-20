import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard144Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard144Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard144EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard144EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 144 k) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard144EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 144 k)) at h
  exact h

def suzukiDF6D4FixedGridShard144EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard144EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard144EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard144EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard144EvenComparisonData)

theorem suzukiDF6D4FixedGridShard144EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard144EvenSolveData =
      suzukiDF6D4FixedGridShard144EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard144Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard144EvenSolveData =
    suzukiDF6D4FixedGridShard144EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard144EvenCross_eq_live :
    suzukiDF6D4FixedGridShard144EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 144) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard144EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 144)) at h
  exact h

theorem suzukiDF6D4FixedGridShard144EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard144EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 144 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 144 k) := by
    rw [suzukiDF6D4FixedGridShard144EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 144 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144EvenDotSoundness i
          suzukiDF6D4FixedGridShard144EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 144 k) := by
    simpa [suzukiDF6D4FixedGridShard144EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard144EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 144 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 144) := by
    rw [suzukiDF6D4FixedGridShard144EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 144)
  rw [suzukiDF6D4FixedGridShard144EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard144EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard144EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard144EvenDotSoundness i
            suzukiDF6D4FixedGridShard144EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard144EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard144OddComparison_eq_live :
    suzukiDF6D4FixedGridShard144OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 144 k) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard144OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 144 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard144OddCross_eq_live :
    suzukiDF6D4FixedGridShard144OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 144) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard144OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 144)) at h
  exact h

def suzukiDF6D4FixedGridShard144OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard144OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard144OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard144OddDotSoundness i.val
      suzukiDF6D4FixedGridShard144OddComparisonData)

theorem suzukiDF6D4FixedGridShard144OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard144OddSolveData =
      suzukiDF6D4FixedGridShard144OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard144Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard144OddSolveData =
    suzukiDF6D4FixedGridShard144OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard144OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard144OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 144 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 144 k) := by
    rw [suzukiDF6D4FixedGridShard144OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 144 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144OddDotSoundness i
          suzukiDF6D4FixedGridShard144OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 144 k) := by
    simpa [suzukiDF6D4FixedGridShard144OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard144OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 144 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 144) := by
    rw [suzukiDF6D4FixedGridShard144OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 144)
  rw [suzukiDF6D4FixedGridShard144OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard144OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard144OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard144OddDotSoundness i
            suzukiDF6D4FixedGridShard144OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard144OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard144EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard144EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 445) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard144EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 445)) at h
  exact h

theorem suzukiDF6D4FixedGridShard144EvenFull_eq_live :
    suzukiDF6D4FixedGridShard144EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 445) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard144EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 445)) at h
  exact h

def suzukiDF6D4FixedGridShard144EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard144EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard144EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard144EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard144EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard144EvenResidualData =
      suzukiDF6D4FixedGridShard144EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard144Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard144EvenResidualData =
    suzukiDF6D4FixedGridShard144EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard144EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard144EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 445 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 445) := by
    rw [suzukiDF6D4FixedGridShard144EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 445
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144EvenDotSoundness i
          suzukiDF6D4FixedGridShard144EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 445) := by
    simpa [suzukiDF6D4FixedGridShard144EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard144EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 445) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 445) := by
    rw [suzukiDF6D4FixedGridShard144EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 445
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard144EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard144EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard144EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard144EvenDotSoundness i
            suzukiDF6D4FixedGridShard144EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard144EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard144OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard144OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 445) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard144OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 445)) at h
  exact h

theorem suzukiDF6D4FixedGridShard144OddFull_eq_live :
    suzukiDF6D4FixedGridShard144OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 445) := by
  have h := suzukiDF6D4FixedGridShard144Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard144OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 445)) at h
  exact h

def suzukiDF6D4FixedGridShard144OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard144OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard144OddDotSoundness i.val
        suzukiDF6D4FixedGridShard144OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard144OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard144OddResidualData =
      suzukiDF6D4FixedGridShard144OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard144Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard144OddResidualData =
    suzukiDF6D4FixedGridShard144OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard144OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard144OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 445 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 445) := by
    rw [suzukiDF6D4FixedGridShard144OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 445
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144OddDotSoundness i
          suzukiDF6D4FixedGridShard144OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 445) := by
    simpa [suzukiDF6D4FixedGridShard144OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard144OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 445) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard144OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 445) := by
    rw [suzukiDF6D4FixedGridShard144OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 445
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard144OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard144OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard144OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard144OddDotSoundness i
            suzukiDF6D4FixedGridShard144OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard144OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
