import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard118Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard118Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard118EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard118EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 118 k) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard118EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 118 k)) at h
  exact h

def suzukiDF6D4FixedGridShard118EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard118EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard118EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard118EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard118EvenComparisonData)

theorem suzukiDF6D4FixedGridShard118EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard118EvenSolveData =
      suzukiDF6D4FixedGridShard118EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard118Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard118EvenSolveData =
    suzukiDF6D4FixedGridShard118EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard118EvenCross_eq_live :
    suzukiDF6D4FixedGridShard118EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 118) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard118EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 118)) at h
  exact h

theorem suzukiDF6D4FixedGridShard118EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard118EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 118 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 118 k) := by
    rw [suzukiDF6D4FixedGridShard118EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 118 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118EvenDotSoundness i
          suzukiDF6D4FixedGridShard118EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 118 k) := by
    simpa [suzukiDF6D4FixedGridShard118EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard118EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 118 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 118) := by
    rw [suzukiDF6D4FixedGridShard118EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 118)
  rw [suzukiDF6D4FixedGridShard118EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard118EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard118EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard118EvenDotSoundness i
            suzukiDF6D4FixedGridShard118EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard118EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard118OddComparison_eq_live :
    suzukiDF6D4FixedGridShard118OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 118 k) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard118OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 118 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard118OddCross_eq_live :
    suzukiDF6D4FixedGridShard118OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 118) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard118OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 118)) at h
  exact h

def suzukiDF6D4FixedGridShard118OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard118OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard118OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard118OddDotSoundness i.val
      suzukiDF6D4FixedGridShard118OddComparisonData)

theorem suzukiDF6D4FixedGridShard118OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard118OddSolveData =
      suzukiDF6D4FixedGridShard118OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard118Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard118OddSolveData =
    suzukiDF6D4FixedGridShard118OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard118OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard118OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 118 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 118 k) := by
    rw [suzukiDF6D4FixedGridShard118OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 118 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118OddDotSoundness i
          suzukiDF6D4FixedGridShard118OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 118 k) := by
    simpa [suzukiDF6D4FixedGridShard118OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard118OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 118 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 118) := by
    rw [suzukiDF6D4FixedGridShard118OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 118)
  rw [suzukiDF6D4FixedGridShard118OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard118OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard118OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard118OddDotSoundness i
            suzukiDF6D4FixedGridShard118OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard118OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard118EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard118EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 419) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard118EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 419)) at h
  exact h

theorem suzukiDF6D4FixedGridShard118EvenFull_eq_live :
    suzukiDF6D4FixedGridShard118EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 419) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard118EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 419)) at h
  exact h

def suzukiDF6D4FixedGridShard118EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard118EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard118EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard118EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard118EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard118EvenResidualData =
      suzukiDF6D4FixedGridShard118EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard118Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard118EvenResidualData =
    suzukiDF6D4FixedGridShard118EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard118EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard118EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 419 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 419) := by
    rw [suzukiDF6D4FixedGridShard118EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 419
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118EvenDotSoundness i
          suzukiDF6D4FixedGridShard118EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 419) := by
    simpa [suzukiDF6D4FixedGridShard118EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard118EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 419) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 419) := by
    rw [suzukiDF6D4FixedGridShard118EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 419
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard118EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard118EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard118EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard118EvenDotSoundness i
            suzukiDF6D4FixedGridShard118EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard118EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard118OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard118OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 419) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard118OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 419)) at h
  exact h

theorem suzukiDF6D4FixedGridShard118OddFull_eq_live :
    suzukiDF6D4FixedGridShard118OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 419) := by
  have h := suzukiDF6D4FixedGridShard118Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard118OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 419)) at h
  exact h

def suzukiDF6D4FixedGridShard118OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard118OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard118OddDotSoundness i.val
        suzukiDF6D4FixedGridShard118OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard118OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard118OddResidualData =
      suzukiDF6D4FixedGridShard118OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard118Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard118OddResidualData =
    suzukiDF6D4FixedGridShard118OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard118OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard118OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 419 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 419) := by
    rw [suzukiDF6D4FixedGridShard118OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 419
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118OddDotSoundness i
          suzukiDF6D4FixedGridShard118OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 419) := by
    simpa [suzukiDF6D4FixedGridShard118OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard118OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 419) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard118OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 419) := by
    rw [suzukiDF6D4FixedGridShard118OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 419
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard118OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard118OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard118OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard118OddDotSoundness i
            suzukiDF6D4FixedGridShard118OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard118OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
