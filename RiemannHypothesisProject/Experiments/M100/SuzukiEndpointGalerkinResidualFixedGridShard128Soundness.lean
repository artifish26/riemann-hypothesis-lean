import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard128Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard128Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard128EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard128EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 128 k) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard128EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 128 k)) at h
  exact h

def suzukiDF6D4FixedGridShard128EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard128EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard128EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard128EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard128EvenComparisonData)

theorem suzukiDF6D4FixedGridShard128EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard128EvenSolveData =
      suzukiDF6D4FixedGridShard128EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard128Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard128EvenSolveData =
    suzukiDF6D4FixedGridShard128EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard128EvenCross_eq_live :
    suzukiDF6D4FixedGridShard128EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 128) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard128EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 128)) at h
  exact h

theorem suzukiDF6D4FixedGridShard128EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard128EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 128 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 128 k) := by
    rw [suzukiDF6D4FixedGridShard128EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 128 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128EvenDotSoundness i
          suzukiDF6D4FixedGridShard128EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 128 k) := by
    simpa [suzukiDF6D4FixedGridShard128EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard128EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 128 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 128) := by
    rw [suzukiDF6D4FixedGridShard128EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 128)
  rw [suzukiDF6D4FixedGridShard128EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard128EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard128EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard128EvenDotSoundness i
            suzukiDF6D4FixedGridShard128EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard128EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard128OddComparison_eq_live :
    suzukiDF6D4FixedGridShard128OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 128 k) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard128OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 128 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard128OddCross_eq_live :
    suzukiDF6D4FixedGridShard128OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 128) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard128OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 128)) at h
  exact h

def suzukiDF6D4FixedGridShard128OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard128OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard128OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard128OddDotSoundness i.val
      suzukiDF6D4FixedGridShard128OddComparisonData)

theorem suzukiDF6D4FixedGridShard128OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard128OddSolveData =
      suzukiDF6D4FixedGridShard128OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard128Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard128OddSolveData =
    suzukiDF6D4FixedGridShard128OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard128OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard128OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 128 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 128 k) := by
    rw [suzukiDF6D4FixedGridShard128OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 128 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128OddDotSoundness i
          suzukiDF6D4FixedGridShard128OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 128 k) := by
    simpa [suzukiDF6D4FixedGridShard128OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard128OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 128 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 128) := by
    rw [suzukiDF6D4FixedGridShard128OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 128)
  rw [suzukiDF6D4FixedGridShard128OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard128OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard128OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard128OddDotSoundness i
            suzukiDF6D4FixedGridShard128OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard128OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard128EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard128EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 429) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard128EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 429)) at h
  exact h

theorem suzukiDF6D4FixedGridShard128EvenFull_eq_live :
    suzukiDF6D4FixedGridShard128EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 429) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard128EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 429)) at h
  exact h

def suzukiDF6D4FixedGridShard128EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard128EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard128EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard128EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard128EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard128EvenResidualData =
      suzukiDF6D4FixedGridShard128EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard128Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard128EvenResidualData =
    suzukiDF6D4FixedGridShard128EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard128EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard128EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 429 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 429) := by
    rw [suzukiDF6D4FixedGridShard128EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 429
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128EvenDotSoundness i
          suzukiDF6D4FixedGridShard128EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 429) := by
    simpa [suzukiDF6D4FixedGridShard128EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard128EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 429) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 429) := by
    rw [suzukiDF6D4FixedGridShard128EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 429
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard128EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard128EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard128EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard128EvenDotSoundness i
            suzukiDF6D4FixedGridShard128EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard128EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard128OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard128OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 429) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard128OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 429)) at h
  exact h

theorem suzukiDF6D4FixedGridShard128OddFull_eq_live :
    suzukiDF6D4FixedGridShard128OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 429) := by
  have h := suzukiDF6D4FixedGridShard128Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard128OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 429)) at h
  exact h

def suzukiDF6D4FixedGridShard128OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard128OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard128OddDotSoundness i.val
        suzukiDF6D4FixedGridShard128OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard128OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard128OddResidualData =
      suzukiDF6D4FixedGridShard128OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard128Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard128OddResidualData =
    suzukiDF6D4FixedGridShard128OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard128OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard128OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 429 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 429) := by
    rw [suzukiDF6D4FixedGridShard128OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 429
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128OddDotSoundness i
          suzukiDF6D4FixedGridShard128OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 429) := by
    simpa [suzukiDF6D4FixedGridShard128OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard128OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 429) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard128OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 429) := by
    rw [suzukiDF6D4FixedGridShard128OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 429
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard128OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard128OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard128OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard128OddDotSoundness i
            suzukiDF6D4FixedGridShard128OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard128OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
