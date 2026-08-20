import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard111Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard111Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard111EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard111EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 111 k) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard111EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 111 k)) at h
  exact h

def suzukiDF6D4FixedGridShard111EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard111EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard111EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard111EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard111EvenComparisonData)

theorem suzukiDF6D4FixedGridShard111EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard111EvenSolveData =
      suzukiDF6D4FixedGridShard111EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard111Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard111EvenSolveData =
    suzukiDF6D4FixedGridShard111EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard111EvenCross_eq_live :
    suzukiDF6D4FixedGridShard111EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 111) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard111EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 111)) at h
  exact h

theorem suzukiDF6D4FixedGridShard111EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard111EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 111 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 111 k) := by
    rw [suzukiDF6D4FixedGridShard111EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 111 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111EvenDotSoundness i
          suzukiDF6D4FixedGridShard111EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 111 k) := by
    simpa [suzukiDF6D4FixedGridShard111EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard111EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 111 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 111) := by
    rw [suzukiDF6D4FixedGridShard111EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 111)
  rw [suzukiDF6D4FixedGridShard111EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard111EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard111EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard111EvenDotSoundness i
            suzukiDF6D4FixedGridShard111EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard111EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard111OddComparison_eq_live :
    suzukiDF6D4FixedGridShard111OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 111 k) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard111OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 111 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard111OddCross_eq_live :
    suzukiDF6D4FixedGridShard111OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 111) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard111OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 111)) at h
  exact h

def suzukiDF6D4FixedGridShard111OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard111OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard111OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard111OddDotSoundness i.val
      suzukiDF6D4FixedGridShard111OddComparisonData)

theorem suzukiDF6D4FixedGridShard111OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard111OddSolveData =
      suzukiDF6D4FixedGridShard111OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard111Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard111OddSolveData =
    suzukiDF6D4FixedGridShard111OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard111OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard111OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 111 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 111 k) := by
    rw [suzukiDF6D4FixedGridShard111OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 111 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111OddDotSoundness i
          suzukiDF6D4FixedGridShard111OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 111 k) := by
    simpa [suzukiDF6D4FixedGridShard111OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard111OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 111 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 111) := by
    rw [suzukiDF6D4FixedGridShard111OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 111)
  rw [suzukiDF6D4FixedGridShard111OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard111OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard111OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard111OddDotSoundness i
            suzukiDF6D4FixedGridShard111OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard111OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard111EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard111EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 412) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard111EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 412)) at h
  exact h

theorem suzukiDF6D4FixedGridShard111EvenFull_eq_live :
    suzukiDF6D4FixedGridShard111EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 412) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard111EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 412)) at h
  exact h

def suzukiDF6D4FixedGridShard111EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard111EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard111EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard111EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard111EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard111EvenResidualData =
      suzukiDF6D4FixedGridShard111EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard111Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard111EvenResidualData =
    suzukiDF6D4FixedGridShard111EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard111EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard111EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 412 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 412) := by
    rw [suzukiDF6D4FixedGridShard111EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 412
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111EvenDotSoundness i
          suzukiDF6D4FixedGridShard111EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 412) := by
    simpa [suzukiDF6D4FixedGridShard111EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard111EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 412) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 412) := by
    rw [suzukiDF6D4FixedGridShard111EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 412
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard111EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard111EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard111EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard111EvenDotSoundness i
            suzukiDF6D4FixedGridShard111EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard111EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard111OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard111OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 412) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard111OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 412)) at h
  exact h

theorem suzukiDF6D4FixedGridShard111OddFull_eq_live :
    suzukiDF6D4FixedGridShard111OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 412) := by
  have h := suzukiDF6D4FixedGridShard111Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard111OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 412)) at h
  exact h

def suzukiDF6D4FixedGridShard111OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard111OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard111OddDotSoundness i.val
        suzukiDF6D4FixedGridShard111OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard111OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard111OddResidualData =
      suzukiDF6D4FixedGridShard111OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard111Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard111OddResidualData =
    suzukiDF6D4FixedGridShard111OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard111OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard111OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 412 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 412) := by
    rw [suzukiDF6D4FixedGridShard111OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 412
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111OddDotSoundness i
          suzukiDF6D4FixedGridShard111OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 412) := by
    simpa [suzukiDF6D4FixedGridShard111OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard111OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 412) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard111OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 412) := by
    rw [suzukiDF6D4FixedGridShard111OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 412
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard111OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard111OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard111OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard111OddDotSoundness i
            suzukiDF6D4FixedGridShard111OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard111OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
