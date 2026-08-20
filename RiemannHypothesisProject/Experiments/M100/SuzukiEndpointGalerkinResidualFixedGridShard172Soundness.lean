import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard172Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard172Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard172EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard172EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 172 k) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard172EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 172 k)) at h
  exact h

def suzukiDF6D4FixedGridShard172EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard172EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard172EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard172EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard172EvenComparisonData)

theorem suzukiDF6D4FixedGridShard172EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard172EvenSolveData =
      suzukiDF6D4FixedGridShard172EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard172Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard172EvenSolveData =
    suzukiDF6D4FixedGridShard172EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard172EvenCross_eq_live :
    suzukiDF6D4FixedGridShard172EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 172) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard172EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 172)) at h
  exact h

theorem suzukiDF6D4FixedGridShard172EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard172EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 172 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 172 k) := by
    rw [suzukiDF6D4FixedGridShard172EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 172 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172EvenDotSoundness i
          suzukiDF6D4FixedGridShard172EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 172 k) := by
    simpa [suzukiDF6D4FixedGridShard172EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard172EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 172 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 172) := by
    rw [suzukiDF6D4FixedGridShard172EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 172)
  rw [suzukiDF6D4FixedGridShard172EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard172EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard172EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard172EvenDotSoundness i
            suzukiDF6D4FixedGridShard172EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard172EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard172OddComparison_eq_live :
    suzukiDF6D4FixedGridShard172OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 172 k) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard172OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 172 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard172OddCross_eq_live :
    suzukiDF6D4FixedGridShard172OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 172) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard172OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 172)) at h
  exact h

def suzukiDF6D4FixedGridShard172OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard172OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard172OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard172OddDotSoundness i.val
      suzukiDF6D4FixedGridShard172OddComparisonData)

theorem suzukiDF6D4FixedGridShard172OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard172OddSolveData =
      suzukiDF6D4FixedGridShard172OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard172Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard172OddSolveData =
    suzukiDF6D4FixedGridShard172OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard172OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard172OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 172 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 172 k) := by
    rw [suzukiDF6D4FixedGridShard172OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 172 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172OddDotSoundness i
          suzukiDF6D4FixedGridShard172OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 172 k) := by
    simpa [suzukiDF6D4FixedGridShard172OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard172OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 172 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 172) := by
    rw [suzukiDF6D4FixedGridShard172OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 172)
  rw [suzukiDF6D4FixedGridShard172OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard172OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard172OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard172OddDotSoundness i
            suzukiDF6D4FixedGridShard172OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard172OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard172EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard172EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 473) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard172EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 473)) at h
  exact h

theorem suzukiDF6D4FixedGridShard172EvenFull_eq_live :
    suzukiDF6D4FixedGridShard172EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 473) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard172EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 473)) at h
  exact h

def suzukiDF6D4FixedGridShard172EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard172EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard172EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard172EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard172EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard172EvenResidualData =
      suzukiDF6D4FixedGridShard172EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard172Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard172EvenResidualData =
    suzukiDF6D4FixedGridShard172EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard172EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard172EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 473 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 473) := by
    rw [suzukiDF6D4FixedGridShard172EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 473
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172EvenDotSoundness i
          suzukiDF6D4FixedGridShard172EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 473) := by
    simpa [suzukiDF6D4FixedGridShard172EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard172EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 473) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 473) := by
    rw [suzukiDF6D4FixedGridShard172EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 473
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard172EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard172EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard172EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard172EvenDotSoundness i
            suzukiDF6D4FixedGridShard172EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard172EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard172OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard172OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 473) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard172OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 473)) at h
  exact h

theorem suzukiDF6D4FixedGridShard172OddFull_eq_live :
    suzukiDF6D4FixedGridShard172OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 473) := by
  have h := suzukiDF6D4FixedGridShard172Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard172OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 473)) at h
  exact h

def suzukiDF6D4FixedGridShard172OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard172OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard172OddDotSoundness i.val
        suzukiDF6D4FixedGridShard172OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard172OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard172OddResidualData =
      suzukiDF6D4FixedGridShard172OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard172Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard172OddResidualData =
    suzukiDF6D4FixedGridShard172OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard172OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard172OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 473 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 473) := by
    rw [suzukiDF6D4FixedGridShard172OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 473
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172OddDotSoundness i
          suzukiDF6D4FixedGridShard172OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 473) := by
    simpa [suzukiDF6D4FixedGridShard172OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard172OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 473) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard172OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 473) := by
    rw [suzukiDF6D4FixedGridShard172OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 473
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard172OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard172OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard172OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard172OddDotSoundness i
            suzukiDF6D4FixedGridShard172OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard172OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
