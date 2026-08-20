import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard083Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard083Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard083EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard083EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 83 k) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard083EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 83 k)) at h
  exact h

def suzukiDF6D4FixedGridShard083EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard083EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard083EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard083EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard083EvenComparisonData)

theorem suzukiDF6D4FixedGridShard083EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard083EvenSolveData =
      suzukiDF6D4FixedGridShard083EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard083Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard083EvenSolveData =
    suzukiDF6D4FixedGridShard083EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard083EvenCross_eq_live :
    suzukiDF6D4FixedGridShard083EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 83) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard083EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 83)) at h
  exact h

theorem suzukiDF6D4FixedGridShard083EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard083EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 83 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 83 k) := by
    rw [suzukiDF6D4FixedGridShard083EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 83 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083EvenDotSoundness i
          suzukiDF6D4FixedGridShard083EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 83 k) := by
    simpa [suzukiDF6D4FixedGridShard083EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard083EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 83 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 83) := by
    rw [suzukiDF6D4FixedGridShard083EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 83)
  rw [suzukiDF6D4FixedGridShard083EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard083EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard083EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard083EvenDotSoundness i
            suzukiDF6D4FixedGridShard083EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard083EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard083OddComparison_eq_live :
    suzukiDF6D4FixedGridShard083OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 83 k) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard083OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 83 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard083OddCross_eq_live :
    suzukiDF6D4FixedGridShard083OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 83) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard083OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 83)) at h
  exact h

def suzukiDF6D4FixedGridShard083OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard083OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard083OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard083OddDotSoundness i.val
      suzukiDF6D4FixedGridShard083OddComparisonData)

theorem suzukiDF6D4FixedGridShard083OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard083OddSolveData =
      suzukiDF6D4FixedGridShard083OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard083Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard083OddSolveData =
    suzukiDF6D4FixedGridShard083OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard083OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard083OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 83 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 83 k) := by
    rw [suzukiDF6D4FixedGridShard083OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 83 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083OddDotSoundness i
          suzukiDF6D4FixedGridShard083OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 83 k) := by
    simpa [suzukiDF6D4FixedGridShard083OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard083OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 83 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 83) := by
    rw [suzukiDF6D4FixedGridShard083OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 83)
  rw [suzukiDF6D4FixedGridShard083OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard083OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard083OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard083OddDotSoundness i
            suzukiDF6D4FixedGridShard083OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard083OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard083EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard083EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 384) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard083EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 384)) at h
  exact h

theorem suzukiDF6D4FixedGridShard083EvenFull_eq_live :
    suzukiDF6D4FixedGridShard083EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 384) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard083EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 384)) at h
  exact h

def suzukiDF6D4FixedGridShard083EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard083EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard083EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard083EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard083EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard083EvenResidualData =
      suzukiDF6D4FixedGridShard083EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard083Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard083EvenResidualData =
    suzukiDF6D4FixedGridShard083EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard083EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard083EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 384 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 384) := by
    rw [suzukiDF6D4FixedGridShard083EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 384
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083EvenDotSoundness i
          suzukiDF6D4FixedGridShard083EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 384) := by
    simpa [suzukiDF6D4FixedGridShard083EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard083EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 384) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 384) := by
    rw [suzukiDF6D4FixedGridShard083EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 384
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard083EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard083EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard083EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard083EvenDotSoundness i
            suzukiDF6D4FixedGridShard083EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard083EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard083OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard083OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 384) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard083OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 384)) at h
  exact h

theorem suzukiDF6D4FixedGridShard083OddFull_eq_live :
    suzukiDF6D4FixedGridShard083OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 384) := by
  have h := suzukiDF6D4FixedGridShard083Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard083OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 384)) at h
  exact h

def suzukiDF6D4FixedGridShard083OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard083OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard083OddDotSoundness i.val
        suzukiDF6D4FixedGridShard083OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard083OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard083OddResidualData =
      suzukiDF6D4FixedGridShard083OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard083Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard083OddResidualData =
    suzukiDF6D4FixedGridShard083OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard083OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard083OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 384 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 384) := by
    rw [suzukiDF6D4FixedGridShard083OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 384
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083OddDotSoundness i
          suzukiDF6D4FixedGridShard083OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 384) := by
    simpa [suzukiDF6D4FixedGridShard083OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard083OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 384) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard083OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 384) := by
    rw [suzukiDF6D4FixedGridShard083OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 384
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard083OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard083OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard083OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard083OddDotSoundness i
            suzukiDF6D4FixedGridShard083OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard083OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
