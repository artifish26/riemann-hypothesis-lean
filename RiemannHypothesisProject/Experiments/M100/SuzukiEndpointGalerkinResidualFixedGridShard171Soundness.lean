import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard171Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard171Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard171EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard171EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 171 k) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard171EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 171 k)) at h
  exact h

def suzukiDF6D4FixedGridShard171EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard171EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard171EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard171EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard171EvenComparisonData)

theorem suzukiDF6D4FixedGridShard171EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard171EvenSolveData =
      suzukiDF6D4FixedGridShard171EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard171Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard171EvenSolveData =
    suzukiDF6D4FixedGridShard171EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard171EvenCross_eq_live :
    suzukiDF6D4FixedGridShard171EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 171) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard171EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 171)) at h
  exact h

theorem suzukiDF6D4FixedGridShard171EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard171EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 171 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 171 k) := by
    rw [suzukiDF6D4FixedGridShard171EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 171 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171EvenDotSoundness i
          suzukiDF6D4FixedGridShard171EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 171 k) := by
    simpa [suzukiDF6D4FixedGridShard171EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard171EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 171 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 171) := by
    rw [suzukiDF6D4FixedGridShard171EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 171)
  rw [suzukiDF6D4FixedGridShard171EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard171EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard171EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard171EvenDotSoundness i
            suzukiDF6D4FixedGridShard171EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard171EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard171OddComparison_eq_live :
    suzukiDF6D4FixedGridShard171OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 171 k) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard171OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 171 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard171OddCross_eq_live :
    suzukiDF6D4FixedGridShard171OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 171) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard171OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 171)) at h
  exact h

def suzukiDF6D4FixedGridShard171OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard171OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard171OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard171OddDotSoundness i.val
      suzukiDF6D4FixedGridShard171OddComparisonData)

theorem suzukiDF6D4FixedGridShard171OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard171OddSolveData =
      suzukiDF6D4FixedGridShard171OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard171Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard171OddSolveData =
    suzukiDF6D4FixedGridShard171OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard171OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard171OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 171 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 171 k) := by
    rw [suzukiDF6D4FixedGridShard171OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 171 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171OddDotSoundness i
          suzukiDF6D4FixedGridShard171OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 171 k) := by
    simpa [suzukiDF6D4FixedGridShard171OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard171OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 171 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 171) := by
    rw [suzukiDF6D4FixedGridShard171OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 171)
  rw [suzukiDF6D4FixedGridShard171OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard171OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard171OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard171OddDotSoundness i
            suzukiDF6D4FixedGridShard171OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard171OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard171EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard171EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 472) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard171EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 472)) at h
  exact h

theorem suzukiDF6D4FixedGridShard171EvenFull_eq_live :
    suzukiDF6D4FixedGridShard171EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 472) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard171EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 472)) at h
  exact h

def suzukiDF6D4FixedGridShard171EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard171EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard171EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard171EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard171EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard171EvenResidualData =
      suzukiDF6D4FixedGridShard171EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard171Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard171EvenResidualData =
    suzukiDF6D4FixedGridShard171EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard171EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard171EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 472 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 472) := by
    rw [suzukiDF6D4FixedGridShard171EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 472
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171EvenDotSoundness i
          suzukiDF6D4FixedGridShard171EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 472) := by
    simpa [suzukiDF6D4FixedGridShard171EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard171EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 472) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 472) := by
    rw [suzukiDF6D4FixedGridShard171EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 472
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard171EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard171EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard171EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard171EvenDotSoundness i
            suzukiDF6D4FixedGridShard171EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard171EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard171OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard171OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 472) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard171OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 472)) at h
  exact h

theorem suzukiDF6D4FixedGridShard171OddFull_eq_live :
    suzukiDF6D4FixedGridShard171OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 472) := by
  have h := suzukiDF6D4FixedGridShard171Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard171OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 472)) at h
  exact h

def suzukiDF6D4FixedGridShard171OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard171OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard171OddDotSoundness i.val
        suzukiDF6D4FixedGridShard171OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard171OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard171OddResidualData =
      suzukiDF6D4FixedGridShard171OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard171Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard171OddResidualData =
    suzukiDF6D4FixedGridShard171OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard171OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard171OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 472 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 472) := by
    rw [suzukiDF6D4FixedGridShard171OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 472
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171OddDotSoundness i
          suzukiDF6D4FixedGridShard171OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 472) := by
    simpa [suzukiDF6D4FixedGridShard171OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard171OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 472) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard171OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 472) := by
    rw [suzukiDF6D4FixedGridShard171OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 472
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard171OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard171OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard171OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard171OddDotSoundness i
            suzukiDF6D4FixedGridShard171OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard171OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
