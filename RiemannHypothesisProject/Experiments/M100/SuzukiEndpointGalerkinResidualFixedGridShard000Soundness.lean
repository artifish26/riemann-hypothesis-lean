import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard000EvenComparison_eq_live :
    suzukiDF6D4FixedGridStage0ComparisonRow00Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 0 k) := by
  have h := suzukiDF6D4FixedGridStage0BoundedBlock_valid.1
  change suzukiDF6D4FixedGridStage0ComparisonRow00Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 0 k)) at h
  exact h

def suzukiDF6D4FixedGridShard000EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard000EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridStage0SolveCrossRow00Data[i.val]!).sub
    (suzukiDF6D4FixedGridShard000EvenDotSoundness i.val
      suzukiDF6D4FixedGridStage0ComparisonRow00Data)

theorem suzukiDF6D4FixedGridShard000EvenSolve_eq_checked :
    suzukiDF6D4FixedGridStage1SolveRow00Data =
      suzukiDF6D4FixedGridShard000EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridStage1BoundedBlock_valid.1
  change suzukiDF6D4FixedGridStage1SolveRow00Data =
    suzukiDF6D4FixedGridShard000EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard000EvenCross_eq_live :
    suzukiDF6D4FixedGridStage0SolveCrossRow00Data =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 0) := by
  have h := suzukiDF6D4FixedGridStage0BoundedBlock_valid.2.1
  change suzukiDF6D4FixedGridStage0SolveCrossRow00Data =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 0)) at h
  exact h

theorem suzukiDF6D4FixedGridStage1SolveRow00Data_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridStage1SolveRow00Data[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 0 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0ComparisonRow00Data[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 0 k) := by
    rw [suzukiDF6D4FixedGridShard000EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 0 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard000EvenDotSoundness i
          suzukiDF6D4FixedGridStage0ComparisonRow00Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 0 k) := by
    simpa [suzukiDF6D4FixedGridShard000EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridStage0ComparisonRow00Data
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 0 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0SolveCrossRow00Data[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 0) := by
    rw [suzukiDF6D4FixedGridShard000EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 0)
  rw [suzukiDF6D4FixedGridShard000EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard000EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridStage0SolveCrossRow00Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard000EvenDotSoundness i
            suzukiDF6D4FixedGridStage0ComparisonRow00Data) := by
    simp [suzukiDF6D4FixedGridShard000EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard000OddComparison_eq_live :
    suzukiDF6D4FixedGridOddStage0ComparisonRow00Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 0 k) := by
  have h := suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.1
  change suzukiDF6D4FixedGridOddStage0ComparisonRow00Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 0 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard000OddCross_eq_live :
    suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 0) := by
  have h := suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.2.1
  change suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 0)) at h
  exact h

def suzukiDF6D4FixedGridShard000OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard000OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data[i.val]!).sub
    (suzukiDF6D4FixedGridShard000OddDotSoundness i.val
      suzukiDF6D4FixedGridOddStage0ComparisonRow00Data)

theorem suzukiDF6D4FixedGridShard000OddSolve_eq_checked :
    suzukiDF6D4FixedGridOddStage1SolveRow00Data =
      suzukiDF6D4FixedGridShard000OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridOddStage1BoundedBlock_valid.1
  change suzukiDF6D4FixedGridOddStage1SolveRow00Data =
    suzukiDF6D4FixedGridShard000OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridOddStage1SolveRow00Data_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridOddStage1SolveRow00Data[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 0 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0ComparisonRow00Data[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 0 k) := by
    rw [suzukiDF6D4FixedGridShard000OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 0 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard000OddDotSoundness i
          suzukiDF6D4FixedGridOddStage0ComparisonRow00Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 0 k) := by
    simpa [suzukiDF6D4FixedGridShard000OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridOddStage0ComparisonRow00Data
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 0 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 0) := by
    rw [suzukiDF6D4FixedGridShard000OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 0)
  rw [suzukiDF6D4FixedGridShard000OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard000OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridOddStage0SolveCrossRow00Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard000OddDotSoundness i
            suzukiDF6D4FixedGridOddStage0ComparisonRow00Data) := by
    simp [suzukiDF6D4FixedGridShard000OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard000EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 301) := by
  have h := suzukiDF6D4FixedGridStage0BoundedBlock_valid.2.2.1
  change suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 301)) at h
  exact h

theorem suzukiDF6D4FixedGridShard000EvenFull_eq_live :
    suzukiDF6D4FixedGridStage0FullPrefixRow301Data =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 301) := by
  have h := suzukiDF6D4FixedGridStage0BoundedBlock_valid.2.2.2.1
  change suzukiDF6D4FixedGridStage0FullPrefixRow301Data =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 301)) at h
  exact h

def suzukiDF6D4FixedGridShard000EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridStage0FullPrefixRow301Data[i.val]!).sub
      (suzukiDF6D4FixedGridShard000EvenDotSoundness i.val
        suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data)

theorem suzukiDF6D4FixedGridShard000EvenResidual_eq_checked :
    suzukiDF6D4FixedGridStage1ResidualRow301Data =
      suzukiDF6D4FixedGridShard000EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridStage1BoundedBlock_valid.2
  change suzukiDF6D4FixedGridStage1ResidualRow301Data =
    suzukiDF6D4FixedGridShard000EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridStage1ResidualRow301Data_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridStage1ResidualRow301Data[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 301 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 301) := by
    rw [suzukiDF6D4FixedGridShard000EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 301
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard000EvenDotSoundness i
          suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 301) := by
    simpa [suzukiDF6D4FixedGridShard000EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 301) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0FullPrefixRow301Data[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 301) := by
    rw [suzukiDF6D4FixedGridShard000EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 301
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard000EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard000EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridStage0FullPrefixRow301Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard000EvenDotSoundness i
            suzukiDF6D4FixedGridStage0ComparisonPrefixRow301Data) := by
    simp [suzukiDF6D4FixedGridShard000EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard000OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 301) := by
  have h := suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.2.2.1
  change suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 301)) at h
  exact h

theorem suzukiDF6D4FixedGridShard000OddFull_eq_live :
    suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 301) := by
  have h := suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.2.2.2.1
  change suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 301)) at h
  exact h

def suzukiDF6D4FixedGridShard000OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data[i.val]!).sub
      (suzukiDF6D4FixedGridShard000OddDotSoundness i.val
        suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data)

theorem suzukiDF6D4FixedGridShard000OddResidual_eq_checked :
    suzukiDF6D4FixedGridOddStage1ResidualRow301Data =
      suzukiDF6D4FixedGridShard000OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridOddStage1BoundedBlock_valid.2
  change suzukiDF6D4FixedGridOddStage1ResidualRow301Data =
    suzukiDF6D4FixedGridShard000OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridOddStage1ResidualRow301Data_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridOddStage1ResidualRow301Data[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 301 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 301) := by
    rw [suzukiDF6D4FixedGridShard000OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 301
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard000OddDotSoundness i
          suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 301) := by
    simpa [suzukiDF6D4FixedGridShard000OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 301) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 301) := by
    rw [suzukiDF6D4FixedGridShard000OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 301
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard000OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard000OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridOddStage0FullPrefixRow301Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard000OddDotSoundness i
            suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow301Data) := by
    simp [suzukiDF6D4FixedGridShard000OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
