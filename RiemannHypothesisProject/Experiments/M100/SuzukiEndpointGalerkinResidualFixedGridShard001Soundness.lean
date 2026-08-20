import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard001EvenComparison_eq_live :
    suzukiDF6D4FixedGridStage0ComparisonRow01Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 1 k) := by
  have h := suzukiDF6D4FixedGridStage0Shard01_valid.1
  change suzukiDF6D4FixedGridStage0ComparisonRow01Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 1 k)) at h
  exact h

def suzukiDF6D4FixedGridShard001EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard001EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridStage0SolveCrossRow01Data[i.val]!).sub
    (suzukiDF6D4FixedGridShard001EvenDotSoundness i.val
      suzukiDF6D4FixedGridStage0ComparisonRow01Data)

theorem suzukiDF6D4FixedGridShard001EvenSolve_eq_checked :
    suzukiDF6D4FixedGridStage1SolveRow01Data =
      suzukiDF6D4FixedGridShard001EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridStage1Shard01_valid.1
  change suzukiDF6D4FixedGridStage1SolveRow01Data =
    suzukiDF6D4FixedGridShard001EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard001EvenCross_eq_live :
    suzukiDF6D4FixedGridStage0SolveCrossRow01Data =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 1) := by
  have h := suzukiDF6D4FixedGridStage0Shard01_valid.2.1
  change suzukiDF6D4FixedGridStage0SolveCrossRow01Data =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 1)) at h
  exact h

theorem suzukiDF6D4FixedGridStage1SolveRow01Data_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridStage1SolveRow01Data[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 1 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0ComparisonRow01Data[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 1 k) := by
    rw [suzukiDF6D4FixedGridShard001EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 1 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard001EvenDotSoundness i
          suzukiDF6D4FixedGridStage0ComparisonRow01Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 1 k) := by
    simpa [suzukiDF6D4FixedGridShard001EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridStage0ComparisonRow01Data
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 1 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0SolveCrossRow01Data[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 1) := by
    rw [suzukiDF6D4FixedGridShard001EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 1)
  rw [suzukiDF6D4FixedGridShard001EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard001EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridStage0SolveCrossRow01Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard001EvenDotSoundness i
            suzukiDF6D4FixedGridStage0ComparisonRow01Data) := by
    simp [suzukiDF6D4FixedGridShard001EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard001OddComparison_eq_live :
    suzukiDF6D4FixedGridOddStage0ComparisonRow01Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 1 k) := by
  have h := suzukiDF6D4FixedGridOddStage0Shard01_valid.1
  change suzukiDF6D4FixedGridOddStage0ComparisonRow01Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 1 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard001OddCross_eq_live :
    suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 1) := by
  have h := suzukiDF6D4FixedGridOddStage0Shard01_valid.2.1
  change suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 1)) at h
  exact h

def suzukiDF6D4FixedGridShard001OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard001OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data[i.val]!).sub
    (suzukiDF6D4FixedGridShard001OddDotSoundness i.val
      suzukiDF6D4FixedGridOddStage0ComparisonRow01Data)

theorem suzukiDF6D4FixedGridShard001OddSolve_eq_checked :
    suzukiDF6D4FixedGridOddStage1SolveRow01Data =
      suzukiDF6D4FixedGridShard001OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridOddStage1Shard01_valid.1
  change suzukiDF6D4FixedGridOddStage1SolveRow01Data =
    suzukiDF6D4FixedGridShard001OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridOddStage1SolveRow01Data_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridOddStage1SolveRow01Data[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 1 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0ComparisonRow01Data[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 1 k) := by
    rw [suzukiDF6D4FixedGridShard001OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 1 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard001OddDotSoundness i
          suzukiDF6D4FixedGridOddStage0ComparisonRow01Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 1 k) := by
    simpa [suzukiDF6D4FixedGridShard001OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridOddStage0ComparisonRow01Data
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 1 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 1) := by
    rw [suzukiDF6D4FixedGridShard001OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 1)
  rw [suzukiDF6D4FixedGridShard001OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard001OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridOddStage0SolveCrossRow01Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard001OddDotSoundness i
            suzukiDF6D4FixedGridOddStage0ComparisonRow01Data) := by
    simp [suzukiDF6D4FixedGridShard001OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard001EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 302) := by
  have h := suzukiDF6D4FixedGridStage0Shard01_valid.2.2.1
  change suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 302)) at h
  exact h

theorem suzukiDF6D4FixedGridShard001EvenFull_eq_live :
    suzukiDF6D4FixedGridStage0FullPrefixRow302Data =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 302) := by
  have h := suzukiDF6D4FixedGridStage0Shard01_valid.2.2.2
  change suzukiDF6D4FixedGridStage0FullPrefixRow302Data =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 302)) at h
  exact h

def suzukiDF6D4FixedGridShard001EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridStage0FullPrefixRow302Data[i.val]!).sub
      (suzukiDF6D4FixedGridShard001EvenDotSoundness i.val
        suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data)

theorem suzukiDF6D4FixedGridShard001EvenResidual_eq_checked :
    suzukiDF6D4FixedGridStage1ResidualRow302Data =
      suzukiDF6D4FixedGridShard001EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridStage1Shard01_valid.2
  change suzukiDF6D4FixedGridStage1ResidualRow302Data =
    suzukiDF6D4FixedGridShard001EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridStage1ResidualRow302Data_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridStage1ResidualRow302Data[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 302 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 302) := by
    rw [suzukiDF6D4FixedGridShard001EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 302
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard001EvenDotSoundness i
          suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 302) := by
    simpa [suzukiDF6D4FixedGridShard001EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 302) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridStage0FullPrefixRow302Data[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 302) := by
    rw [suzukiDF6D4FixedGridShard001EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 302
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard001EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard001EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridStage0FullPrefixRow302Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard001EvenDotSoundness i
            suzukiDF6D4FixedGridStage0ComparisonPrefixRow302Data) := by
    simp [suzukiDF6D4FixedGridShard001EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard001OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 302) := by
  have h := suzukiDF6D4FixedGridOddStage0Shard01_valid.2.2.1
  change suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 302)) at h
  exact h

theorem suzukiDF6D4FixedGridShard001OddFull_eq_live :
    suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 302) := by
  have h := suzukiDF6D4FixedGridOddStage0Shard01_valid.2.2.2
  change suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 302)) at h
  exact h

def suzukiDF6D4FixedGridShard001OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data[i.val]!).sub
      (suzukiDF6D4FixedGridShard001OddDotSoundness i.val
        suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data)

theorem suzukiDF6D4FixedGridShard001OddResidual_eq_checked :
    suzukiDF6D4FixedGridOddStage1ResidualRow302Data =
      suzukiDF6D4FixedGridShard001OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridOddStage1Shard01_valid.2
  change suzukiDF6D4FixedGridOddStage1ResidualRow302Data =
    suzukiDF6D4FixedGridShard001OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridOddStage1ResidualRow302Data_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridOddStage1ResidualRow302Data[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 302 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 302) := by
    rw [suzukiDF6D4FixedGridShard001OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 302
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard001OddDotSoundness i
          suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 302) := by
    simpa [suzukiDF6D4FixedGridShard001OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 302) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 302) := by
    rw [suzukiDF6D4FixedGridShard001OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 302
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard001OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard001OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridOddStage0FullPrefixRow302Data[i.val]!).sub
          (suzukiDF6D4FixedGridShard001OddDotSoundness i
            suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow302Data) := by
    simp [suzukiDF6D4FixedGridShard001OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
