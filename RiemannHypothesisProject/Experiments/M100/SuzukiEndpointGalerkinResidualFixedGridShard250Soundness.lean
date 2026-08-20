import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard250Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard250Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard250EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard250EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 250 k) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard250EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 250 k)) at h
  exact h

def suzukiDF6D4FixedGridShard250EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard250EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard250EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard250EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard250EvenComparisonData)

theorem suzukiDF6D4FixedGridShard250EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard250EvenSolveData =
      suzukiDF6D4FixedGridShard250EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard250Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard250EvenSolveData =
    suzukiDF6D4FixedGridShard250EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard250EvenCross_eq_live :
    suzukiDF6D4FixedGridShard250EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 250) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard250EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 250)) at h
  exact h

theorem suzukiDF6D4FixedGridShard250EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard250EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 250 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 250 k) := by
    rw [suzukiDF6D4FixedGridShard250EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 250 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250EvenDotSoundness i
          suzukiDF6D4FixedGridShard250EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 250 k) := by
    simpa [suzukiDF6D4FixedGridShard250EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard250EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 250 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 250) := by
    rw [suzukiDF6D4FixedGridShard250EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 250)
  rw [suzukiDF6D4FixedGridShard250EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard250EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard250EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard250EvenDotSoundness i
            suzukiDF6D4FixedGridShard250EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard250EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard250OddComparison_eq_live :
    suzukiDF6D4FixedGridShard250OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 250 k) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard250OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 250 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard250OddCross_eq_live :
    suzukiDF6D4FixedGridShard250OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 250) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard250OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 250)) at h
  exact h

def suzukiDF6D4FixedGridShard250OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard250OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard250OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard250OddDotSoundness i.val
      suzukiDF6D4FixedGridShard250OddComparisonData)

theorem suzukiDF6D4FixedGridShard250OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard250OddSolveData =
      suzukiDF6D4FixedGridShard250OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard250Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard250OddSolveData =
    suzukiDF6D4FixedGridShard250OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard250OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard250OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 250 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 250 k) := by
    rw [suzukiDF6D4FixedGridShard250OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 250 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250OddDotSoundness i
          suzukiDF6D4FixedGridShard250OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 250 k) := by
    simpa [suzukiDF6D4FixedGridShard250OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard250OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 250 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 250) := by
    rw [suzukiDF6D4FixedGridShard250OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 250)
  rw [suzukiDF6D4FixedGridShard250OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard250OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard250OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard250OddDotSoundness i
            suzukiDF6D4FixedGridShard250OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard250OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard250EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard250EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 551) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard250EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 551)) at h
  exact h

theorem suzukiDF6D4FixedGridShard250EvenFull_eq_live :
    suzukiDF6D4FixedGridShard250EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 551) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard250EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 551)) at h
  exact h

def suzukiDF6D4FixedGridShard250EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard250EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard250EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard250EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard250EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard250EvenResidualData =
      suzukiDF6D4FixedGridShard250EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard250Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard250EvenResidualData =
    suzukiDF6D4FixedGridShard250EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard250EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard250EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 551 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 551) := by
    rw [suzukiDF6D4FixedGridShard250EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 551
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250EvenDotSoundness i
          suzukiDF6D4FixedGridShard250EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 551) := by
    simpa [suzukiDF6D4FixedGridShard250EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard250EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 551) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 551) := by
    rw [suzukiDF6D4FixedGridShard250EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 551
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard250EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard250EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard250EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard250EvenDotSoundness i
            suzukiDF6D4FixedGridShard250EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard250EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard250OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard250OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 551) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard250OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 551)) at h
  exact h

theorem suzukiDF6D4FixedGridShard250OddFull_eq_live :
    suzukiDF6D4FixedGridShard250OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 551) := by
  have h := suzukiDF6D4FixedGridShard250Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard250OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 551)) at h
  exact h

def suzukiDF6D4FixedGridShard250OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard250OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard250OddDotSoundness i.val
        suzukiDF6D4FixedGridShard250OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard250OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard250OddResidualData =
      suzukiDF6D4FixedGridShard250OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard250Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard250OddResidualData =
    suzukiDF6D4FixedGridShard250OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard250OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard250OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 551 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 551) := by
    rw [suzukiDF6D4FixedGridShard250OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 551
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250OddDotSoundness i
          suzukiDF6D4FixedGridShard250OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 551) := by
    simpa [suzukiDF6D4FixedGridShard250OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard250OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 551) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard250OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 551) := by
    rw [suzukiDF6D4FixedGridShard250OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 551
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard250OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard250OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard250OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard250OddDotSoundness i
            suzukiDF6D4FixedGridShard250OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard250OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
