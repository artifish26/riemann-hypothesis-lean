import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard183Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard183Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard183EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard183EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 183 k) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard183EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 183 k)) at h
  exact h

def suzukiDF6D4FixedGridShard183EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard183EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard183EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard183EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard183EvenComparisonData)

theorem suzukiDF6D4FixedGridShard183EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard183EvenSolveData =
      suzukiDF6D4FixedGridShard183EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard183Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard183EvenSolveData =
    suzukiDF6D4FixedGridShard183EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard183EvenCross_eq_live :
    suzukiDF6D4FixedGridShard183EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 183) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard183EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 183)) at h
  exact h

theorem suzukiDF6D4FixedGridShard183EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard183EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 183 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 183 k) := by
    rw [suzukiDF6D4FixedGridShard183EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 183 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183EvenDotSoundness i
          suzukiDF6D4FixedGridShard183EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 183 k) := by
    simpa [suzukiDF6D4FixedGridShard183EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard183EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 183 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 183) := by
    rw [suzukiDF6D4FixedGridShard183EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 183)
  rw [suzukiDF6D4FixedGridShard183EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard183EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard183EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard183EvenDotSoundness i
            suzukiDF6D4FixedGridShard183EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard183EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard183OddComparison_eq_live :
    suzukiDF6D4FixedGridShard183OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 183 k) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard183OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 183 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard183OddCross_eq_live :
    suzukiDF6D4FixedGridShard183OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 183) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard183OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 183)) at h
  exact h

def suzukiDF6D4FixedGridShard183OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard183OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard183OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard183OddDotSoundness i.val
      suzukiDF6D4FixedGridShard183OddComparisonData)

theorem suzukiDF6D4FixedGridShard183OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard183OddSolveData =
      suzukiDF6D4FixedGridShard183OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard183Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard183OddSolveData =
    suzukiDF6D4FixedGridShard183OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard183OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard183OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 183 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 183 k) := by
    rw [suzukiDF6D4FixedGridShard183OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 183 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183OddDotSoundness i
          suzukiDF6D4FixedGridShard183OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 183 k) := by
    simpa [suzukiDF6D4FixedGridShard183OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard183OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 183 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 183) := by
    rw [suzukiDF6D4FixedGridShard183OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 183)
  rw [suzukiDF6D4FixedGridShard183OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard183OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard183OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard183OddDotSoundness i
            suzukiDF6D4FixedGridShard183OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard183OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard183EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard183EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 484) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard183EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 484)) at h
  exact h

theorem suzukiDF6D4FixedGridShard183EvenFull_eq_live :
    suzukiDF6D4FixedGridShard183EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 484) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard183EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 484)) at h
  exact h

def suzukiDF6D4FixedGridShard183EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard183EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard183EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard183EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard183EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard183EvenResidualData =
      suzukiDF6D4FixedGridShard183EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard183Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard183EvenResidualData =
    suzukiDF6D4FixedGridShard183EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard183EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard183EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 484 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 484) := by
    rw [suzukiDF6D4FixedGridShard183EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 484
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183EvenDotSoundness i
          suzukiDF6D4FixedGridShard183EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 484) := by
    simpa [suzukiDF6D4FixedGridShard183EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard183EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 484) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 484) := by
    rw [suzukiDF6D4FixedGridShard183EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 484
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard183EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard183EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard183EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard183EvenDotSoundness i
            suzukiDF6D4FixedGridShard183EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard183EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard183OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard183OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 484) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard183OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 484)) at h
  exact h

theorem suzukiDF6D4FixedGridShard183OddFull_eq_live :
    suzukiDF6D4FixedGridShard183OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 484) := by
  have h := suzukiDF6D4FixedGridShard183Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard183OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 484)) at h
  exact h

def suzukiDF6D4FixedGridShard183OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard183OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard183OddDotSoundness i.val
        suzukiDF6D4FixedGridShard183OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard183OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard183OddResidualData =
      suzukiDF6D4FixedGridShard183OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard183Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard183OddResidualData =
    suzukiDF6D4FixedGridShard183OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard183OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard183OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 484 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 484) := by
    rw [suzukiDF6D4FixedGridShard183OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 484
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183OddDotSoundness i
          suzukiDF6D4FixedGridShard183OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 484) := by
    simpa [suzukiDF6D4FixedGridShard183OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard183OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 484) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard183OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 484) := by
    rw [suzukiDF6D4FixedGridShard183OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 484
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard183OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard183OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard183OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard183OddDotSoundness i
            suzukiDF6D4FixedGridShard183OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard183OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
