import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard238Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard238Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard238EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard238EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 238 k) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard238EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 238 k)) at h
  exact h

def suzukiDF6D4FixedGridShard238EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard238EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard238EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard238EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard238EvenComparisonData)

theorem suzukiDF6D4FixedGridShard238EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard238EvenSolveData =
      suzukiDF6D4FixedGridShard238EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard238Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard238EvenSolveData =
    suzukiDF6D4FixedGridShard238EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard238EvenCross_eq_live :
    suzukiDF6D4FixedGridShard238EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 238) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard238EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 238)) at h
  exact h

theorem suzukiDF6D4FixedGridShard238EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard238EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 238 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 238 k) := by
    rw [suzukiDF6D4FixedGridShard238EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 238 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238EvenDotSoundness i
          suzukiDF6D4FixedGridShard238EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 238 k) := by
    simpa [suzukiDF6D4FixedGridShard238EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard238EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 238 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 238) := by
    rw [suzukiDF6D4FixedGridShard238EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 238)
  rw [suzukiDF6D4FixedGridShard238EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard238EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard238EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard238EvenDotSoundness i
            suzukiDF6D4FixedGridShard238EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard238EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard238OddComparison_eq_live :
    suzukiDF6D4FixedGridShard238OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 238 k) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard238OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 238 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard238OddCross_eq_live :
    suzukiDF6D4FixedGridShard238OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 238) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard238OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 238)) at h
  exact h

def suzukiDF6D4FixedGridShard238OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard238OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard238OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard238OddDotSoundness i.val
      suzukiDF6D4FixedGridShard238OddComparisonData)

theorem suzukiDF6D4FixedGridShard238OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard238OddSolveData =
      suzukiDF6D4FixedGridShard238OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard238Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard238OddSolveData =
    suzukiDF6D4FixedGridShard238OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard238OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard238OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 238 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 238 k) := by
    rw [suzukiDF6D4FixedGridShard238OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 238 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238OddDotSoundness i
          suzukiDF6D4FixedGridShard238OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 238 k) := by
    simpa [suzukiDF6D4FixedGridShard238OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard238OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 238 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 238) := by
    rw [suzukiDF6D4FixedGridShard238OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 238)
  rw [suzukiDF6D4FixedGridShard238OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard238OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard238OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard238OddDotSoundness i
            suzukiDF6D4FixedGridShard238OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard238OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard238EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard238EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 539) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard238EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 539)) at h
  exact h

theorem suzukiDF6D4FixedGridShard238EvenFull_eq_live :
    suzukiDF6D4FixedGridShard238EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 539) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard238EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 539)) at h
  exact h

def suzukiDF6D4FixedGridShard238EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard238EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard238EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard238EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard238EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard238EvenResidualData =
      suzukiDF6D4FixedGridShard238EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard238Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard238EvenResidualData =
    suzukiDF6D4FixedGridShard238EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard238EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard238EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 539 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 539) := by
    rw [suzukiDF6D4FixedGridShard238EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 539
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238EvenDotSoundness i
          suzukiDF6D4FixedGridShard238EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 539) := by
    simpa [suzukiDF6D4FixedGridShard238EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard238EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 539) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 539) := by
    rw [suzukiDF6D4FixedGridShard238EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 539
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard238EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard238EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard238EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard238EvenDotSoundness i
            suzukiDF6D4FixedGridShard238EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard238EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard238OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard238OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 539) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard238OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 539)) at h
  exact h

theorem suzukiDF6D4FixedGridShard238OddFull_eq_live :
    suzukiDF6D4FixedGridShard238OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 539) := by
  have h := suzukiDF6D4FixedGridShard238Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard238OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 539)) at h
  exact h

def suzukiDF6D4FixedGridShard238OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard238OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard238OddDotSoundness i.val
        suzukiDF6D4FixedGridShard238OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard238OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard238OddResidualData =
      suzukiDF6D4FixedGridShard238OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard238Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard238OddResidualData =
    suzukiDF6D4FixedGridShard238OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard238OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard238OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 539 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 539) := by
    rw [suzukiDF6D4FixedGridShard238OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 539
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238OddDotSoundness i
          suzukiDF6D4FixedGridShard238OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 539) := by
    simpa [suzukiDF6D4FixedGridShard238OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard238OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 539) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard238OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 539) := by
    rw [suzukiDF6D4FixedGridShard238OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 539
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard238OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard238OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard238OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard238OddDotSoundness i
            suzukiDF6D4FixedGridShard238OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard238OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
