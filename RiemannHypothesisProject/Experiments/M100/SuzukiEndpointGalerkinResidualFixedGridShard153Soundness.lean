import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard153Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard153Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard153EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard153EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 153 k) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard153EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 153 k)) at h
  exact h

def suzukiDF6D4FixedGridShard153EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard153EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard153EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard153EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard153EvenComparisonData)

theorem suzukiDF6D4FixedGridShard153EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard153EvenSolveData =
      suzukiDF6D4FixedGridShard153EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard153Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard153EvenSolveData =
    suzukiDF6D4FixedGridShard153EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard153EvenCross_eq_live :
    suzukiDF6D4FixedGridShard153EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 153) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard153EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 153)) at h
  exact h

theorem suzukiDF6D4FixedGridShard153EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard153EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 153 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 153 k) := by
    rw [suzukiDF6D4FixedGridShard153EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 153 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153EvenDotSoundness i
          suzukiDF6D4FixedGridShard153EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 153 k) := by
    simpa [suzukiDF6D4FixedGridShard153EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard153EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 153 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 153) := by
    rw [suzukiDF6D4FixedGridShard153EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 153)
  rw [suzukiDF6D4FixedGridShard153EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard153EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard153EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard153EvenDotSoundness i
            suzukiDF6D4FixedGridShard153EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard153EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard153OddComparison_eq_live :
    suzukiDF6D4FixedGridShard153OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 153 k) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard153OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 153 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard153OddCross_eq_live :
    suzukiDF6D4FixedGridShard153OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 153) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard153OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 153)) at h
  exact h

def suzukiDF6D4FixedGridShard153OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard153OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard153OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard153OddDotSoundness i.val
      suzukiDF6D4FixedGridShard153OddComparisonData)

theorem suzukiDF6D4FixedGridShard153OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard153OddSolveData =
      suzukiDF6D4FixedGridShard153OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard153Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard153OddSolveData =
    suzukiDF6D4FixedGridShard153OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard153OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard153OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 153 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 153 k) := by
    rw [suzukiDF6D4FixedGridShard153OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 153 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153OddDotSoundness i
          suzukiDF6D4FixedGridShard153OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 153 k) := by
    simpa [suzukiDF6D4FixedGridShard153OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard153OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 153 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 153) := by
    rw [suzukiDF6D4FixedGridShard153OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 153)
  rw [suzukiDF6D4FixedGridShard153OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard153OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard153OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard153OddDotSoundness i
            suzukiDF6D4FixedGridShard153OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard153OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard153EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard153EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 454) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard153EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 454)) at h
  exact h

theorem suzukiDF6D4FixedGridShard153EvenFull_eq_live :
    suzukiDF6D4FixedGridShard153EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 454) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard153EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 454)) at h
  exact h

def suzukiDF6D4FixedGridShard153EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard153EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard153EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard153EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard153EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard153EvenResidualData =
      suzukiDF6D4FixedGridShard153EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard153Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard153EvenResidualData =
    suzukiDF6D4FixedGridShard153EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard153EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard153EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 454 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 454) := by
    rw [suzukiDF6D4FixedGridShard153EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 454
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153EvenDotSoundness i
          suzukiDF6D4FixedGridShard153EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 454) := by
    simpa [suzukiDF6D4FixedGridShard153EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard153EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 454) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 454) := by
    rw [suzukiDF6D4FixedGridShard153EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 454
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard153EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard153EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard153EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard153EvenDotSoundness i
            suzukiDF6D4FixedGridShard153EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard153EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard153OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard153OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 454) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard153OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 454)) at h
  exact h

theorem suzukiDF6D4FixedGridShard153OddFull_eq_live :
    suzukiDF6D4FixedGridShard153OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 454) := by
  have h := suzukiDF6D4FixedGridShard153Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard153OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 454)) at h
  exact h

def suzukiDF6D4FixedGridShard153OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard153OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard153OddDotSoundness i.val
        suzukiDF6D4FixedGridShard153OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard153OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard153OddResidualData =
      suzukiDF6D4FixedGridShard153OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard153Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard153OddResidualData =
    suzukiDF6D4FixedGridShard153OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard153OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard153OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 454 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 454) := by
    rw [suzukiDF6D4FixedGridShard153OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 454
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153OddDotSoundness i
          suzukiDF6D4FixedGridShard153OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 454) := by
    simpa [suzukiDF6D4FixedGridShard153OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard153OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 454) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard153OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 454) := by
    rw [suzukiDF6D4FixedGridShard153OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 454
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard153OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard153OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard153OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard153OddDotSoundness i
            suzukiDF6D4FixedGridShard153OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard153OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
