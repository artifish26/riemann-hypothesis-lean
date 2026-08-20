import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard012Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard012Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard012EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard012EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 12 k) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard012EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 12 k)) at h
  exact h

def suzukiDF6D4FixedGridShard012EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard012EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard012EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard012EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard012EvenComparisonData)

theorem suzukiDF6D4FixedGridShard012EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard012EvenSolveData =
      suzukiDF6D4FixedGridShard012EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard012Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard012EvenSolveData =
    suzukiDF6D4FixedGridShard012EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard012EvenCross_eq_live :
    suzukiDF6D4FixedGridShard012EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 12) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard012EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 12)) at h
  exact h

theorem suzukiDF6D4FixedGridShard012EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard012EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 12 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 12 k) := by
    rw [suzukiDF6D4FixedGridShard012EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 12 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012EvenDotSoundness i
          suzukiDF6D4FixedGridShard012EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 12 k) := by
    simpa [suzukiDF6D4FixedGridShard012EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard012EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 12 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 12) := by
    rw [suzukiDF6D4FixedGridShard012EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 12)
  rw [suzukiDF6D4FixedGridShard012EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard012EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard012EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard012EvenDotSoundness i
            suzukiDF6D4FixedGridShard012EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard012EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard012OddComparison_eq_live :
    suzukiDF6D4FixedGridShard012OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 12 k) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard012OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 12 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard012OddCross_eq_live :
    suzukiDF6D4FixedGridShard012OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 12) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard012OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 12)) at h
  exact h

def suzukiDF6D4FixedGridShard012OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard012OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard012OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard012OddDotSoundness i.val
      suzukiDF6D4FixedGridShard012OddComparisonData)

theorem suzukiDF6D4FixedGridShard012OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard012OddSolveData =
      suzukiDF6D4FixedGridShard012OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard012Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard012OddSolveData =
    suzukiDF6D4FixedGridShard012OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard012OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard012OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 12 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 12 k) := by
    rw [suzukiDF6D4FixedGridShard012OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 12 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012OddDotSoundness i
          suzukiDF6D4FixedGridShard012OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 12 k) := by
    simpa [suzukiDF6D4FixedGridShard012OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard012OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 12 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 12) := by
    rw [suzukiDF6D4FixedGridShard012OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 12)
  rw [suzukiDF6D4FixedGridShard012OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard012OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard012OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard012OddDotSoundness i
            suzukiDF6D4FixedGridShard012OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard012OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard012EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard012EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 313) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard012EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 313)) at h
  exact h

theorem suzukiDF6D4FixedGridShard012EvenFull_eq_live :
    suzukiDF6D4FixedGridShard012EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 313) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard012EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 313)) at h
  exact h

def suzukiDF6D4FixedGridShard012EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard012EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard012EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard012EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard012EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard012EvenResidualData =
      suzukiDF6D4FixedGridShard012EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard012Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard012EvenResidualData =
    suzukiDF6D4FixedGridShard012EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard012EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard012EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 313 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 313) := by
    rw [suzukiDF6D4FixedGridShard012EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 313
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012EvenDotSoundness i
          suzukiDF6D4FixedGridShard012EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 313) := by
    simpa [suzukiDF6D4FixedGridShard012EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard012EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 313) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 313) := by
    rw [suzukiDF6D4FixedGridShard012EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 313
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard012EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard012EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard012EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard012EvenDotSoundness i
            suzukiDF6D4FixedGridShard012EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard012EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard012OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard012OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 313) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard012OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 313)) at h
  exact h

theorem suzukiDF6D4FixedGridShard012OddFull_eq_live :
    suzukiDF6D4FixedGridShard012OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 313) := by
  have h := suzukiDF6D4FixedGridShard012Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard012OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 313)) at h
  exact h

def suzukiDF6D4FixedGridShard012OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard012OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard012OddDotSoundness i.val
        suzukiDF6D4FixedGridShard012OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard012OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard012OddResidualData =
      suzukiDF6D4FixedGridShard012OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard012Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard012OddResidualData =
    suzukiDF6D4FixedGridShard012OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard012OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard012OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 313 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 313) := by
    rw [suzukiDF6D4FixedGridShard012OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 313
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012OddDotSoundness i
          suzukiDF6D4FixedGridShard012OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 313) := by
    simpa [suzukiDF6D4FixedGridShard012OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard012OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 313) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard012OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 313) := by
    rw [suzukiDF6D4FixedGridShard012OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 313
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard012OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard012OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard012OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard012OddDotSoundness i
            suzukiDF6D4FixedGridShard012OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard012OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
