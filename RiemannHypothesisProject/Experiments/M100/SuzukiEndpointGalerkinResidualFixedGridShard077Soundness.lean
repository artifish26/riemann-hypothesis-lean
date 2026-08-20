import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard077Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard077Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard077EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard077EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 77 k) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard077EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 77 k)) at h
  exact h

def suzukiDF6D4FixedGridShard077EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard077EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard077EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard077EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard077EvenComparisonData)

theorem suzukiDF6D4FixedGridShard077EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard077EvenSolveData =
      suzukiDF6D4FixedGridShard077EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard077Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard077EvenSolveData =
    suzukiDF6D4FixedGridShard077EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard077EvenCross_eq_live :
    suzukiDF6D4FixedGridShard077EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 77) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard077EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 77)) at h
  exact h

theorem suzukiDF6D4FixedGridShard077EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard077EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 77 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 77 k) := by
    rw [suzukiDF6D4FixedGridShard077EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 77 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077EvenDotSoundness i
          suzukiDF6D4FixedGridShard077EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 77 k) := by
    simpa [suzukiDF6D4FixedGridShard077EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard077EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 77 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 77) := by
    rw [suzukiDF6D4FixedGridShard077EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 77)
  rw [suzukiDF6D4FixedGridShard077EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard077EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard077EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard077EvenDotSoundness i
            suzukiDF6D4FixedGridShard077EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard077EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard077OddComparison_eq_live :
    suzukiDF6D4FixedGridShard077OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 77 k) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard077OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 77 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard077OddCross_eq_live :
    suzukiDF6D4FixedGridShard077OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 77) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard077OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 77)) at h
  exact h

def suzukiDF6D4FixedGridShard077OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard077OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard077OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard077OddDotSoundness i.val
      suzukiDF6D4FixedGridShard077OddComparisonData)

theorem suzukiDF6D4FixedGridShard077OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard077OddSolveData =
      suzukiDF6D4FixedGridShard077OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard077Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard077OddSolveData =
    suzukiDF6D4FixedGridShard077OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard077OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard077OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 77 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 77 k) := by
    rw [suzukiDF6D4FixedGridShard077OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 77 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077OddDotSoundness i
          suzukiDF6D4FixedGridShard077OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 77 k) := by
    simpa [suzukiDF6D4FixedGridShard077OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard077OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 77 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 77) := by
    rw [suzukiDF6D4FixedGridShard077OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 77)
  rw [suzukiDF6D4FixedGridShard077OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard077OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard077OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard077OddDotSoundness i
            suzukiDF6D4FixedGridShard077OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard077OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard077EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard077EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 378) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard077EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 378)) at h
  exact h

theorem suzukiDF6D4FixedGridShard077EvenFull_eq_live :
    suzukiDF6D4FixedGridShard077EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 378) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard077EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 378)) at h
  exact h

def suzukiDF6D4FixedGridShard077EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard077EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard077EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard077EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard077EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard077EvenResidualData =
      suzukiDF6D4FixedGridShard077EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard077Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard077EvenResidualData =
    suzukiDF6D4FixedGridShard077EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard077EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard077EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 378 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 378) := by
    rw [suzukiDF6D4FixedGridShard077EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 378
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077EvenDotSoundness i
          suzukiDF6D4FixedGridShard077EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 378) := by
    simpa [suzukiDF6D4FixedGridShard077EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard077EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 378) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 378) := by
    rw [suzukiDF6D4FixedGridShard077EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 378
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard077EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard077EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard077EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard077EvenDotSoundness i
            suzukiDF6D4FixedGridShard077EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard077EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard077OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard077OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 378) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard077OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 378)) at h
  exact h

theorem suzukiDF6D4FixedGridShard077OddFull_eq_live :
    suzukiDF6D4FixedGridShard077OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 378) := by
  have h := suzukiDF6D4FixedGridShard077Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard077OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 378)) at h
  exact h

def suzukiDF6D4FixedGridShard077OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard077OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard077OddDotSoundness i.val
        suzukiDF6D4FixedGridShard077OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard077OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard077OddResidualData =
      suzukiDF6D4FixedGridShard077OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard077Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard077OddResidualData =
    suzukiDF6D4FixedGridShard077OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard077OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard077OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 378 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 378) := by
    rw [suzukiDF6D4FixedGridShard077OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 378
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077OddDotSoundness i
          suzukiDF6D4FixedGridShard077OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 378) := by
    simpa [suzukiDF6D4FixedGridShard077OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard077OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 378) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard077OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 378) := by
    rw [suzukiDF6D4FixedGridShard077OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 378
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard077OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard077OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard077OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard077OddDotSoundness i
            suzukiDF6D4FixedGridShard077OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard077OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
