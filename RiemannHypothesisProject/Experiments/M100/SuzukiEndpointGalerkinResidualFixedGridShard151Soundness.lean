import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard151Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard151Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard151EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard151EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 151 k) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard151EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 151 k)) at h
  exact h

def suzukiDF6D4FixedGridShard151EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard151EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard151EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard151EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard151EvenComparisonData)

theorem suzukiDF6D4FixedGridShard151EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard151EvenSolveData =
      suzukiDF6D4FixedGridShard151EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard151Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard151EvenSolveData =
    suzukiDF6D4FixedGridShard151EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard151EvenCross_eq_live :
    suzukiDF6D4FixedGridShard151EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 151) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard151EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 151)) at h
  exact h

theorem suzukiDF6D4FixedGridShard151EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard151EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 151 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 151 k) := by
    rw [suzukiDF6D4FixedGridShard151EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 151 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151EvenDotSoundness i
          suzukiDF6D4FixedGridShard151EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 151 k) := by
    simpa [suzukiDF6D4FixedGridShard151EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard151EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 151 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 151) := by
    rw [suzukiDF6D4FixedGridShard151EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 151)
  rw [suzukiDF6D4FixedGridShard151EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard151EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard151EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard151EvenDotSoundness i
            suzukiDF6D4FixedGridShard151EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard151EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard151OddComparison_eq_live :
    suzukiDF6D4FixedGridShard151OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 151 k) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard151OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 151 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard151OddCross_eq_live :
    suzukiDF6D4FixedGridShard151OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 151) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard151OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 151)) at h
  exact h

def suzukiDF6D4FixedGridShard151OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard151OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard151OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard151OddDotSoundness i.val
      suzukiDF6D4FixedGridShard151OddComparisonData)

theorem suzukiDF6D4FixedGridShard151OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard151OddSolveData =
      suzukiDF6D4FixedGridShard151OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard151Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard151OddSolveData =
    suzukiDF6D4FixedGridShard151OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard151OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard151OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 151 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 151 k) := by
    rw [suzukiDF6D4FixedGridShard151OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 151 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151OddDotSoundness i
          suzukiDF6D4FixedGridShard151OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 151 k) := by
    simpa [suzukiDF6D4FixedGridShard151OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard151OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 151 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 151) := by
    rw [suzukiDF6D4FixedGridShard151OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 151)
  rw [suzukiDF6D4FixedGridShard151OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard151OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard151OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard151OddDotSoundness i
            suzukiDF6D4FixedGridShard151OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard151OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard151EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard151EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 452) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard151EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 452)) at h
  exact h

theorem suzukiDF6D4FixedGridShard151EvenFull_eq_live :
    suzukiDF6D4FixedGridShard151EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 452) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard151EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 452)) at h
  exact h

def suzukiDF6D4FixedGridShard151EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard151EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard151EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard151EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard151EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard151EvenResidualData =
      suzukiDF6D4FixedGridShard151EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard151Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard151EvenResidualData =
    suzukiDF6D4FixedGridShard151EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard151EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard151EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 452 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 452) := by
    rw [suzukiDF6D4FixedGridShard151EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 452
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151EvenDotSoundness i
          suzukiDF6D4FixedGridShard151EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 452) := by
    simpa [suzukiDF6D4FixedGridShard151EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard151EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 452) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 452) := by
    rw [suzukiDF6D4FixedGridShard151EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 452
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard151EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard151EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard151EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard151EvenDotSoundness i
            suzukiDF6D4FixedGridShard151EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard151EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard151OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard151OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 452) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard151OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 452)) at h
  exact h

theorem suzukiDF6D4FixedGridShard151OddFull_eq_live :
    suzukiDF6D4FixedGridShard151OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 452) := by
  have h := suzukiDF6D4FixedGridShard151Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard151OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 452)) at h
  exact h

def suzukiDF6D4FixedGridShard151OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard151OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard151OddDotSoundness i.val
        suzukiDF6D4FixedGridShard151OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard151OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard151OddResidualData =
      suzukiDF6D4FixedGridShard151OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard151Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard151OddResidualData =
    suzukiDF6D4FixedGridShard151OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard151OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard151OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 452 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 452) := by
    rw [suzukiDF6D4FixedGridShard151OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 452
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151OddDotSoundness i
          suzukiDF6D4FixedGridShard151OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 452) := by
    simpa [suzukiDF6D4FixedGridShard151OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard151OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 452) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard151OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 452) := by
    rw [suzukiDF6D4FixedGridShard151OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 452
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard151OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard151OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard151OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard151OddDotSoundness i
            suzukiDF6D4FixedGridShard151OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard151OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
