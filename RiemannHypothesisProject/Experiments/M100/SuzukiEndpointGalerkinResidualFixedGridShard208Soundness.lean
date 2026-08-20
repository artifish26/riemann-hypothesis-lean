import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard208Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard208Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard208EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard208EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 208 k) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard208EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 208 k)) at h
  exact h

def suzukiDF6D4FixedGridShard208EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard208EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard208EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard208EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard208EvenComparisonData)

theorem suzukiDF6D4FixedGridShard208EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard208EvenSolveData =
      suzukiDF6D4FixedGridShard208EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard208Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard208EvenSolveData =
    suzukiDF6D4FixedGridShard208EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard208EvenCross_eq_live :
    suzukiDF6D4FixedGridShard208EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 208) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard208EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 208)) at h
  exact h

theorem suzukiDF6D4FixedGridShard208EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard208EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 208 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 208 k) := by
    rw [suzukiDF6D4FixedGridShard208EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 208 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208EvenDotSoundness i
          suzukiDF6D4FixedGridShard208EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 208 k) := by
    simpa [suzukiDF6D4FixedGridShard208EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard208EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 208 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 208) := by
    rw [suzukiDF6D4FixedGridShard208EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 208)
  rw [suzukiDF6D4FixedGridShard208EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard208EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard208EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard208EvenDotSoundness i
            suzukiDF6D4FixedGridShard208EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard208EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard208OddComparison_eq_live :
    suzukiDF6D4FixedGridShard208OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 208 k) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard208OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 208 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard208OddCross_eq_live :
    suzukiDF6D4FixedGridShard208OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 208) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard208OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 208)) at h
  exact h

def suzukiDF6D4FixedGridShard208OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard208OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard208OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard208OddDotSoundness i.val
      suzukiDF6D4FixedGridShard208OddComparisonData)

theorem suzukiDF6D4FixedGridShard208OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard208OddSolveData =
      suzukiDF6D4FixedGridShard208OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard208Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard208OddSolveData =
    suzukiDF6D4FixedGridShard208OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard208OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard208OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 208 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 208 k) := by
    rw [suzukiDF6D4FixedGridShard208OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 208 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208OddDotSoundness i
          suzukiDF6D4FixedGridShard208OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 208 k) := by
    simpa [suzukiDF6D4FixedGridShard208OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard208OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 208 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 208) := by
    rw [suzukiDF6D4FixedGridShard208OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 208)
  rw [suzukiDF6D4FixedGridShard208OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard208OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard208OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard208OddDotSoundness i
            suzukiDF6D4FixedGridShard208OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard208OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard208EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard208EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 509) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard208EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 509)) at h
  exact h

theorem suzukiDF6D4FixedGridShard208EvenFull_eq_live :
    suzukiDF6D4FixedGridShard208EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 509) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard208EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 509)) at h
  exact h

def suzukiDF6D4FixedGridShard208EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard208EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard208EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard208EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard208EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard208EvenResidualData =
      suzukiDF6D4FixedGridShard208EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard208Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard208EvenResidualData =
    suzukiDF6D4FixedGridShard208EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard208EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard208EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 509 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 509) := by
    rw [suzukiDF6D4FixedGridShard208EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 509
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208EvenDotSoundness i
          suzukiDF6D4FixedGridShard208EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 509) := by
    simpa [suzukiDF6D4FixedGridShard208EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard208EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 509) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 509) := by
    rw [suzukiDF6D4FixedGridShard208EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 509
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard208EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard208EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard208EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard208EvenDotSoundness i
            suzukiDF6D4FixedGridShard208EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard208EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard208OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard208OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 509) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard208OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 509)) at h
  exact h

theorem suzukiDF6D4FixedGridShard208OddFull_eq_live :
    suzukiDF6D4FixedGridShard208OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 509) := by
  have h := suzukiDF6D4FixedGridShard208Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard208OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 509)) at h
  exact h

def suzukiDF6D4FixedGridShard208OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard208OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard208OddDotSoundness i.val
        suzukiDF6D4FixedGridShard208OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard208OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard208OddResidualData =
      suzukiDF6D4FixedGridShard208OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard208Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard208OddResidualData =
    suzukiDF6D4FixedGridShard208OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard208OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard208OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 509 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 509) := by
    rw [suzukiDF6D4FixedGridShard208OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 509
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208OddDotSoundness i
          suzukiDF6D4FixedGridShard208OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 509) := by
    simpa [suzukiDF6D4FixedGridShard208OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard208OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 509) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard208OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 509) := by
    rw [suzukiDF6D4FixedGridShard208OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 509
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard208OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard208OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard208OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard208OddDotSoundness i
            suzukiDF6D4FixedGridShard208OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard208OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
