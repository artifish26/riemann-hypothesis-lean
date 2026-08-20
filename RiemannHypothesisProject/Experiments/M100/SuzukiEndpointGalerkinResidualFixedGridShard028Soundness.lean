import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard028Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard028Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard028EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard028EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 28 k) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard028EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 28 k)) at h
  exact h

def suzukiDF6D4FixedGridShard028EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard028EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard028EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard028EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard028EvenComparisonData)

theorem suzukiDF6D4FixedGridShard028EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard028EvenSolveData =
      suzukiDF6D4FixedGridShard028EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard028Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard028EvenSolveData =
    suzukiDF6D4FixedGridShard028EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard028EvenCross_eq_live :
    suzukiDF6D4FixedGridShard028EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 28) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard028EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 28)) at h
  exact h

theorem suzukiDF6D4FixedGridShard028EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard028EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 28 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 28 k) := by
    rw [suzukiDF6D4FixedGridShard028EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 28 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028EvenDotSoundness i
          suzukiDF6D4FixedGridShard028EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 28 k) := by
    simpa [suzukiDF6D4FixedGridShard028EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard028EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 28 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 28) := by
    rw [suzukiDF6D4FixedGridShard028EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 28)
  rw [suzukiDF6D4FixedGridShard028EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard028EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard028EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard028EvenDotSoundness i
            suzukiDF6D4FixedGridShard028EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard028EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard028OddComparison_eq_live :
    suzukiDF6D4FixedGridShard028OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 28 k) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard028OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 28 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard028OddCross_eq_live :
    suzukiDF6D4FixedGridShard028OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 28) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard028OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 28)) at h
  exact h

def suzukiDF6D4FixedGridShard028OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard028OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard028OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard028OddDotSoundness i.val
      suzukiDF6D4FixedGridShard028OddComparisonData)

theorem suzukiDF6D4FixedGridShard028OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard028OddSolveData =
      suzukiDF6D4FixedGridShard028OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard028Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard028OddSolveData =
    suzukiDF6D4FixedGridShard028OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard028OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard028OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 28 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 28 k) := by
    rw [suzukiDF6D4FixedGridShard028OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 28 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028OddDotSoundness i
          suzukiDF6D4FixedGridShard028OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 28 k) := by
    simpa [suzukiDF6D4FixedGridShard028OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard028OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 28 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 28) := by
    rw [suzukiDF6D4FixedGridShard028OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 28)
  rw [suzukiDF6D4FixedGridShard028OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard028OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard028OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard028OddDotSoundness i
            suzukiDF6D4FixedGridShard028OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard028OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard028EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard028EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 329) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard028EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 329)) at h
  exact h

theorem suzukiDF6D4FixedGridShard028EvenFull_eq_live :
    suzukiDF6D4FixedGridShard028EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 329) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard028EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 329)) at h
  exact h

def suzukiDF6D4FixedGridShard028EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard028EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard028EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard028EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard028EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard028EvenResidualData =
      suzukiDF6D4FixedGridShard028EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard028Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard028EvenResidualData =
    suzukiDF6D4FixedGridShard028EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard028EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard028EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 329 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 329) := by
    rw [suzukiDF6D4FixedGridShard028EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 329
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028EvenDotSoundness i
          suzukiDF6D4FixedGridShard028EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 329) := by
    simpa [suzukiDF6D4FixedGridShard028EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard028EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 329) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 329) := by
    rw [suzukiDF6D4FixedGridShard028EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 329
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard028EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard028EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard028EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard028EvenDotSoundness i
            suzukiDF6D4FixedGridShard028EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard028EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard028OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard028OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 329) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard028OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 329)) at h
  exact h

theorem suzukiDF6D4FixedGridShard028OddFull_eq_live :
    suzukiDF6D4FixedGridShard028OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 329) := by
  have h := suzukiDF6D4FixedGridShard028Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard028OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 329)) at h
  exact h

def suzukiDF6D4FixedGridShard028OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard028OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard028OddDotSoundness i.val
        suzukiDF6D4FixedGridShard028OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard028OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard028OddResidualData =
      suzukiDF6D4FixedGridShard028OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard028Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard028OddResidualData =
    suzukiDF6D4FixedGridShard028OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard028OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard028OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 329 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 329) := by
    rw [suzukiDF6D4FixedGridShard028OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 329
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028OddDotSoundness i
          suzukiDF6D4FixedGridShard028OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 329) := by
    simpa [suzukiDF6D4FixedGridShard028OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard028OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 329) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard028OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 329) := by
    rw [suzukiDF6D4FixedGridShard028OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 329
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard028OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard028OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard028OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard028OddDotSoundness i
            suzukiDF6D4FixedGridShard028OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard028OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
