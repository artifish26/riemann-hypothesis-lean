import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard155Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard155Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard155EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard155EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 155 k) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard155EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 155 k)) at h
  exact h

def suzukiDF6D4FixedGridShard155EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard155EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard155EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard155EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard155EvenComparisonData)

theorem suzukiDF6D4FixedGridShard155EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard155EvenSolveData =
      suzukiDF6D4FixedGridShard155EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard155Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard155EvenSolveData =
    suzukiDF6D4FixedGridShard155EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard155EvenCross_eq_live :
    suzukiDF6D4FixedGridShard155EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 155) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard155EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 155)) at h
  exact h

theorem suzukiDF6D4FixedGridShard155EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard155EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 155 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 155 k) := by
    rw [suzukiDF6D4FixedGridShard155EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 155 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155EvenDotSoundness i
          suzukiDF6D4FixedGridShard155EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 155 k) := by
    simpa [suzukiDF6D4FixedGridShard155EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard155EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 155 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 155) := by
    rw [suzukiDF6D4FixedGridShard155EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 155)
  rw [suzukiDF6D4FixedGridShard155EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard155EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard155EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard155EvenDotSoundness i
            suzukiDF6D4FixedGridShard155EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard155EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard155OddComparison_eq_live :
    suzukiDF6D4FixedGridShard155OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 155 k) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard155OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 155 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard155OddCross_eq_live :
    suzukiDF6D4FixedGridShard155OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 155) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard155OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 155)) at h
  exact h

def suzukiDF6D4FixedGridShard155OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard155OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard155OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard155OddDotSoundness i.val
      suzukiDF6D4FixedGridShard155OddComparisonData)

theorem suzukiDF6D4FixedGridShard155OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard155OddSolveData =
      suzukiDF6D4FixedGridShard155OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard155Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard155OddSolveData =
    suzukiDF6D4FixedGridShard155OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard155OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard155OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 155 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 155 k) := by
    rw [suzukiDF6D4FixedGridShard155OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 155 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155OddDotSoundness i
          suzukiDF6D4FixedGridShard155OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 155 k) := by
    simpa [suzukiDF6D4FixedGridShard155OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard155OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 155 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 155) := by
    rw [suzukiDF6D4FixedGridShard155OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 155)
  rw [suzukiDF6D4FixedGridShard155OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard155OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard155OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard155OddDotSoundness i
            suzukiDF6D4FixedGridShard155OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard155OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard155EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard155EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 456) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard155EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 456)) at h
  exact h

theorem suzukiDF6D4FixedGridShard155EvenFull_eq_live :
    suzukiDF6D4FixedGridShard155EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 456) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard155EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 456)) at h
  exact h

def suzukiDF6D4FixedGridShard155EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard155EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard155EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard155EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard155EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard155EvenResidualData =
      suzukiDF6D4FixedGridShard155EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard155Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard155EvenResidualData =
    suzukiDF6D4FixedGridShard155EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard155EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard155EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 456 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 456) := by
    rw [suzukiDF6D4FixedGridShard155EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 456
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155EvenDotSoundness i
          suzukiDF6D4FixedGridShard155EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 456) := by
    simpa [suzukiDF6D4FixedGridShard155EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard155EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 456) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 456) := by
    rw [suzukiDF6D4FixedGridShard155EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 456
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard155EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard155EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard155EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard155EvenDotSoundness i
            suzukiDF6D4FixedGridShard155EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard155EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard155OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard155OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 456) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard155OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 456)) at h
  exact h

theorem suzukiDF6D4FixedGridShard155OddFull_eq_live :
    suzukiDF6D4FixedGridShard155OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 456) := by
  have h := suzukiDF6D4FixedGridShard155Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard155OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 456)) at h
  exact h

def suzukiDF6D4FixedGridShard155OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard155OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard155OddDotSoundness i.val
        suzukiDF6D4FixedGridShard155OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard155OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard155OddResidualData =
      suzukiDF6D4FixedGridShard155OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard155Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard155OddResidualData =
    suzukiDF6D4FixedGridShard155OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard155OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard155OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 456 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 456) := by
    rw [suzukiDF6D4FixedGridShard155OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 456
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155OddDotSoundness i
          suzukiDF6D4FixedGridShard155OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 456) := by
    simpa [suzukiDF6D4FixedGridShard155OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard155OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 456) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard155OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 456) := by
    rw [suzukiDF6D4FixedGridShard155OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 456
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard155OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard155OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard155OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard155OddDotSoundness i
            suzukiDF6D4FixedGridShard155OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard155OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
