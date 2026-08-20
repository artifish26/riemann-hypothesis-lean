import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard062Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard062Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard062EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard062EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 62 k) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard062EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 62 k)) at h
  exact h

def suzukiDF6D4FixedGridShard062EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard062EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard062EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard062EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard062EvenComparisonData)

theorem suzukiDF6D4FixedGridShard062EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard062EvenSolveData =
      suzukiDF6D4FixedGridShard062EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard062Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard062EvenSolveData =
    suzukiDF6D4FixedGridShard062EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard062EvenCross_eq_live :
    suzukiDF6D4FixedGridShard062EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 62) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard062EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 62)) at h
  exact h

theorem suzukiDF6D4FixedGridShard062EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard062EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 62 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 62 k) := by
    rw [suzukiDF6D4FixedGridShard062EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 62 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062EvenDotSoundness i
          suzukiDF6D4FixedGridShard062EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 62 k) := by
    simpa [suzukiDF6D4FixedGridShard062EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard062EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 62 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 62) := by
    rw [suzukiDF6D4FixedGridShard062EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 62)
  rw [suzukiDF6D4FixedGridShard062EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard062EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard062EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard062EvenDotSoundness i
            suzukiDF6D4FixedGridShard062EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard062EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard062OddComparison_eq_live :
    suzukiDF6D4FixedGridShard062OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 62 k) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard062OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 62 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard062OddCross_eq_live :
    suzukiDF6D4FixedGridShard062OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 62) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard062OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 62)) at h
  exact h

def suzukiDF6D4FixedGridShard062OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard062OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard062OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard062OddDotSoundness i.val
      suzukiDF6D4FixedGridShard062OddComparisonData)

theorem suzukiDF6D4FixedGridShard062OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard062OddSolveData =
      suzukiDF6D4FixedGridShard062OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard062Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard062OddSolveData =
    suzukiDF6D4FixedGridShard062OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard062OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard062OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 62 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 62 k) := by
    rw [suzukiDF6D4FixedGridShard062OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 62 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062OddDotSoundness i
          suzukiDF6D4FixedGridShard062OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 62 k) := by
    simpa [suzukiDF6D4FixedGridShard062OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard062OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 62 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 62) := by
    rw [suzukiDF6D4FixedGridShard062OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 62)
  rw [suzukiDF6D4FixedGridShard062OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard062OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard062OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard062OddDotSoundness i
            suzukiDF6D4FixedGridShard062OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard062OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard062EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard062EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 363) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard062EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 363)) at h
  exact h

theorem suzukiDF6D4FixedGridShard062EvenFull_eq_live :
    suzukiDF6D4FixedGridShard062EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 363) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard062EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 363)) at h
  exact h

def suzukiDF6D4FixedGridShard062EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard062EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard062EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard062EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard062EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard062EvenResidualData =
      suzukiDF6D4FixedGridShard062EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard062Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard062EvenResidualData =
    suzukiDF6D4FixedGridShard062EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard062EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard062EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 363 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 363) := by
    rw [suzukiDF6D4FixedGridShard062EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 363
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062EvenDotSoundness i
          suzukiDF6D4FixedGridShard062EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 363) := by
    simpa [suzukiDF6D4FixedGridShard062EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard062EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 363) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 363) := by
    rw [suzukiDF6D4FixedGridShard062EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 363
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard062EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard062EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard062EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard062EvenDotSoundness i
            suzukiDF6D4FixedGridShard062EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard062EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard062OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard062OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 363) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard062OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 363)) at h
  exact h

theorem suzukiDF6D4FixedGridShard062OddFull_eq_live :
    suzukiDF6D4FixedGridShard062OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 363) := by
  have h := suzukiDF6D4FixedGridShard062Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard062OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 363)) at h
  exact h

def suzukiDF6D4FixedGridShard062OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard062OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard062OddDotSoundness i.val
        suzukiDF6D4FixedGridShard062OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard062OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard062OddResidualData =
      suzukiDF6D4FixedGridShard062OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard062Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard062OddResidualData =
    suzukiDF6D4FixedGridShard062OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard062OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard062OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 363 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 363) := by
    rw [suzukiDF6D4FixedGridShard062OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 363
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062OddDotSoundness i
          suzukiDF6D4FixedGridShard062OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 363) := by
    simpa [suzukiDF6D4FixedGridShard062OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard062OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 363) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard062OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 363) := by
    rw [suzukiDF6D4FixedGridShard062OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 363
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard062OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard062OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard062OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard062OddDotSoundness i
            suzukiDF6D4FixedGridShard062OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard062OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
