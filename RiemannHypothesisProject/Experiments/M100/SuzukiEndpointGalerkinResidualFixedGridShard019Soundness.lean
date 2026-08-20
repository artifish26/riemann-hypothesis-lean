import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard019Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard019Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard019EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard019EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 19 k) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard019EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 19 k)) at h
  exact h

def suzukiDF6D4FixedGridShard019EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard019EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard019EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard019EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard019EvenComparisonData)

theorem suzukiDF6D4FixedGridShard019EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard019EvenSolveData =
      suzukiDF6D4FixedGridShard019EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard019Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard019EvenSolveData =
    suzukiDF6D4FixedGridShard019EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard019EvenCross_eq_live :
    suzukiDF6D4FixedGridShard019EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 19) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard019EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 19)) at h
  exact h

theorem suzukiDF6D4FixedGridShard019EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard019EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 19 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 19 k) := by
    rw [suzukiDF6D4FixedGridShard019EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 19 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019EvenDotSoundness i
          suzukiDF6D4FixedGridShard019EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 19 k) := by
    simpa [suzukiDF6D4FixedGridShard019EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard019EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 19 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 19) := by
    rw [suzukiDF6D4FixedGridShard019EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 19)
  rw [suzukiDF6D4FixedGridShard019EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard019EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard019EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard019EvenDotSoundness i
            suzukiDF6D4FixedGridShard019EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard019EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard019OddComparison_eq_live :
    suzukiDF6D4FixedGridShard019OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 19 k) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard019OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 19 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard019OddCross_eq_live :
    suzukiDF6D4FixedGridShard019OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 19) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard019OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 19)) at h
  exact h

def suzukiDF6D4FixedGridShard019OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard019OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard019OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard019OddDotSoundness i.val
      suzukiDF6D4FixedGridShard019OddComparisonData)

theorem suzukiDF6D4FixedGridShard019OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard019OddSolveData =
      suzukiDF6D4FixedGridShard019OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard019Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard019OddSolveData =
    suzukiDF6D4FixedGridShard019OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard019OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard019OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 19 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 19 k) := by
    rw [suzukiDF6D4FixedGridShard019OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 19 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019OddDotSoundness i
          suzukiDF6D4FixedGridShard019OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 19 k) := by
    simpa [suzukiDF6D4FixedGridShard019OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard019OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 19 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 19) := by
    rw [suzukiDF6D4FixedGridShard019OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 19)
  rw [suzukiDF6D4FixedGridShard019OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard019OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard019OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard019OddDotSoundness i
            suzukiDF6D4FixedGridShard019OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard019OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard019EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard019EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 320) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard019EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 320)) at h
  exact h

theorem suzukiDF6D4FixedGridShard019EvenFull_eq_live :
    suzukiDF6D4FixedGridShard019EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 320) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard019EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 320)) at h
  exact h

def suzukiDF6D4FixedGridShard019EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard019EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard019EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard019EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard019EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard019EvenResidualData =
      suzukiDF6D4FixedGridShard019EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard019Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard019EvenResidualData =
    suzukiDF6D4FixedGridShard019EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard019EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard019EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 320 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 320) := by
    rw [suzukiDF6D4FixedGridShard019EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 320
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019EvenDotSoundness i
          suzukiDF6D4FixedGridShard019EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 320) := by
    simpa [suzukiDF6D4FixedGridShard019EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard019EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 320) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 320) := by
    rw [suzukiDF6D4FixedGridShard019EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 320
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard019EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard019EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard019EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard019EvenDotSoundness i
            suzukiDF6D4FixedGridShard019EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard019EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard019OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard019OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 320) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard019OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 320)) at h
  exact h

theorem suzukiDF6D4FixedGridShard019OddFull_eq_live :
    suzukiDF6D4FixedGridShard019OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 320) := by
  have h := suzukiDF6D4FixedGridShard019Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard019OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 320)) at h
  exact h

def suzukiDF6D4FixedGridShard019OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard019OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard019OddDotSoundness i.val
        suzukiDF6D4FixedGridShard019OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard019OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard019OddResidualData =
      suzukiDF6D4FixedGridShard019OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard019Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard019OddResidualData =
    suzukiDF6D4FixedGridShard019OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard019OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard019OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 320 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 320) := by
    rw [suzukiDF6D4FixedGridShard019OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 320
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019OddDotSoundness i
          suzukiDF6D4FixedGridShard019OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 320) := by
    simpa [suzukiDF6D4FixedGridShard019OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard019OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 320) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard019OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 320) := by
    rw [suzukiDF6D4FixedGridShard019OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 320
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard019OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard019OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard019OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard019OddDotSoundness i
            suzukiDF6D4FixedGridShard019OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard019OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
