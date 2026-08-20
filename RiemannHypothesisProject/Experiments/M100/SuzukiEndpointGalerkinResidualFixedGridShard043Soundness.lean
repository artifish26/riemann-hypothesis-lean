import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard043Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard043Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard043EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard043EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 43 k) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard043EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 43 k)) at h
  exact h

def suzukiDF6D4FixedGridShard043EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard043EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard043EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard043EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard043EvenComparisonData)

theorem suzukiDF6D4FixedGridShard043EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard043EvenSolveData =
      suzukiDF6D4FixedGridShard043EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard043Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard043EvenSolveData =
    suzukiDF6D4FixedGridShard043EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard043EvenCross_eq_live :
    suzukiDF6D4FixedGridShard043EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 43) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard043EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 43)) at h
  exact h

theorem suzukiDF6D4FixedGridShard043EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard043EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 43 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 43 k) := by
    rw [suzukiDF6D4FixedGridShard043EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 43 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043EvenDotSoundness i
          suzukiDF6D4FixedGridShard043EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 43 k) := by
    simpa [suzukiDF6D4FixedGridShard043EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard043EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 43 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 43) := by
    rw [suzukiDF6D4FixedGridShard043EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 43)
  rw [suzukiDF6D4FixedGridShard043EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard043EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard043EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard043EvenDotSoundness i
            suzukiDF6D4FixedGridShard043EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard043EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard043OddComparison_eq_live :
    suzukiDF6D4FixedGridShard043OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 43 k) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard043OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 43 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard043OddCross_eq_live :
    suzukiDF6D4FixedGridShard043OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 43) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard043OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 43)) at h
  exact h

def suzukiDF6D4FixedGridShard043OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard043OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard043OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard043OddDotSoundness i.val
      suzukiDF6D4FixedGridShard043OddComparisonData)

theorem suzukiDF6D4FixedGridShard043OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard043OddSolveData =
      suzukiDF6D4FixedGridShard043OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard043Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard043OddSolveData =
    suzukiDF6D4FixedGridShard043OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard043OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard043OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 43 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 43 k) := by
    rw [suzukiDF6D4FixedGridShard043OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 43 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043OddDotSoundness i
          suzukiDF6D4FixedGridShard043OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 43 k) := by
    simpa [suzukiDF6D4FixedGridShard043OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard043OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 43 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 43) := by
    rw [suzukiDF6D4FixedGridShard043OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 43)
  rw [suzukiDF6D4FixedGridShard043OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard043OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard043OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard043OddDotSoundness i
            suzukiDF6D4FixedGridShard043OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard043OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard043EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard043EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 344) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard043EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 344)) at h
  exact h

theorem suzukiDF6D4FixedGridShard043EvenFull_eq_live :
    suzukiDF6D4FixedGridShard043EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 344) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard043EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 344)) at h
  exact h

def suzukiDF6D4FixedGridShard043EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard043EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard043EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard043EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard043EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard043EvenResidualData =
      suzukiDF6D4FixedGridShard043EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard043Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard043EvenResidualData =
    suzukiDF6D4FixedGridShard043EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard043EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard043EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 344 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 344) := by
    rw [suzukiDF6D4FixedGridShard043EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 344
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043EvenDotSoundness i
          suzukiDF6D4FixedGridShard043EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 344) := by
    simpa [suzukiDF6D4FixedGridShard043EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard043EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 344) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 344) := by
    rw [suzukiDF6D4FixedGridShard043EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 344
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard043EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard043EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard043EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard043EvenDotSoundness i
            suzukiDF6D4FixedGridShard043EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard043EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard043OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard043OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 344) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard043OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 344)) at h
  exact h

theorem suzukiDF6D4FixedGridShard043OddFull_eq_live :
    suzukiDF6D4FixedGridShard043OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 344) := by
  have h := suzukiDF6D4FixedGridShard043Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard043OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 344)) at h
  exact h

def suzukiDF6D4FixedGridShard043OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard043OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard043OddDotSoundness i.val
        suzukiDF6D4FixedGridShard043OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard043OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard043OddResidualData =
      suzukiDF6D4FixedGridShard043OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard043Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard043OddResidualData =
    suzukiDF6D4FixedGridShard043OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard043OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard043OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 344 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 344) := by
    rw [suzukiDF6D4FixedGridShard043OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 344
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043OddDotSoundness i
          suzukiDF6D4FixedGridShard043OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 344) := by
    simpa [suzukiDF6D4FixedGridShard043OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard043OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 344) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard043OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 344) := by
    rw [suzukiDF6D4FixedGridShard043OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 344
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard043OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard043OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard043OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard043OddDotSoundness i
            suzukiDF6D4FixedGridShard043OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard043OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
