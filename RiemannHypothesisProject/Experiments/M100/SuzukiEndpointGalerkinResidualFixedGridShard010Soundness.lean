import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard010Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard010Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard010EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard010EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 10 k) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard010EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 10 k)) at h
  exact h

def suzukiDF6D4FixedGridShard010EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard010EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard010EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard010EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard010EvenComparisonData)

theorem suzukiDF6D4FixedGridShard010EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard010EvenSolveData =
      suzukiDF6D4FixedGridShard010EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard010Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard010EvenSolveData =
    suzukiDF6D4FixedGridShard010EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard010EvenCross_eq_live :
    suzukiDF6D4FixedGridShard010EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 10) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard010EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 10)) at h
  exact h

theorem suzukiDF6D4FixedGridShard010EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard010EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 10 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 10 k) := by
    rw [suzukiDF6D4FixedGridShard010EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 10 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010EvenDotSoundness i
          suzukiDF6D4FixedGridShard010EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 10 k) := by
    simpa [suzukiDF6D4FixedGridShard010EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard010EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 10 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 10) := by
    rw [suzukiDF6D4FixedGridShard010EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 10)
  rw [suzukiDF6D4FixedGridShard010EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard010EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard010EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard010EvenDotSoundness i
            suzukiDF6D4FixedGridShard010EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard010EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard010OddComparison_eq_live :
    suzukiDF6D4FixedGridShard010OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 10 k) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard010OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 10 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard010OddCross_eq_live :
    suzukiDF6D4FixedGridShard010OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 10) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard010OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 10)) at h
  exact h

def suzukiDF6D4FixedGridShard010OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard010OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard010OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard010OddDotSoundness i.val
      suzukiDF6D4FixedGridShard010OddComparisonData)

theorem suzukiDF6D4FixedGridShard010OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard010OddSolveData =
      suzukiDF6D4FixedGridShard010OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard010Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard010OddSolveData =
    suzukiDF6D4FixedGridShard010OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard010OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard010OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 10 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 10 k) := by
    rw [suzukiDF6D4FixedGridShard010OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 10 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010OddDotSoundness i
          suzukiDF6D4FixedGridShard010OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 10 k) := by
    simpa [suzukiDF6D4FixedGridShard010OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard010OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 10 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 10) := by
    rw [suzukiDF6D4FixedGridShard010OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 10)
  rw [suzukiDF6D4FixedGridShard010OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard010OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard010OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard010OddDotSoundness i
            suzukiDF6D4FixedGridShard010OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard010OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard010EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard010EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 311) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard010EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 311)) at h
  exact h

theorem suzukiDF6D4FixedGridShard010EvenFull_eq_live :
    suzukiDF6D4FixedGridShard010EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 311) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard010EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 311)) at h
  exact h

def suzukiDF6D4FixedGridShard010EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard010EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard010EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard010EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard010EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard010EvenResidualData =
      suzukiDF6D4FixedGridShard010EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard010Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard010EvenResidualData =
    suzukiDF6D4FixedGridShard010EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard010EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard010EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 311 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 311) := by
    rw [suzukiDF6D4FixedGridShard010EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 311
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010EvenDotSoundness i
          suzukiDF6D4FixedGridShard010EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 311) := by
    simpa [suzukiDF6D4FixedGridShard010EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard010EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 311) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 311) := by
    rw [suzukiDF6D4FixedGridShard010EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 311
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard010EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard010EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard010EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard010EvenDotSoundness i
            suzukiDF6D4FixedGridShard010EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard010EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard010OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard010OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 311) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard010OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 311)) at h
  exact h

theorem suzukiDF6D4FixedGridShard010OddFull_eq_live :
    suzukiDF6D4FixedGridShard010OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 311) := by
  have h := suzukiDF6D4FixedGridShard010Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard010OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 311)) at h
  exact h

def suzukiDF6D4FixedGridShard010OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard010OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard010OddDotSoundness i.val
        suzukiDF6D4FixedGridShard010OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard010OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard010OddResidualData =
      suzukiDF6D4FixedGridShard010OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard010Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard010OddResidualData =
    suzukiDF6D4FixedGridShard010OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard010OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard010OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 311 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 311) := by
    rw [suzukiDF6D4FixedGridShard010OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 311
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010OddDotSoundness i
          suzukiDF6D4FixedGridShard010OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 311) := by
    simpa [suzukiDF6D4FixedGridShard010OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard010OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 311) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard010OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 311) := by
    rw [suzukiDF6D4FixedGridShard010OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 311
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard010OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard010OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard010OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard010OddDotSoundness i
            suzukiDF6D4FixedGridShard010OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard010OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
