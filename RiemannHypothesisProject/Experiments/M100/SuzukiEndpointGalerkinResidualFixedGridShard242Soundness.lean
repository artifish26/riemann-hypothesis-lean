import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard242Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard242Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard242EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard242EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 242 k) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard242EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 242 k)) at h
  exact h

def suzukiDF6D4FixedGridShard242EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard242EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard242EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard242EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard242EvenComparisonData)

theorem suzukiDF6D4FixedGridShard242EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard242EvenSolveData =
      suzukiDF6D4FixedGridShard242EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard242Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard242EvenSolveData =
    suzukiDF6D4FixedGridShard242EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard242EvenCross_eq_live :
    suzukiDF6D4FixedGridShard242EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 242) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard242EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 242)) at h
  exact h

theorem suzukiDF6D4FixedGridShard242EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard242EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 242 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 242 k) := by
    rw [suzukiDF6D4FixedGridShard242EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 242 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242EvenDotSoundness i
          suzukiDF6D4FixedGridShard242EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 242 k) := by
    simpa [suzukiDF6D4FixedGridShard242EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard242EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 242 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 242) := by
    rw [suzukiDF6D4FixedGridShard242EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 242)
  rw [suzukiDF6D4FixedGridShard242EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard242EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard242EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard242EvenDotSoundness i
            suzukiDF6D4FixedGridShard242EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard242EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard242OddComparison_eq_live :
    suzukiDF6D4FixedGridShard242OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 242 k) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard242OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 242 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard242OddCross_eq_live :
    suzukiDF6D4FixedGridShard242OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 242) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard242OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 242)) at h
  exact h

def suzukiDF6D4FixedGridShard242OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard242OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard242OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard242OddDotSoundness i.val
      suzukiDF6D4FixedGridShard242OddComparisonData)

theorem suzukiDF6D4FixedGridShard242OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard242OddSolveData =
      suzukiDF6D4FixedGridShard242OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard242Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard242OddSolveData =
    suzukiDF6D4FixedGridShard242OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard242OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard242OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 242 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 242 k) := by
    rw [suzukiDF6D4FixedGridShard242OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 242 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242OddDotSoundness i
          suzukiDF6D4FixedGridShard242OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 242 k) := by
    simpa [suzukiDF6D4FixedGridShard242OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard242OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 242 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 242) := by
    rw [suzukiDF6D4FixedGridShard242OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 242)
  rw [suzukiDF6D4FixedGridShard242OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard242OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard242OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard242OddDotSoundness i
            suzukiDF6D4FixedGridShard242OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard242OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard242EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard242EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 543) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard242EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 543)) at h
  exact h

theorem suzukiDF6D4FixedGridShard242EvenFull_eq_live :
    suzukiDF6D4FixedGridShard242EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 543) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard242EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 543)) at h
  exact h

def suzukiDF6D4FixedGridShard242EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard242EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard242EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard242EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard242EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard242EvenResidualData =
      suzukiDF6D4FixedGridShard242EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard242Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard242EvenResidualData =
    suzukiDF6D4FixedGridShard242EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard242EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard242EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 543 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 543) := by
    rw [suzukiDF6D4FixedGridShard242EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 543
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242EvenDotSoundness i
          suzukiDF6D4FixedGridShard242EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 543) := by
    simpa [suzukiDF6D4FixedGridShard242EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard242EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 543) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 543) := by
    rw [suzukiDF6D4FixedGridShard242EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 543
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard242EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard242EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard242EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard242EvenDotSoundness i
            suzukiDF6D4FixedGridShard242EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard242EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard242OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard242OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 543) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard242OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 543)) at h
  exact h

theorem suzukiDF6D4FixedGridShard242OddFull_eq_live :
    suzukiDF6D4FixedGridShard242OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 543) := by
  have h := suzukiDF6D4FixedGridShard242Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard242OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 543)) at h
  exact h

def suzukiDF6D4FixedGridShard242OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard242OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard242OddDotSoundness i.val
        suzukiDF6D4FixedGridShard242OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard242OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard242OddResidualData =
      suzukiDF6D4FixedGridShard242OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard242Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard242OddResidualData =
    suzukiDF6D4FixedGridShard242OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard242OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard242OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 543 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 543) := by
    rw [suzukiDF6D4FixedGridShard242OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 543
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242OddDotSoundness i
          suzukiDF6D4FixedGridShard242OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 543) := by
    simpa [suzukiDF6D4FixedGridShard242OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard242OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 543) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard242OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 543) := by
    rw [suzukiDF6D4FixedGridShard242OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 543
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard242OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard242OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard242OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard242OddDotSoundness i
            suzukiDF6D4FixedGridShard242OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard242OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
