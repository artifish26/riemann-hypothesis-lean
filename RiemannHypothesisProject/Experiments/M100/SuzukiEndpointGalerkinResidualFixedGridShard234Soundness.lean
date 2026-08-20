import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard234Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard234Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard234EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard234EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 234 k) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard234EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 234 k)) at h
  exact h

def suzukiDF6D4FixedGridShard234EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard234EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard234EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard234EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard234EvenComparisonData)

theorem suzukiDF6D4FixedGridShard234EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard234EvenSolveData =
      suzukiDF6D4FixedGridShard234EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard234Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard234EvenSolveData =
    suzukiDF6D4FixedGridShard234EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard234EvenCross_eq_live :
    suzukiDF6D4FixedGridShard234EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 234) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard234EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 234)) at h
  exact h

theorem suzukiDF6D4FixedGridShard234EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard234EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 234 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 234 k) := by
    rw [suzukiDF6D4FixedGridShard234EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 234 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234EvenDotSoundness i
          suzukiDF6D4FixedGridShard234EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 234 k) := by
    simpa [suzukiDF6D4FixedGridShard234EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard234EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 234 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 234) := by
    rw [suzukiDF6D4FixedGridShard234EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 234)
  rw [suzukiDF6D4FixedGridShard234EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard234EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard234EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard234EvenDotSoundness i
            suzukiDF6D4FixedGridShard234EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard234EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard234OddComparison_eq_live :
    suzukiDF6D4FixedGridShard234OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 234 k) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard234OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 234 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard234OddCross_eq_live :
    suzukiDF6D4FixedGridShard234OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 234) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard234OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 234)) at h
  exact h

def suzukiDF6D4FixedGridShard234OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard234OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard234OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard234OddDotSoundness i.val
      suzukiDF6D4FixedGridShard234OddComparisonData)

theorem suzukiDF6D4FixedGridShard234OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard234OddSolveData =
      suzukiDF6D4FixedGridShard234OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard234Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard234OddSolveData =
    suzukiDF6D4FixedGridShard234OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard234OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard234OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 234 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 234 k) := by
    rw [suzukiDF6D4FixedGridShard234OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 234 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234OddDotSoundness i
          suzukiDF6D4FixedGridShard234OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 234 k) := by
    simpa [suzukiDF6D4FixedGridShard234OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard234OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 234 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 234) := by
    rw [suzukiDF6D4FixedGridShard234OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 234)
  rw [suzukiDF6D4FixedGridShard234OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard234OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard234OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard234OddDotSoundness i
            suzukiDF6D4FixedGridShard234OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard234OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard234EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard234EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 535) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard234EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 535)) at h
  exact h

theorem suzukiDF6D4FixedGridShard234EvenFull_eq_live :
    suzukiDF6D4FixedGridShard234EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 535) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard234EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 535)) at h
  exact h

def suzukiDF6D4FixedGridShard234EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard234EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard234EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard234EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard234EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard234EvenResidualData =
      suzukiDF6D4FixedGridShard234EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard234Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard234EvenResidualData =
    suzukiDF6D4FixedGridShard234EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard234EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard234EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 535 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 535) := by
    rw [suzukiDF6D4FixedGridShard234EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 535
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234EvenDotSoundness i
          suzukiDF6D4FixedGridShard234EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 535) := by
    simpa [suzukiDF6D4FixedGridShard234EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard234EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 535) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 535) := by
    rw [suzukiDF6D4FixedGridShard234EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 535
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard234EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard234EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard234EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard234EvenDotSoundness i
            suzukiDF6D4FixedGridShard234EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard234EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard234OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard234OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 535) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard234OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 535)) at h
  exact h

theorem suzukiDF6D4FixedGridShard234OddFull_eq_live :
    suzukiDF6D4FixedGridShard234OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 535) := by
  have h := suzukiDF6D4FixedGridShard234Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard234OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 535)) at h
  exact h

def suzukiDF6D4FixedGridShard234OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard234OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard234OddDotSoundness i.val
        suzukiDF6D4FixedGridShard234OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard234OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard234OddResidualData =
      suzukiDF6D4FixedGridShard234OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard234Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard234OddResidualData =
    suzukiDF6D4FixedGridShard234OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard234OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard234OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 535 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 535) := by
    rw [suzukiDF6D4FixedGridShard234OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 535
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234OddDotSoundness i
          suzukiDF6D4FixedGridShard234OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 535) := by
    simpa [suzukiDF6D4FixedGridShard234OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard234OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 535) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard234OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 535) := by
    rw [suzukiDF6D4FixedGridShard234OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 535
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard234OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard234OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard234OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard234OddDotSoundness i
            suzukiDF6D4FixedGridShard234OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard234OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
