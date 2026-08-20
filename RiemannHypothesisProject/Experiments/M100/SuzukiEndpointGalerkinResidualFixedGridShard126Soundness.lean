import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard126Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard126Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard126EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard126EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 126 k) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard126EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 126 k)) at h
  exact h

def suzukiDF6D4FixedGridShard126EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard126EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard126EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard126EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard126EvenComparisonData)

theorem suzukiDF6D4FixedGridShard126EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard126EvenSolveData =
      suzukiDF6D4FixedGridShard126EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard126Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard126EvenSolveData =
    suzukiDF6D4FixedGridShard126EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard126EvenCross_eq_live :
    suzukiDF6D4FixedGridShard126EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 126) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard126EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 126)) at h
  exact h

theorem suzukiDF6D4FixedGridShard126EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard126EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 126 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 126 k) := by
    rw [suzukiDF6D4FixedGridShard126EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 126 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126EvenDotSoundness i
          suzukiDF6D4FixedGridShard126EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 126 k) := by
    simpa [suzukiDF6D4FixedGridShard126EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard126EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 126 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 126) := by
    rw [suzukiDF6D4FixedGridShard126EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 126)
  rw [suzukiDF6D4FixedGridShard126EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard126EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard126EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard126EvenDotSoundness i
            suzukiDF6D4FixedGridShard126EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard126EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard126OddComparison_eq_live :
    suzukiDF6D4FixedGridShard126OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 126 k) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard126OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 126 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard126OddCross_eq_live :
    suzukiDF6D4FixedGridShard126OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 126) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard126OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 126)) at h
  exact h

def suzukiDF6D4FixedGridShard126OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard126OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard126OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard126OddDotSoundness i.val
      suzukiDF6D4FixedGridShard126OddComparisonData)

theorem suzukiDF6D4FixedGridShard126OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard126OddSolveData =
      suzukiDF6D4FixedGridShard126OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard126Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard126OddSolveData =
    suzukiDF6D4FixedGridShard126OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard126OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard126OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 126 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 126 k) := by
    rw [suzukiDF6D4FixedGridShard126OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 126 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126OddDotSoundness i
          suzukiDF6D4FixedGridShard126OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 126 k) := by
    simpa [suzukiDF6D4FixedGridShard126OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard126OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 126 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 126) := by
    rw [suzukiDF6D4FixedGridShard126OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 126)
  rw [suzukiDF6D4FixedGridShard126OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard126OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard126OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard126OddDotSoundness i
            suzukiDF6D4FixedGridShard126OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard126OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard126EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard126EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 427) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard126EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 427)) at h
  exact h

theorem suzukiDF6D4FixedGridShard126EvenFull_eq_live :
    suzukiDF6D4FixedGridShard126EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 427) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard126EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 427)) at h
  exact h

def suzukiDF6D4FixedGridShard126EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard126EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard126EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard126EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard126EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard126EvenResidualData =
      suzukiDF6D4FixedGridShard126EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard126Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard126EvenResidualData =
    suzukiDF6D4FixedGridShard126EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard126EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard126EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 427 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 427) := by
    rw [suzukiDF6D4FixedGridShard126EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 427
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126EvenDotSoundness i
          suzukiDF6D4FixedGridShard126EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 427) := by
    simpa [suzukiDF6D4FixedGridShard126EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard126EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 427) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 427) := by
    rw [suzukiDF6D4FixedGridShard126EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 427
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard126EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard126EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard126EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard126EvenDotSoundness i
            suzukiDF6D4FixedGridShard126EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard126EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard126OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard126OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 427) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard126OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 427)) at h
  exact h

theorem suzukiDF6D4FixedGridShard126OddFull_eq_live :
    suzukiDF6D4FixedGridShard126OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 427) := by
  have h := suzukiDF6D4FixedGridShard126Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard126OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 427)) at h
  exact h

def suzukiDF6D4FixedGridShard126OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard126OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard126OddDotSoundness i.val
        suzukiDF6D4FixedGridShard126OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard126OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard126OddResidualData =
      suzukiDF6D4FixedGridShard126OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard126Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard126OddResidualData =
    suzukiDF6D4FixedGridShard126OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard126OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard126OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 427 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 427) := by
    rw [suzukiDF6D4FixedGridShard126OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 427
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126OddDotSoundness i
          suzukiDF6D4FixedGridShard126OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 427) := by
    simpa [suzukiDF6D4FixedGridShard126OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard126OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 427) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard126OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 427) := by
    rw [suzukiDF6D4FixedGridShard126OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 427
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard126OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard126OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard126OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard126OddDotSoundness i
            suzukiDF6D4FixedGridShard126OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard126OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
