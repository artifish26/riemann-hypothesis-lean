import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard073Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard073Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard073EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard073EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 73 k) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard073EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 73 k)) at h
  exact h

def suzukiDF6D4FixedGridShard073EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard073EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard073EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard073EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard073EvenComparisonData)

theorem suzukiDF6D4FixedGridShard073EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard073EvenSolveData =
      suzukiDF6D4FixedGridShard073EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard073Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard073EvenSolveData =
    suzukiDF6D4FixedGridShard073EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard073EvenCross_eq_live :
    suzukiDF6D4FixedGridShard073EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 73) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard073EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 73)) at h
  exact h

theorem suzukiDF6D4FixedGridShard073EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard073EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 73 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 73 k) := by
    rw [suzukiDF6D4FixedGridShard073EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 73 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073EvenDotSoundness i
          suzukiDF6D4FixedGridShard073EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 73 k) := by
    simpa [suzukiDF6D4FixedGridShard073EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard073EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 73 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 73) := by
    rw [suzukiDF6D4FixedGridShard073EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 73)
  rw [suzukiDF6D4FixedGridShard073EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard073EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard073EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard073EvenDotSoundness i
            suzukiDF6D4FixedGridShard073EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard073EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard073OddComparison_eq_live :
    suzukiDF6D4FixedGridShard073OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 73 k) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard073OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 73 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard073OddCross_eq_live :
    suzukiDF6D4FixedGridShard073OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 73) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard073OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 73)) at h
  exact h

def suzukiDF6D4FixedGridShard073OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard073OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard073OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard073OddDotSoundness i.val
      suzukiDF6D4FixedGridShard073OddComparisonData)

theorem suzukiDF6D4FixedGridShard073OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard073OddSolveData =
      suzukiDF6D4FixedGridShard073OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard073Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard073OddSolveData =
    suzukiDF6D4FixedGridShard073OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard073OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard073OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 73 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 73 k) := by
    rw [suzukiDF6D4FixedGridShard073OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 73 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073OddDotSoundness i
          suzukiDF6D4FixedGridShard073OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 73 k) := by
    simpa [suzukiDF6D4FixedGridShard073OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard073OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 73 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 73) := by
    rw [suzukiDF6D4FixedGridShard073OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 73)
  rw [suzukiDF6D4FixedGridShard073OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard073OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard073OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard073OddDotSoundness i
            suzukiDF6D4FixedGridShard073OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard073OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard073EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard073EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 374) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard073EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 374)) at h
  exact h

theorem suzukiDF6D4FixedGridShard073EvenFull_eq_live :
    suzukiDF6D4FixedGridShard073EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 374) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard073EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 374)) at h
  exact h

def suzukiDF6D4FixedGridShard073EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard073EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard073EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard073EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard073EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard073EvenResidualData =
      suzukiDF6D4FixedGridShard073EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard073Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard073EvenResidualData =
    suzukiDF6D4FixedGridShard073EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard073EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard073EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 374 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 374) := by
    rw [suzukiDF6D4FixedGridShard073EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 374
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073EvenDotSoundness i
          suzukiDF6D4FixedGridShard073EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 374) := by
    simpa [suzukiDF6D4FixedGridShard073EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard073EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 374) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 374) := by
    rw [suzukiDF6D4FixedGridShard073EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 374
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard073EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard073EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard073EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard073EvenDotSoundness i
            suzukiDF6D4FixedGridShard073EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard073EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard073OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard073OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 374) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard073OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 374)) at h
  exact h

theorem suzukiDF6D4FixedGridShard073OddFull_eq_live :
    suzukiDF6D4FixedGridShard073OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 374) := by
  have h := suzukiDF6D4FixedGridShard073Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard073OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 374)) at h
  exact h

def suzukiDF6D4FixedGridShard073OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard073OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard073OddDotSoundness i.val
        suzukiDF6D4FixedGridShard073OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard073OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard073OddResidualData =
      suzukiDF6D4FixedGridShard073OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard073Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard073OddResidualData =
    suzukiDF6D4FixedGridShard073OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard073OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard073OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 374 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 374) := by
    rw [suzukiDF6D4FixedGridShard073OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 374
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073OddDotSoundness i
          suzukiDF6D4FixedGridShard073OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 374) := by
    simpa [suzukiDF6D4FixedGridShard073OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard073OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 374) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard073OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 374) := by
    rw [suzukiDF6D4FixedGridShard073OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 374
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard073OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard073OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard073OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard073OddDotSoundness i
            suzukiDF6D4FixedGridShard073OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard073OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
