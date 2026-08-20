import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard173Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard173Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard173EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard173EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 173 k) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard173EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 173 k)) at h
  exact h

def suzukiDF6D4FixedGridShard173EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard173EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard173EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard173EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard173EvenComparisonData)

theorem suzukiDF6D4FixedGridShard173EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard173EvenSolveData =
      suzukiDF6D4FixedGridShard173EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard173Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard173EvenSolveData =
    suzukiDF6D4FixedGridShard173EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard173EvenCross_eq_live :
    suzukiDF6D4FixedGridShard173EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 173) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard173EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 173)) at h
  exact h

theorem suzukiDF6D4FixedGridShard173EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard173EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 173 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 173 k) := by
    rw [suzukiDF6D4FixedGridShard173EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 173 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173EvenDotSoundness i
          suzukiDF6D4FixedGridShard173EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 173 k) := by
    simpa [suzukiDF6D4FixedGridShard173EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard173EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 173 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 173) := by
    rw [suzukiDF6D4FixedGridShard173EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 173)
  rw [suzukiDF6D4FixedGridShard173EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard173EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard173EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard173EvenDotSoundness i
            suzukiDF6D4FixedGridShard173EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard173EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard173OddComparison_eq_live :
    suzukiDF6D4FixedGridShard173OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 173 k) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard173OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 173 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard173OddCross_eq_live :
    suzukiDF6D4FixedGridShard173OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 173) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard173OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 173)) at h
  exact h

def suzukiDF6D4FixedGridShard173OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard173OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard173OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard173OddDotSoundness i.val
      suzukiDF6D4FixedGridShard173OddComparisonData)

theorem suzukiDF6D4FixedGridShard173OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard173OddSolveData =
      suzukiDF6D4FixedGridShard173OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard173Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard173OddSolveData =
    suzukiDF6D4FixedGridShard173OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard173OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard173OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 173 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 173 k) := by
    rw [suzukiDF6D4FixedGridShard173OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 173 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173OddDotSoundness i
          suzukiDF6D4FixedGridShard173OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 173 k) := by
    simpa [suzukiDF6D4FixedGridShard173OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard173OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 173 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 173) := by
    rw [suzukiDF6D4FixedGridShard173OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 173)
  rw [suzukiDF6D4FixedGridShard173OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard173OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard173OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard173OddDotSoundness i
            suzukiDF6D4FixedGridShard173OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard173OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard173EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard173EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 474) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard173EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 474)) at h
  exact h

theorem suzukiDF6D4FixedGridShard173EvenFull_eq_live :
    suzukiDF6D4FixedGridShard173EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 474) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard173EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 474)) at h
  exact h

def suzukiDF6D4FixedGridShard173EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard173EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard173EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard173EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard173EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard173EvenResidualData =
      suzukiDF6D4FixedGridShard173EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard173Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard173EvenResidualData =
    suzukiDF6D4FixedGridShard173EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard173EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard173EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 474 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 474) := by
    rw [suzukiDF6D4FixedGridShard173EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 474
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173EvenDotSoundness i
          suzukiDF6D4FixedGridShard173EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 474) := by
    simpa [suzukiDF6D4FixedGridShard173EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard173EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 474) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 474) := by
    rw [suzukiDF6D4FixedGridShard173EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 474
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard173EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard173EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard173EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard173EvenDotSoundness i
            suzukiDF6D4FixedGridShard173EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard173EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard173OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard173OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 474) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard173OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 474)) at h
  exact h

theorem suzukiDF6D4FixedGridShard173OddFull_eq_live :
    suzukiDF6D4FixedGridShard173OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 474) := by
  have h := suzukiDF6D4FixedGridShard173Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard173OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 474)) at h
  exact h

def suzukiDF6D4FixedGridShard173OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard173OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard173OddDotSoundness i.val
        suzukiDF6D4FixedGridShard173OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard173OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard173OddResidualData =
      suzukiDF6D4FixedGridShard173OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard173Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard173OddResidualData =
    suzukiDF6D4FixedGridShard173OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard173OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard173OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 474 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 474) := by
    rw [suzukiDF6D4FixedGridShard173OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 474
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173OddDotSoundness i
          suzukiDF6D4FixedGridShard173OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 474) := by
    simpa [suzukiDF6D4FixedGridShard173OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard173OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 474) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard173OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 474) := by
    rw [suzukiDF6D4FixedGridShard173OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 474
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard173OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard173OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard173OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard173OddDotSoundness i
            suzukiDF6D4FixedGridShard173OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard173OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
