import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard212Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard212Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard212EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard212EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 212 k) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard212EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 212 k)) at h
  exact h

def suzukiDF6D4FixedGridShard212EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard212EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard212EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard212EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard212EvenComparisonData)

theorem suzukiDF6D4FixedGridShard212EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard212EvenSolveData =
      suzukiDF6D4FixedGridShard212EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard212Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard212EvenSolveData =
    suzukiDF6D4FixedGridShard212EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard212EvenCross_eq_live :
    suzukiDF6D4FixedGridShard212EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 212) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard212EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 212)) at h
  exact h

theorem suzukiDF6D4FixedGridShard212EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard212EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 212 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 212 k) := by
    rw [suzukiDF6D4FixedGridShard212EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 212 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212EvenDotSoundness i
          suzukiDF6D4FixedGridShard212EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 212 k) := by
    simpa [suzukiDF6D4FixedGridShard212EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard212EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 212 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 212) := by
    rw [suzukiDF6D4FixedGridShard212EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 212)
  rw [suzukiDF6D4FixedGridShard212EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard212EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard212EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard212EvenDotSoundness i
            suzukiDF6D4FixedGridShard212EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard212EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard212OddComparison_eq_live :
    suzukiDF6D4FixedGridShard212OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 212 k) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard212OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 212 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard212OddCross_eq_live :
    suzukiDF6D4FixedGridShard212OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 212) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard212OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 212)) at h
  exact h

def suzukiDF6D4FixedGridShard212OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard212OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard212OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard212OddDotSoundness i.val
      suzukiDF6D4FixedGridShard212OddComparisonData)

theorem suzukiDF6D4FixedGridShard212OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard212OddSolveData =
      suzukiDF6D4FixedGridShard212OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard212Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard212OddSolveData =
    suzukiDF6D4FixedGridShard212OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard212OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard212OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 212 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 212 k) := by
    rw [suzukiDF6D4FixedGridShard212OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 212 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212OddDotSoundness i
          suzukiDF6D4FixedGridShard212OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 212 k) := by
    simpa [suzukiDF6D4FixedGridShard212OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard212OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 212 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 212) := by
    rw [suzukiDF6D4FixedGridShard212OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 212)
  rw [suzukiDF6D4FixedGridShard212OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard212OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard212OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard212OddDotSoundness i
            suzukiDF6D4FixedGridShard212OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard212OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard212EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard212EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 513) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard212EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 513)) at h
  exact h

theorem suzukiDF6D4FixedGridShard212EvenFull_eq_live :
    suzukiDF6D4FixedGridShard212EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 513) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard212EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 513)) at h
  exact h

def suzukiDF6D4FixedGridShard212EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard212EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard212EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard212EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard212EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard212EvenResidualData =
      suzukiDF6D4FixedGridShard212EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard212Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard212EvenResidualData =
    suzukiDF6D4FixedGridShard212EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard212EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard212EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 513 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 513) := by
    rw [suzukiDF6D4FixedGridShard212EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 513
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212EvenDotSoundness i
          suzukiDF6D4FixedGridShard212EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 513) := by
    simpa [suzukiDF6D4FixedGridShard212EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard212EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 513) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 513) := by
    rw [suzukiDF6D4FixedGridShard212EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 513
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard212EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard212EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard212EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard212EvenDotSoundness i
            suzukiDF6D4FixedGridShard212EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard212EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard212OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard212OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 513) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard212OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 513)) at h
  exact h

theorem suzukiDF6D4FixedGridShard212OddFull_eq_live :
    suzukiDF6D4FixedGridShard212OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 513) := by
  have h := suzukiDF6D4FixedGridShard212Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard212OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 513)) at h
  exact h

def suzukiDF6D4FixedGridShard212OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard212OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard212OddDotSoundness i.val
        suzukiDF6D4FixedGridShard212OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard212OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard212OddResidualData =
      suzukiDF6D4FixedGridShard212OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard212Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard212OddResidualData =
    suzukiDF6D4FixedGridShard212OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard212OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard212OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 513 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 513) := by
    rw [suzukiDF6D4FixedGridShard212OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 513
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212OddDotSoundness i
          suzukiDF6D4FixedGridShard212OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 513) := by
    simpa [suzukiDF6D4FixedGridShard212OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard212OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 513) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard212OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 513) := by
    rw [suzukiDF6D4FixedGridShard212OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 513
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard212OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard212OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard212OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard212OddDotSoundness i
            suzukiDF6D4FixedGridShard212OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard212OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
