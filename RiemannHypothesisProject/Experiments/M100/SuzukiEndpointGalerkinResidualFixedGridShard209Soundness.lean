import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard209Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard209Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard209EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard209EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 209 k) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard209EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 209 k)) at h
  exact h

def suzukiDF6D4FixedGridShard209EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard209EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard209EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard209EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard209EvenComparisonData)

theorem suzukiDF6D4FixedGridShard209EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard209EvenSolveData =
      suzukiDF6D4FixedGridShard209EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard209Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard209EvenSolveData =
    suzukiDF6D4FixedGridShard209EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard209EvenCross_eq_live :
    suzukiDF6D4FixedGridShard209EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 209) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard209EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 209)) at h
  exact h

theorem suzukiDF6D4FixedGridShard209EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard209EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 209 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 209 k) := by
    rw [suzukiDF6D4FixedGridShard209EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 209 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209EvenDotSoundness i
          suzukiDF6D4FixedGridShard209EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 209 k) := by
    simpa [suzukiDF6D4FixedGridShard209EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard209EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 209 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 209) := by
    rw [suzukiDF6D4FixedGridShard209EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 209)
  rw [suzukiDF6D4FixedGridShard209EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard209EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard209EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard209EvenDotSoundness i
            suzukiDF6D4FixedGridShard209EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard209EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard209OddComparison_eq_live :
    suzukiDF6D4FixedGridShard209OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 209 k) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard209OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 209 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard209OddCross_eq_live :
    suzukiDF6D4FixedGridShard209OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 209) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard209OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 209)) at h
  exact h

def suzukiDF6D4FixedGridShard209OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard209OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard209OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard209OddDotSoundness i.val
      suzukiDF6D4FixedGridShard209OddComparisonData)

theorem suzukiDF6D4FixedGridShard209OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard209OddSolveData =
      suzukiDF6D4FixedGridShard209OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard209Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard209OddSolveData =
    suzukiDF6D4FixedGridShard209OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard209OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard209OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 209 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 209 k) := by
    rw [suzukiDF6D4FixedGridShard209OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 209 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209OddDotSoundness i
          suzukiDF6D4FixedGridShard209OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 209 k) := by
    simpa [suzukiDF6D4FixedGridShard209OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard209OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 209 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 209) := by
    rw [suzukiDF6D4FixedGridShard209OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 209)
  rw [suzukiDF6D4FixedGridShard209OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard209OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard209OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard209OddDotSoundness i
            suzukiDF6D4FixedGridShard209OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard209OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard209EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard209EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 510) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard209EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 510)) at h
  exact h

theorem suzukiDF6D4FixedGridShard209EvenFull_eq_live :
    suzukiDF6D4FixedGridShard209EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 510) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard209EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 510)) at h
  exact h

def suzukiDF6D4FixedGridShard209EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard209EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard209EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard209EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard209EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard209EvenResidualData =
      suzukiDF6D4FixedGridShard209EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard209Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard209EvenResidualData =
    suzukiDF6D4FixedGridShard209EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard209EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard209EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 510 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 510) := by
    rw [suzukiDF6D4FixedGridShard209EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 510
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209EvenDotSoundness i
          suzukiDF6D4FixedGridShard209EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 510) := by
    simpa [suzukiDF6D4FixedGridShard209EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard209EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 510) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 510) := by
    rw [suzukiDF6D4FixedGridShard209EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 510
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard209EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard209EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard209EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard209EvenDotSoundness i
            suzukiDF6D4FixedGridShard209EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard209EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard209OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard209OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 510) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard209OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 510)) at h
  exact h

theorem suzukiDF6D4FixedGridShard209OddFull_eq_live :
    suzukiDF6D4FixedGridShard209OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 510) := by
  have h := suzukiDF6D4FixedGridShard209Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard209OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 510)) at h
  exact h

def suzukiDF6D4FixedGridShard209OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard209OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard209OddDotSoundness i.val
        suzukiDF6D4FixedGridShard209OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard209OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard209OddResidualData =
      suzukiDF6D4FixedGridShard209OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard209Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard209OddResidualData =
    suzukiDF6D4FixedGridShard209OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard209OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard209OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 510 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 510) := by
    rw [suzukiDF6D4FixedGridShard209OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 510
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209OddDotSoundness i
          suzukiDF6D4FixedGridShard209OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 510) := by
    simpa [suzukiDF6D4FixedGridShard209OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard209OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 510) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard209OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 510) := by
    rw [suzukiDF6D4FixedGridShard209OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 510
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard209OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard209OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard209OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard209OddDotSoundness i
            suzukiDF6D4FixedGridShard209OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard209OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
