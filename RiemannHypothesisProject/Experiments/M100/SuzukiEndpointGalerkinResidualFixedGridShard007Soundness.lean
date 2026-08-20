import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard007Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard007Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard007EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard007EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 7 k) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard007EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 7 k)) at h
  exact h

def suzukiDF6D4FixedGridShard007EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard007EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard007EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard007EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard007EvenComparisonData)

theorem suzukiDF6D4FixedGridShard007EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard007EvenSolveData =
      suzukiDF6D4FixedGridShard007EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard007Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard007EvenSolveData =
    suzukiDF6D4FixedGridShard007EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard007EvenCross_eq_live :
    suzukiDF6D4FixedGridShard007EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 7) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard007EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 7)) at h
  exact h

theorem suzukiDF6D4FixedGridShard007EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard007EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 7 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 7 k) := by
    rw [suzukiDF6D4FixedGridShard007EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 7 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007EvenDotSoundness i
          suzukiDF6D4FixedGridShard007EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 7 k) := by
    simpa [suzukiDF6D4FixedGridShard007EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard007EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 7 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 7) := by
    rw [suzukiDF6D4FixedGridShard007EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 7)
  rw [suzukiDF6D4FixedGridShard007EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard007EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard007EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard007EvenDotSoundness i
            suzukiDF6D4FixedGridShard007EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard007EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard007OddComparison_eq_live :
    suzukiDF6D4FixedGridShard007OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 7 k) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard007OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 7 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard007OddCross_eq_live :
    suzukiDF6D4FixedGridShard007OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 7) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard007OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 7)) at h
  exact h

def suzukiDF6D4FixedGridShard007OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard007OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard007OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard007OddDotSoundness i.val
      suzukiDF6D4FixedGridShard007OddComparisonData)

theorem suzukiDF6D4FixedGridShard007OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard007OddSolveData =
      suzukiDF6D4FixedGridShard007OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard007Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard007OddSolveData =
    suzukiDF6D4FixedGridShard007OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard007OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard007OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 7 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 7 k) := by
    rw [suzukiDF6D4FixedGridShard007OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 7 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007OddDotSoundness i
          suzukiDF6D4FixedGridShard007OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 7 k) := by
    simpa [suzukiDF6D4FixedGridShard007OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard007OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 7 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 7) := by
    rw [suzukiDF6D4FixedGridShard007OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 7)
  rw [suzukiDF6D4FixedGridShard007OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard007OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard007OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard007OddDotSoundness i
            suzukiDF6D4FixedGridShard007OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard007OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard007EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard007EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 308) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard007EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 308)) at h
  exact h

theorem suzukiDF6D4FixedGridShard007EvenFull_eq_live :
    suzukiDF6D4FixedGridShard007EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 308) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard007EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 308)) at h
  exact h

def suzukiDF6D4FixedGridShard007EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard007EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard007EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard007EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard007EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard007EvenResidualData =
      suzukiDF6D4FixedGridShard007EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard007Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard007EvenResidualData =
    suzukiDF6D4FixedGridShard007EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard007EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard007EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 308 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 308) := by
    rw [suzukiDF6D4FixedGridShard007EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 308
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007EvenDotSoundness i
          suzukiDF6D4FixedGridShard007EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 308) := by
    simpa [suzukiDF6D4FixedGridShard007EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard007EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 308) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 308) := by
    rw [suzukiDF6D4FixedGridShard007EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 308
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard007EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard007EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard007EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard007EvenDotSoundness i
            suzukiDF6D4FixedGridShard007EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard007EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard007OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard007OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 308) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard007OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 308)) at h
  exact h

theorem suzukiDF6D4FixedGridShard007OddFull_eq_live :
    suzukiDF6D4FixedGridShard007OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 308) := by
  have h := suzukiDF6D4FixedGridShard007Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard007OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 308)) at h
  exact h

def suzukiDF6D4FixedGridShard007OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard007OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard007OddDotSoundness i.val
        suzukiDF6D4FixedGridShard007OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard007OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard007OddResidualData =
      suzukiDF6D4FixedGridShard007OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard007Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard007OddResidualData =
    suzukiDF6D4FixedGridShard007OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard007OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard007OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 308 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 308) := by
    rw [suzukiDF6D4FixedGridShard007OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 308
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007OddDotSoundness i
          suzukiDF6D4FixedGridShard007OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 308) := by
    simpa [suzukiDF6D4FixedGridShard007OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard007OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 308) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard007OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 308) := by
    rw [suzukiDF6D4FixedGridShard007OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 308
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard007OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard007OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard007OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard007OddDotSoundness i
            suzukiDF6D4FixedGridShard007OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard007OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
