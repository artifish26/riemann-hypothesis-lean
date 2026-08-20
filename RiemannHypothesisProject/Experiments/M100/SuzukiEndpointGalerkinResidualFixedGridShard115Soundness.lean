import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard115Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard115Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard115EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard115EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 115 k) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard115EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 115 k)) at h
  exact h

def suzukiDF6D4FixedGridShard115EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard115EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard115EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard115EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard115EvenComparisonData)

theorem suzukiDF6D4FixedGridShard115EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard115EvenSolveData =
      suzukiDF6D4FixedGridShard115EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard115Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard115EvenSolveData =
    suzukiDF6D4FixedGridShard115EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard115EvenCross_eq_live :
    suzukiDF6D4FixedGridShard115EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 115) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard115EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 115)) at h
  exact h

theorem suzukiDF6D4FixedGridShard115EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard115EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 115 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 115 k) := by
    rw [suzukiDF6D4FixedGridShard115EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 115 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115EvenDotSoundness i
          suzukiDF6D4FixedGridShard115EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 115 k) := by
    simpa [suzukiDF6D4FixedGridShard115EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard115EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 115 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 115) := by
    rw [suzukiDF6D4FixedGridShard115EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 115)
  rw [suzukiDF6D4FixedGridShard115EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard115EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard115EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard115EvenDotSoundness i
            suzukiDF6D4FixedGridShard115EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard115EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard115OddComparison_eq_live :
    suzukiDF6D4FixedGridShard115OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 115 k) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard115OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 115 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard115OddCross_eq_live :
    suzukiDF6D4FixedGridShard115OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 115) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard115OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 115)) at h
  exact h

def suzukiDF6D4FixedGridShard115OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard115OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard115OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard115OddDotSoundness i.val
      suzukiDF6D4FixedGridShard115OddComparisonData)

theorem suzukiDF6D4FixedGridShard115OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard115OddSolveData =
      suzukiDF6D4FixedGridShard115OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard115Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard115OddSolveData =
    suzukiDF6D4FixedGridShard115OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard115OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard115OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 115 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 115 k) := by
    rw [suzukiDF6D4FixedGridShard115OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 115 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115OddDotSoundness i
          suzukiDF6D4FixedGridShard115OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 115 k) := by
    simpa [suzukiDF6D4FixedGridShard115OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard115OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 115 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 115) := by
    rw [suzukiDF6D4FixedGridShard115OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 115)
  rw [suzukiDF6D4FixedGridShard115OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard115OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard115OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard115OddDotSoundness i
            suzukiDF6D4FixedGridShard115OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard115OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard115EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard115EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 416) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard115EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 416)) at h
  exact h

theorem suzukiDF6D4FixedGridShard115EvenFull_eq_live :
    suzukiDF6D4FixedGridShard115EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 416) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard115EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 416)) at h
  exact h

def suzukiDF6D4FixedGridShard115EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard115EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard115EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard115EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard115EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard115EvenResidualData =
      suzukiDF6D4FixedGridShard115EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard115Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard115EvenResidualData =
    suzukiDF6D4FixedGridShard115EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard115EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard115EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 416 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 416) := by
    rw [suzukiDF6D4FixedGridShard115EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 416
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115EvenDotSoundness i
          suzukiDF6D4FixedGridShard115EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 416) := by
    simpa [suzukiDF6D4FixedGridShard115EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard115EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 416) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 416) := by
    rw [suzukiDF6D4FixedGridShard115EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 416
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard115EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard115EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard115EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard115EvenDotSoundness i
            suzukiDF6D4FixedGridShard115EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard115EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard115OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard115OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 416) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard115OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 416)) at h
  exact h

theorem suzukiDF6D4FixedGridShard115OddFull_eq_live :
    suzukiDF6D4FixedGridShard115OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 416) := by
  have h := suzukiDF6D4FixedGridShard115Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard115OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 416)) at h
  exact h

def suzukiDF6D4FixedGridShard115OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard115OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard115OddDotSoundness i.val
        suzukiDF6D4FixedGridShard115OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard115OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard115OddResidualData =
      suzukiDF6D4FixedGridShard115OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard115Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard115OddResidualData =
    suzukiDF6D4FixedGridShard115OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard115OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard115OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 416 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 416) := by
    rw [suzukiDF6D4FixedGridShard115OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 416
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115OddDotSoundness i
          suzukiDF6D4FixedGridShard115OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 416) := by
    simpa [suzukiDF6D4FixedGridShard115OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard115OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 416) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard115OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 416) := by
    rw [suzukiDF6D4FixedGridShard115OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 416
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard115OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard115OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard115OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard115OddDotSoundness i
            suzukiDF6D4FixedGridShard115OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard115OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
