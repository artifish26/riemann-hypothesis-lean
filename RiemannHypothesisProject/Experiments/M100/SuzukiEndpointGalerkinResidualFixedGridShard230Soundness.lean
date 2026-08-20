import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard230Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard230Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard230EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard230EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 230 k) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard230EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 230 k)) at h
  exact h

def suzukiDF6D4FixedGridShard230EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard230EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard230EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard230EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard230EvenComparisonData)

theorem suzukiDF6D4FixedGridShard230EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard230EvenSolveData =
      suzukiDF6D4FixedGridShard230EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard230Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard230EvenSolveData =
    suzukiDF6D4FixedGridShard230EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard230EvenCross_eq_live :
    suzukiDF6D4FixedGridShard230EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 230) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard230EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 230)) at h
  exact h

theorem suzukiDF6D4FixedGridShard230EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard230EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 230 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 230 k) := by
    rw [suzukiDF6D4FixedGridShard230EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 230 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230EvenDotSoundness i
          suzukiDF6D4FixedGridShard230EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 230 k) := by
    simpa [suzukiDF6D4FixedGridShard230EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard230EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 230 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 230) := by
    rw [suzukiDF6D4FixedGridShard230EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 230)
  rw [suzukiDF6D4FixedGridShard230EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard230EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard230EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard230EvenDotSoundness i
            suzukiDF6D4FixedGridShard230EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard230EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard230OddComparison_eq_live :
    suzukiDF6D4FixedGridShard230OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 230 k) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard230OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 230 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard230OddCross_eq_live :
    suzukiDF6D4FixedGridShard230OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 230) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard230OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 230)) at h
  exact h

def suzukiDF6D4FixedGridShard230OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard230OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard230OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard230OddDotSoundness i.val
      suzukiDF6D4FixedGridShard230OddComparisonData)

theorem suzukiDF6D4FixedGridShard230OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard230OddSolveData =
      suzukiDF6D4FixedGridShard230OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard230Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard230OddSolveData =
    suzukiDF6D4FixedGridShard230OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard230OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard230OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 230 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 230 k) := by
    rw [suzukiDF6D4FixedGridShard230OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 230 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230OddDotSoundness i
          suzukiDF6D4FixedGridShard230OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 230 k) := by
    simpa [suzukiDF6D4FixedGridShard230OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard230OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 230 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 230) := by
    rw [suzukiDF6D4FixedGridShard230OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 230)
  rw [suzukiDF6D4FixedGridShard230OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard230OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard230OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard230OddDotSoundness i
            suzukiDF6D4FixedGridShard230OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard230OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard230EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard230EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 531) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard230EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 531)) at h
  exact h

theorem suzukiDF6D4FixedGridShard230EvenFull_eq_live :
    suzukiDF6D4FixedGridShard230EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 531) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard230EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 531)) at h
  exact h

def suzukiDF6D4FixedGridShard230EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard230EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard230EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard230EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard230EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard230EvenResidualData =
      suzukiDF6D4FixedGridShard230EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard230Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard230EvenResidualData =
    suzukiDF6D4FixedGridShard230EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard230EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard230EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 531 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 531) := by
    rw [suzukiDF6D4FixedGridShard230EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 531
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230EvenDotSoundness i
          suzukiDF6D4FixedGridShard230EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 531) := by
    simpa [suzukiDF6D4FixedGridShard230EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard230EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 531) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 531) := by
    rw [suzukiDF6D4FixedGridShard230EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 531
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard230EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard230EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard230EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard230EvenDotSoundness i
            suzukiDF6D4FixedGridShard230EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard230EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard230OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard230OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 531) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard230OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 531)) at h
  exact h

theorem suzukiDF6D4FixedGridShard230OddFull_eq_live :
    suzukiDF6D4FixedGridShard230OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 531) := by
  have h := suzukiDF6D4FixedGridShard230Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard230OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 531)) at h
  exact h

def suzukiDF6D4FixedGridShard230OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard230OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard230OddDotSoundness i.val
        suzukiDF6D4FixedGridShard230OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard230OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard230OddResidualData =
      suzukiDF6D4FixedGridShard230OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard230Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard230OddResidualData =
    suzukiDF6D4FixedGridShard230OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard230OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard230OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 531 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 531) := by
    rw [suzukiDF6D4FixedGridShard230OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 531
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230OddDotSoundness i
          suzukiDF6D4FixedGridShard230OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 531) := by
    simpa [suzukiDF6D4FixedGridShard230OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard230OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 531) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard230OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 531) := by
    rw [suzukiDF6D4FixedGridShard230OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 531
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard230OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard230OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard230OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard230OddDotSoundness i
            suzukiDF6D4FixedGridShard230OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard230OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
