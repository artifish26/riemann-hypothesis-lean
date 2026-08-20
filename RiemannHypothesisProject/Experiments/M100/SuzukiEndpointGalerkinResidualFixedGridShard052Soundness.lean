import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard052Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard052Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard052EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard052EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 52 k) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard052EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 52 k)) at h
  exact h

def suzukiDF6D4FixedGridShard052EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard052EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard052EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard052EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard052EvenComparisonData)

theorem suzukiDF6D4FixedGridShard052EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard052EvenSolveData =
      suzukiDF6D4FixedGridShard052EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard052Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard052EvenSolveData =
    suzukiDF6D4FixedGridShard052EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard052EvenCross_eq_live :
    suzukiDF6D4FixedGridShard052EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 52) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard052EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 52)) at h
  exact h

theorem suzukiDF6D4FixedGridShard052EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard052EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 52 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 52 k) := by
    rw [suzukiDF6D4FixedGridShard052EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 52 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052EvenDotSoundness i
          suzukiDF6D4FixedGridShard052EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 52 k) := by
    simpa [suzukiDF6D4FixedGridShard052EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard052EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 52 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 52) := by
    rw [suzukiDF6D4FixedGridShard052EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 52)
  rw [suzukiDF6D4FixedGridShard052EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard052EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard052EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard052EvenDotSoundness i
            suzukiDF6D4FixedGridShard052EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard052EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard052OddComparison_eq_live :
    suzukiDF6D4FixedGridShard052OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 52 k) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard052OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 52 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard052OddCross_eq_live :
    suzukiDF6D4FixedGridShard052OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 52) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard052OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 52)) at h
  exact h

def suzukiDF6D4FixedGridShard052OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard052OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard052OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard052OddDotSoundness i.val
      suzukiDF6D4FixedGridShard052OddComparisonData)

theorem suzukiDF6D4FixedGridShard052OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard052OddSolveData =
      suzukiDF6D4FixedGridShard052OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard052Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard052OddSolveData =
    suzukiDF6D4FixedGridShard052OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard052OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard052OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 52 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 52 k) := by
    rw [suzukiDF6D4FixedGridShard052OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 52 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052OddDotSoundness i
          suzukiDF6D4FixedGridShard052OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 52 k) := by
    simpa [suzukiDF6D4FixedGridShard052OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard052OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 52 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 52) := by
    rw [suzukiDF6D4FixedGridShard052OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 52)
  rw [suzukiDF6D4FixedGridShard052OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard052OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard052OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard052OddDotSoundness i
            suzukiDF6D4FixedGridShard052OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard052OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard052EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard052EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 353) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard052EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 353)) at h
  exact h

theorem suzukiDF6D4FixedGridShard052EvenFull_eq_live :
    suzukiDF6D4FixedGridShard052EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 353) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard052EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 353)) at h
  exact h

def suzukiDF6D4FixedGridShard052EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard052EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard052EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard052EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard052EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard052EvenResidualData =
      suzukiDF6D4FixedGridShard052EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard052Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard052EvenResidualData =
    suzukiDF6D4FixedGridShard052EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard052EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard052EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 353 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 353) := by
    rw [suzukiDF6D4FixedGridShard052EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 353
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052EvenDotSoundness i
          suzukiDF6D4FixedGridShard052EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 353) := by
    simpa [suzukiDF6D4FixedGridShard052EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard052EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 353) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 353) := by
    rw [suzukiDF6D4FixedGridShard052EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 353
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard052EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard052EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard052EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard052EvenDotSoundness i
            suzukiDF6D4FixedGridShard052EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard052EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard052OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard052OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 353) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard052OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 353)) at h
  exact h

theorem suzukiDF6D4FixedGridShard052OddFull_eq_live :
    suzukiDF6D4FixedGridShard052OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 353) := by
  have h := suzukiDF6D4FixedGridShard052Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard052OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 353)) at h
  exact h

def suzukiDF6D4FixedGridShard052OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard052OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard052OddDotSoundness i.val
        suzukiDF6D4FixedGridShard052OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard052OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard052OddResidualData =
      suzukiDF6D4FixedGridShard052OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard052Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard052OddResidualData =
    suzukiDF6D4FixedGridShard052OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard052OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard052OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 353 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 353) := by
    rw [suzukiDF6D4FixedGridShard052OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 353
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052OddDotSoundness i
          suzukiDF6D4FixedGridShard052OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 353) := by
    simpa [suzukiDF6D4FixedGridShard052OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard052OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 353) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard052OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 353) := by
    rw [suzukiDF6D4FixedGridShard052OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 353
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard052OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard052OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard052OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard052OddDotSoundness i
            suzukiDF6D4FixedGridShard052OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard052OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
