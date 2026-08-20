import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard089Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard089Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard089EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard089EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 89 k) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard089EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 89 k)) at h
  exact h

def suzukiDF6D4FixedGridShard089EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard089EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard089EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard089EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard089EvenComparisonData)

theorem suzukiDF6D4FixedGridShard089EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard089EvenSolveData =
      suzukiDF6D4FixedGridShard089EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard089Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard089EvenSolveData =
    suzukiDF6D4FixedGridShard089EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard089EvenCross_eq_live :
    suzukiDF6D4FixedGridShard089EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 89) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard089EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 89)) at h
  exact h

theorem suzukiDF6D4FixedGridShard089EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard089EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 89 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 89 k) := by
    rw [suzukiDF6D4FixedGridShard089EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 89 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089EvenDotSoundness i
          suzukiDF6D4FixedGridShard089EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 89 k) := by
    simpa [suzukiDF6D4FixedGridShard089EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard089EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 89 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 89) := by
    rw [suzukiDF6D4FixedGridShard089EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 89)
  rw [suzukiDF6D4FixedGridShard089EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard089EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard089EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard089EvenDotSoundness i
            suzukiDF6D4FixedGridShard089EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard089EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard089OddComparison_eq_live :
    suzukiDF6D4FixedGridShard089OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 89 k) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard089OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 89 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard089OddCross_eq_live :
    suzukiDF6D4FixedGridShard089OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 89) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard089OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 89)) at h
  exact h

def suzukiDF6D4FixedGridShard089OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard089OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard089OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard089OddDotSoundness i.val
      suzukiDF6D4FixedGridShard089OddComparisonData)

theorem suzukiDF6D4FixedGridShard089OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard089OddSolveData =
      suzukiDF6D4FixedGridShard089OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard089Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard089OddSolveData =
    suzukiDF6D4FixedGridShard089OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard089OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard089OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 89 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 89 k) := by
    rw [suzukiDF6D4FixedGridShard089OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 89 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089OddDotSoundness i
          suzukiDF6D4FixedGridShard089OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 89 k) := by
    simpa [suzukiDF6D4FixedGridShard089OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard089OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 89 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 89) := by
    rw [suzukiDF6D4FixedGridShard089OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 89)
  rw [suzukiDF6D4FixedGridShard089OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard089OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard089OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard089OddDotSoundness i
            suzukiDF6D4FixedGridShard089OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard089OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard089EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard089EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 390) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard089EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 390)) at h
  exact h

theorem suzukiDF6D4FixedGridShard089EvenFull_eq_live :
    suzukiDF6D4FixedGridShard089EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 390) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard089EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 390)) at h
  exact h

def suzukiDF6D4FixedGridShard089EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard089EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard089EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard089EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard089EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard089EvenResidualData =
      suzukiDF6D4FixedGridShard089EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard089Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard089EvenResidualData =
    suzukiDF6D4FixedGridShard089EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard089EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard089EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 390 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 390) := by
    rw [suzukiDF6D4FixedGridShard089EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 390
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089EvenDotSoundness i
          suzukiDF6D4FixedGridShard089EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 390) := by
    simpa [suzukiDF6D4FixedGridShard089EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard089EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 390) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 390) := by
    rw [suzukiDF6D4FixedGridShard089EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 390
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard089EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard089EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard089EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard089EvenDotSoundness i
            suzukiDF6D4FixedGridShard089EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard089EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard089OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard089OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 390) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard089OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 390)) at h
  exact h

theorem suzukiDF6D4FixedGridShard089OddFull_eq_live :
    suzukiDF6D4FixedGridShard089OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 390) := by
  have h := suzukiDF6D4FixedGridShard089Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard089OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 390)) at h
  exact h

def suzukiDF6D4FixedGridShard089OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard089OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard089OddDotSoundness i.val
        suzukiDF6D4FixedGridShard089OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard089OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard089OddResidualData =
      suzukiDF6D4FixedGridShard089OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard089Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard089OddResidualData =
    suzukiDF6D4FixedGridShard089OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard089OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard089OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 390 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 390) := by
    rw [suzukiDF6D4FixedGridShard089OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 390
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089OddDotSoundness i
          suzukiDF6D4FixedGridShard089OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 390) := by
    simpa [suzukiDF6D4FixedGridShard089OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard089OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 390) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard089OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 390) := by
    rw [suzukiDF6D4FixedGridShard089OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 390
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard089OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard089OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard089OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard089OddDotSoundness i
            suzukiDF6D4FixedGridShard089OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard089OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
