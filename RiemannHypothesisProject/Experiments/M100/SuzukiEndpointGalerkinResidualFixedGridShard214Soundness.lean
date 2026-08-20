import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard214Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard214Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard214EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard214EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 214 k) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard214EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 214 k)) at h
  exact h

def suzukiDF6D4FixedGridShard214EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard214EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard214EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard214EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard214EvenComparisonData)

theorem suzukiDF6D4FixedGridShard214EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard214EvenSolveData =
      suzukiDF6D4FixedGridShard214EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard214Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard214EvenSolveData =
    suzukiDF6D4FixedGridShard214EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard214EvenCross_eq_live :
    suzukiDF6D4FixedGridShard214EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 214) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard214EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 214)) at h
  exact h

theorem suzukiDF6D4FixedGridShard214EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard214EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 214 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 214 k) := by
    rw [suzukiDF6D4FixedGridShard214EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 214 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214EvenDotSoundness i
          suzukiDF6D4FixedGridShard214EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 214 k) := by
    simpa [suzukiDF6D4FixedGridShard214EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard214EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 214 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 214) := by
    rw [suzukiDF6D4FixedGridShard214EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 214)
  rw [suzukiDF6D4FixedGridShard214EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard214EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard214EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard214EvenDotSoundness i
            suzukiDF6D4FixedGridShard214EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard214EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard214OddComparison_eq_live :
    suzukiDF6D4FixedGridShard214OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 214 k) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard214OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 214 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard214OddCross_eq_live :
    suzukiDF6D4FixedGridShard214OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 214) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard214OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 214)) at h
  exact h

def suzukiDF6D4FixedGridShard214OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard214OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard214OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard214OddDotSoundness i.val
      suzukiDF6D4FixedGridShard214OddComparisonData)

theorem suzukiDF6D4FixedGridShard214OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard214OddSolveData =
      suzukiDF6D4FixedGridShard214OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard214Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard214OddSolveData =
    suzukiDF6D4FixedGridShard214OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard214OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard214OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 214 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 214 k) := by
    rw [suzukiDF6D4FixedGridShard214OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 214 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214OddDotSoundness i
          suzukiDF6D4FixedGridShard214OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 214 k) := by
    simpa [suzukiDF6D4FixedGridShard214OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard214OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 214 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 214) := by
    rw [suzukiDF6D4FixedGridShard214OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 214)
  rw [suzukiDF6D4FixedGridShard214OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard214OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard214OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard214OddDotSoundness i
            suzukiDF6D4FixedGridShard214OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard214OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard214EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard214EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 515) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard214EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 515)) at h
  exact h

theorem suzukiDF6D4FixedGridShard214EvenFull_eq_live :
    suzukiDF6D4FixedGridShard214EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 515) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard214EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 515)) at h
  exact h

def suzukiDF6D4FixedGridShard214EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard214EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard214EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard214EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard214EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard214EvenResidualData =
      suzukiDF6D4FixedGridShard214EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard214Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard214EvenResidualData =
    suzukiDF6D4FixedGridShard214EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard214EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard214EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 515 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 515) := by
    rw [suzukiDF6D4FixedGridShard214EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 515
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214EvenDotSoundness i
          suzukiDF6D4FixedGridShard214EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 515) := by
    simpa [suzukiDF6D4FixedGridShard214EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard214EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 515) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 515) := by
    rw [suzukiDF6D4FixedGridShard214EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 515
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard214EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard214EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard214EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard214EvenDotSoundness i
            suzukiDF6D4FixedGridShard214EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard214EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard214OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard214OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 515) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard214OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 515)) at h
  exact h

theorem suzukiDF6D4FixedGridShard214OddFull_eq_live :
    suzukiDF6D4FixedGridShard214OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 515) := by
  have h := suzukiDF6D4FixedGridShard214Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard214OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 515)) at h
  exact h

def suzukiDF6D4FixedGridShard214OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard214OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard214OddDotSoundness i.val
        suzukiDF6D4FixedGridShard214OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard214OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard214OddResidualData =
      suzukiDF6D4FixedGridShard214OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard214Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard214OddResidualData =
    suzukiDF6D4FixedGridShard214OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard214OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard214OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 515 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 515) := by
    rw [suzukiDF6D4FixedGridShard214OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 515
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214OddDotSoundness i
          suzukiDF6D4FixedGridShard214OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 515) := by
    simpa [suzukiDF6D4FixedGridShard214OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard214OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 515) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard214OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 515) := by
    rw [suzukiDF6D4FixedGridShard214OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 515
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard214OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard214OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard214OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard214OddDotSoundness i
            suzukiDF6D4FixedGridShard214OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard214OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
