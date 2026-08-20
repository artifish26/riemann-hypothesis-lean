import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard057Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard057Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard057EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard057EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 57 k) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard057EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 57 k)) at h
  exact h

def suzukiDF6D4FixedGridShard057EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard057EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard057EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard057EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard057EvenComparisonData)

theorem suzukiDF6D4FixedGridShard057EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard057EvenSolveData =
      suzukiDF6D4FixedGridShard057EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard057Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard057EvenSolveData =
    suzukiDF6D4FixedGridShard057EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard057EvenCross_eq_live :
    suzukiDF6D4FixedGridShard057EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 57) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard057EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 57)) at h
  exact h

theorem suzukiDF6D4FixedGridShard057EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard057EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 57 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 57 k) := by
    rw [suzukiDF6D4FixedGridShard057EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 57 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057EvenDotSoundness i
          suzukiDF6D4FixedGridShard057EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 57 k) := by
    simpa [suzukiDF6D4FixedGridShard057EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard057EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 57 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 57) := by
    rw [suzukiDF6D4FixedGridShard057EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 57)
  rw [suzukiDF6D4FixedGridShard057EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard057EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard057EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard057EvenDotSoundness i
            suzukiDF6D4FixedGridShard057EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard057EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard057OddComparison_eq_live :
    suzukiDF6D4FixedGridShard057OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 57 k) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard057OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 57 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard057OddCross_eq_live :
    suzukiDF6D4FixedGridShard057OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 57) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard057OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 57)) at h
  exact h

def suzukiDF6D4FixedGridShard057OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard057OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard057OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard057OddDotSoundness i.val
      suzukiDF6D4FixedGridShard057OddComparisonData)

theorem suzukiDF6D4FixedGridShard057OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard057OddSolveData =
      suzukiDF6D4FixedGridShard057OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard057Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard057OddSolveData =
    suzukiDF6D4FixedGridShard057OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard057OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard057OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 57 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 57 k) := by
    rw [suzukiDF6D4FixedGridShard057OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 57 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057OddDotSoundness i
          suzukiDF6D4FixedGridShard057OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 57 k) := by
    simpa [suzukiDF6D4FixedGridShard057OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard057OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 57 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 57) := by
    rw [suzukiDF6D4FixedGridShard057OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 57)
  rw [suzukiDF6D4FixedGridShard057OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard057OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard057OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard057OddDotSoundness i
            suzukiDF6D4FixedGridShard057OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard057OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard057EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard057EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 358) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard057EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 358)) at h
  exact h

theorem suzukiDF6D4FixedGridShard057EvenFull_eq_live :
    suzukiDF6D4FixedGridShard057EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 358) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard057EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 358)) at h
  exact h

def suzukiDF6D4FixedGridShard057EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard057EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard057EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard057EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard057EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard057EvenResidualData =
      suzukiDF6D4FixedGridShard057EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard057Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard057EvenResidualData =
    suzukiDF6D4FixedGridShard057EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard057EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard057EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 358 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 358) := by
    rw [suzukiDF6D4FixedGridShard057EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 358
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057EvenDotSoundness i
          suzukiDF6D4FixedGridShard057EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 358) := by
    simpa [suzukiDF6D4FixedGridShard057EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard057EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 358) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 358) := by
    rw [suzukiDF6D4FixedGridShard057EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 358
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard057EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard057EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard057EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard057EvenDotSoundness i
            suzukiDF6D4FixedGridShard057EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard057EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard057OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard057OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 358) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard057OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 358)) at h
  exact h

theorem suzukiDF6D4FixedGridShard057OddFull_eq_live :
    suzukiDF6D4FixedGridShard057OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 358) := by
  have h := suzukiDF6D4FixedGridShard057Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard057OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 358)) at h
  exact h

def suzukiDF6D4FixedGridShard057OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard057OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard057OddDotSoundness i.val
        suzukiDF6D4FixedGridShard057OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard057OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard057OddResidualData =
      suzukiDF6D4FixedGridShard057OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard057Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard057OddResidualData =
    suzukiDF6D4FixedGridShard057OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard057OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard057OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 358 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 358) := by
    rw [suzukiDF6D4FixedGridShard057OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 358
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057OddDotSoundness i
          suzukiDF6D4FixedGridShard057OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 358) := by
    simpa [suzukiDF6D4FixedGridShard057OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard057OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 358) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard057OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 358) := by
    rw [suzukiDF6D4FixedGridShard057OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 358
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard057OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard057OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard057OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard057OddDotSoundness i
            suzukiDF6D4FixedGridShard057OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard057OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
