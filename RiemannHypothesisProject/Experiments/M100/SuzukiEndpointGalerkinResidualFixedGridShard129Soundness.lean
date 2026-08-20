import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard129Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard129Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard129EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard129EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 129 k) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard129EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 129 k)) at h
  exact h

def suzukiDF6D4FixedGridShard129EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard129EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard129EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard129EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard129EvenComparisonData)

theorem suzukiDF6D4FixedGridShard129EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard129EvenSolveData =
      suzukiDF6D4FixedGridShard129EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard129Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard129EvenSolveData =
    suzukiDF6D4FixedGridShard129EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard129EvenCross_eq_live :
    suzukiDF6D4FixedGridShard129EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 129) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard129EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 129)) at h
  exact h

theorem suzukiDF6D4FixedGridShard129EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard129EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 129 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 129 k) := by
    rw [suzukiDF6D4FixedGridShard129EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 129 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129EvenDotSoundness i
          suzukiDF6D4FixedGridShard129EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 129 k) := by
    simpa [suzukiDF6D4FixedGridShard129EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard129EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 129 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 129) := by
    rw [suzukiDF6D4FixedGridShard129EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 129)
  rw [suzukiDF6D4FixedGridShard129EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard129EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard129EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard129EvenDotSoundness i
            suzukiDF6D4FixedGridShard129EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard129EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard129OddComparison_eq_live :
    suzukiDF6D4FixedGridShard129OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 129 k) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard129OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 129 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard129OddCross_eq_live :
    suzukiDF6D4FixedGridShard129OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 129) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard129OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 129)) at h
  exact h

def suzukiDF6D4FixedGridShard129OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard129OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard129OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard129OddDotSoundness i.val
      suzukiDF6D4FixedGridShard129OddComparisonData)

theorem suzukiDF6D4FixedGridShard129OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard129OddSolveData =
      suzukiDF6D4FixedGridShard129OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard129Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard129OddSolveData =
    suzukiDF6D4FixedGridShard129OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard129OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard129OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 129 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 129 k) := by
    rw [suzukiDF6D4FixedGridShard129OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 129 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129OddDotSoundness i
          suzukiDF6D4FixedGridShard129OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 129 k) := by
    simpa [suzukiDF6D4FixedGridShard129OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard129OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 129 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 129) := by
    rw [suzukiDF6D4FixedGridShard129OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 129)
  rw [suzukiDF6D4FixedGridShard129OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard129OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard129OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard129OddDotSoundness i
            suzukiDF6D4FixedGridShard129OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard129OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard129EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard129EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 430) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard129EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 430)) at h
  exact h

theorem suzukiDF6D4FixedGridShard129EvenFull_eq_live :
    suzukiDF6D4FixedGridShard129EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 430) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard129EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 430)) at h
  exact h

def suzukiDF6D4FixedGridShard129EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard129EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard129EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard129EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard129EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard129EvenResidualData =
      suzukiDF6D4FixedGridShard129EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard129Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard129EvenResidualData =
    suzukiDF6D4FixedGridShard129EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard129EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard129EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 430 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 430) := by
    rw [suzukiDF6D4FixedGridShard129EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 430
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129EvenDotSoundness i
          suzukiDF6D4FixedGridShard129EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 430) := by
    simpa [suzukiDF6D4FixedGridShard129EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard129EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 430) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 430) := by
    rw [suzukiDF6D4FixedGridShard129EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 430
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard129EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard129EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard129EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard129EvenDotSoundness i
            suzukiDF6D4FixedGridShard129EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard129EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard129OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard129OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 430) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard129OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 430)) at h
  exact h

theorem suzukiDF6D4FixedGridShard129OddFull_eq_live :
    suzukiDF6D4FixedGridShard129OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 430) := by
  have h := suzukiDF6D4FixedGridShard129Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard129OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 430)) at h
  exact h

def suzukiDF6D4FixedGridShard129OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard129OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard129OddDotSoundness i.val
        suzukiDF6D4FixedGridShard129OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard129OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard129OddResidualData =
      suzukiDF6D4FixedGridShard129OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard129Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard129OddResidualData =
    suzukiDF6D4FixedGridShard129OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard129OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard129OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 430 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 430) := by
    rw [suzukiDF6D4FixedGridShard129OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 430
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129OddDotSoundness i
          suzukiDF6D4FixedGridShard129OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 430) := by
    simpa [suzukiDF6D4FixedGridShard129OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard129OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 430) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard129OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 430) := by
    rw [suzukiDF6D4FixedGridShard129OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 430
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard129OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard129OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard129OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard129OddDotSoundness i
            suzukiDF6D4FixedGridShard129OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard129OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
