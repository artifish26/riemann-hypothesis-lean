import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard110Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard110Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard110EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard110EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 110 k) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard110EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 110 k)) at h
  exact h

def suzukiDF6D4FixedGridShard110EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard110EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard110EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard110EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard110EvenComparisonData)

theorem suzukiDF6D4FixedGridShard110EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard110EvenSolveData =
      suzukiDF6D4FixedGridShard110EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard110Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard110EvenSolveData =
    suzukiDF6D4FixedGridShard110EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard110EvenCross_eq_live :
    suzukiDF6D4FixedGridShard110EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 110) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard110EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 110)) at h
  exact h

theorem suzukiDF6D4FixedGridShard110EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard110EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 110 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 110 k) := by
    rw [suzukiDF6D4FixedGridShard110EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 110 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110EvenDotSoundness i
          suzukiDF6D4FixedGridShard110EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 110 k) := by
    simpa [suzukiDF6D4FixedGridShard110EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard110EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 110 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 110) := by
    rw [suzukiDF6D4FixedGridShard110EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 110)
  rw [suzukiDF6D4FixedGridShard110EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard110EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard110EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard110EvenDotSoundness i
            suzukiDF6D4FixedGridShard110EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard110EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard110OddComparison_eq_live :
    suzukiDF6D4FixedGridShard110OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 110 k) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard110OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 110 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard110OddCross_eq_live :
    suzukiDF6D4FixedGridShard110OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 110) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard110OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 110)) at h
  exact h

def suzukiDF6D4FixedGridShard110OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard110OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard110OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard110OddDotSoundness i.val
      suzukiDF6D4FixedGridShard110OddComparisonData)

theorem suzukiDF6D4FixedGridShard110OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard110OddSolveData =
      suzukiDF6D4FixedGridShard110OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard110Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard110OddSolveData =
    suzukiDF6D4FixedGridShard110OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard110OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard110OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 110 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 110 k) := by
    rw [suzukiDF6D4FixedGridShard110OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 110 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110OddDotSoundness i
          suzukiDF6D4FixedGridShard110OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 110 k) := by
    simpa [suzukiDF6D4FixedGridShard110OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard110OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 110 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 110) := by
    rw [suzukiDF6D4FixedGridShard110OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 110)
  rw [suzukiDF6D4FixedGridShard110OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard110OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard110OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard110OddDotSoundness i
            suzukiDF6D4FixedGridShard110OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard110OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard110EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard110EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 411) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard110EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 411)) at h
  exact h

theorem suzukiDF6D4FixedGridShard110EvenFull_eq_live :
    suzukiDF6D4FixedGridShard110EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 411) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard110EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 411)) at h
  exact h

def suzukiDF6D4FixedGridShard110EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard110EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard110EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard110EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard110EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard110EvenResidualData =
      suzukiDF6D4FixedGridShard110EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard110Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard110EvenResidualData =
    suzukiDF6D4FixedGridShard110EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard110EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard110EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 411 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 411) := by
    rw [suzukiDF6D4FixedGridShard110EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 411
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110EvenDotSoundness i
          suzukiDF6D4FixedGridShard110EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 411) := by
    simpa [suzukiDF6D4FixedGridShard110EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard110EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 411) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 411) := by
    rw [suzukiDF6D4FixedGridShard110EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 411
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard110EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard110EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard110EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard110EvenDotSoundness i
            suzukiDF6D4FixedGridShard110EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard110EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard110OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard110OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 411) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard110OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 411)) at h
  exact h

theorem suzukiDF6D4FixedGridShard110OddFull_eq_live :
    suzukiDF6D4FixedGridShard110OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 411) := by
  have h := suzukiDF6D4FixedGridShard110Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard110OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 411)) at h
  exact h

def suzukiDF6D4FixedGridShard110OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard110OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard110OddDotSoundness i.val
        suzukiDF6D4FixedGridShard110OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard110OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard110OddResidualData =
      suzukiDF6D4FixedGridShard110OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard110Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard110OddResidualData =
    suzukiDF6D4FixedGridShard110OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard110OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard110OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 411 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 411) := by
    rw [suzukiDF6D4FixedGridShard110OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 411
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110OddDotSoundness i
          suzukiDF6D4FixedGridShard110OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 411) := by
    simpa [suzukiDF6D4FixedGridShard110OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard110OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 411) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard110OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 411) := by
    rw [suzukiDF6D4FixedGridShard110OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 411
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard110OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard110OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard110OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard110OddDotSoundness i
            suzukiDF6D4FixedGridShard110OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard110OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
