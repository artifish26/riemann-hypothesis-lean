import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard095Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard095Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard095EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard095EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 95 k) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard095EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 95 k)) at h
  exact h

def suzukiDF6D4FixedGridShard095EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard095EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard095EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard095EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard095EvenComparisonData)

theorem suzukiDF6D4FixedGridShard095EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard095EvenSolveData =
      suzukiDF6D4FixedGridShard095EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard095Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard095EvenSolveData =
    suzukiDF6D4FixedGridShard095EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard095EvenCross_eq_live :
    suzukiDF6D4FixedGridShard095EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 95) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard095EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 95)) at h
  exact h

theorem suzukiDF6D4FixedGridShard095EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard095EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 95 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 95 k) := by
    rw [suzukiDF6D4FixedGridShard095EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 95 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095EvenDotSoundness i
          suzukiDF6D4FixedGridShard095EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 95 k) := by
    simpa [suzukiDF6D4FixedGridShard095EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard095EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 95 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 95) := by
    rw [suzukiDF6D4FixedGridShard095EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 95)
  rw [suzukiDF6D4FixedGridShard095EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard095EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard095EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard095EvenDotSoundness i
            suzukiDF6D4FixedGridShard095EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard095EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard095OddComparison_eq_live :
    suzukiDF6D4FixedGridShard095OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 95 k) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard095OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 95 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard095OddCross_eq_live :
    suzukiDF6D4FixedGridShard095OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 95) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard095OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 95)) at h
  exact h

def suzukiDF6D4FixedGridShard095OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard095OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard095OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard095OddDotSoundness i.val
      suzukiDF6D4FixedGridShard095OddComparisonData)

theorem suzukiDF6D4FixedGridShard095OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard095OddSolveData =
      suzukiDF6D4FixedGridShard095OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard095Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard095OddSolveData =
    suzukiDF6D4FixedGridShard095OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard095OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard095OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 95 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 95 k) := by
    rw [suzukiDF6D4FixedGridShard095OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 95 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095OddDotSoundness i
          suzukiDF6D4FixedGridShard095OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 95 k) := by
    simpa [suzukiDF6D4FixedGridShard095OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard095OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 95 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 95) := by
    rw [suzukiDF6D4FixedGridShard095OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 95)
  rw [suzukiDF6D4FixedGridShard095OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard095OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard095OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard095OddDotSoundness i
            suzukiDF6D4FixedGridShard095OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard095OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard095EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard095EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 396) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard095EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 396)) at h
  exact h

theorem suzukiDF6D4FixedGridShard095EvenFull_eq_live :
    suzukiDF6D4FixedGridShard095EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 396) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard095EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 396)) at h
  exact h

def suzukiDF6D4FixedGridShard095EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard095EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard095EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard095EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard095EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard095EvenResidualData =
      suzukiDF6D4FixedGridShard095EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard095Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard095EvenResidualData =
    suzukiDF6D4FixedGridShard095EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard095EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard095EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 396 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 396) := by
    rw [suzukiDF6D4FixedGridShard095EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 396
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095EvenDotSoundness i
          suzukiDF6D4FixedGridShard095EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 396) := by
    simpa [suzukiDF6D4FixedGridShard095EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard095EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 396) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 396) := by
    rw [suzukiDF6D4FixedGridShard095EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 396
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard095EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard095EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard095EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard095EvenDotSoundness i
            suzukiDF6D4FixedGridShard095EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard095EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard095OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard095OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 396) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard095OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 396)) at h
  exact h

theorem suzukiDF6D4FixedGridShard095OddFull_eq_live :
    suzukiDF6D4FixedGridShard095OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 396) := by
  have h := suzukiDF6D4FixedGridShard095Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard095OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 396)) at h
  exact h

def suzukiDF6D4FixedGridShard095OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard095OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard095OddDotSoundness i.val
        suzukiDF6D4FixedGridShard095OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard095OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard095OddResidualData =
      suzukiDF6D4FixedGridShard095OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard095Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard095OddResidualData =
    suzukiDF6D4FixedGridShard095OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard095OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard095OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 396 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 396) := by
    rw [suzukiDF6D4FixedGridShard095OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 396
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095OddDotSoundness i
          suzukiDF6D4FixedGridShard095OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 396) := by
    simpa [suzukiDF6D4FixedGridShard095OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard095OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 396) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard095OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 396) := by
    rw [suzukiDF6D4FixedGridShard095OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 396
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard095OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard095OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard095OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard095OddDotSoundness i
            suzukiDF6D4FixedGridShard095OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard095OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
