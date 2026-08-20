import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard050Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard050Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard050EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard050EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 50 k) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard050EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 50 k)) at h
  exact h

def suzukiDF6D4FixedGridShard050EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard050EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard050EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard050EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard050EvenComparisonData)

theorem suzukiDF6D4FixedGridShard050EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard050EvenSolveData =
      suzukiDF6D4FixedGridShard050EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard050Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard050EvenSolveData =
    suzukiDF6D4FixedGridShard050EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard050EvenCross_eq_live :
    suzukiDF6D4FixedGridShard050EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 50) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard050EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 50)) at h
  exact h

theorem suzukiDF6D4FixedGridShard050EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard050EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 50 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 50 k) := by
    rw [suzukiDF6D4FixedGridShard050EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 50 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050EvenDotSoundness i
          suzukiDF6D4FixedGridShard050EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 50 k) := by
    simpa [suzukiDF6D4FixedGridShard050EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard050EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 50 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 50) := by
    rw [suzukiDF6D4FixedGridShard050EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 50)
  rw [suzukiDF6D4FixedGridShard050EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard050EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard050EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard050EvenDotSoundness i
            suzukiDF6D4FixedGridShard050EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard050EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard050OddComparison_eq_live :
    suzukiDF6D4FixedGridShard050OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 50 k) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard050OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 50 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard050OddCross_eq_live :
    suzukiDF6D4FixedGridShard050OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 50) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard050OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 50)) at h
  exact h

def suzukiDF6D4FixedGridShard050OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard050OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard050OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard050OddDotSoundness i.val
      suzukiDF6D4FixedGridShard050OddComparisonData)

theorem suzukiDF6D4FixedGridShard050OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard050OddSolveData =
      suzukiDF6D4FixedGridShard050OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard050Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard050OddSolveData =
    suzukiDF6D4FixedGridShard050OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard050OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard050OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 50 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 50 k) := by
    rw [suzukiDF6D4FixedGridShard050OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 50 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050OddDotSoundness i
          suzukiDF6D4FixedGridShard050OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 50 k) := by
    simpa [suzukiDF6D4FixedGridShard050OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard050OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 50 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 50) := by
    rw [suzukiDF6D4FixedGridShard050OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 50)
  rw [suzukiDF6D4FixedGridShard050OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard050OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard050OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard050OddDotSoundness i
            suzukiDF6D4FixedGridShard050OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard050OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard050EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard050EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 351) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard050EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 351)) at h
  exact h

theorem suzukiDF6D4FixedGridShard050EvenFull_eq_live :
    suzukiDF6D4FixedGridShard050EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 351) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard050EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 351)) at h
  exact h

def suzukiDF6D4FixedGridShard050EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard050EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard050EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard050EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard050EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard050EvenResidualData =
      suzukiDF6D4FixedGridShard050EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard050Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard050EvenResidualData =
    suzukiDF6D4FixedGridShard050EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard050EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard050EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 351 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 351) := by
    rw [suzukiDF6D4FixedGridShard050EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 351
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050EvenDotSoundness i
          suzukiDF6D4FixedGridShard050EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 351) := by
    simpa [suzukiDF6D4FixedGridShard050EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard050EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 351) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 351) := by
    rw [suzukiDF6D4FixedGridShard050EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 351
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard050EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard050EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard050EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard050EvenDotSoundness i
            suzukiDF6D4FixedGridShard050EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard050EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard050OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard050OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 351) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard050OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 351)) at h
  exact h

theorem suzukiDF6D4FixedGridShard050OddFull_eq_live :
    suzukiDF6D4FixedGridShard050OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 351) := by
  have h := suzukiDF6D4FixedGridShard050Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard050OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 351)) at h
  exact h

def suzukiDF6D4FixedGridShard050OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard050OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard050OddDotSoundness i.val
        suzukiDF6D4FixedGridShard050OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard050OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard050OddResidualData =
      suzukiDF6D4FixedGridShard050OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard050Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard050OddResidualData =
    suzukiDF6D4FixedGridShard050OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard050OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard050OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 351 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 351) := by
    rw [suzukiDF6D4FixedGridShard050OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 351
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050OddDotSoundness i
          suzukiDF6D4FixedGridShard050OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 351) := by
    simpa [suzukiDF6D4FixedGridShard050OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard050OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 351) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard050OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 351) := by
    rw [suzukiDF6D4FixedGridShard050OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 351
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard050OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard050OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard050OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard050OddDotSoundness i
            suzukiDF6D4FixedGridShard050OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard050OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
