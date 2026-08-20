import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard252Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard252Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard252EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard252EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 252 k) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard252EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 252 k)) at h
  exact h

def suzukiDF6D4FixedGridShard252EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard252EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard252EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard252EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard252EvenComparisonData)

theorem suzukiDF6D4FixedGridShard252EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard252EvenSolveData =
      suzukiDF6D4FixedGridShard252EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard252Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard252EvenSolveData =
    suzukiDF6D4FixedGridShard252EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard252EvenCross_eq_live :
    suzukiDF6D4FixedGridShard252EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 252) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard252EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 252)) at h
  exact h

theorem suzukiDF6D4FixedGridShard252EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard252EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 252 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 252 k) := by
    rw [suzukiDF6D4FixedGridShard252EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 252 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252EvenDotSoundness i
          suzukiDF6D4FixedGridShard252EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 252 k) := by
    simpa [suzukiDF6D4FixedGridShard252EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard252EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 252 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 252) := by
    rw [suzukiDF6D4FixedGridShard252EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 252)
  rw [suzukiDF6D4FixedGridShard252EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard252EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard252EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard252EvenDotSoundness i
            suzukiDF6D4FixedGridShard252EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard252EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard252OddComparison_eq_live :
    suzukiDF6D4FixedGridShard252OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 252 k) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard252OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 252 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard252OddCross_eq_live :
    suzukiDF6D4FixedGridShard252OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 252) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard252OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 252)) at h
  exact h

def suzukiDF6D4FixedGridShard252OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard252OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard252OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard252OddDotSoundness i.val
      suzukiDF6D4FixedGridShard252OddComparisonData)

theorem suzukiDF6D4FixedGridShard252OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard252OddSolveData =
      suzukiDF6D4FixedGridShard252OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard252Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard252OddSolveData =
    suzukiDF6D4FixedGridShard252OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard252OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard252OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 252 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 252 k) := by
    rw [suzukiDF6D4FixedGridShard252OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 252 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252OddDotSoundness i
          suzukiDF6D4FixedGridShard252OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 252 k) := by
    simpa [suzukiDF6D4FixedGridShard252OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard252OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 252 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 252) := by
    rw [suzukiDF6D4FixedGridShard252OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 252)
  rw [suzukiDF6D4FixedGridShard252OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard252OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard252OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard252OddDotSoundness i
            suzukiDF6D4FixedGridShard252OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard252OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard252EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard252EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 553) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard252EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 553)) at h
  exact h

theorem suzukiDF6D4FixedGridShard252EvenFull_eq_live :
    suzukiDF6D4FixedGridShard252EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 553) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard252EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 553)) at h
  exact h

def suzukiDF6D4FixedGridShard252EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard252EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard252EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard252EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard252EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard252EvenResidualData =
      suzukiDF6D4FixedGridShard252EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard252Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard252EvenResidualData =
    suzukiDF6D4FixedGridShard252EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard252EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard252EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 553 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 553) := by
    rw [suzukiDF6D4FixedGridShard252EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 553
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252EvenDotSoundness i
          suzukiDF6D4FixedGridShard252EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 553) := by
    simpa [suzukiDF6D4FixedGridShard252EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard252EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 553) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 553) := by
    rw [suzukiDF6D4FixedGridShard252EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 553
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard252EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard252EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard252EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard252EvenDotSoundness i
            suzukiDF6D4FixedGridShard252EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard252EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard252OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard252OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 553) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard252OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 553)) at h
  exact h

theorem suzukiDF6D4FixedGridShard252OddFull_eq_live :
    suzukiDF6D4FixedGridShard252OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 553) := by
  have h := suzukiDF6D4FixedGridShard252Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard252OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 553)) at h
  exact h

def suzukiDF6D4FixedGridShard252OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard252OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard252OddDotSoundness i.val
        suzukiDF6D4FixedGridShard252OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard252OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard252OddResidualData =
      suzukiDF6D4FixedGridShard252OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard252Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard252OddResidualData =
    suzukiDF6D4FixedGridShard252OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard252OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard252OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 553 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 553) := by
    rw [suzukiDF6D4FixedGridShard252OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 553
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252OddDotSoundness i
          suzukiDF6D4FixedGridShard252OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 553) := by
    simpa [suzukiDF6D4FixedGridShard252OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard252OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 553) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard252OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 553) := by
    rw [suzukiDF6D4FixedGridShard252OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 553
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard252OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard252OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard252OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard252OddDotSoundness i
            suzukiDF6D4FixedGridShard252OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard252OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
