import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard104Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard104Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard104EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard104EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 104 k) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard104EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 104 k)) at h
  exact h

def suzukiDF6D4FixedGridShard104EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard104EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard104EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard104EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard104EvenComparisonData)

theorem suzukiDF6D4FixedGridShard104EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard104EvenSolveData =
      suzukiDF6D4FixedGridShard104EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard104Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard104EvenSolveData =
    suzukiDF6D4FixedGridShard104EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard104EvenCross_eq_live :
    suzukiDF6D4FixedGridShard104EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 104) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard104EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 104)) at h
  exact h

theorem suzukiDF6D4FixedGridShard104EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard104EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 104 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 104 k) := by
    rw [suzukiDF6D4FixedGridShard104EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 104 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104EvenDotSoundness i
          suzukiDF6D4FixedGridShard104EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 104 k) := by
    simpa [suzukiDF6D4FixedGridShard104EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard104EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 104 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 104) := by
    rw [suzukiDF6D4FixedGridShard104EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 104)
  rw [suzukiDF6D4FixedGridShard104EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard104EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard104EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard104EvenDotSoundness i
            suzukiDF6D4FixedGridShard104EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard104EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard104OddComparison_eq_live :
    suzukiDF6D4FixedGridShard104OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 104 k) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard104OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 104 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard104OddCross_eq_live :
    suzukiDF6D4FixedGridShard104OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 104) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard104OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 104)) at h
  exact h

def suzukiDF6D4FixedGridShard104OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard104OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard104OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard104OddDotSoundness i.val
      suzukiDF6D4FixedGridShard104OddComparisonData)

theorem suzukiDF6D4FixedGridShard104OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard104OddSolveData =
      suzukiDF6D4FixedGridShard104OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard104Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard104OddSolveData =
    suzukiDF6D4FixedGridShard104OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard104OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard104OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 104 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 104 k) := by
    rw [suzukiDF6D4FixedGridShard104OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 104 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104OddDotSoundness i
          suzukiDF6D4FixedGridShard104OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 104 k) := by
    simpa [suzukiDF6D4FixedGridShard104OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard104OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 104 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 104) := by
    rw [suzukiDF6D4FixedGridShard104OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 104)
  rw [suzukiDF6D4FixedGridShard104OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard104OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard104OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard104OddDotSoundness i
            suzukiDF6D4FixedGridShard104OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard104OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard104EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard104EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 405) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard104EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 405)) at h
  exact h

theorem suzukiDF6D4FixedGridShard104EvenFull_eq_live :
    suzukiDF6D4FixedGridShard104EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 405) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard104EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 405)) at h
  exact h

def suzukiDF6D4FixedGridShard104EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard104EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard104EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard104EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard104EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard104EvenResidualData =
      suzukiDF6D4FixedGridShard104EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard104Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard104EvenResidualData =
    suzukiDF6D4FixedGridShard104EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard104EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard104EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 405 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 405) := by
    rw [suzukiDF6D4FixedGridShard104EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 405
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104EvenDotSoundness i
          suzukiDF6D4FixedGridShard104EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 405) := by
    simpa [suzukiDF6D4FixedGridShard104EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard104EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 405) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 405) := by
    rw [suzukiDF6D4FixedGridShard104EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 405
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard104EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard104EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard104EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard104EvenDotSoundness i
            suzukiDF6D4FixedGridShard104EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard104EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard104OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard104OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 405) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard104OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 405)) at h
  exact h

theorem suzukiDF6D4FixedGridShard104OddFull_eq_live :
    suzukiDF6D4FixedGridShard104OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 405) := by
  have h := suzukiDF6D4FixedGridShard104Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard104OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 405)) at h
  exact h

def suzukiDF6D4FixedGridShard104OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard104OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard104OddDotSoundness i.val
        suzukiDF6D4FixedGridShard104OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard104OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard104OddResidualData =
      suzukiDF6D4FixedGridShard104OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard104Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard104OddResidualData =
    suzukiDF6D4FixedGridShard104OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard104OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard104OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 405 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 405) := by
    rw [suzukiDF6D4FixedGridShard104OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 405
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104OddDotSoundness i
          suzukiDF6D4FixedGridShard104OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 405) := by
    simpa [suzukiDF6D4FixedGridShard104OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard104OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 405) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard104OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 405) := by
    rw [suzukiDF6D4FixedGridShard104OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 405
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard104OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard104OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard104OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard104OddDotSoundness i
            suzukiDF6D4FixedGridShard104OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard104OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
