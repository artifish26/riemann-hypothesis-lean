import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard053Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard053Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard053EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard053EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 53 k) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard053EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 53 k)) at h
  exact h

def suzukiDF6D4FixedGridShard053EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard053EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard053EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard053EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard053EvenComparisonData)

theorem suzukiDF6D4FixedGridShard053EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard053EvenSolveData =
      suzukiDF6D4FixedGridShard053EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard053Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard053EvenSolveData =
    suzukiDF6D4FixedGridShard053EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard053EvenCross_eq_live :
    suzukiDF6D4FixedGridShard053EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 53) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard053EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 53)) at h
  exact h

theorem suzukiDF6D4FixedGridShard053EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard053EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 53 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 53 k) := by
    rw [suzukiDF6D4FixedGridShard053EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 53 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053EvenDotSoundness i
          suzukiDF6D4FixedGridShard053EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 53 k) := by
    simpa [suzukiDF6D4FixedGridShard053EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard053EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 53 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 53) := by
    rw [suzukiDF6D4FixedGridShard053EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 53)
  rw [suzukiDF6D4FixedGridShard053EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard053EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard053EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard053EvenDotSoundness i
            suzukiDF6D4FixedGridShard053EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard053EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard053OddComparison_eq_live :
    suzukiDF6D4FixedGridShard053OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 53 k) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard053OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 53 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard053OddCross_eq_live :
    suzukiDF6D4FixedGridShard053OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 53) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard053OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 53)) at h
  exact h

def suzukiDF6D4FixedGridShard053OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard053OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard053OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard053OddDotSoundness i.val
      suzukiDF6D4FixedGridShard053OddComparisonData)

theorem suzukiDF6D4FixedGridShard053OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard053OddSolveData =
      suzukiDF6D4FixedGridShard053OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard053Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard053OddSolveData =
    suzukiDF6D4FixedGridShard053OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard053OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard053OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 53 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 53 k) := by
    rw [suzukiDF6D4FixedGridShard053OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 53 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053OddDotSoundness i
          suzukiDF6D4FixedGridShard053OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 53 k) := by
    simpa [suzukiDF6D4FixedGridShard053OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard053OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 53 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 53) := by
    rw [suzukiDF6D4FixedGridShard053OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 53)
  rw [suzukiDF6D4FixedGridShard053OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard053OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard053OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard053OddDotSoundness i
            suzukiDF6D4FixedGridShard053OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard053OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard053EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard053EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 354) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard053EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 354)) at h
  exact h

theorem suzukiDF6D4FixedGridShard053EvenFull_eq_live :
    suzukiDF6D4FixedGridShard053EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 354) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard053EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 354)) at h
  exact h

def suzukiDF6D4FixedGridShard053EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard053EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard053EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard053EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard053EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard053EvenResidualData =
      suzukiDF6D4FixedGridShard053EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard053Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard053EvenResidualData =
    suzukiDF6D4FixedGridShard053EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard053EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard053EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 354 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 354) := by
    rw [suzukiDF6D4FixedGridShard053EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 354
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053EvenDotSoundness i
          suzukiDF6D4FixedGridShard053EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 354) := by
    simpa [suzukiDF6D4FixedGridShard053EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard053EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 354) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 354) := by
    rw [suzukiDF6D4FixedGridShard053EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 354
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard053EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard053EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard053EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard053EvenDotSoundness i
            suzukiDF6D4FixedGridShard053EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard053EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard053OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard053OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 354) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard053OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 354)) at h
  exact h

theorem suzukiDF6D4FixedGridShard053OddFull_eq_live :
    suzukiDF6D4FixedGridShard053OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 354) := by
  have h := suzukiDF6D4FixedGridShard053Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard053OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 354)) at h
  exact h

def suzukiDF6D4FixedGridShard053OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard053OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard053OddDotSoundness i.val
        suzukiDF6D4FixedGridShard053OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard053OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard053OddResidualData =
      suzukiDF6D4FixedGridShard053OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard053Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard053OddResidualData =
    suzukiDF6D4FixedGridShard053OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard053OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard053OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 354 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 354) := by
    rw [suzukiDF6D4FixedGridShard053OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 354
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053OddDotSoundness i
          suzukiDF6D4FixedGridShard053OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 354) := by
    simpa [suzukiDF6D4FixedGridShard053OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard053OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 354) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard053OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 354) := by
    rw [suzukiDF6D4FixedGridShard053OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 354
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard053OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard053OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard053OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard053OddDotSoundness i
            suzukiDF6D4FixedGridShard053OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard053OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
