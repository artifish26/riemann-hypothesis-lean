import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard181Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard181Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard181EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard181EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 181 k) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard181EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 181 k)) at h
  exact h

def suzukiDF6D4FixedGridShard181EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard181EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard181EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard181EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard181EvenComparisonData)

theorem suzukiDF6D4FixedGridShard181EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard181EvenSolveData =
      suzukiDF6D4FixedGridShard181EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard181Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard181EvenSolveData =
    suzukiDF6D4FixedGridShard181EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard181EvenCross_eq_live :
    suzukiDF6D4FixedGridShard181EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 181) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard181EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 181)) at h
  exact h

theorem suzukiDF6D4FixedGridShard181EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard181EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 181 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 181 k) := by
    rw [suzukiDF6D4FixedGridShard181EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 181 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181EvenDotSoundness i
          suzukiDF6D4FixedGridShard181EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 181 k) := by
    simpa [suzukiDF6D4FixedGridShard181EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard181EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 181 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 181) := by
    rw [suzukiDF6D4FixedGridShard181EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 181)
  rw [suzukiDF6D4FixedGridShard181EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard181EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard181EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard181EvenDotSoundness i
            suzukiDF6D4FixedGridShard181EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard181EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard181OddComparison_eq_live :
    suzukiDF6D4FixedGridShard181OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 181 k) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard181OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 181 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard181OddCross_eq_live :
    suzukiDF6D4FixedGridShard181OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 181) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard181OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 181)) at h
  exact h

def suzukiDF6D4FixedGridShard181OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard181OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard181OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard181OddDotSoundness i.val
      suzukiDF6D4FixedGridShard181OddComparisonData)

theorem suzukiDF6D4FixedGridShard181OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard181OddSolveData =
      suzukiDF6D4FixedGridShard181OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard181Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard181OddSolveData =
    suzukiDF6D4FixedGridShard181OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard181OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard181OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 181 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 181 k) := by
    rw [suzukiDF6D4FixedGridShard181OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 181 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181OddDotSoundness i
          suzukiDF6D4FixedGridShard181OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 181 k) := by
    simpa [suzukiDF6D4FixedGridShard181OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard181OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 181 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 181) := by
    rw [suzukiDF6D4FixedGridShard181OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 181)
  rw [suzukiDF6D4FixedGridShard181OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard181OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard181OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard181OddDotSoundness i
            suzukiDF6D4FixedGridShard181OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard181OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard181EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard181EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 482) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard181EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 482)) at h
  exact h

theorem suzukiDF6D4FixedGridShard181EvenFull_eq_live :
    suzukiDF6D4FixedGridShard181EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 482) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard181EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 482)) at h
  exact h

def suzukiDF6D4FixedGridShard181EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard181EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard181EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard181EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard181EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard181EvenResidualData =
      suzukiDF6D4FixedGridShard181EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard181Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard181EvenResidualData =
    suzukiDF6D4FixedGridShard181EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard181EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard181EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 482 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 482) := by
    rw [suzukiDF6D4FixedGridShard181EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 482
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181EvenDotSoundness i
          suzukiDF6D4FixedGridShard181EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 482) := by
    simpa [suzukiDF6D4FixedGridShard181EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard181EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 482) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 482) := by
    rw [suzukiDF6D4FixedGridShard181EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 482
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard181EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard181EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard181EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard181EvenDotSoundness i
            suzukiDF6D4FixedGridShard181EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard181EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard181OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard181OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 482) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard181OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 482)) at h
  exact h

theorem suzukiDF6D4FixedGridShard181OddFull_eq_live :
    suzukiDF6D4FixedGridShard181OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 482) := by
  have h := suzukiDF6D4FixedGridShard181Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard181OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 482)) at h
  exact h

def suzukiDF6D4FixedGridShard181OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard181OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard181OddDotSoundness i.val
        suzukiDF6D4FixedGridShard181OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard181OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard181OddResidualData =
      suzukiDF6D4FixedGridShard181OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard181Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard181OddResidualData =
    suzukiDF6D4FixedGridShard181OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard181OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard181OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 482 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 482) := by
    rw [suzukiDF6D4FixedGridShard181OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 482
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181OddDotSoundness i
          suzukiDF6D4FixedGridShard181OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 482) := by
    simpa [suzukiDF6D4FixedGridShard181OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard181OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 482) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard181OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 482) := by
    rw [suzukiDF6D4FixedGridShard181OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 482
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard181OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard181OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard181OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard181OddDotSoundness i
            suzukiDF6D4FixedGridShard181OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard181OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
