import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard159Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard159Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard159EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard159EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 159 k) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard159EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 159 k)) at h
  exact h

def suzukiDF6D4FixedGridShard159EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard159EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard159EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard159EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard159EvenComparisonData)

theorem suzukiDF6D4FixedGridShard159EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard159EvenSolveData =
      suzukiDF6D4FixedGridShard159EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard159Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard159EvenSolveData =
    suzukiDF6D4FixedGridShard159EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard159EvenCross_eq_live :
    suzukiDF6D4FixedGridShard159EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 159) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard159EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 159)) at h
  exact h

theorem suzukiDF6D4FixedGridShard159EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard159EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 159 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 159 k) := by
    rw [suzukiDF6D4FixedGridShard159EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 159 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159EvenDotSoundness i
          suzukiDF6D4FixedGridShard159EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 159 k) := by
    simpa [suzukiDF6D4FixedGridShard159EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard159EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 159 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 159) := by
    rw [suzukiDF6D4FixedGridShard159EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 159)
  rw [suzukiDF6D4FixedGridShard159EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard159EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard159EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard159EvenDotSoundness i
            suzukiDF6D4FixedGridShard159EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard159EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard159OddComparison_eq_live :
    suzukiDF6D4FixedGridShard159OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 159 k) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard159OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 159 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard159OddCross_eq_live :
    suzukiDF6D4FixedGridShard159OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 159) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard159OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 159)) at h
  exact h

def suzukiDF6D4FixedGridShard159OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard159OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard159OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard159OddDotSoundness i.val
      suzukiDF6D4FixedGridShard159OddComparisonData)

theorem suzukiDF6D4FixedGridShard159OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard159OddSolveData =
      suzukiDF6D4FixedGridShard159OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard159Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard159OddSolveData =
    suzukiDF6D4FixedGridShard159OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard159OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard159OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 159 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 159 k) := by
    rw [suzukiDF6D4FixedGridShard159OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 159 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159OddDotSoundness i
          suzukiDF6D4FixedGridShard159OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 159 k) := by
    simpa [suzukiDF6D4FixedGridShard159OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard159OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 159 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 159) := by
    rw [suzukiDF6D4FixedGridShard159OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 159)
  rw [suzukiDF6D4FixedGridShard159OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard159OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard159OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard159OddDotSoundness i
            suzukiDF6D4FixedGridShard159OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard159OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard159EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard159EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 460) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard159EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 460)) at h
  exact h

theorem suzukiDF6D4FixedGridShard159EvenFull_eq_live :
    suzukiDF6D4FixedGridShard159EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 460) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard159EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 460)) at h
  exact h

def suzukiDF6D4FixedGridShard159EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard159EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard159EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard159EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard159EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard159EvenResidualData =
      suzukiDF6D4FixedGridShard159EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard159Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard159EvenResidualData =
    suzukiDF6D4FixedGridShard159EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard159EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard159EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 460 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 460) := by
    rw [suzukiDF6D4FixedGridShard159EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 460
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159EvenDotSoundness i
          suzukiDF6D4FixedGridShard159EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 460) := by
    simpa [suzukiDF6D4FixedGridShard159EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard159EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 460) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 460) := by
    rw [suzukiDF6D4FixedGridShard159EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 460
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard159EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard159EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard159EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard159EvenDotSoundness i
            suzukiDF6D4FixedGridShard159EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard159EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard159OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard159OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 460) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard159OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 460)) at h
  exact h

theorem suzukiDF6D4FixedGridShard159OddFull_eq_live :
    suzukiDF6D4FixedGridShard159OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 460) := by
  have h := suzukiDF6D4FixedGridShard159Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard159OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 460)) at h
  exact h

def suzukiDF6D4FixedGridShard159OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard159OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard159OddDotSoundness i.val
        suzukiDF6D4FixedGridShard159OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard159OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard159OddResidualData =
      suzukiDF6D4FixedGridShard159OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard159Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard159OddResidualData =
    suzukiDF6D4FixedGridShard159OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard159OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard159OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 460 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 460) := by
    rw [suzukiDF6D4FixedGridShard159OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 460
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159OddDotSoundness i
          suzukiDF6D4FixedGridShard159OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 460) := by
    simpa [suzukiDF6D4FixedGridShard159OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard159OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 460) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard159OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 460) := by
    rw [suzukiDF6D4FixedGridShard159OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 460
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard159OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard159OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard159OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard159OddDotSoundness i
            suzukiDF6D4FixedGridShard159OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard159OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
