import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard158Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard158Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard158EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard158EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 158 k) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard158EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 158 k)) at h
  exact h

def suzukiDF6D4FixedGridShard158EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard158EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard158EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard158EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard158EvenComparisonData)

theorem suzukiDF6D4FixedGridShard158EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard158EvenSolveData =
      suzukiDF6D4FixedGridShard158EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard158Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard158EvenSolveData =
    suzukiDF6D4FixedGridShard158EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard158EvenCross_eq_live :
    suzukiDF6D4FixedGridShard158EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 158) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard158EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 158)) at h
  exact h

theorem suzukiDF6D4FixedGridShard158EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard158EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 158 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 158 k) := by
    rw [suzukiDF6D4FixedGridShard158EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 158 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158EvenDotSoundness i
          suzukiDF6D4FixedGridShard158EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 158 k) := by
    simpa [suzukiDF6D4FixedGridShard158EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard158EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 158 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 158) := by
    rw [suzukiDF6D4FixedGridShard158EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 158)
  rw [suzukiDF6D4FixedGridShard158EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard158EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard158EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard158EvenDotSoundness i
            suzukiDF6D4FixedGridShard158EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard158EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard158OddComparison_eq_live :
    suzukiDF6D4FixedGridShard158OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 158 k) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard158OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 158 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard158OddCross_eq_live :
    suzukiDF6D4FixedGridShard158OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 158) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard158OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 158)) at h
  exact h

def suzukiDF6D4FixedGridShard158OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard158OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard158OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard158OddDotSoundness i.val
      suzukiDF6D4FixedGridShard158OddComparisonData)

theorem suzukiDF6D4FixedGridShard158OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard158OddSolveData =
      suzukiDF6D4FixedGridShard158OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard158Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard158OddSolveData =
    suzukiDF6D4FixedGridShard158OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard158OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard158OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 158 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 158 k) := by
    rw [suzukiDF6D4FixedGridShard158OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 158 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158OddDotSoundness i
          suzukiDF6D4FixedGridShard158OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 158 k) := by
    simpa [suzukiDF6D4FixedGridShard158OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard158OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 158 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 158) := by
    rw [suzukiDF6D4FixedGridShard158OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 158)
  rw [suzukiDF6D4FixedGridShard158OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard158OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard158OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard158OddDotSoundness i
            suzukiDF6D4FixedGridShard158OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard158OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard158EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard158EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 459) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard158EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 459)) at h
  exact h

theorem suzukiDF6D4FixedGridShard158EvenFull_eq_live :
    suzukiDF6D4FixedGridShard158EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 459) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard158EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 459)) at h
  exact h

def suzukiDF6D4FixedGridShard158EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard158EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard158EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard158EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard158EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard158EvenResidualData =
      suzukiDF6D4FixedGridShard158EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard158Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard158EvenResidualData =
    suzukiDF6D4FixedGridShard158EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard158EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard158EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 459 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 459) := by
    rw [suzukiDF6D4FixedGridShard158EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 459
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158EvenDotSoundness i
          suzukiDF6D4FixedGridShard158EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 459) := by
    simpa [suzukiDF6D4FixedGridShard158EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard158EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 459) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 459) := by
    rw [suzukiDF6D4FixedGridShard158EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 459
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard158EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard158EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard158EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard158EvenDotSoundness i
            suzukiDF6D4FixedGridShard158EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard158EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard158OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard158OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 459) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard158OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 459)) at h
  exact h

theorem suzukiDF6D4FixedGridShard158OddFull_eq_live :
    suzukiDF6D4FixedGridShard158OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 459) := by
  have h := suzukiDF6D4FixedGridShard158Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard158OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 459)) at h
  exact h

def suzukiDF6D4FixedGridShard158OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard158OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard158OddDotSoundness i.val
        suzukiDF6D4FixedGridShard158OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard158OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard158OddResidualData =
      suzukiDF6D4FixedGridShard158OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard158Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard158OddResidualData =
    suzukiDF6D4FixedGridShard158OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard158OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard158OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 459 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 459) := by
    rw [suzukiDF6D4FixedGridShard158OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 459
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158OddDotSoundness i
          suzukiDF6D4FixedGridShard158OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 459) := by
    simpa [suzukiDF6D4FixedGridShard158OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard158OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 459) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard158OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 459) := by
    rw [suzukiDF6D4FixedGridShard158OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 459
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard158OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard158OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard158OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard158OddDotSoundness i
            suzukiDF6D4FixedGridShard158OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard158OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
