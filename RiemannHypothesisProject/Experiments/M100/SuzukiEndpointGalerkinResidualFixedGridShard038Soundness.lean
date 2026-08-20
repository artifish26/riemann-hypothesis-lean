import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard038Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard038Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard038EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard038EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 38 k) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard038EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 38 k)) at h
  exact h

def suzukiDF6D4FixedGridShard038EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard038EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard038EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard038EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard038EvenComparisonData)

theorem suzukiDF6D4FixedGridShard038EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard038EvenSolveData =
      suzukiDF6D4FixedGridShard038EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard038Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard038EvenSolveData =
    suzukiDF6D4FixedGridShard038EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard038EvenCross_eq_live :
    suzukiDF6D4FixedGridShard038EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 38) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard038EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 38)) at h
  exact h

theorem suzukiDF6D4FixedGridShard038EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard038EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 38 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 38 k) := by
    rw [suzukiDF6D4FixedGridShard038EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 38 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038EvenDotSoundness i
          suzukiDF6D4FixedGridShard038EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 38 k) := by
    simpa [suzukiDF6D4FixedGridShard038EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard038EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 38 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 38) := by
    rw [suzukiDF6D4FixedGridShard038EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 38)
  rw [suzukiDF6D4FixedGridShard038EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard038EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard038EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard038EvenDotSoundness i
            suzukiDF6D4FixedGridShard038EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard038EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard038OddComparison_eq_live :
    suzukiDF6D4FixedGridShard038OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 38 k) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard038OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 38 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard038OddCross_eq_live :
    suzukiDF6D4FixedGridShard038OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 38) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard038OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 38)) at h
  exact h

def suzukiDF6D4FixedGridShard038OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard038OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard038OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard038OddDotSoundness i.val
      suzukiDF6D4FixedGridShard038OddComparisonData)

theorem suzukiDF6D4FixedGridShard038OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard038OddSolveData =
      suzukiDF6D4FixedGridShard038OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard038Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard038OddSolveData =
    suzukiDF6D4FixedGridShard038OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard038OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard038OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 38 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 38 k) := by
    rw [suzukiDF6D4FixedGridShard038OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 38 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038OddDotSoundness i
          suzukiDF6D4FixedGridShard038OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 38 k) := by
    simpa [suzukiDF6D4FixedGridShard038OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard038OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 38 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 38) := by
    rw [suzukiDF6D4FixedGridShard038OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 38)
  rw [suzukiDF6D4FixedGridShard038OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard038OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard038OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard038OddDotSoundness i
            suzukiDF6D4FixedGridShard038OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard038OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard038EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard038EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 339) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard038EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 339)) at h
  exact h

theorem suzukiDF6D4FixedGridShard038EvenFull_eq_live :
    suzukiDF6D4FixedGridShard038EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 339) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard038EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 339)) at h
  exact h

def suzukiDF6D4FixedGridShard038EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard038EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard038EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard038EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard038EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard038EvenResidualData =
      suzukiDF6D4FixedGridShard038EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard038Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard038EvenResidualData =
    suzukiDF6D4FixedGridShard038EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard038EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard038EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 339 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 339) := by
    rw [suzukiDF6D4FixedGridShard038EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 339
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038EvenDotSoundness i
          suzukiDF6D4FixedGridShard038EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 339) := by
    simpa [suzukiDF6D4FixedGridShard038EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard038EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 339) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 339) := by
    rw [suzukiDF6D4FixedGridShard038EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 339
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard038EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard038EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard038EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard038EvenDotSoundness i
            suzukiDF6D4FixedGridShard038EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard038EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard038OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard038OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 339) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard038OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 339)) at h
  exact h

theorem suzukiDF6D4FixedGridShard038OddFull_eq_live :
    suzukiDF6D4FixedGridShard038OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 339) := by
  have h := suzukiDF6D4FixedGridShard038Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard038OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 339)) at h
  exact h

def suzukiDF6D4FixedGridShard038OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard038OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard038OddDotSoundness i.val
        suzukiDF6D4FixedGridShard038OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard038OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard038OddResidualData =
      suzukiDF6D4FixedGridShard038OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard038Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard038OddResidualData =
    suzukiDF6D4FixedGridShard038OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard038OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard038OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 339 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 339) := by
    rw [suzukiDF6D4FixedGridShard038OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 339
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038OddDotSoundness i
          suzukiDF6D4FixedGridShard038OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 339) := by
    simpa [suzukiDF6D4FixedGridShard038OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard038OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 339) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard038OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 339) := by
    rw [suzukiDF6D4FixedGridShard038OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 339
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard038OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard038OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard038OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard038OddDotSoundness i
            suzukiDF6D4FixedGridShard038OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard038OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
