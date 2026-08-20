import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard076Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard076Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard076EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard076EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 76 k) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard076EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 76 k)) at h
  exact h

def suzukiDF6D4FixedGridShard076EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard076EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard076EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard076EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard076EvenComparisonData)

theorem suzukiDF6D4FixedGridShard076EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard076EvenSolveData =
      suzukiDF6D4FixedGridShard076EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard076Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard076EvenSolveData =
    suzukiDF6D4FixedGridShard076EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard076EvenCross_eq_live :
    suzukiDF6D4FixedGridShard076EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 76) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard076EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 76)) at h
  exact h

theorem suzukiDF6D4FixedGridShard076EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard076EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 76 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 76 k) := by
    rw [suzukiDF6D4FixedGridShard076EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 76 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076EvenDotSoundness i
          suzukiDF6D4FixedGridShard076EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 76 k) := by
    simpa [suzukiDF6D4FixedGridShard076EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard076EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 76 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 76) := by
    rw [suzukiDF6D4FixedGridShard076EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 76)
  rw [suzukiDF6D4FixedGridShard076EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard076EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard076EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard076EvenDotSoundness i
            suzukiDF6D4FixedGridShard076EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard076EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard076OddComparison_eq_live :
    suzukiDF6D4FixedGridShard076OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 76 k) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard076OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 76 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard076OddCross_eq_live :
    suzukiDF6D4FixedGridShard076OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 76) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard076OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 76)) at h
  exact h

def suzukiDF6D4FixedGridShard076OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard076OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard076OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard076OddDotSoundness i.val
      suzukiDF6D4FixedGridShard076OddComparisonData)

theorem suzukiDF6D4FixedGridShard076OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard076OddSolveData =
      suzukiDF6D4FixedGridShard076OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard076Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard076OddSolveData =
    suzukiDF6D4FixedGridShard076OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard076OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard076OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 76 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 76 k) := by
    rw [suzukiDF6D4FixedGridShard076OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 76 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076OddDotSoundness i
          suzukiDF6D4FixedGridShard076OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 76 k) := by
    simpa [suzukiDF6D4FixedGridShard076OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard076OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 76 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 76) := by
    rw [suzukiDF6D4FixedGridShard076OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 76)
  rw [suzukiDF6D4FixedGridShard076OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard076OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard076OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard076OddDotSoundness i
            suzukiDF6D4FixedGridShard076OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard076OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard076EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard076EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 377) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard076EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 377)) at h
  exact h

theorem suzukiDF6D4FixedGridShard076EvenFull_eq_live :
    suzukiDF6D4FixedGridShard076EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 377) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard076EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 377)) at h
  exact h

def suzukiDF6D4FixedGridShard076EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard076EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard076EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard076EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard076EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard076EvenResidualData =
      suzukiDF6D4FixedGridShard076EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard076Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard076EvenResidualData =
    suzukiDF6D4FixedGridShard076EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard076EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard076EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 377 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 377) := by
    rw [suzukiDF6D4FixedGridShard076EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 377
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076EvenDotSoundness i
          suzukiDF6D4FixedGridShard076EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 377) := by
    simpa [suzukiDF6D4FixedGridShard076EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard076EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 377) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 377) := by
    rw [suzukiDF6D4FixedGridShard076EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 377
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard076EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard076EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard076EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard076EvenDotSoundness i
            suzukiDF6D4FixedGridShard076EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard076EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard076OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard076OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 377) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard076OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 377)) at h
  exact h

theorem suzukiDF6D4FixedGridShard076OddFull_eq_live :
    suzukiDF6D4FixedGridShard076OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 377) := by
  have h := suzukiDF6D4FixedGridShard076Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard076OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 377)) at h
  exact h

def suzukiDF6D4FixedGridShard076OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard076OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard076OddDotSoundness i.val
        suzukiDF6D4FixedGridShard076OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard076OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard076OddResidualData =
      suzukiDF6D4FixedGridShard076OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard076Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard076OddResidualData =
    suzukiDF6D4FixedGridShard076OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard076OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard076OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 377 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 377) := by
    rw [suzukiDF6D4FixedGridShard076OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 377
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076OddDotSoundness i
          suzukiDF6D4FixedGridShard076OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 377) := by
    simpa [suzukiDF6D4FixedGridShard076OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard076OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 377) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard076OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 377) := by
    rw [suzukiDF6D4FixedGridShard076OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 377
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard076OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard076OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard076OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard076OddDotSoundness i
            suzukiDF6D4FixedGridShard076OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard076OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
