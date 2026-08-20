import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard100Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard100Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard100EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard100EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 100 k) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard100EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 100 k)) at h
  exact h

def suzukiDF6D4FixedGridShard100EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard100EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard100EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard100EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard100EvenComparisonData)

theorem suzukiDF6D4FixedGridShard100EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard100EvenSolveData =
      suzukiDF6D4FixedGridShard100EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard100Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard100EvenSolveData =
    suzukiDF6D4FixedGridShard100EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard100EvenCross_eq_live :
    suzukiDF6D4FixedGridShard100EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 100) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard100EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 100)) at h
  exact h

theorem suzukiDF6D4FixedGridShard100EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard100EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 100 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 100 k) := by
    rw [suzukiDF6D4FixedGridShard100EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 100 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100EvenDotSoundness i
          suzukiDF6D4FixedGridShard100EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 100 k) := by
    simpa [suzukiDF6D4FixedGridShard100EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard100EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 100 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 100) := by
    rw [suzukiDF6D4FixedGridShard100EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 100)
  rw [suzukiDF6D4FixedGridShard100EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard100EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard100EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard100EvenDotSoundness i
            suzukiDF6D4FixedGridShard100EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard100EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard100OddComparison_eq_live :
    suzukiDF6D4FixedGridShard100OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 100 k) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard100OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 100 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard100OddCross_eq_live :
    suzukiDF6D4FixedGridShard100OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 100) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard100OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 100)) at h
  exact h

def suzukiDF6D4FixedGridShard100OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard100OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard100OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard100OddDotSoundness i.val
      suzukiDF6D4FixedGridShard100OddComparisonData)

theorem suzukiDF6D4FixedGridShard100OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard100OddSolveData =
      suzukiDF6D4FixedGridShard100OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard100Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard100OddSolveData =
    suzukiDF6D4FixedGridShard100OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard100OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard100OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 100 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 100 k) := by
    rw [suzukiDF6D4FixedGridShard100OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 100 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100OddDotSoundness i
          suzukiDF6D4FixedGridShard100OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 100 k) := by
    simpa [suzukiDF6D4FixedGridShard100OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard100OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 100 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 100) := by
    rw [suzukiDF6D4FixedGridShard100OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 100)
  rw [suzukiDF6D4FixedGridShard100OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard100OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard100OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard100OddDotSoundness i
            suzukiDF6D4FixedGridShard100OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard100OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard100EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard100EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 401) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard100EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 401)) at h
  exact h

theorem suzukiDF6D4FixedGridShard100EvenFull_eq_live :
    suzukiDF6D4FixedGridShard100EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 401) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard100EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 401)) at h
  exact h

def suzukiDF6D4FixedGridShard100EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard100EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard100EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard100EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard100EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard100EvenResidualData =
      suzukiDF6D4FixedGridShard100EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard100Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard100EvenResidualData =
    suzukiDF6D4FixedGridShard100EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard100EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard100EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 401 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 401) := by
    rw [suzukiDF6D4FixedGridShard100EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 401
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100EvenDotSoundness i
          suzukiDF6D4FixedGridShard100EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 401) := by
    simpa [suzukiDF6D4FixedGridShard100EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard100EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 401) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 401) := by
    rw [suzukiDF6D4FixedGridShard100EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 401
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard100EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard100EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard100EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard100EvenDotSoundness i
            suzukiDF6D4FixedGridShard100EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard100EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard100OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard100OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 401) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard100OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 401)) at h
  exact h

theorem suzukiDF6D4FixedGridShard100OddFull_eq_live :
    suzukiDF6D4FixedGridShard100OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 401) := by
  have h := suzukiDF6D4FixedGridShard100Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard100OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 401)) at h
  exact h

def suzukiDF6D4FixedGridShard100OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard100OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard100OddDotSoundness i.val
        suzukiDF6D4FixedGridShard100OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard100OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard100OddResidualData =
      suzukiDF6D4FixedGridShard100OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard100Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard100OddResidualData =
    suzukiDF6D4FixedGridShard100OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard100OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard100OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 401 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 401) := by
    rw [suzukiDF6D4FixedGridShard100OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 401
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100OddDotSoundness i
          suzukiDF6D4FixedGridShard100OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 401) := by
    simpa [suzukiDF6D4FixedGridShard100OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard100OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 401) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard100OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 401) := by
    rw [suzukiDF6D4FixedGridShard100OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 401
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard100OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard100OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard100OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard100OddDotSoundness i
            suzukiDF6D4FixedGridShard100OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard100OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
