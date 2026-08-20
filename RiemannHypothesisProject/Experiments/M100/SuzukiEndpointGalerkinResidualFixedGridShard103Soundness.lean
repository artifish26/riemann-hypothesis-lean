import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard103Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard103Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard103EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard103EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 103 k) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard103EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 103 k)) at h
  exact h

def suzukiDF6D4FixedGridShard103EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard103EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard103EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard103EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard103EvenComparisonData)

theorem suzukiDF6D4FixedGridShard103EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard103EvenSolveData =
      suzukiDF6D4FixedGridShard103EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard103Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard103EvenSolveData =
    suzukiDF6D4FixedGridShard103EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard103EvenCross_eq_live :
    suzukiDF6D4FixedGridShard103EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 103) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard103EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 103)) at h
  exact h

theorem suzukiDF6D4FixedGridShard103EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard103EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 103 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 103 k) := by
    rw [suzukiDF6D4FixedGridShard103EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 103 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103EvenDotSoundness i
          suzukiDF6D4FixedGridShard103EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 103 k) := by
    simpa [suzukiDF6D4FixedGridShard103EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard103EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 103 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 103) := by
    rw [suzukiDF6D4FixedGridShard103EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 103)
  rw [suzukiDF6D4FixedGridShard103EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard103EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard103EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard103EvenDotSoundness i
            suzukiDF6D4FixedGridShard103EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard103EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard103OddComparison_eq_live :
    suzukiDF6D4FixedGridShard103OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 103 k) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard103OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 103 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard103OddCross_eq_live :
    suzukiDF6D4FixedGridShard103OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 103) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard103OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 103)) at h
  exact h

def suzukiDF6D4FixedGridShard103OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard103OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard103OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard103OddDotSoundness i.val
      suzukiDF6D4FixedGridShard103OddComparisonData)

theorem suzukiDF6D4FixedGridShard103OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard103OddSolveData =
      suzukiDF6D4FixedGridShard103OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard103Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard103OddSolveData =
    suzukiDF6D4FixedGridShard103OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard103OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard103OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 103 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 103 k) := by
    rw [suzukiDF6D4FixedGridShard103OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 103 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103OddDotSoundness i
          suzukiDF6D4FixedGridShard103OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 103 k) := by
    simpa [suzukiDF6D4FixedGridShard103OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard103OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 103 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 103) := by
    rw [suzukiDF6D4FixedGridShard103OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 103)
  rw [suzukiDF6D4FixedGridShard103OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard103OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard103OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard103OddDotSoundness i
            suzukiDF6D4FixedGridShard103OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard103OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard103EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard103EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 404) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard103EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 404)) at h
  exact h

theorem suzukiDF6D4FixedGridShard103EvenFull_eq_live :
    suzukiDF6D4FixedGridShard103EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 404) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard103EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 404)) at h
  exact h

def suzukiDF6D4FixedGridShard103EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard103EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard103EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard103EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard103EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard103EvenResidualData =
      suzukiDF6D4FixedGridShard103EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard103Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard103EvenResidualData =
    suzukiDF6D4FixedGridShard103EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard103EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard103EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 404 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 404) := by
    rw [suzukiDF6D4FixedGridShard103EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 404
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103EvenDotSoundness i
          suzukiDF6D4FixedGridShard103EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 404) := by
    simpa [suzukiDF6D4FixedGridShard103EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard103EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 404) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 404) := by
    rw [suzukiDF6D4FixedGridShard103EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 404
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard103EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard103EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard103EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard103EvenDotSoundness i
            suzukiDF6D4FixedGridShard103EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard103EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard103OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard103OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 404) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard103OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 404)) at h
  exact h

theorem suzukiDF6D4FixedGridShard103OddFull_eq_live :
    suzukiDF6D4FixedGridShard103OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 404) := by
  have h := suzukiDF6D4FixedGridShard103Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard103OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 404)) at h
  exact h

def suzukiDF6D4FixedGridShard103OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard103OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard103OddDotSoundness i.val
        suzukiDF6D4FixedGridShard103OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard103OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard103OddResidualData =
      suzukiDF6D4FixedGridShard103OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard103Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard103OddResidualData =
    suzukiDF6D4FixedGridShard103OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard103OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard103OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 404 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 404) := by
    rw [suzukiDF6D4FixedGridShard103OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 404
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103OddDotSoundness i
          suzukiDF6D4FixedGridShard103OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 404) := by
    simpa [suzukiDF6D4FixedGridShard103OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard103OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 404) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard103OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 404) := by
    rw [suzukiDF6D4FixedGridShard103OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 404
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard103OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard103OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard103OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard103OddDotSoundness i
            suzukiDF6D4FixedGridShard103OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard103OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
