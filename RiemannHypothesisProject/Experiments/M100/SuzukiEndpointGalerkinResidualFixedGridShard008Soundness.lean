import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard008Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard008Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard008EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard008EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 8 k) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard008EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 8 k)) at h
  exact h

def suzukiDF6D4FixedGridShard008EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard008EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard008EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard008EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard008EvenComparisonData)

theorem suzukiDF6D4FixedGridShard008EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard008EvenSolveData =
      suzukiDF6D4FixedGridShard008EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard008Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard008EvenSolveData =
    suzukiDF6D4FixedGridShard008EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard008EvenCross_eq_live :
    suzukiDF6D4FixedGridShard008EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 8) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard008EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 8)) at h
  exact h

theorem suzukiDF6D4FixedGridShard008EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard008EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 8 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 8 k) := by
    rw [suzukiDF6D4FixedGridShard008EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 8 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008EvenDotSoundness i
          suzukiDF6D4FixedGridShard008EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 8 k) := by
    simpa [suzukiDF6D4FixedGridShard008EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard008EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 8 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 8) := by
    rw [suzukiDF6D4FixedGridShard008EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 8)
  rw [suzukiDF6D4FixedGridShard008EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard008EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard008EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard008EvenDotSoundness i
            suzukiDF6D4FixedGridShard008EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard008EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard008OddComparison_eq_live :
    suzukiDF6D4FixedGridShard008OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 8 k) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard008OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 8 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard008OddCross_eq_live :
    suzukiDF6D4FixedGridShard008OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 8) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard008OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 8)) at h
  exact h

def suzukiDF6D4FixedGridShard008OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard008OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard008OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard008OddDotSoundness i.val
      suzukiDF6D4FixedGridShard008OddComparisonData)

theorem suzukiDF6D4FixedGridShard008OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard008OddSolveData =
      suzukiDF6D4FixedGridShard008OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard008Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard008OddSolveData =
    suzukiDF6D4FixedGridShard008OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard008OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard008OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 8 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 8 k) := by
    rw [suzukiDF6D4FixedGridShard008OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 8 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008OddDotSoundness i
          suzukiDF6D4FixedGridShard008OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 8 k) := by
    simpa [suzukiDF6D4FixedGridShard008OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard008OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 8 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 8) := by
    rw [suzukiDF6D4FixedGridShard008OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 8)
  rw [suzukiDF6D4FixedGridShard008OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard008OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard008OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard008OddDotSoundness i
            suzukiDF6D4FixedGridShard008OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard008OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard008EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard008EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 309) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard008EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 309)) at h
  exact h

theorem suzukiDF6D4FixedGridShard008EvenFull_eq_live :
    suzukiDF6D4FixedGridShard008EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 309) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard008EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 309)) at h
  exact h

def suzukiDF6D4FixedGridShard008EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard008EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard008EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard008EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard008EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard008EvenResidualData =
      suzukiDF6D4FixedGridShard008EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard008Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard008EvenResidualData =
    suzukiDF6D4FixedGridShard008EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard008EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard008EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 309 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 309) := by
    rw [suzukiDF6D4FixedGridShard008EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 309
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008EvenDotSoundness i
          suzukiDF6D4FixedGridShard008EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 309) := by
    simpa [suzukiDF6D4FixedGridShard008EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard008EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 309) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 309) := by
    rw [suzukiDF6D4FixedGridShard008EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 309
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard008EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard008EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard008EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard008EvenDotSoundness i
            suzukiDF6D4FixedGridShard008EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard008EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard008OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard008OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 309) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard008OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 309)) at h
  exact h

theorem suzukiDF6D4FixedGridShard008OddFull_eq_live :
    suzukiDF6D4FixedGridShard008OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 309) := by
  have h := suzukiDF6D4FixedGridShard008Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard008OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 309)) at h
  exact h

def suzukiDF6D4FixedGridShard008OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard008OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard008OddDotSoundness i.val
        suzukiDF6D4FixedGridShard008OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard008OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard008OddResidualData =
      suzukiDF6D4FixedGridShard008OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard008Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard008OddResidualData =
    suzukiDF6D4FixedGridShard008OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard008OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard008OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 309 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 309) := by
    rw [suzukiDF6D4FixedGridShard008OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 309
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008OddDotSoundness i
          suzukiDF6D4FixedGridShard008OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 309) := by
    simpa [suzukiDF6D4FixedGridShard008OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard008OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 309) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard008OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 309) := by
    rw [suzukiDF6D4FixedGridShard008OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 309
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard008OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard008OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard008OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard008OddDotSoundness i
            suzukiDF6D4FixedGridShard008OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard008OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
