import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard037Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard037Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard037EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard037EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 37 k) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard037EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 37 k)) at h
  exact h

def suzukiDF6D4FixedGridShard037EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard037EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard037EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard037EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard037EvenComparisonData)

theorem suzukiDF6D4FixedGridShard037EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard037EvenSolveData =
      suzukiDF6D4FixedGridShard037EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard037Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard037EvenSolveData =
    suzukiDF6D4FixedGridShard037EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard037EvenCross_eq_live :
    suzukiDF6D4FixedGridShard037EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 37) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard037EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 37)) at h
  exact h

theorem suzukiDF6D4FixedGridShard037EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard037EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 37 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 37 k) := by
    rw [suzukiDF6D4FixedGridShard037EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 37 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037EvenDotSoundness i
          suzukiDF6D4FixedGridShard037EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 37 k) := by
    simpa [suzukiDF6D4FixedGridShard037EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard037EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 37 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 37) := by
    rw [suzukiDF6D4FixedGridShard037EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 37)
  rw [suzukiDF6D4FixedGridShard037EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard037EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard037EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard037EvenDotSoundness i
            suzukiDF6D4FixedGridShard037EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard037EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard037OddComparison_eq_live :
    suzukiDF6D4FixedGridShard037OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 37 k) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard037OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 37 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard037OddCross_eq_live :
    suzukiDF6D4FixedGridShard037OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 37) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard037OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 37)) at h
  exact h

def suzukiDF6D4FixedGridShard037OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard037OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard037OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard037OddDotSoundness i.val
      suzukiDF6D4FixedGridShard037OddComparisonData)

theorem suzukiDF6D4FixedGridShard037OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard037OddSolveData =
      suzukiDF6D4FixedGridShard037OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard037Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard037OddSolveData =
    suzukiDF6D4FixedGridShard037OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard037OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard037OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 37 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 37 k) := by
    rw [suzukiDF6D4FixedGridShard037OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 37 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037OddDotSoundness i
          suzukiDF6D4FixedGridShard037OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 37 k) := by
    simpa [suzukiDF6D4FixedGridShard037OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard037OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 37 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 37) := by
    rw [suzukiDF6D4FixedGridShard037OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 37)
  rw [suzukiDF6D4FixedGridShard037OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard037OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard037OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard037OddDotSoundness i
            suzukiDF6D4FixedGridShard037OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard037OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard037EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard037EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 338) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard037EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 338)) at h
  exact h

theorem suzukiDF6D4FixedGridShard037EvenFull_eq_live :
    suzukiDF6D4FixedGridShard037EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 338) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard037EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 338)) at h
  exact h

def suzukiDF6D4FixedGridShard037EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard037EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard037EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard037EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard037EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard037EvenResidualData =
      suzukiDF6D4FixedGridShard037EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard037Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard037EvenResidualData =
    suzukiDF6D4FixedGridShard037EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard037EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard037EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 338 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 338) := by
    rw [suzukiDF6D4FixedGridShard037EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 338
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037EvenDotSoundness i
          suzukiDF6D4FixedGridShard037EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 338) := by
    simpa [suzukiDF6D4FixedGridShard037EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard037EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 338) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 338) := by
    rw [suzukiDF6D4FixedGridShard037EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 338
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard037EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard037EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard037EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard037EvenDotSoundness i
            suzukiDF6D4FixedGridShard037EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard037EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard037OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard037OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 338) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard037OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 338)) at h
  exact h

theorem suzukiDF6D4FixedGridShard037OddFull_eq_live :
    suzukiDF6D4FixedGridShard037OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 338) := by
  have h := suzukiDF6D4FixedGridShard037Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard037OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 338)) at h
  exact h

def suzukiDF6D4FixedGridShard037OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard037OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard037OddDotSoundness i.val
        suzukiDF6D4FixedGridShard037OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard037OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard037OddResidualData =
      suzukiDF6D4FixedGridShard037OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard037Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard037OddResidualData =
    suzukiDF6D4FixedGridShard037OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard037OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard037OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 338 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 338) := by
    rw [suzukiDF6D4FixedGridShard037OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 338
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037OddDotSoundness i
          suzukiDF6D4FixedGridShard037OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 338) := by
    simpa [suzukiDF6D4FixedGridShard037OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard037OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 338) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard037OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 338) := by
    rw [suzukiDF6D4FixedGridShard037OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 338
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard037OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard037OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard037OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard037OddDotSoundness i
            suzukiDF6D4FixedGridShard037OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard037OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
