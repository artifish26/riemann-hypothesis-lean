import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard228Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard228Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard228EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard228EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 228 k) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard228EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 228 k)) at h
  exact h

def suzukiDF6D4FixedGridShard228EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard228EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard228EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard228EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard228EvenComparisonData)

theorem suzukiDF6D4FixedGridShard228EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard228EvenSolveData =
      suzukiDF6D4FixedGridShard228EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard228Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard228EvenSolveData =
    suzukiDF6D4FixedGridShard228EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard228EvenCross_eq_live :
    suzukiDF6D4FixedGridShard228EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 228) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard228EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 228)) at h
  exact h

theorem suzukiDF6D4FixedGridShard228EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard228EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 228 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 228 k) := by
    rw [suzukiDF6D4FixedGridShard228EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 228 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228EvenDotSoundness i
          suzukiDF6D4FixedGridShard228EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 228 k) := by
    simpa [suzukiDF6D4FixedGridShard228EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard228EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 228 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 228) := by
    rw [suzukiDF6D4FixedGridShard228EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 228)
  rw [suzukiDF6D4FixedGridShard228EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard228EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard228EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard228EvenDotSoundness i
            suzukiDF6D4FixedGridShard228EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard228EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard228OddComparison_eq_live :
    suzukiDF6D4FixedGridShard228OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 228 k) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard228OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 228 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard228OddCross_eq_live :
    suzukiDF6D4FixedGridShard228OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 228) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard228OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 228)) at h
  exact h

def suzukiDF6D4FixedGridShard228OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard228OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard228OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard228OddDotSoundness i.val
      suzukiDF6D4FixedGridShard228OddComparisonData)

theorem suzukiDF6D4FixedGridShard228OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard228OddSolveData =
      suzukiDF6D4FixedGridShard228OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard228Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard228OddSolveData =
    suzukiDF6D4FixedGridShard228OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard228OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard228OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 228 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 228 k) := by
    rw [suzukiDF6D4FixedGridShard228OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 228 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228OddDotSoundness i
          suzukiDF6D4FixedGridShard228OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 228 k) := by
    simpa [suzukiDF6D4FixedGridShard228OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard228OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 228 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 228) := by
    rw [suzukiDF6D4FixedGridShard228OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 228)
  rw [suzukiDF6D4FixedGridShard228OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard228OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard228OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard228OddDotSoundness i
            suzukiDF6D4FixedGridShard228OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard228OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard228EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard228EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 529) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard228EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 529)) at h
  exact h

theorem suzukiDF6D4FixedGridShard228EvenFull_eq_live :
    suzukiDF6D4FixedGridShard228EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 529) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard228EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 529)) at h
  exact h

def suzukiDF6D4FixedGridShard228EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard228EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard228EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard228EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard228EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard228EvenResidualData =
      suzukiDF6D4FixedGridShard228EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard228Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard228EvenResidualData =
    suzukiDF6D4FixedGridShard228EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard228EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard228EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 529 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 529) := by
    rw [suzukiDF6D4FixedGridShard228EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 529
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228EvenDotSoundness i
          suzukiDF6D4FixedGridShard228EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 529) := by
    simpa [suzukiDF6D4FixedGridShard228EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard228EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 529) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 529) := by
    rw [suzukiDF6D4FixedGridShard228EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 529
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard228EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard228EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard228EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard228EvenDotSoundness i
            suzukiDF6D4FixedGridShard228EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard228EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard228OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard228OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 529) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard228OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 529)) at h
  exact h

theorem suzukiDF6D4FixedGridShard228OddFull_eq_live :
    suzukiDF6D4FixedGridShard228OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 529) := by
  have h := suzukiDF6D4FixedGridShard228Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard228OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 529)) at h
  exact h

def suzukiDF6D4FixedGridShard228OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard228OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard228OddDotSoundness i.val
        suzukiDF6D4FixedGridShard228OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard228OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard228OddResidualData =
      suzukiDF6D4FixedGridShard228OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard228Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard228OddResidualData =
    suzukiDF6D4FixedGridShard228OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard228OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard228OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 529 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 529) := by
    rw [suzukiDF6D4FixedGridShard228OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 529
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228OddDotSoundness i
          suzukiDF6D4FixedGridShard228OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 529) := by
    simpa [suzukiDF6D4FixedGridShard228OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard228OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 529) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard228OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 529) := by
    rw [suzukiDF6D4FixedGridShard228OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 529
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard228OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard228OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard228OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard228OddDotSoundness i
            suzukiDF6D4FixedGridShard228OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard228OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
