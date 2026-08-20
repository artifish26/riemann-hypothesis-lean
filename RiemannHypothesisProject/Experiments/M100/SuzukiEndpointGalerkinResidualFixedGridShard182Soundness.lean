import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard182Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard182Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard182EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard182EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 182 k) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard182EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 182 k)) at h
  exact h

def suzukiDF6D4FixedGridShard182EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard182EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard182EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard182EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard182EvenComparisonData)

theorem suzukiDF6D4FixedGridShard182EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard182EvenSolveData =
      suzukiDF6D4FixedGridShard182EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard182Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard182EvenSolveData =
    suzukiDF6D4FixedGridShard182EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard182EvenCross_eq_live :
    suzukiDF6D4FixedGridShard182EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 182) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard182EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 182)) at h
  exact h

theorem suzukiDF6D4FixedGridShard182EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard182EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 182 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 182 k) := by
    rw [suzukiDF6D4FixedGridShard182EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 182 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182EvenDotSoundness i
          suzukiDF6D4FixedGridShard182EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 182 k) := by
    simpa [suzukiDF6D4FixedGridShard182EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard182EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 182 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 182) := by
    rw [suzukiDF6D4FixedGridShard182EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 182)
  rw [suzukiDF6D4FixedGridShard182EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard182EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard182EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard182EvenDotSoundness i
            suzukiDF6D4FixedGridShard182EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard182EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard182OddComparison_eq_live :
    suzukiDF6D4FixedGridShard182OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 182 k) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard182OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 182 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard182OddCross_eq_live :
    suzukiDF6D4FixedGridShard182OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 182) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard182OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 182)) at h
  exact h

def suzukiDF6D4FixedGridShard182OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard182OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard182OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard182OddDotSoundness i.val
      suzukiDF6D4FixedGridShard182OddComparisonData)

theorem suzukiDF6D4FixedGridShard182OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard182OddSolveData =
      suzukiDF6D4FixedGridShard182OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard182Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard182OddSolveData =
    suzukiDF6D4FixedGridShard182OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard182OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard182OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 182 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 182 k) := by
    rw [suzukiDF6D4FixedGridShard182OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 182 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182OddDotSoundness i
          suzukiDF6D4FixedGridShard182OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 182 k) := by
    simpa [suzukiDF6D4FixedGridShard182OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard182OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 182 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 182) := by
    rw [suzukiDF6D4FixedGridShard182OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 182)
  rw [suzukiDF6D4FixedGridShard182OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard182OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard182OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard182OddDotSoundness i
            suzukiDF6D4FixedGridShard182OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard182OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard182EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard182EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 483) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard182EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 483)) at h
  exact h

theorem suzukiDF6D4FixedGridShard182EvenFull_eq_live :
    suzukiDF6D4FixedGridShard182EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 483) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard182EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 483)) at h
  exact h

def suzukiDF6D4FixedGridShard182EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard182EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard182EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard182EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard182EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard182EvenResidualData =
      suzukiDF6D4FixedGridShard182EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard182Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard182EvenResidualData =
    suzukiDF6D4FixedGridShard182EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard182EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard182EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 483 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 483) := by
    rw [suzukiDF6D4FixedGridShard182EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 483
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182EvenDotSoundness i
          suzukiDF6D4FixedGridShard182EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 483) := by
    simpa [suzukiDF6D4FixedGridShard182EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard182EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 483) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 483) := by
    rw [suzukiDF6D4FixedGridShard182EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 483
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard182EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard182EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard182EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard182EvenDotSoundness i
            suzukiDF6D4FixedGridShard182EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard182EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard182OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard182OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 483) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard182OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 483)) at h
  exact h

theorem suzukiDF6D4FixedGridShard182OddFull_eq_live :
    suzukiDF6D4FixedGridShard182OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 483) := by
  have h := suzukiDF6D4FixedGridShard182Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard182OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 483)) at h
  exact h

def suzukiDF6D4FixedGridShard182OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard182OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard182OddDotSoundness i.val
        suzukiDF6D4FixedGridShard182OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard182OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard182OddResidualData =
      suzukiDF6D4FixedGridShard182OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard182Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard182OddResidualData =
    suzukiDF6D4FixedGridShard182OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard182OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard182OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 483 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 483) := by
    rw [suzukiDF6D4FixedGridShard182OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 483
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182OddDotSoundness i
          suzukiDF6D4FixedGridShard182OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 483) := by
    simpa [suzukiDF6D4FixedGridShard182OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard182OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 483) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard182OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 483) := by
    rw [suzukiDF6D4FixedGridShard182OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 483
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard182OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard182OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard182OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard182OddDotSoundness i
            suzukiDF6D4FixedGridShard182OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard182OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
