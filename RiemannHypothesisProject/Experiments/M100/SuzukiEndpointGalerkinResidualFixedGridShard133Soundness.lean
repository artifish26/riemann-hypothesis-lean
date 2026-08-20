import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard133Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard133Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard133EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard133EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 133 k) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard133EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 133 k)) at h
  exact h

def suzukiDF6D4FixedGridShard133EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard133EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard133EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard133EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard133EvenComparisonData)

theorem suzukiDF6D4FixedGridShard133EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard133EvenSolveData =
      suzukiDF6D4FixedGridShard133EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard133Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard133EvenSolveData =
    suzukiDF6D4FixedGridShard133EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard133EvenCross_eq_live :
    suzukiDF6D4FixedGridShard133EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 133) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard133EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 133)) at h
  exact h

theorem suzukiDF6D4FixedGridShard133EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard133EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 133 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 133 k) := by
    rw [suzukiDF6D4FixedGridShard133EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 133 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133EvenDotSoundness i
          suzukiDF6D4FixedGridShard133EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 133 k) := by
    simpa [suzukiDF6D4FixedGridShard133EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard133EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 133 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 133) := by
    rw [suzukiDF6D4FixedGridShard133EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 133)
  rw [suzukiDF6D4FixedGridShard133EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard133EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard133EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard133EvenDotSoundness i
            suzukiDF6D4FixedGridShard133EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard133EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard133OddComparison_eq_live :
    suzukiDF6D4FixedGridShard133OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 133 k) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard133OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 133 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard133OddCross_eq_live :
    suzukiDF6D4FixedGridShard133OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 133) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard133OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 133)) at h
  exact h

def suzukiDF6D4FixedGridShard133OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard133OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard133OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard133OddDotSoundness i.val
      suzukiDF6D4FixedGridShard133OddComparisonData)

theorem suzukiDF6D4FixedGridShard133OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard133OddSolveData =
      suzukiDF6D4FixedGridShard133OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard133Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard133OddSolveData =
    suzukiDF6D4FixedGridShard133OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard133OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard133OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 133 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 133 k) := by
    rw [suzukiDF6D4FixedGridShard133OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 133 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133OddDotSoundness i
          suzukiDF6D4FixedGridShard133OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 133 k) := by
    simpa [suzukiDF6D4FixedGridShard133OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard133OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 133 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 133) := by
    rw [suzukiDF6D4FixedGridShard133OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 133)
  rw [suzukiDF6D4FixedGridShard133OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard133OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard133OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard133OddDotSoundness i
            suzukiDF6D4FixedGridShard133OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard133OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard133EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard133EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 434) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard133EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 434)) at h
  exact h

theorem suzukiDF6D4FixedGridShard133EvenFull_eq_live :
    suzukiDF6D4FixedGridShard133EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 434) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard133EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 434)) at h
  exact h

def suzukiDF6D4FixedGridShard133EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard133EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard133EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard133EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard133EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard133EvenResidualData =
      suzukiDF6D4FixedGridShard133EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard133Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard133EvenResidualData =
    suzukiDF6D4FixedGridShard133EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard133EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard133EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 434 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 434) := by
    rw [suzukiDF6D4FixedGridShard133EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 434
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133EvenDotSoundness i
          suzukiDF6D4FixedGridShard133EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 434) := by
    simpa [suzukiDF6D4FixedGridShard133EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard133EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 434) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 434) := by
    rw [suzukiDF6D4FixedGridShard133EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 434
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard133EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard133EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard133EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard133EvenDotSoundness i
            suzukiDF6D4FixedGridShard133EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard133EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard133OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard133OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 434) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard133OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 434)) at h
  exact h

theorem suzukiDF6D4FixedGridShard133OddFull_eq_live :
    suzukiDF6D4FixedGridShard133OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 434) := by
  have h := suzukiDF6D4FixedGridShard133Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard133OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 434)) at h
  exact h

def suzukiDF6D4FixedGridShard133OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard133OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard133OddDotSoundness i.val
        suzukiDF6D4FixedGridShard133OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard133OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard133OddResidualData =
      suzukiDF6D4FixedGridShard133OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard133Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard133OddResidualData =
    suzukiDF6D4FixedGridShard133OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard133OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard133OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 434 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 434) := by
    rw [suzukiDF6D4FixedGridShard133OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 434
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133OddDotSoundness i
          suzukiDF6D4FixedGridShard133OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 434) := by
    simpa [suzukiDF6D4FixedGridShard133OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard133OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 434) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard133OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 434) := by
    rw [suzukiDF6D4FixedGridShard133OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 434
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard133OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard133OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard133OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard133OddDotSoundness i
            suzukiDF6D4FixedGridShard133OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard133OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
