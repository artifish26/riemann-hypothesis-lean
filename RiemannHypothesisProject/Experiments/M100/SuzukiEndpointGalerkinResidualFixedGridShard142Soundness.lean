import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard142Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard142Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard142EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard142EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 142 k) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard142EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 142 k)) at h
  exact h

def suzukiDF6D4FixedGridShard142EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard142EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard142EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard142EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard142EvenComparisonData)

theorem suzukiDF6D4FixedGridShard142EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard142EvenSolveData =
      suzukiDF6D4FixedGridShard142EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard142Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard142EvenSolveData =
    suzukiDF6D4FixedGridShard142EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard142EvenCross_eq_live :
    suzukiDF6D4FixedGridShard142EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 142) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard142EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 142)) at h
  exact h

theorem suzukiDF6D4FixedGridShard142EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard142EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 142 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 142 k) := by
    rw [suzukiDF6D4FixedGridShard142EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 142 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142EvenDotSoundness i
          suzukiDF6D4FixedGridShard142EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 142 k) := by
    simpa [suzukiDF6D4FixedGridShard142EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard142EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 142 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 142) := by
    rw [suzukiDF6D4FixedGridShard142EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 142)
  rw [suzukiDF6D4FixedGridShard142EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard142EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard142EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard142EvenDotSoundness i
            suzukiDF6D4FixedGridShard142EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard142EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard142OddComparison_eq_live :
    suzukiDF6D4FixedGridShard142OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 142 k) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard142OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 142 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard142OddCross_eq_live :
    suzukiDF6D4FixedGridShard142OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 142) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard142OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 142)) at h
  exact h

def suzukiDF6D4FixedGridShard142OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard142OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard142OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard142OddDotSoundness i.val
      suzukiDF6D4FixedGridShard142OddComparisonData)

theorem suzukiDF6D4FixedGridShard142OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard142OddSolveData =
      suzukiDF6D4FixedGridShard142OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard142Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard142OddSolveData =
    suzukiDF6D4FixedGridShard142OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard142OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard142OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 142 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 142 k) := by
    rw [suzukiDF6D4FixedGridShard142OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 142 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142OddDotSoundness i
          suzukiDF6D4FixedGridShard142OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 142 k) := by
    simpa [suzukiDF6D4FixedGridShard142OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard142OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 142 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 142) := by
    rw [suzukiDF6D4FixedGridShard142OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 142)
  rw [suzukiDF6D4FixedGridShard142OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard142OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard142OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard142OddDotSoundness i
            suzukiDF6D4FixedGridShard142OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard142OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard142EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard142EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 443) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard142EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 443)) at h
  exact h

theorem suzukiDF6D4FixedGridShard142EvenFull_eq_live :
    suzukiDF6D4FixedGridShard142EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 443) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard142EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 443)) at h
  exact h

def suzukiDF6D4FixedGridShard142EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard142EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard142EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard142EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard142EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard142EvenResidualData =
      suzukiDF6D4FixedGridShard142EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard142Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard142EvenResidualData =
    suzukiDF6D4FixedGridShard142EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard142EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard142EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 443 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 443) := by
    rw [suzukiDF6D4FixedGridShard142EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 443
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142EvenDotSoundness i
          suzukiDF6D4FixedGridShard142EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 443) := by
    simpa [suzukiDF6D4FixedGridShard142EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard142EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 443) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 443) := by
    rw [suzukiDF6D4FixedGridShard142EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 443
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard142EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard142EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard142EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard142EvenDotSoundness i
            suzukiDF6D4FixedGridShard142EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard142EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard142OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard142OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 443) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard142OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 443)) at h
  exact h

theorem suzukiDF6D4FixedGridShard142OddFull_eq_live :
    suzukiDF6D4FixedGridShard142OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 443) := by
  have h := suzukiDF6D4FixedGridShard142Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard142OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 443)) at h
  exact h

def suzukiDF6D4FixedGridShard142OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard142OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard142OddDotSoundness i.val
        suzukiDF6D4FixedGridShard142OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard142OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard142OddResidualData =
      suzukiDF6D4FixedGridShard142OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard142Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard142OddResidualData =
    suzukiDF6D4FixedGridShard142OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard142OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard142OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 443 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 443) := by
    rw [suzukiDF6D4FixedGridShard142OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 443
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142OddDotSoundness i
          suzukiDF6D4FixedGridShard142OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 443) := by
    simpa [suzukiDF6D4FixedGridShard142OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard142OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 443) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard142OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 443) := by
    rw [suzukiDF6D4FixedGridShard142OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 443
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard142OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard142OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard142OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard142OddDotSoundness i
            suzukiDF6D4FixedGridShard142OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard142OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
