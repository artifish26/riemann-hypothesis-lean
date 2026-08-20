import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard225Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard225Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard225EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard225EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 225 k) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard225EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 225 k)) at h
  exact h

def suzukiDF6D4FixedGridShard225EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard225EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard225EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard225EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard225EvenComparisonData)

theorem suzukiDF6D4FixedGridShard225EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard225EvenSolveData =
      suzukiDF6D4FixedGridShard225EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard225Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard225EvenSolveData =
    suzukiDF6D4FixedGridShard225EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard225EvenCross_eq_live :
    suzukiDF6D4FixedGridShard225EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 225) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard225EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 225)) at h
  exact h

theorem suzukiDF6D4FixedGridShard225EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard225EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 225 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 225 k) := by
    rw [suzukiDF6D4FixedGridShard225EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 225 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225EvenDotSoundness i
          suzukiDF6D4FixedGridShard225EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 225 k) := by
    simpa [suzukiDF6D4FixedGridShard225EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard225EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 225 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 225) := by
    rw [suzukiDF6D4FixedGridShard225EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 225)
  rw [suzukiDF6D4FixedGridShard225EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard225EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard225EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard225EvenDotSoundness i
            suzukiDF6D4FixedGridShard225EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard225EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard225OddComparison_eq_live :
    suzukiDF6D4FixedGridShard225OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 225 k) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard225OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 225 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard225OddCross_eq_live :
    suzukiDF6D4FixedGridShard225OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 225) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard225OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 225)) at h
  exact h

def suzukiDF6D4FixedGridShard225OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard225OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard225OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard225OddDotSoundness i.val
      suzukiDF6D4FixedGridShard225OddComparisonData)

theorem suzukiDF6D4FixedGridShard225OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard225OddSolveData =
      suzukiDF6D4FixedGridShard225OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard225Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard225OddSolveData =
    suzukiDF6D4FixedGridShard225OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard225OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard225OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 225 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 225 k) := by
    rw [suzukiDF6D4FixedGridShard225OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 225 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225OddDotSoundness i
          suzukiDF6D4FixedGridShard225OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 225 k) := by
    simpa [suzukiDF6D4FixedGridShard225OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard225OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 225 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 225) := by
    rw [suzukiDF6D4FixedGridShard225OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 225)
  rw [suzukiDF6D4FixedGridShard225OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard225OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard225OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard225OddDotSoundness i
            suzukiDF6D4FixedGridShard225OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard225OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard225EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard225EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 526) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard225EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 526)) at h
  exact h

theorem suzukiDF6D4FixedGridShard225EvenFull_eq_live :
    suzukiDF6D4FixedGridShard225EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 526) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard225EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 526)) at h
  exact h

def suzukiDF6D4FixedGridShard225EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard225EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard225EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard225EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard225EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard225EvenResidualData =
      suzukiDF6D4FixedGridShard225EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard225Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard225EvenResidualData =
    suzukiDF6D4FixedGridShard225EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard225EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard225EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 526 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 526) := by
    rw [suzukiDF6D4FixedGridShard225EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 526
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225EvenDotSoundness i
          suzukiDF6D4FixedGridShard225EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 526) := by
    simpa [suzukiDF6D4FixedGridShard225EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard225EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 526) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 526) := by
    rw [suzukiDF6D4FixedGridShard225EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 526
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard225EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard225EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard225EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard225EvenDotSoundness i
            suzukiDF6D4FixedGridShard225EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard225EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard225OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard225OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 526) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard225OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 526)) at h
  exact h

theorem suzukiDF6D4FixedGridShard225OddFull_eq_live :
    suzukiDF6D4FixedGridShard225OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 526) := by
  have h := suzukiDF6D4FixedGridShard225Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard225OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 526)) at h
  exact h

def suzukiDF6D4FixedGridShard225OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard225OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard225OddDotSoundness i.val
        suzukiDF6D4FixedGridShard225OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard225OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard225OddResidualData =
      suzukiDF6D4FixedGridShard225OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard225Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard225OddResidualData =
    suzukiDF6D4FixedGridShard225OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard225OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard225OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 526 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 526) := by
    rw [suzukiDF6D4FixedGridShard225OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 526
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225OddDotSoundness i
          suzukiDF6D4FixedGridShard225OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 526) := by
    simpa [suzukiDF6D4FixedGridShard225OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard225OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 526) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard225OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 526) := by
    rw [suzukiDF6D4FixedGridShard225OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 526
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard225OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard225OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard225OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard225OddDotSoundness i
            suzukiDF6D4FixedGridShard225OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard225OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
