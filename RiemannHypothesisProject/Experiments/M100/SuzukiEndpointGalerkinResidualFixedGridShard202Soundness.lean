import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard202Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard202Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard202EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard202EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 202 k) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard202EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 202 k)) at h
  exact h

def suzukiDF6D4FixedGridShard202EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard202EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard202EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard202EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard202EvenComparisonData)

theorem suzukiDF6D4FixedGridShard202EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard202EvenSolveData =
      suzukiDF6D4FixedGridShard202EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard202Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard202EvenSolveData =
    suzukiDF6D4FixedGridShard202EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard202EvenCross_eq_live :
    suzukiDF6D4FixedGridShard202EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 202) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard202EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 202)) at h
  exact h

theorem suzukiDF6D4FixedGridShard202EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard202EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 202 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 202 k) := by
    rw [suzukiDF6D4FixedGridShard202EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 202 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202EvenDotSoundness i
          suzukiDF6D4FixedGridShard202EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 202 k) := by
    simpa [suzukiDF6D4FixedGridShard202EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard202EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 202 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 202) := by
    rw [suzukiDF6D4FixedGridShard202EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 202)
  rw [suzukiDF6D4FixedGridShard202EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard202EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard202EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard202EvenDotSoundness i
            suzukiDF6D4FixedGridShard202EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard202EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard202OddComparison_eq_live :
    suzukiDF6D4FixedGridShard202OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 202 k) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard202OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 202 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard202OddCross_eq_live :
    suzukiDF6D4FixedGridShard202OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 202) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard202OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 202)) at h
  exact h

def suzukiDF6D4FixedGridShard202OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard202OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard202OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard202OddDotSoundness i.val
      suzukiDF6D4FixedGridShard202OddComparisonData)

theorem suzukiDF6D4FixedGridShard202OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard202OddSolveData =
      suzukiDF6D4FixedGridShard202OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard202Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard202OddSolveData =
    suzukiDF6D4FixedGridShard202OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard202OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard202OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 202 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 202 k) := by
    rw [suzukiDF6D4FixedGridShard202OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 202 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202OddDotSoundness i
          suzukiDF6D4FixedGridShard202OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 202 k) := by
    simpa [suzukiDF6D4FixedGridShard202OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard202OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 202 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 202) := by
    rw [suzukiDF6D4FixedGridShard202OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 202)
  rw [suzukiDF6D4FixedGridShard202OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard202OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard202OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard202OddDotSoundness i
            suzukiDF6D4FixedGridShard202OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard202OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard202EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard202EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 503) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard202EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 503)) at h
  exact h

theorem suzukiDF6D4FixedGridShard202EvenFull_eq_live :
    suzukiDF6D4FixedGridShard202EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 503) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard202EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 503)) at h
  exact h

def suzukiDF6D4FixedGridShard202EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard202EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard202EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard202EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard202EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard202EvenResidualData =
      suzukiDF6D4FixedGridShard202EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard202Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard202EvenResidualData =
    suzukiDF6D4FixedGridShard202EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard202EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard202EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 503 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 503) := by
    rw [suzukiDF6D4FixedGridShard202EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 503
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202EvenDotSoundness i
          suzukiDF6D4FixedGridShard202EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 503) := by
    simpa [suzukiDF6D4FixedGridShard202EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard202EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 503) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 503) := by
    rw [suzukiDF6D4FixedGridShard202EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 503
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard202EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard202EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard202EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard202EvenDotSoundness i
            suzukiDF6D4FixedGridShard202EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard202EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard202OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard202OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 503) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard202OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 503)) at h
  exact h

theorem suzukiDF6D4FixedGridShard202OddFull_eq_live :
    suzukiDF6D4FixedGridShard202OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 503) := by
  have h := suzukiDF6D4FixedGridShard202Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard202OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 503)) at h
  exact h

def suzukiDF6D4FixedGridShard202OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard202OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard202OddDotSoundness i.val
        suzukiDF6D4FixedGridShard202OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard202OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard202OddResidualData =
      suzukiDF6D4FixedGridShard202OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard202Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard202OddResidualData =
    suzukiDF6D4FixedGridShard202OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard202OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard202OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 503 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 503) := by
    rw [suzukiDF6D4FixedGridShard202OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 503
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202OddDotSoundness i
          suzukiDF6D4FixedGridShard202OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 503) := by
    simpa [suzukiDF6D4FixedGridShard202OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard202OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 503) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard202OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 503) := by
    rw [suzukiDF6D4FixedGridShard202OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 503
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard202OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard202OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard202OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard202OddDotSoundness i
            suzukiDF6D4FixedGridShard202OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard202OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
