import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard184Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard184Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard184EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard184EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 184 k) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard184EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 184 k)) at h
  exact h

def suzukiDF6D4FixedGridShard184EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard184EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard184EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard184EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard184EvenComparisonData)

theorem suzukiDF6D4FixedGridShard184EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard184EvenSolveData =
      suzukiDF6D4FixedGridShard184EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard184Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard184EvenSolveData =
    suzukiDF6D4FixedGridShard184EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard184EvenCross_eq_live :
    suzukiDF6D4FixedGridShard184EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 184) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard184EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 184)) at h
  exact h

theorem suzukiDF6D4FixedGridShard184EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard184EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 184 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 184 k) := by
    rw [suzukiDF6D4FixedGridShard184EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 184 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184EvenDotSoundness i
          suzukiDF6D4FixedGridShard184EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 184 k) := by
    simpa [suzukiDF6D4FixedGridShard184EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard184EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 184 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 184) := by
    rw [suzukiDF6D4FixedGridShard184EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 184)
  rw [suzukiDF6D4FixedGridShard184EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard184EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard184EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard184EvenDotSoundness i
            suzukiDF6D4FixedGridShard184EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard184EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard184OddComparison_eq_live :
    suzukiDF6D4FixedGridShard184OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 184 k) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard184OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 184 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard184OddCross_eq_live :
    suzukiDF6D4FixedGridShard184OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 184) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard184OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 184)) at h
  exact h

def suzukiDF6D4FixedGridShard184OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard184OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard184OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard184OddDotSoundness i.val
      suzukiDF6D4FixedGridShard184OddComparisonData)

theorem suzukiDF6D4FixedGridShard184OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard184OddSolveData =
      suzukiDF6D4FixedGridShard184OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard184Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard184OddSolveData =
    suzukiDF6D4FixedGridShard184OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard184OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard184OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 184 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 184 k) := by
    rw [suzukiDF6D4FixedGridShard184OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 184 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184OddDotSoundness i
          suzukiDF6D4FixedGridShard184OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 184 k) := by
    simpa [suzukiDF6D4FixedGridShard184OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard184OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 184 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 184) := by
    rw [suzukiDF6D4FixedGridShard184OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 184)
  rw [suzukiDF6D4FixedGridShard184OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard184OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard184OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard184OddDotSoundness i
            suzukiDF6D4FixedGridShard184OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard184OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard184EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard184EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 485) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard184EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 485)) at h
  exact h

theorem suzukiDF6D4FixedGridShard184EvenFull_eq_live :
    suzukiDF6D4FixedGridShard184EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 485) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard184EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 485)) at h
  exact h

def suzukiDF6D4FixedGridShard184EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard184EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard184EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard184EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard184EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard184EvenResidualData =
      suzukiDF6D4FixedGridShard184EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard184Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard184EvenResidualData =
    suzukiDF6D4FixedGridShard184EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard184EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard184EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 485 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 485) := by
    rw [suzukiDF6D4FixedGridShard184EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 485
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184EvenDotSoundness i
          suzukiDF6D4FixedGridShard184EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 485) := by
    simpa [suzukiDF6D4FixedGridShard184EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard184EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 485) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 485) := by
    rw [suzukiDF6D4FixedGridShard184EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 485
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard184EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard184EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard184EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard184EvenDotSoundness i
            suzukiDF6D4FixedGridShard184EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard184EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard184OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard184OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 485) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard184OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 485)) at h
  exact h

theorem suzukiDF6D4FixedGridShard184OddFull_eq_live :
    suzukiDF6D4FixedGridShard184OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 485) := by
  have h := suzukiDF6D4FixedGridShard184Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard184OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 485)) at h
  exact h

def suzukiDF6D4FixedGridShard184OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard184OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard184OddDotSoundness i.val
        suzukiDF6D4FixedGridShard184OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard184OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard184OddResidualData =
      suzukiDF6D4FixedGridShard184OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard184Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard184OddResidualData =
    suzukiDF6D4FixedGridShard184OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard184OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard184OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 485 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 485) := by
    rw [suzukiDF6D4FixedGridShard184OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 485
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184OddDotSoundness i
          suzukiDF6D4FixedGridShard184OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 485) := by
    simpa [suzukiDF6D4FixedGridShard184OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard184OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 485) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard184OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 485) := by
    rw [suzukiDF6D4FixedGridShard184OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 485
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard184OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard184OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard184OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard184OddDotSoundness i
            suzukiDF6D4FixedGridShard184OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard184OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
