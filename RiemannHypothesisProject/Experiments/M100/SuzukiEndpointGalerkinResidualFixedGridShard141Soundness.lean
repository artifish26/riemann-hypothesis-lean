import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard141Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard141Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard141EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard141EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 141 k) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard141EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 141 k)) at h
  exact h

def suzukiDF6D4FixedGridShard141EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard141EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard141EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard141EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard141EvenComparisonData)

theorem suzukiDF6D4FixedGridShard141EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard141EvenSolveData =
      suzukiDF6D4FixedGridShard141EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard141Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard141EvenSolveData =
    suzukiDF6D4FixedGridShard141EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard141EvenCross_eq_live :
    suzukiDF6D4FixedGridShard141EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 141) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard141EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 141)) at h
  exact h

theorem suzukiDF6D4FixedGridShard141EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard141EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 141 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 141 k) := by
    rw [suzukiDF6D4FixedGridShard141EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 141 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141EvenDotSoundness i
          suzukiDF6D4FixedGridShard141EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 141 k) := by
    simpa [suzukiDF6D4FixedGridShard141EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard141EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 141 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 141) := by
    rw [suzukiDF6D4FixedGridShard141EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 141)
  rw [suzukiDF6D4FixedGridShard141EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard141EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard141EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard141EvenDotSoundness i
            suzukiDF6D4FixedGridShard141EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard141EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard141OddComparison_eq_live :
    suzukiDF6D4FixedGridShard141OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 141 k) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard141OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 141 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard141OddCross_eq_live :
    suzukiDF6D4FixedGridShard141OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 141) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard141OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 141)) at h
  exact h

def suzukiDF6D4FixedGridShard141OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard141OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard141OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard141OddDotSoundness i.val
      suzukiDF6D4FixedGridShard141OddComparisonData)

theorem suzukiDF6D4FixedGridShard141OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard141OddSolveData =
      suzukiDF6D4FixedGridShard141OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard141Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard141OddSolveData =
    suzukiDF6D4FixedGridShard141OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard141OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard141OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 141 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 141 k) := by
    rw [suzukiDF6D4FixedGridShard141OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 141 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141OddDotSoundness i
          suzukiDF6D4FixedGridShard141OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 141 k) := by
    simpa [suzukiDF6D4FixedGridShard141OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard141OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 141 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 141) := by
    rw [suzukiDF6D4FixedGridShard141OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 141)
  rw [suzukiDF6D4FixedGridShard141OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard141OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard141OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard141OddDotSoundness i
            suzukiDF6D4FixedGridShard141OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard141OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard141EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard141EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 442) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard141EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 442)) at h
  exact h

theorem suzukiDF6D4FixedGridShard141EvenFull_eq_live :
    suzukiDF6D4FixedGridShard141EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 442) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard141EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 442)) at h
  exact h

def suzukiDF6D4FixedGridShard141EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard141EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard141EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard141EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard141EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard141EvenResidualData =
      suzukiDF6D4FixedGridShard141EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard141Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard141EvenResidualData =
    suzukiDF6D4FixedGridShard141EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard141EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard141EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 442 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 442) := by
    rw [suzukiDF6D4FixedGridShard141EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 442
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141EvenDotSoundness i
          suzukiDF6D4FixedGridShard141EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 442) := by
    simpa [suzukiDF6D4FixedGridShard141EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard141EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 442) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 442) := by
    rw [suzukiDF6D4FixedGridShard141EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 442
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard141EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard141EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard141EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard141EvenDotSoundness i
            suzukiDF6D4FixedGridShard141EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard141EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard141OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard141OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 442) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard141OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 442)) at h
  exact h

theorem suzukiDF6D4FixedGridShard141OddFull_eq_live :
    suzukiDF6D4FixedGridShard141OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 442) := by
  have h := suzukiDF6D4FixedGridShard141Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard141OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 442)) at h
  exact h

def suzukiDF6D4FixedGridShard141OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard141OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard141OddDotSoundness i.val
        suzukiDF6D4FixedGridShard141OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard141OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard141OddResidualData =
      suzukiDF6D4FixedGridShard141OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard141Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard141OddResidualData =
    suzukiDF6D4FixedGridShard141OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard141OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard141OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 442 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 442) := by
    rw [suzukiDF6D4FixedGridShard141OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 442
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141OddDotSoundness i
          suzukiDF6D4FixedGridShard141OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 442) := by
    simpa [suzukiDF6D4FixedGridShard141OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard141OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 442) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard141OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 442) := by
    rw [suzukiDF6D4FixedGridShard141OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 442
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard141OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard141OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard141OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard141OddDotSoundness i
            suzukiDF6D4FixedGridShard141OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard141OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
