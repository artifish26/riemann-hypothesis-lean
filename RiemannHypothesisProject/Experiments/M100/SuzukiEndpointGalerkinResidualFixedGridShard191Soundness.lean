import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard191Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard191Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard191EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard191EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 191 k) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard191EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 191 k)) at h
  exact h

def suzukiDF6D4FixedGridShard191EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard191EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard191EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard191EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard191EvenComparisonData)

theorem suzukiDF6D4FixedGridShard191EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard191EvenSolveData =
      suzukiDF6D4FixedGridShard191EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard191Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard191EvenSolveData =
    suzukiDF6D4FixedGridShard191EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard191EvenCross_eq_live :
    suzukiDF6D4FixedGridShard191EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 191) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard191EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 191)) at h
  exact h

theorem suzukiDF6D4FixedGridShard191EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard191EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 191 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 191 k) := by
    rw [suzukiDF6D4FixedGridShard191EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 191 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191EvenDotSoundness i
          suzukiDF6D4FixedGridShard191EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 191 k) := by
    simpa [suzukiDF6D4FixedGridShard191EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard191EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 191 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 191) := by
    rw [suzukiDF6D4FixedGridShard191EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 191)
  rw [suzukiDF6D4FixedGridShard191EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard191EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard191EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard191EvenDotSoundness i
            suzukiDF6D4FixedGridShard191EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard191EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard191OddComparison_eq_live :
    suzukiDF6D4FixedGridShard191OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 191 k) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard191OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 191 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard191OddCross_eq_live :
    suzukiDF6D4FixedGridShard191OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 191) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard191OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 191)) at h
  exact h

def suzukiDF6D4FixedGridShard191OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard191OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard191OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard191OddDotSoundness i.val
      suzukiDF6D4FixedGridShard191OddComparisonData)

theorem suzukiDF6D4FixedGridShard191OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard191OddSolveData =
      suzukiDF6D4FixedGridShard191OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard191Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard191OddSolveData =
    suzukiDF6D4FixedGridShard191OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard191OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard191OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 191 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 191 k) := by
    rw [suzukiDF6D4FixedGridShard191OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 191 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191OddDotSoundness i
          suzukiDF6D4FixedGridShard191OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 191 k) := by
    simpa [suzukiDF6D4FixedGridShard191OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard191OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 191 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 191) := by
    rw [suzukiDF6D4FixedGridShard191OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 191)
  rw [suzukiDF6D4FixedGridShard191OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard191OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard191OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard191OddDotSoundness i
            suzukiDF6D4FixedGridShard191OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard191OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard191EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard191EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 492) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard191EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 492)) at h
  exact h

theorem suzukiDF6D4FixedGridShard191EvenFull_eq_live :
    suzukiDF6D4FixedGridShard191EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 492) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard191EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 492)) at h
  exact h

def suzukiDF6D4FixedGridShard191EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard191EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard191EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard191EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard191EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard191EvenResidualData =
      suzukiDF6D4FixedGridShard191EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard191Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard191EvenResidualData =
    suzukiDF6D4FixedGridShard191EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard191EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard191EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 492 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 492) := by
    rw [suzukiDF6D4FixedGridShard191EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 492
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191EvenDotSoundness i
          suzukiDF6D4FixedGridShard191EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 492) := by
    simpa [suzukiDF6D4FixedGridShard191EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard191EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 492) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 492) := by
    rw [suzukiDF6D4FixedGridShard191EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 492
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard191EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard191EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard191EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard191EvenDotSoundness i
            suzukiDF6D4FixedGridShard191EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard191EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard191OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard191OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 492) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard191OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 492)) at h
  exact h

theorem suzukiDF6D4FixedGridShard191OddFull_eq_live :
    suzukiDF6D4FixedGridShard191OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 492) := by
  have h := suzukiDF6D4FixedGridShard191Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard191OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 492)) at h
  exact h

def suzukiDF6D4FixedGridShard191OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard191OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard191OddDotSoundness i.val
        suzukiDF6D4FixedGridShard191OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard191OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard191OddResidualData =
      suzukiDF6D4FixedGridShard191OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard191Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard191OddResidualData =
    suzukiDF6D4FixedGridShard191OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard191OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard191OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 492 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 492) := by
    rw [suzukiDF6D4FixedGridShard191OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 492
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191OddDotSoundness i
          suzukiDF6D4FixedGridShard191OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 492) := by
    simpa [suzukiDF6D4FixedGridShard191OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard191OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 492) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard191OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 492) := by
    rw [suzukiDF6D4FixedGridShard191OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 492
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard191OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard191OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard191OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard191OddDotSoundness i
            suzukiDF6D4FixedGridShard191OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard191OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
