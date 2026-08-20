import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard079Stage0Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridShard079Stage1Check
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundness

namespace RiemannHypothesisProject.Experiments.M100

set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGridShard079EvenComparison_eq_live :
    suzukiDF6D4FixedGridShard079EvenComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 79 k) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.1.1
  change suzukiDF6D4FixedGridShard079EvenComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 79 k)) at h
  exact h

def suzukiDF6D4FixedGridShard079EvenDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridEvenDotSoundness i a

def suzukiDF6D4FixedGridShard079EvenSolveSoundness := Array.ofFn fun i : Fin 45 =>
  (suzukiDF6D4FixedGridShard079EvenCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard079EvenDotSoundness i.val
      suzukiDF6D4FixedGridShard079EvenComparisonData)

theorem suzukiDF6D4FixedGridShard079EvenSolve_eq_checked :
    suzukiDF6D4FixedGridShard079EvenSolveData =
      suzukiDF6D4FixedGridShard079EvenSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard079Stage1_valid.1.1
  change suzukiDF6D4FixedGridShard079EvenSolveData =
    suzukiDF6D4FixedGridShard079EvenSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard079EvenCross_eq_live :
    suzukiDF6D4FixedGridShard079EvenCrossData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4EvenCompleteCrossEntryInterval i 79) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.1.2.1
  change suzukiDF6D4FixedGridShard079EvenCrossData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4EvenCompleteCrossEntryInterval i 79)) at h
  exact h

theorem suzukiDF6D4FixedGridShard079EvenSolveData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard079EvenSolveData[i.val]!)).Contains
        (suzukiDF6D4EvenGalerkinSolveResidual 79 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079EvenComparisonData[k.val]!)).Contains
          (suzukiDF6D4EvenComparisonGalerkinEntry 79 k) := by
    rw [suzukiDF6D4FixedGridShard079EvenComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval_contains 79 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079EvenDotSoundness i
          suzukiDF6D4FixedGridShard079EvenComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4EvenComparisonGalerkinEntry 79 k) := by
    simpa [suzukiDF6D4FixedGridShard079EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard079EvenComparisonData
        (fun k => suzukiDF6D4EvenComparisonGalerkinEntry 79 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079EvenCrossData[i.val]!)).Contains
          (suzukiDF6D4EvenCompleteCrossEntry i 79) := by
    rw [suzukiDF6D4FixedGridShard079EvenCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4EvenCompleteCrossEntryInterval_contains i 79)
  rw [suzukiDF6D4FixedGridShard079EvenSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard079EvenSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard079EvenCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard079EvenDotSoundness i
            suzukiDF6D4FixedGridShard079EvenComparisonData) := by
    simp [suzukiDF6D4FixedGridShard079EvenSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard079OddComparison_eq_live :
    suzukiDF6D4FixedGridShard079OddComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddComparisonGalerkinEntryInterval 79 k) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.1.2.2.1
  change suzukiDF6D4FixedGridShard079OddComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddComparisonGalerkinEntryInterval 79 k)) at h
  exact h

theorem suzukiDF6D4FixedGridShard079OddCross_eq_live :
    suzukiDF6D4FixedGridShard079OddCrossData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4OddCompleteCrossEntryInterval i 79) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.1.2.2.2
  change suzukiDF6D4FixedGridShard079OddCrossData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4OddCompleteCrossEntryInterval i 79)) at h
  exact h

def suzukiDF6D4FixedGridShard079OddDotSoundness
    (i : Nat) (a : Array FixedGridInterval) :=
  suzukiDF6D4FixedGridOddDotSoundness i a

def suzukiDF6D4FixedGridShard079OddSolveSoundness := Array.ofFn fun i : Fin 44 =>
  (suzukiDF6D4FixedGridShard079OddCrossData[i.val]!).sub
    (suzukiDF6D4FixedGridShard079OddDotSoundness i.val
      suzukiDF6D4FixedGridShard079OddComparisonData)

theorem suzukiDF6D4FixedGridShard079OddSolve_eq_checked :
    suzukiDF6D4FixedGridShard079OddSolveData =
      suzukiDF6D4FixedGridShard079OddSolveSoundness := by
  have h := suzukiDF6D4FixedGridShard079Stage1_valid.1.2
  change suzukiDF6D4FixedGridShard079OddSolveData =
    suzukiDF6D4FixedGridShard079OddSolveSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard079OddSolveData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard079OddSolveData[i.val]!)).Contains
        (suzukiDF6D4OddGalerkinSolveResidual 79 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079OddComparisonData[k.val]!)).Contains
          (suzukiDF6D4OddComparisonGalerkinEntry 79 k) := by
    rw [suzukiDF6D4FixedGridShard079OddComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddComparisonGalerkinEntryInterval_contains 79 k)
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079OddDotSoundness i
          suzukiDF6D4FixedGridShard079OddComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4OddComparisonGalerkinEntry 79 k) := by
    simpa [suzukiDF6D4FixedGridShard079OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard079OddComparisonData
        (fun k => suzukiDF6D4OddComparisonGalerkinEntry 79 k) hx
  have hcross :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079OddCrossData[i.val]!)).Contains
          (suzukiDF6D4OddCompleteCrossEntry i 79) := by
    rw [suzukiDF6D4FixedGridShard079OddCross_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4OddCompleteCrossEntryInterval_contains i 79)
  rw [suzukiDF6D4FixedGridShard079OddSolve_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard079OddSolveSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard079OddCrossData[i.val]!).sub
          (suzukiDF6D4FixedGridShard079OddDotSoundness i
            suzukiDF6D4FixedGridShard079OddComparisonData) := by
    simp [suzukiDF6D4FixedGridShard079OddSolveSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hcross (by
    simpa only [mul_comm] using hdot')

theorem suzukiDF6D4FixedGridShard079EvenResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard079EvenResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 380) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.2.1
  change suzukiDF6D4FixedGridShard079EvenResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 380)) at h
  exact h

theorem suzukiDF6D4FixedGridShard079EvenFull_eq_live :
    suzukiDF6D4FixedGridShard079EvenFullData =
      Array.ofFn fun i : Fin 45 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullEvenOffDiagonalInterval
            (suzukiDF6D4EvenLowMode i) 380) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.2.2.1
  change suzukiDF6D4FixedGridShard079EvenFullData =
    Array.ofFn (fun i : Fin 45 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) 380)) at h
  exact h

def suzukiDF6D4FixedGridShard079EvenResidualSoundness :=
  Array.ofFn fun i : Fin 45 =>
    (suzukiDF6D4FixedGridShard079EvenFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard079EvenDotSoundness i.val
        suzukiDF6D4FixedGridShard079EvenResidualComparisonData)

theorem suzukiDF6D4FixedGridShard079EvenResidual_eq_checked :
    suzukiDF6D4FixedGridShard079EvenResidualData =
      suzukiDF6D4FixedGridShard079EvenResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard079Stage1_valid.2.1
  change suzukiDF6D4FixedGridShard079EvenResidualData =
    suzukiDF6D4FixedGridShard079EvenResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard079EvenResidualData_contains (i : Fin 45) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard079EvenResidualData[i.val]!)).Contains
        (suzukiDF6D4EvenResidualColumn 380 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079EvenResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) 380) := by
    rw [suzukiDF6D4FixedGridShard079EvenResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 380
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega)
        (by omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079EvenDotSoundness i
          suzukiDF6D4FixedGridShard079EvenResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4EvenGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonEvenOffDiagonal
              (suzukiDF6D4GalerkinMode k) 380) := by
    simpa [suzukiDF6D4FixedGridShard079EvenDotSoundness] using
      suzukiDF6D4FixedGridEvenDotSoundness_contains i
        suzukiDF6D4FixedGridShard079EvenResidualComparisonData
        (fun k => suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) 380) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079EvenFullData[i.val]!)).Contains
          (suzukiDF6D4EvenOffDiagonal (suzukiDF6D4EvenLowMode i) 380) := by
    rw [suzukiDF6D4FixedGridShard079EvenFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullEvenOffDiagonalInterval_contains
        (suzukiDF6D4EvenLowMode i) 380
        (by simp [suzukiDF6D4EvenLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard079EvenResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard079EvenResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard079EvenFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard079EvenDotSoundness i
            suzukiDF6D4FixedGridShard079EvenResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard079EvenResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

theorem suzukiDF6D4FixedGridShard079OddResidualComparison_eq_live :
    suzukiDF6D4FixedGridShard079OddResidualComparisonData =
      Array.ofFn fun k : Fin 256 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) 380) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.2.2.2.1
  change suzukiDF6D4FixedGridShard079OddResidualComparisonData =
    Array.ofFn (fun k : Fin 256 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4ComparisonOddOffDiagonalInterval
          (suzukiDF6D4GalerkinMode k) 380)) at h
  exact h

theorem suzukiDF6D4FixedGridShard079OddFull_eq_live :
    suzukiDF6D4FixedGridShard079OddFullData =
      Array.ofFn fun i : Fin 44 =>
        FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
          (suzukiDF6D4FullOddOffDiagonalInterval
            (suzukiDF6D4OddLowMode i) 380) := by
  have h := suzukiDF6D4FixedGridShard079Stage0_valid.2.2.2.2
  change suzukiDF6D4FixedGridShard079OddFullData =
    Array.ofFn (fun i : Fin 44 =>
      FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) 380)) at h
  exact h

def suzukiDF6D4FixedGridShard079OddResidualSoundness :=
  Array.ofFn fun i : Fin 44 =>
    (suzukiDF6D4FixedGridShard079OddFullData[i.val]!).sub
      (suzukiDF6D4FixedGridShard079OddDotSoundness i.val
        suzukiDF6D4FixedGridShard079OddResidualComparisonData)

theorem suzukiDF6D4FixedGridShard079OddResidual_eq_checked :
    suzukiDF6D4FixedGridShard079OddResidualData =
      suzukiDF6D4FixedGridShard079OddResidualSoundness := by
  have h := suzukiDF6D4FixedGridShard079Stage1_valid.2.2
  change suzukiDF6D4FixedGridShard079OddResidualData =
    suzukiDF6D4FixedGridShard079OddResidualSoundness at h
  exact h

theorem suzukiDF6D4FixedGridShard079OddResidualData_contains (i : Fin 44) :
    (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
      (suzukiDF6D4FixedGridShard079OddResidualData[i.val]!)).Contains
        (suzukiDF6D4OddResidualColumn 380 i) := by
  have hx (k : Fin 256) :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079OddResidualComparisonData[k.val]!)).Contains
          (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) 380) := by
    rw [suzukiDF6D4FixedGridShard079OddResidualComparison_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4ComparisonOddOffDiagonalInterval_contains
        (suzukiDF6D4GalerkinMode k) 380
        (by simp [suzukiDF6D4GalerkinMode])
        (by have := k.isLt; simp [suzukiDF6D4GalerkinMode] at *; omega))
  have hdot' :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079OddDotSoundness i
          suzukiDF6D4FixedGridShard079OddResidualComparisonData)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4OddGalerkinApproximant k i : Rat) : Real) *
            suzukiDF6D4ComparisonOddOffDiagonal
              (suzukiDF6D4GalerkinMode k) 380) := by
    simpa [suzukiDF6D4FixedGridShard079OddDotSoundness] using
      suzukiDF6D4FixedGridOddDotSoundness_contains i
        suzukiDF6D4FixedGridShard079OddResidualComparisonData
        (fun k => suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) 380) hx
  have hfull :
      (FixedGridInterval.toRationalInterval suzukiDF6D4FixedGridDenominator
        (suzukiDF6D4FixedGridShard079OddFullData[i.val]!)).Contains
          (suzukiDF6D4OddOffDiagonal (suzukiDF6D4OddLowMode i) 380) := by
    rw [suzukiDF6D4FixedGridShard079OddFull_eq_live]
    simpa using FixedGridInterval.contains_ofRationalInterval
      suzukiDF6D4FixedGridDenominator_pos
      (suzukiDF6D4FullOddOffDiagonalInterval_contains
        (suzukiDF6D4OddLowMode i) 380
        (by simp [suzukiDF6D4OddLowMode])
        (by simp [suzukiDF6D4OddLowMode]; omega)
        (by omega))
  rw [suzukiDF6D4FixedGridShard079OddResidual_eq_checked]
  have hentry :
      suzukiDF6D4FixedGridShard079OddResidualSoundness[i.val]! =
        (suzukiDF6D4FixedGridShard079OddFullData[i.val]!).sub
          (suzukiDF6D4FixedGridShard079OddDotSoundness i
            suzukiDF6D4FixedGridShard079OddResidualComparisonData) := by
    simp [suzukiDF6D4FixedGridShard079OddResidualSoundness, i.isLt]
  rw [hentry]
  exact FixedGridInterval.contains_sub hfull hdot'

end RiemannHypothesisProject.Experiments.M100
