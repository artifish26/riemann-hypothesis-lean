import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTailAggregate
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDF0Enclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDiagonalIntervalEvaluator

/-!
# Final residual-certificate matrix assembly for M100-DF6D4

This module connects DF0's checked local-energy normalization to the finite
Galerkin residual and analytic-tail matrices.  It freezes the exact even and
odd comparison targets used by FT3 and DF1 and supplies rational entry grids
for the final positive-semidefinite certificate check.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators
open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## DF0 source normalization -/

/-- The strict checked inequality `E_8 > 5 I` gives the `1/5` residual-Gram
coefficient used by both frozen Galerkin certificates. -/
theorem suzukiDF6D4DF0_normSq_le_one_fifth_energy
    {qE normSq : Real} (hnorm : 0 ≤ normSq)
    (henergy : suzukiDF6D4DF0LocalEnergyLower * normSq ≤ qE) :
    normSq ≤ (1 / 5 : Real) * qE := by
  have hfive : 5 * normSq ≤
      suzukiDF6D4DF0LocalEnergyLower * normSq :=
    mul_le_mul_of_nonneg_right
      suzukiDF6D4DF0LocalEnergyLower_gt_five.le hnorm
  calc
    normSq = (1 / 5 : Real) * (5 * normSq) := by ring
    _ ≤ (1 / 5 : Real) * qE :=
      mul_le_mul_of_nonneg_left (hfive.trans henergy) (by norm_num)

def suzukiDF6D4StrictReserve : Rat := 1 / 1000000000

def suzukiDF6D4EvenComparisonCoefficient : Rat := 19 / 1000

def suzukiDF6D4OddComparisonCoefficient : Rat := 2 / 5

def suzukiDF6D4EvenStrictComparisonCoefficient : Rat :=
  suzukiDF6D4EvenComparisonCoefficient * (1 - suzukiDF6D4StrictReserve)

def suzukiDF6D4OddStrictComparisonCoefficient : Rat :=
  suzukiDF6D4OddComparisonCoefficient * (1 - suzukiDF6D4StrictReserve)

/-! ## Unshifted endpoint matrices -/

def suzukiDF6D4EvenEndpointMatrix : Matrix (Fin 45) (Fin 45) Real :=
  fun i j =>
    if i.val = j.val then
      suzukiDF6D4EvenDiagonalEntry i.val
    else
      suzukiDF6D4EvenOffDiagonal (min i.val j.val) (max i.val j.val)

def suzukiDF6D4OddEndpointMatrix : Matrix (Fin 44) (Fin 44) Real :=
  fun i j =>
    if i.val = j.val then
      suzukiDF6D4OddDiagonalEntry (i.val + 1)
    else
      suzukiDF6D4OddOffDiagonal
        (min i.val j.val + 1) (max i.val j.val + 1)

def suzukiDF6D4EvenEndpointEntryInterval
    (i j : Fin 45) : RationalInterval :=
  if i.val = j.val then
    suzukiDF6D4FrozenEvenDiagonalEntryInterval i.val
  else
    suzukiDF6D4FrozenEvenOffDiagonalInterval
      (min i.val j.val) (max i.val j.val)

def suzukiDF6D4OddEndpointEntryInterval
    (i j : Fin 44) : RationalInterval :=
  if i.val = j.val then
    suzukiDF6D4FrozenOddDiagonalEntryInterval (i.val + 1)
  else
    suzukiDF6D4FrozenOddOffDiagonalInterval
      (min i.val j.val + 1) (max i.val j.val + 1)

theorem suzukiDF6D4EvenEndpointEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenEndpointEntryInterval i j).Contains
      (suzukiDF6D4EvenEndpointMatrix i j) := by
  by_cases heq : i.val = j.val
  · simpa [suzukiDF6D4EvenEndpointEntryInterval,
      suzukiDF6D4EvenEndpointMatrix, heq] using
      suzukiDF6D4FrozenEvenDiagonalEntryInterval_contains i.val (by omega)
  · by_cases hlt : i.val < j.val
    · have hle : i.val ≤ j.val := Nat.le_of_lt hlt
      simpa [suzukiDF6D4EvenEndpointEntryInterval,
        suzukiDF6D4EvenEndpointMatrix, heq, Nat.min_eq_left hle,
        Nat.max_eq_right hle] using
        (suzukiDF6D4FrozenEvenOffDiagonalInterval_contains
          i.val j.val hlt (by omega))
    · have hji : j.val < i.val := by omega
      have hle : j.val ≤ i.val := Nat.le_of_lt hji
      simpa [suzukiDF6D4EvenEndpointEntryInterval,
        suzukiDF6D4EvenEndpointMatrix, heq, Nat.min_eq_right hle,
        Nat.max_eq_left hle] using
        (suzukiDF6D4FrozenEvenOffDiagonalInterval_contains
          j.val i.val hji (by omega))

theorem suzukiDF6D4OddEndpointEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddEndpointEntryInterval i j).Contains
      (suzukiDF6D4OddEndpointMatrix i j) := by
  by_cases heq : i.val = j.val
  · simpa [suzukiDF6D4OddEndpointEntryInterval,
      suzukiDF6D4OddEndpointMatrix, heq] using
      suzukiDF6D4FrozenOddDiagonalEntryInterval_contains
        (i.val + 1) (by omega) (by omega)
  · by_cases hlt : i.val < j.val
    · have hle : i.val ≤ j.val := Nat.le_of_lt hlt
      simpa [suzukiDF6D4OddEndpointEntryInterval,
        suzukiDF6D4OddEndpointMatrix, heq, Nat.min_eq_left hle,
        Nat.max_eq_right hle] using
        (suzukiDF6D4FrozenOddOffDiagonalInterval_contains
          (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega))
    · have hji : j.val < i.val := by omega
      have hle : j.val ≤ i.val := Nat.le_of_lt hji
      simpa [suzukiDF6D4OddEndpointEntryInterval,
        suzukiDF6D4OddEndpointMatrix, heq, Nat.min_eq_right hle,
        Nat.max_eq_left hle] using
        (suzukiDF6D4FrozenOddOffDiagonalInterval_contains
          (j.val + 1) (i.val + 1) (by omega) (by omega) (by omega))

/-! ## Finite Galerkin and residual matrices -/

def suzukiDF6D4EvenGalerkinBaseMatrix : Matrix (Fin 45) (Fin 45) Real :=
  fun i j => suzukiDF6D4EvenGalerkinBaseEntry i j

def suzukiDF6D4OddGalerkinBaseMatrix : Matrix (Fin 44) (Fin 44) Real :=
  fun i j => suzukiDF6D4OddGalerkinBaseEntry i j

def suzukiDF6D4EvenFiniteResidualGramMatrix :
    Matrix (Fin 45) (Fin 45) Real :=
  fun i j => suzukiDF6D4EvenFiniteResidualGramEntry i j

def suzukiDF6D4OddFiniteResidualGramMatrix :
    Matrix (Fin 44) (Fin 44) Real :=
  fun i j => suzukiDF6D4OddFiniteResidualGramEntry i j

theorem suzukiDF6D4EvenGalerkinBaseEntryInterval_contains_matrix
    (i j : Fin 45) :
    (suzukiDF6D4EvenGalerkinBaseEntryInterval i j).Contains
      (suzukiDF6D4EvenGalerkinBaseMatrix i j) :=
  suzukiDF6D4EvenGalerkinBaseEntryInterval_contains i j

theorem suzukiDF6D4OddGalerkinBaseEntryInterval_contains_matrix
    (i j : Fin 44) :
    (suzukiDF6D4OddGalerkinBaseEntryInterval i j).Contains
      (suzukiDF6D4OddGalerkinBaseMatrix i j) :=
  suzukiDF6D4OddGalerkinBaseEntryInterval_contains i j

theorem suzukiDF6D4EvenFiniteResidualGramEntryInterval_contains_matrix
    (i j : Fin 45) :
    (suzukiDF6D4EvenFiniteResidualGramEntryInterval i j).Contains
      (suzukiDF6D4EvenFiniteResidualGramMatrix i j) :=
  suzukiDF6D4EvenFiniteResidualGramEntryInterval_contains i j

theorem suzukiDF6D4OddFiniteResidualGramEntryInterval_contains_matrix
    (i j : Fin 44) :
    (suzukiDF6D4OddFiniteResidualGramEntryInterval i j).Contains
      (suzukiDF6D4OddFiniteResidualGramMatrix i j) :=
  suzukiDF6D4OddFiniteResidualGramEntryInterval_contains i j

/-! ## Complete checked coupling upper bounds -/

def suzukiDF6D4EvenCouplingUpperMatrix : Matrix (Fin 45) (Fin 45) Real :=
  suzukiDF6D4EvenGalerkinBaseMatrix +
    (((1 / 5 : Rat) : Real)) • suzukiDF6D4EvenFiniteResidualGramMatrix +
    (((1 / 5 : Rat) : Real)) • suzukiDF6D4EvenAnalyticTailMatrix

def suzukiDF6D4OddCouplingUpperMatrix : Matrix (Fin 44) (Fin 44) Real :=
  suzukiDF6D4OddGalerkinBaseMatrix +
    (((1 / 5 : Rat) : Real)) • suzukiDF6D4OddFiniteResidualGramMatrix +
    (((1 / 5 : Rat) : Real)) • suzukiDF6D4OddAnalyticTailMatrix

def suzukiDF6D4EvenCouplingUpperEntryInterval
    (i j : Fin 45) : RationalInterval :=
  ((suzukiDF6D4EvenGalerkinBaseEntryInterval i j).add
    (RationalInterval.scale (1 / 5)
      (suzukiDF6D4EvenFiniteResidualGramEntryInterval i j))).add
    (RationalInterval.scale (1 / 5)
      (suzukiDF6D4EvenAnalyticTailEntryInterval i j))

def suzukiDF6D4OddCouplingUpperEntryInterval
    (i j : Fin 44) : RationalInterval :=
  ((suzukiDF6D4OddGalerkinBaseEntryInterval i j).add
    (RationalInterval.scale (1 / 5)
      (suzukiDF6D4OddFiniteResidualGramEntryInterval i j))).add
    (RationalInterval.scale (1 / 5)
      (suzukiDF6D4OddAnalyticTailEntryInterval i j))

theorem suzukiDF6D4EvenCouplingUpperEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenCouplingUpperEntryInterval i j).Contains
      (suzukiDF6D4EvenCouplingUpperMatrix i j) := by
  unfold suzukiDF6D4EvenCouplingUpperEntryInterval
    suzukiDF6D4EvenCouplingUpperMatrix
    suzukiDF6D4EvenGalerkinBaseMatrix
    suzukiDF6D4EvenFiniteResidualGramMatrix
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
    RationalInterval.contains_add
      (RationalInterval.contains_add
        (suzukiDF6D4EvenGalerkinBaseEntryInterval_contains i j)
        (RationalInterval.contains_scale (1 / 5)
          (suzukiDF6D4EvenFiniteResidualGramEntryInterval_contains i j)))
      (RationalInterval.contains_scale (1 / 5)
        (suzukiDF6D4EvenAnalyticTailEntryInterval_contains i j))

theorem suzukiDF6D4OddCouplingUpperEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddCouplingUpperEntryInterval i j).Contains
      (suzukiDF6D4OddCouplingUpperMatrix i j) := by
  unfold suzukiDF6D4OddCouplingUpperEntryInterval
    suzukiDF6D4OddCouplingUpperMatrix
    suzukiDF6D4OddGalerkinBaseMatrix
    suzukiDF6D4OddFiniteResidualGramMatrix
  simpa only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
    RationalInterval.contains_add
      (RationalInterval.contains_add
        (suzukiDF6D4OddGalerkinBaseEntryInterval_contains i j)
        (RationalInterval.contains_scale (1 / 5)
          (suzukiDF6D4OddFiniteResidualGramEntryInterval_contains i j)))
      (RationalInterval.contains_scale (1 / 5)
        (suzukiDF6D4OddAnalyticTailEntryInterval_contains i j))

/-! ## Final strict comparison targets -/

def suzukiDF6D4EvenResidualCertificateTargetMatrix :
    Matrix (Fin 45) (Fin 45) Real :=
  ((suzukiDF6D4EvenStrictComparisonCoefficient : Rat) : Real) •
      suzukiDF6D4EvenEndpointMatrix -
    suzukiDF6D4EvenCouplingUpperMatrix

def suzukiDF6D4OddResidualCertificateTargetMatrix :
    Matrix (Fin 44) (Fin 44) Real :=
  ((suzukiDF6D4OddStrictComparisonCoefficient : Rat) : Real) •
      suzukiDF6D4OddEndpointMatrix -
    suzukiDF6D4OddCouplingUpperMatrix

def suzukiDF6D4EvenResidualCertificateTargetEntryInterval
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.scale suzukiDF6D4EvenStrictComparisonCoefficient
    (suzukiDF6D4EvenEndpointEntryInterval i j)).sub
      (suzukiDF6D4EvenCouplingUpperEntryInterval i j)

def suzukiDF6D4OddResidualCertificateTargetEntryInterval
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.scale suzukiDF6D4OddStrictComparisonCoefficient
    (suzukiDF6D4OddEndpointEntryInterval i j)).sub
      (suzukiDF6D4OddCouplingUpperEntryInterval i j)

theorem suzukiDF6D4EvenResidualCertificateTargetEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenResidualCertificateTargetEntryInterval i j).Contains
      (suzukiDF6D4EvenResidualCertificateTargetMatrix i j) := by
  unfold suzukiDF6D4EvenResidualCertificateTargetEntryInterval
    suzukiDF6D4EvenResidualCertificateTargetMatrix
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using
    RationalInterval.contains_sub
      (RationalInterval.contains_scale
        suzukiDF6D4EvenStrictComparisonCoefficient
        (suzukiDF6D4EvenEndpointEntryInterval_contains i j))
      (suzukiDF6D4EvenCouplingUpperEntryInterval_contains i j)

theorem suzukiDF6D4OddResidualCertificateTargetEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddResidualCertificateTargetEntryInterval i j).Contains
      (suzukiDF6D4OddResidualCertificateTargetMatrix i j) := by
  unfold suzukiDF6D4OddResidualCertificateTargetEntryInterval
    suzukiDF6D4OddResidualCertificateTargetMatrix
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using
    RationalInterval.contains_sub
      (RationalInterval.contains_scale
        suzukiDF6D4OddStrictComparisonCoefficient
        (suzukiDF6D4OddEndpointEntryInterval_contains i j))
      (suzukiDF6D4OddCouplingUpperEntryInterval_contains i j)

end

end RiemannHypothesisProject.Experiments.M100
