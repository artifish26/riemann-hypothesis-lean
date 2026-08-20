import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDiagonalIntervalEvaluator
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointConvolutionEnclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFiniteCertificate

/-!
# Analytic entry enclosures for the M100-DF6D4 endpoint certificates

The interval evaluators in this experiment are wider than the generated
`10^-8` grid only where a proved analytic tail requires it.  This module checks
exactly that every such live interval lies inside the corresponding generated
certificate entry, then transports the analytic containment theorems to the
three concrete shifted matrices.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open RationalInterval

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-- Enlarge only the diagonal grid cells of a rational certificate.  The
generated Arb intervals use an outward `10^-8` grid; one further grid cell is
enough to absorb the independently proved analytic-evaluator widths.  The
resulting certificates are checked again below, so this padding is not an
assumption. -/
def suzukiDF6D4PadCertificateDiagonal {n : Nat}
    (c : RationalMatrixCertificate n) (padding : Rat) :
    RationalMatrixCertificate n where
  entry i j :=
    if i.val = j.val then
      ⟨(c.entry i j).lower - padding, (c.entry i j).upper + padding⟩
    else
      c.entry i j
  gramFactor := c.gramFactor

def suzukiDF6D4EvenLowerAnalyticCertificate :
    RationalMatrixCertificate 45 :=
  suzukiDF6D4PadCertificateDiagonal suzukiDF6D4EvenLowerCertificate
    (1 / 100000000)

def suzukiDF6D4OddLowerAnalyticCertificate :
    RationalMatrixCertificate 44 :=
  suzukiDF6D4PadCertificateDiagonal suzukiDF6D4OddLowerCertificate
    (1 / 100000000)

def suzukiDF6D4OddUpperAnalyticCertificate :
    RationalMatrixCertificate 44 :=
  suzukiDF6D4PadCertificateDiagonal suzukiDF6D4OddUpperCertificate
    (1 / 100000000)

theorem suzukiDF6D4EvenLowerAnalyticCertificate_valid :
    suzukiDF6D4EvenLowerAnalyticCertificate.Valid := by
  unfold RationalMatrixCertificate.Valid
  native_decide

theorem suzukiDF6D4OddLowerAnalyticCertificate_valid :
    suzukiDF6D4OddLowerAnalyticCertificate.Valid := by
  unfold RationalMatrixCertificate.Valid
  native_decide

theorem suzukiDF6D4OddUpperAnalyticCertificate_valid :
    suzukiDF6D4OddUpperAnalyticCertificate.Valid := by
  unfold RationalMatrixCertificate.Valid
  native_decide

def suzukiDF6D4EvenLowerDiagonalInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4FrozenEvenDiagonalEntryInterval mode).sub
    (RationalInterval.point (1 / 25000))

def suzukiDF6D4OddLowerDiagonalInterval (mode : Nat) : RationalInterval :=
  (suzukiDF6D4FrozenOddDiagonalEntryInterval mode).sub
    (RationalInterval.point (1 / 200))

def suzukiDF6D4OddUpperDiagonalInterval (mode : Nat) : RationalInterval :=
  (RationalInterval.point 5).sub
    (suzukiDF6D4FrozenOddDiagonalEntryInterval mode)

theorem suzukiDF6D4EvenLowerDiagonalIntervals_admitted :
    ∀ i : Fin 45,
      (suzukiDF6D4EvenLowerAnalyticCertificate.entry i i).lower ≤
          (suzukiDF6D4EvenLowerDiagonalInterval i.val).lower ∧
        (suzukiDF6D4EvenLowerDiagonalInterval i.val).upper ≤
          (suzukiDF6D4EvenLowerAnalyticCertificate.entry i i).upper := by
  native_decide

theorem suzukiDF6D4OddLowerDiagonalIntervals_admitted :
    ∀ i : Fin 44,
      (suzukiDF6D4OddLowerAnalyticCertificate.entry i i).lower ≤
          (suzukiDF6D4OddLowerDiagonalInterval (i.val + 1)).lower ∧
        (suzukiDF6D4OddLowerDiagonalInterval (i.val + 1)).upper ≤
          (suzukiDF6D4OddLowerAnalyticCertificate.entry i i).upper := by
  native_decide

theorem suzukiDF6D4OddUpperDiagonalIntervals_admitted :
    ∀ i : Fin 44,
      (suzukiDF6D4OddUpperAnalyticCertificate.entry i i).lower ≤
          (suzukiDF6D4OddUpperDiagonalInterval (i.val + 1)).lower ∧
        (suzukiDF6D4OddUpperDiagonalInterval (i.val + 1)).upper ≤
          (suzukiDF6D4OddUpperAnalyticCertificate.entry i i).upper := by
  native_decide

/-! ## Complete shifted matrices and their analytic interval grids -/

def suzukiDF6D4EvenLowerMatrix : Matrix (Fin 45) (Fin 45) Real :=
  fun i j =>
    if i.val = j.val then
      suzukiDF6D4EvenDiagonalEntry i.val - (1 / 25000 : Real)
    else
      suzukiDF6D4EvenOffDiagonal (min i.val j.val) (max i.val j.val)

def suzukiDF6D4OddLowerMatrix : Matrix (Fin 44) (Fin 44) Real :=
  fun i j =>
    if i.val = j.val then
      suzukiDF6D4OddDiagonalEntry (i.val + 1) - (1 / 200 : Real)
    else
      suzukiDF6D4OddOffDiagonal
        (min i.val j.val + 1) (max i.val j.val + 1)

def suzukiDF6D4OddUpperMatrix : Matrix (Fin 44) (Fin 44) Real :=
  fun i j =>
    if i.val = j.val then
      5 - suzukiDF6D4OddDiagonalEntry (i.val + 1)
    else
      -suzukiDF6D4OddOffDiagonal
        (min i.val j.val + 1) (max i.val j.val + 1)

def suzukiDF6D4EvenLowerEntryInterval
    (i j : Fin 45) : RationalInterval :=
  if i.val = j.val then
    suzukiDF6D4EvenLowerDiagonalInterval i.val
  else
    suzukiDF6D4FrozenEvenOffDiagonalInterval
      (min i.val j.val) (max i.val j.val)

def suzukiDF6D4OddLowerEntryInterval
    (i j : Fin 44) : RationalInterval :=
  if i.val = j.val then
    suzukiDF6D4OddLowerDiagonalInterval (i.val + 1)
  else
    suzukiDF6D4FrozenOddOffDiagonalInterval
      (min i.val j.val + 1) (max i.val j.val + 1)

def suzukiDF6D4OddUpperEntryInterval
    (i j : Fin 44) : RationalInterval :=
  if i.val = j.val then
    suzukiDF6D4OddUpperDiagonalInterval (i.val + 1)
  else
    (suzukiDF6D4FrozenOddOffDiagonalInterval
      (min i.val j.val + 1) (max i.val j.val + 1)).neg

theorem suzukiDF6D4EvenLowerEntryInterval_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenLowerEntryInterval i j).Contains
      (suzukiDF6D4EvenLowerMatrix i j) := by
  by_cases heq : i.val = j.val
  · have hdiag := suzukiDF6D4FrozenEvenDiagonalEntryInterval_contains
      i.val (by omega)
    have hshift := RationalInterval.contains_point (1 / 25000 : Rat)
    simpa [suzukiDF6D4EvenLowerEntryInterval,
      suzukiDF6D4EvenLowerDiagonalInterval,
      suzukiDF6D4EvenLowerMatrix, heq] using
      (RationalInterval.contains_sub hdiag hshift)
  · by_cases hlt : i.val < j.val
    · have hle : i.val ≤ j.val := Nat.le_of_lt hlt
      simpa [suzukiDF6D4EvenLowerEntryInterval,
        suzukiDF6D4EvenLowerMatrix, heq, Nat.min_eq_left hle,
        Nat.max_eq_right hle] using
        (suzukiDF6D4FrozenEvenOffDiagonalInterval_contains
          i.val j.val hlt (by omega))
    · have hji : j.val < i.val := by omega
      have hle : j.val ≤ i.val := Nat.le_of_lt hji
      simpa [suzukiDF6D4EvenLowerEntryInterval,
        suzukiDF6D4EvenLowerMatrix, heq, Nat.min_eq_right hle,
        Nat.max_eq_left hle] using
        (suzukiDF6D4FrozenEvenOffDiagonalInterval_contains
          j.val i.val hji (by omega))

theorem suzukiDF6D4OddLowerEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddLowerEntryInterval i j).Contains
      (suzukiDF6D4OddLowerMatrix i j) := by
  by_cases heq : i.val = j.val
  · have hdiag := suzukiDF6D4FrozenOddDiagonalEntryInterval_contains
      (i.val + 1) (by omega) (by omega)
    have hshift := RationalInterval.contains_point (1 / 200 : Rat)
    simpa [suzukiDF6D4OddLowerEntryInterval,
      suzukiDF6D4OddLowerDiagonalInterval,
      suzukiDF6D4OddLowerMatrix, heq] using
      (RationalInterval.contains_sub hdiag hshift)
  · by_cases hlt : i.val < j.val
    · have hle : i.val ≤ j.val := Nat.le_of_lt hlt
      simpa [suzukiDF6D4OddLowerEntryInterval,
        suzukiDF6D4OddLowerMatrix, heq, Nat.min_eq_left hle,
        Nat.max_eq_right hle] using
        (suzukiDF6D4FrozenOddOffDiagonalInterval_contains
          (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega))
    · have hji : j.val < i.val := by omega
      have hle : j.val ≤ i.val := Nat.le_of_lt hji
      simpa [suzukiDF6D4OddLowerEntryInterval,
        suzukiDF6D4OddLowerMatrix, heq, Nat.min_eq_right hle,
        Nat.max_eq_left hle] using
        (suzukiDF6D4FrozenOddOffDiagonalInterval_contains
          (j.val + 1) (i.val + 1) (by omega) (by omega) (by omega))

theorem suzukiDF6D4OddUpperEntryInterval_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddUpperEntryInterval i j).Contains
      (suzukiDF6D4OddUpperMatrix i j) := by
  by_cases heq : i.val = j.val
  · have hdiag := suzukiDF6D4FrozenOddDiagonalEntryInterval_contains
      (i.val + 1) (by omega) (by omega)
    have hfive := RationalInterval.contains_point (5 : Rat)
    simpa [suzukiDF6D4OddUpperEntryInterval,
      suzukiDF6D4OddUpperDiagonalInterval,
      suzukiDF6D4OddUpperMatrix, heq] using
      (RationalInterval.contains_sub hfive hdiag)
  · by_cases hlt : i.val < j.val
    · have hle : i.val ≤ j.val := Nat.le_of_lt hlt
      have hoff := suzukiDF6D4FrozenOddOffDiagonalInterval_contains
        (i.val + 1) (j.val + 1) (by omega) (by omega) (by omega)
      simpa [suzukiDF6D4OddUpperEntryInterval,
        suzukiDF6D4OddUpperMatrix, heq, Nat.min_eq_left hle,
        Nat.max_eq_right hle] using RationalInterval.contains_neg hoff
    · have hji : j.val < i.val := by omega
      have hle : j.val ≤ i.val := Nat.le_of_lt hji
      have hoff := suzukiDF6D4FrozenOddOffDiagonalInterval_contains
        (j.val + 1) (i.val + 1) (by omega) (by omega) (by omega)
      simpa [suzukiDF6D4OddUpperEntryInterval,
        suzukiDF6D4OddUpperMatrix, heq, Nat.min_eq_right hle,
        Nat.max_eq_left hle] using RationalInterval.contains_neg hoff

theorem suzukiDF6D4EvenLowerEntryIntervals_admitted :
    ∀ i j : Fin 45,
      (suzukiDF6D4EvenLowerAnalyticCertificate.entry i j).lower ≤
          (suzukiDF6D4EvenLowerEntryInterval i j).lower ∧
        (suzukiDF6D4EvenLowerEntryInterval i j).upper ≤
          (suzukiDF6D4EvenLowerAnalyticCertificate.entry i j).upper := by
  native_decide

theorem suzukiDF6D4OddLowerEntryIntervals_admitted :
    ∀ i j : Fin 44,
      (suzukiDF6D4OddLowerAnalyticCertificate.entry i j).lower ≤
          (suzukiDF6D4OddLowerEntryInterval i j).lower ∧
        (suzukiDF6D4OddLowerEntryInterval i j).upper ≤
          (suzukiDF6D4OddLowerAnalyticCertificate.entry i j).upper := by
  native_decide

theorem suzukiDF6D4OddUpperEntryIntervals_admitted :
    ∀ i j : Fin 44,
      (suzukiDF6D4OddUpperAnalyticCertificate.entry i j).lower ≤
          (suzukiDF6D4OddUpperEntryInterval i j).lower ∧
        (suzukiDF6D4OddUpperEntryInterval i j).upper ≤
          (suzukiDF6D4OddUpperAnalyticCertificate.entry i j).upper := by
  native_decide

theorem suzukiDF6D4EvenLowerMatrix_isHermitian :
    suzukiDF6D4EvenLowerMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases heq : i.val = j.val
  · have hij : i = j := Fin.ext heq
    subst j
    rfl
  · have hne : j.val ≠ i.val := Ne.symm heq
    simp [suzukiDF6D4EvenLowerMatrix, star_trivial, heq, hne,
      Nat.min_comm, Nat.max_comm]

theorem suzukiDF6D4OddLowerMatrix_isHermitian :
    suzukiDF6D4OddLowerMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases heq : i.val = j.val
  · have hij : i = j := Fin.ext heq
    subst j
    rfl
  · have hne : j.val ≠ i.val := Ne.symm heq
    simp [suzukiDF6D4OddLowerMatrix, star_trivial, heq, hne,
      Nat.min_comm, Nat.max_comm]

theorem suzukiDF6D4OddUpperMatrix_isHermitian :
    suzukiDF6D4OddUpperMatrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases heq : i.val = j.val
  · have hij : i = j := Fin.ext heq
    subst j
    rfl
  · have hne : j.val ≠ i.val := Ne.symm heq
    simp [suzukiDF6D4OddUpperMatrix, star_trivial, heq, hne,
      Nat.min_comm, Nat.max_comm]

theorem suzukiDF6D4EvenLowerMatrix_posSemidef :
    suzukiDF6D4EvenLowerMatrix.PosSemidef := by
  refine RationalMatrixCertificate.posSemidef_of_valid_of_entry_enclosures
    suzukiDF6D4EvenLowerAnalyticCertificate
    suzukiDF6D4EvenLowerMatrix
    suzukiDF6D4EvenLowerAnalyticCertificate_valid
    suzukiDF6D4EvenLowerMatrix_isHermitian ?_
  intro i j
  exact RationalInterval.contains_of_widen
    (suzukiDF6D4EvenLowerEntryIntervals_admitted i j).1
    (suzukiDF6D4EvenLowerEntryIntervals_admitted i j).2
    (suzukiDF6D4EvenLowerEntryInterval_contains i j)

theorem suzukiDF6D4OddLowerMatrix_posSemidef :
    suzukiDF6D4OddLowerMatrix.PosSemidef := by
  refine RationalMatrixCertificate.posSemidef_of_valid_of_entry_enclosures
    suzukiDF6D4OddLowerAnalyticCertificate
    suzukiDF6D4OddLowerMatrix
    suzukiDF6D4OddLowerAnalyticCertificate_valid
    suzukiDF6D4OddLowerMatrix_isHermitian ?_
  intro i j
  exact RationalInterval.contains_of_widen
    (suzukiDF6D4OddLowerEntryIntervals_admitted i j).1
    (suzukiDF6D4OddLowerEntryIntervals_admitted i j).2
    (suzukiDF6D4OddLowerEntryInterval_contains i j)

theorem suzukiDF6D4OddUpperMatrix_posSemidef :
    suzukiDF6D4OddUpperMatrix.PosSemidef := by
  refine RationalMatrixCertificate.posSemidef_of_valid_of_entry_enclosures
    suzukiDF6D4OddUpperAnalyticCertificate
    suzukiDF6D4OddUpperMatrix
    suzukiDF6D4OddUpperAnalyticCertificate_valid
    suzukiDF6D4OddUpperMatrix_isHermitian ?_
  intro i j
  exact RationalInterval.contains_of_widen
    (suzukiDF6D4OddUpperEntryIntervals_admitted i j).1
    (suzukiDF6D4OddUpperEntryIntervals_admitted i j).2
    (suzukiDF6D4OddUpperEntryInterval_contains i j)

end

end RiemannHypothesisProject.Experiments.M100
