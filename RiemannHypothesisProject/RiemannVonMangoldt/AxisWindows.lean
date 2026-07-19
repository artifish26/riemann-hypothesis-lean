import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.AtTopBot.Basic
import RiemannHypothesisProject.RiemannVonMangoldtHeightTarget
import RiemannHypothesisProject.ZetaConjugation
import RiemannHypothesisProject.ZetaSetup

/-!
# Axis-window bookkeeping for Riemann-von-Mangoldt cleanup

This module contains the real-axis closed-ball window split into project-known
trivial zeroes and residual real-axis zeroes, plus the checked linear bound for
the known-trivial contribution.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section

/-- A zeta-zero subtype element is one of the project-known trivial zeroes. -/
def IsKnownTrivialAxisZetaZero (rho : ZetaZeroSubtype) : Prop :=
  IsTrivialZetaZero (rho : Complex)

/-- Known trivial zeta zeroes inside the real-axis closed-ball window. -/
noncomputable def closedBallZeroKnownTrivialAxisFinset
    (n : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact (closedBallZeroAxisOrdinateFinset n).filter
    IsKnownTrivialAxisZetaZero

/--
The residual real-axis closed-ball window after removing the project-known
trivial zeroes.
-/
noncomputable def closedBallZeroResidualRealAxisFinset
    (n : Nat) : Finset ZetaZeroSubtype := by
  classical
  exact (closedBallZeroAxisOrdinateFinset n).filter
    (fun rho : ZetaZeroSubtype => ¬ IsKnownTrivialAxisZetaZero rho)

/-- Membership in the known-trivial axis window. -/
theorem mem_closedBallZeroKnownTrivialAxisFinset
    (n : Nat) {rho : ZetaZeroSubtype} :
    rho ∈ closedBallZeroKnownTrivialAxisFinset n ↔
      rho ∈ closedBallZeroAxisOrdinateFinset n ∧
        IsKnownTrivialAxisZetaZero rho := by
  classical
  simp [closedBallZeroKnownTrivialAxisFinset]

/-- Membership in the residual real-axis window. -/
theorem mem_closedBallZeroResidualRealAxisFinset
    (n : Nat) {rho : ZetaZeroSubtype} :
    rho ∈ closedBallZeroResidualRealAxisFinset n ↔
      rho ∈ closedBallZeroAxisOrdinateFinset n ∧
        ¬ IsKnownTrivialAxisZetaZero rho := by
  classical
  simp [closedBallZeroResidualRealAxisFinset]

/--
The known-trivial and residual real-axis windows partition the full axis
window, at the level of cardinalities.
-/
theorem closedBallZeroKnownTrivialAxis_card_add_residual_card_eq_axis
    (n : Nat) :
    (closedBallZeroKnownTrivialAxisFinset n).card +
        (closedBallZeroResidualRealAxisFinset n).card =
      (closedBallZeroAxisOrdinateFinset n).card := by
  classical
  simpa [closedBallZeroKnownTrivialAxisFinset,
    closedBallZeroResidualRealAxisFinset] using
    (Finset.card_filter_add_card_filter_not
      (s := closedBallZeroAxisOrdinateFinset n)
      (p := IsKnownTrivialAxisZetaZero))

/-- Real-valued cardinality form of the axis-window decomposition. -/
theorem closedBallZeroAxis_card_eq_knownTrivial_add_residual_real
    (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset n).card : Real) =
      ((closedBallZeroKnownTrivialAxisFinset n).card : Real) +
        ((closedBallZeroResidualRealAxisFinset n).card : Real) := by
  exact_mod_cast
    (closedBallZeroKnownTrivialAxis_card_add_residual_card_eq_axis n).symm

/--
Separate bounds for the known-trivial and residual real-axis parts combine into
a bound for the full axis window.
-/
theorem closedBallZeroAxis_card_le_knownTrivial_add_residual_bounds
    (knownTrivialBound residualRealAxisBound : Nat -> Real)
    (knownTrivialCard_le :
      forall n : Nat,
        ((closedBallZeroKnownTrivialAxisFinset n).card : Real) <=
          knownTrivialBound n)
    (residualRealAxisCard_le :
      forall n : Nat,
        ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
          residualRealAxisBound n)
    (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
      knownTrivialBound n + residualRealAxisBound n := by
  rw [closedBallZeroAxis_card_eq_knownTrivial_add_residual_real n]
  exact add_le_add (knownTrivialCard_le n) (residualRealAxisCard_le n)

/--
If both pieces of the axis window have linear index bounds, then so does the
full axis window.
-/
theorem closedBallZeroAxis_card_le_splitLinearAxisBound
    {knownTrivialSlope residualRealAxisSlope : Real}
    (knownTrivialCard_le :
      forall n : Nat,
        ((closedBallZeroKnownTrivialAxisFinset n).card : Real) <=
          knownTrivialSlope * ((n : Real) + 1))
    (residualRealAxisCard_le :
      forall n : Nat,
        ((closedBallZeroResidualRealAxisFinset n).card : Real) <=
          residualRealAxisSlope * ((n : Real) + 1))
    (n : Nat) :
    ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
      (knownTrivialSlope + residualRealAxisSlope) * ((n : Real) + 1) := by
  calc
    ((closedBallZeroAxisOrdinateFinset n).card : Real)
        = ((closedBallZeroKnownTrivialAxisFinset n).card : Real) +
            ((closedBallZeroResidualRealAxisFinset n).card : Real) := by
          rw [closedBallZeroAxis_card_eq_knownTrivial_add_residual_real n]
    _ <= knownTrivialSlope * ((n : Real) + 1) +
          residualRealAxisSlope * ((n : Real) + 1) := by
          exact add_le_add (knownTrivialCard_le n) (residualRealAxisCard_le n)
    _ = (knownTrivialSlope + residualRealAxisSlope) * ((n : Real) + 1) := by
          ring

/--
The project-known trivial zeroes in the real-axis closed-ball window have a
linear count. This is the easy half of the axis/trivial-zero obligation: the
remaining hard part is the residual real-axis window.
-/
theorem closedBallZeroKnownTrivialAxis_card_le_linear
    (n : Nat) :
    ((closedBallZeroKnownTrivialAxisFinset n).card : Real) <=
      1 * ((n : Real) + 1) := by
  classical
  let idx : (closedBallZeroKnownTrivialAxisFinset n) -> Nat := fun rho =>
    Classical.choose
      ((mem_closedBallZeroKnownTrivialAxisFinset n).mp rho.property).2
  have idx_spec :
      forall rho : (closedBallZeroKnownTrivialAxisFinset n),
        (rho.1 : Complex) =
          -2 * (((idx rho : Nat) : Complex) + 1) := by
    intro rho
    dsimp [idx]
    exact Classical.choose_spec
      ((mem_closedBallZeroKnownTrivialAxisFinset n).mp rho.property).2
  have idx_lt : forall rho : (closedBallZeroKnownTrivialAxisFinset n),
      idx rho < n + 1 := by
    intro rho
    have hknown :=
      (mem_closedBallZeroKnownTrivialAxisFinset n).mp rho.property
    have hwindow :
        rho.1 ∈ closedBallZero.zetaZeroSubtypeFinset n :=
      ((mem_closedBallZeroAxisOrdinateFinset n).mp hknown.1).1
    have hmemWindow : (rho.1 : Complex) ∈ closedBallZero.window n :=
      (closedBallZero.mem_zetaZeroSubtypeFinset_iff n).mp hwindow
    have hdist : dist (rho.1 : Complex) 0 <= (n : Real) :=
      (mem_closedBallZero_iff n).mp hmemWindow
    have hnorm : ‖(rho.1 : Complex)‖ <= (n : Real) := by
      simpa [dist_eq_norm] using hdist
    have hnorm_trivial :
        ‖-2 * (((idx rho : Nat) : Complex) + 1)‖ <= (n : Real) := by
      simpa [idx_spec rho] using hnorm
    have hnorm_eq :
        ‖-2 * (((idx rho : Nat) : Complex) + 1)‖ =
          2 * ((idx rho : Real) + 1) := by
      have hsum_cast :
          (((idx rho : Nat) : Complex) + 1) =
            (((idx rho : Real) + 1 : Real) : Complex) := by
        norm_num
      rw [Complex.norm_mul, hsum_cast,
        Complex.norm_of_nonneg (by positivity : 0 <= (idx rho : Real) + 1)]
      norm_num
    rw [hnorm_eq] at hnorm_trivial
    have hidx_real : (idx rho : Real) <= n := by
      nlinarith
    have hidx_nat : idx rho <= n := by
      exact_mod_cast hidx_real
    exact Nat.lt_succ_of_le hidx_nat
  let toRange :
      (closedBallZeroKnownTrivialAxisFinset n) -> (Finset.range (n + 1)) :=
    fun rho => ⟨idx rho, by simpa [Finset.mem_range] using idx_lt rho⟩
  have toRange_injective : Function.Injective toRange := by
    intro rho sigma h
    have hidx : idx rho = idx sigma :=
      congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    calc
      (rho.1 : Complex) =
          -2 * (((idx rho : Nat) : Complex) + 1) := idx_spec rho
      _ = -2 * (((idx sigma : Nat) : Complex) + 1) := by rw [hidx]
      _ = (sigma.1 : Complex) := (idx_spec sigma).symm
  have hcard_nat :
      (closedBallZeroKnownTrivialAxisFinset n).card <=
        (Finset.range (n + 1)).card :=
    Finset.card_le_card_of_injective (f := toRange) toRange_injective
  have hcard_nat' :
      (closedBallZeroKnownTrivialAxisFinset n).card <= n + 1 := by
    simpa using hcard_nat
  have hcard_real :
      ((closedBallZeroKnownTrivialAxisFinset n).card : Real) <=
        (n : Real) + 1 := by
    exact_mod_cast hcard_nat'
  simpa using hcard_real

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
