import RiemannHypothesisProject.SchwartzRiemannWeilTailEstimates

/-!
# Standard compact exhaustions

This file provides concrete compact exhaustions that later analytic estimates
can target.  The first one is the usual exhaustion of `Complex` by closed balls
centered at zero with natural-number radii.
-/

namespace RiemannHypothesisProject

open Filter

namespace ComplexCompactExhaustion

/-- The standard exhaustion of `Complex` by closed balls centered at zero. -/
noncomputable def closedBallZero : ComplexCompactExhaustion where
  window := fun n : Nat => Metric.closedBall (0 : Complex) (n : Real)
  compact_window := fun n => isCompact_closedBall (0 : Complex) (n : Real)
  monotone_window := by
    intro m n hmn
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  eventually_mem := by
    intro z
    rcases exists_nat_ge (dist z (0 : Complex)) with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Metric.mem_closedBall.mpr <| hN.trans (by exact_mod_cast hn)

/-- Membership in the standard closed-ball exhaustion. -/
theorem mem_closedBallZero_iff (n : Nat) {z : Complex} :
    z ∈ closedBallZero.window n ↔ dist z (0 : Complex) ≤ (n : Real) :=
  Iff.rfl

/--
The zero-counting target for the standard closed-ball exhaustion: prove a
polynomial bound for cumulative zeta zeroes in closed balls centered at zero.
-/
abbrev ClosedBallZeroCumulativeWindowCountingEstimate :=
  SchwartzRiemannWeilCumulativeWindowCountingEstimate closedBallZero

end ComplexCompactExhaustion

end RiemannHypothesisProject
