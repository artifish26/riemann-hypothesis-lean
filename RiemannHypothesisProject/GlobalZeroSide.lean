import RiemannHypothesisProject.ZetaZeroCofinite
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Global zero-side weights

This file starts the passage from finite zeta-zero windows to a global zero
side. The mathematical content of a real explicit formula is not asserted here;
instead we isolate the convergence mechanism it will need.

If a weight on the zeta-zero subtype is summable, then sums over any compact
exhaustion of the zero set converge to the global `tsum`.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/-- Sum a zeta-zero weight over the `n`th finite window of a compact exhaustion. -/
noncomputable def ComplexCompactExhaustion.zetaZeroWindowSum
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (weight : ZetaZeroSubtype → ℝ) : ℝ :=
  (exhaustion.zetaZeroSubtypeFinset n).sum weight

/--
For a summable weight on actual zeta zeroes, the finite sums over a compact
exhaustion converge to the global zero-side `tsum`.
-/
theorem ComplexCompactExhaustion.tendsto_zetaZeroWindowSum
    (exhaustion : ComplexCompactExhaustion)
    {weight : ZetaZeroSubtype → ℝ}
    (hweight : Summable weight) :
    Tendsto (fun n : ℕ => exhaustion.zetaZeroWindowSum n weight)
      atTop (𝓝 (∑' z : ZetaZeroSubtype, weight z)) := by
  have hfinsets :
      Tendsto (fun n : ℕ => exhaustion.zetaZeroSubtypeFinset n)
        atTop (atTop : Filter (Finset ZetaZeroSubtype)) :=
    Filter.tendsto_atTop_finset_of_monotone
      (fun m n hmn => exhaustion.zetaZeroSubtypeFinset_mono hmn)
      (fun z => (exhaustion.eventually_mem_zetaZeroSubtypeFinset z).exists)
  simpa [ComplexCompactExhaustion.zetaZeroWindowSum, Function.comp_def] using
    hweight.hasSum.comp hfinsets

/--
A global zeta-zero side for a class of test functions.

The field `weight f` is the contribution of each actual zeta zero to the zero
side for the test function `f`. The summability field is the analytic hypothesis
needed to turn this into a genuine global `tsum`.
-/
structure GlobalZetaZeroSide (TestFunction : Type) where
  weight : TestFunction → ZetaZeroSubtype → ℝ
  summable_weight : ∀ f : TestFunction, Summable (weight f)

namespace GlobalZetaZeroSide

/-- The global zero-side value of a summable zeta-zero side. -/
noncomputable def zeroSide {TestFunction : Type}
    (side : GlobalZetaZeroSide TestFunction) (f : TestFunction) : ℝ :=
  ∑' z : ZetaZeroSubtype, side.weight f z

/-- The `n`th compact-exhaustion window sum for a global zeta-zero side. -/
noncomputable def windowZeroSide {TestFunction : Type}
    (side : GlobalZetaZeroSide TestFunction)
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (f : TestFunction) : ℝ :=
  exhaustion.zetaZeroWindowSum n (side.weight f)

/-- Window zero sides converge to the global zero side along any compact exhaustion. -/
theorem tendsto_windowZeroSide {TestFunction : Type}
    (side : GlobalZetaZeroSide TestFunction)
    (exhaustion : ComplexCompactExhaustion)
    (f : TestFunction) :
    Tendsto (fun n : ℕ => side.windowZeroSide exhaustion n f)
      atTop (𝓝 (side.zeroSide f)) := by
  unfold windowZeroSide zeroSide
  exact exhaustion.tendsto_zetaZeroWindowSum (side.summable_weight f)

/-- Build a global zeta-zero side from weights supported in one compact set. -/
def of_supportedInCompact {TestFunction : Type}
    (K : Set ℂ) (hK : IsCompact K)
    (weight : TestFunction → ZetaZeroSubtype → ℝ)
    (hweight : ∀ f : TestFunction,
      ZetaZeroWeightSupportedInCompact K (weight f)) :
    GlobalZetaZeroSide TestFunction where
  weight := weight
  summable_weight := fun f =>
    zetaZeroWeight_summable_of_supportedInCompact K hK (hweight f)

/-- A compactly supported global zero side reduces to a finite compact-window sum. -/
theorem zeroSide_eq_sum_compact_of_supportedInCompact {TestFunction : Type}
    (side : GlobalZetaZeroSide TestFunction)
    (K : Set ℂ) (hK : IsCompact K)
    (hside : ∀ f : TestFunction,
      ZetaZeroWeightSupportedInCompact K (side.weight f))
    (f : TestFunction) :
    side.zeroSide f =
      (compactZetaZeroSubtypeFinset K hK).sum (side.weight f) := by
  unfold zeroSide
  exact zetaZeroWeight_tsum_eq_sum_compact_of_supportedInCompact K hK (hside f)

end GlobalZetaZeroSide

/-- A global zeta-zero side specialized to Schwartz test functions. -/
abbrev SchwartzGlobalZetaZeroSide :=
  GlobalZetaZeroSide SchwartzLineTestFunction

end RiemannHypothesisProject
