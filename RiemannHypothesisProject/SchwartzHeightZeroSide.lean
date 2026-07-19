import RiemannHypothesisProject.SchwartzGlobalExplicitFormula
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Schwartz height-sampling zero side

This file defines a concrete toy zero-weight shape on actual zeta zeroes:
sample a Schwartz test function at the imaginary part of a zero and take the
squared norm.

This is still not the Riemann-Weil zero side. The useful formal step is that the
same height-sampling expression now lives on the actual zeta-zero subtype and is
connected to the finite compact-window energies and global zero-side bridge.
The required global summability is kept as an explicit hypothesis.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/-- Height-sampling weight on actual zeta zeroes for a Schwartz test function. -/
noncomputable def schwartzHeightZeroWeight
    (f : SchwartzLineTestFunction) (z : ZetaZeroSubtype) : ℝ :=
  ‖f (Complex.im (z : ℂ))‖ ^ 2

/-- The height-sampling zero weight is pointwise nonnegative. -/
theorem schwartzHeightZeroWeight_nonneg
    (f : SchwartzLineTestFunction) (z : ZetaZeroSubtype) :
    0 ≤ schwartzHeightZeroWeight f z := by
  unfold schwartzHeightZeroWeight
  exact sq_nonneg ‖f (Complex.im (z : ℂ))‖

/--
The subtype finite sum of the height-sampling weight agrees with the compact
zeta-zero window energy over complex zeroes.
-/
theorem compactZetaZeroSubtype_sum_schwartzHeightZeroWeight_eq_energy
    (K : Set ℂ) (hK : IsCompact K) (f : SchwartzLineTestFunction) :
    (compactZetaZeroSubtypeFinset K hK).sum (schwartzHeightZeroWeight f) =
      schwartzCompactZetaZeroWindowEnergy K hK f := by
  classical
  unfold schwartzCompactZetaZeroWindowEnergy schwartzZeroWindowEnergy
    schwartzHeightZeroWeight
  refine Finset.sum_bij
    (fun z _ => (z : ℂ))
    ?_
    ?_
    ?_
    ?_
  · intro z hz
    have hz_window := (mem_compactZetaZeroSubtypeFinset hK).mp hz
    have hz_zero : IsZetaZero (z : ℂ) := by
      exact mem_riemannZetaZeros.mp z.2
    exact (mem_compactZetaZeroFinset hK).mpr ⟨hz_window, hz_zero⟩
  · intro z₁ _ z₂ _ hz_eq
    exact Subtype.ext hz_eq
  · intro rho hrho
    have hrho_data := (mem_compactZetaZeroFinset hK).mp hrho
    let z : ZetaZeroSubtype :=
      ⟨rho, by simpa [IsZetaZero, riemannZetaZeros] using hrho_data.2⟩
    refine ⟨z, ?_, rfl⟩
    exact (mem_compactZetaZeroSubtypeFinset hK).mpr hrho_data.1
  · intro z _
    rfl

/-- Height-sampling sums over an exhaustion window. -/
noncomputable def ComplexCompactExhaustion.schwartzHeightZeroWindowSum
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (f : SchwartzLineTestFunction) : ℝ :=
  exhaustion.zetaZeroWindowSum n (schwartzHeightZeroWeight f)

/-- Exhaustion-window height-sampling sums agree with the earlier compact-window energy. -/
theorem ComplexCompactExhaustion.schwartzHeightZeroWindowSum_eq_energy
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (f : SchwartzLineTestFunction) :
    exhaustion.schwartzHeightZeroWindowSum n f =
      exhaustion.schwartzZetaZeroWindowEnergy n f := by
  unfold ComplexCompactExhaustion.schwartzHeightZeroWindowSum
    ComplexCompactExhaustion.zetaZeroWindowSum
    ComplexCompactExhaustion.schwartzZetaZeroWindowEnergy
  exact compactZetaZeroSubtype_sum_schwartzHeightZeroWeight_eq_energy
    (exhaustion.window n) (exhaustion.compact_window n) f

/--
A summability hypothesis for the Schwartz height-sampling zero side.

This is the analytic input not proved here.
-/
structure SchwartzHeightZeroSide where
  summable_weight :
    ∀ f : SchwartzLineTestFunction, Summable (schwartzHeightZeroWeight f)

namespace SchwartzHeightZeroSide

/-- The height-sampling side as a global zeta-zero side. -/
noncomputable def toGlobalZetaZeroSide
    (side : SchwartzHeightZeroSide) : SchwartzGlobalZetaZeroSide where
  weight := schwartzHeightZeroWeight
  summable_weight := side.summable_weight

/-- The global height-sampling zero-side value. -/
noncomputable def zeroSide
    (side : SchwartzHeightZeroSide) (f : SchwartzLineTestFunction) : ℝ :=
  side.toGlobalZetaZeroSide.zeroSide f

/-- The global height-sampling zero side is nonnegative. -/
theorem zeroSide_nonneg
    (side : SchwartzHeightZeroSide) (f : SchwartzLineTestFunction) :
    0 ≤ side.zeroSide f := by
  unfold zeroSide GlobalZetaZeroSide.zeroSide
  exact tsum_nonneg (fun z => schwartzHeightZeroWeight_nonneg f z)

/-- Exhaustion height-sampling sums converge to the global height-sampling side. -/
theorem tendsto_schwartzHeightZeroWindowSum
    (side : SchwartzHeightZeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => exhaustion.schwartzHeightZeroWindowSum n f)
      atTop (𝓝 (side.zeroSide f)) := by
  unfold ComplexCompactExhaustion.schwartzHeightZeroWindowSum zeroSide
  exact side.toGlobalZetaZeroSide.tendsto_windowZeroSide exhaustion f

/-- Exhaustion compact-window energies converge to the global height-sampling side. -/
theorem tendsto_schwartzZetaZeroWindowEnergy
    (side : SchwartzHeightZeroSide)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => exhaustion.schwartzZetaZeroWindowEnergy n f)
      atTop (𝓝 (side.zeroSide f)) := by
  have h := side.tendsto_schwartzHeightZeroWindowSum exhaustion f
  refine h.congr' ?_
  filter_upwards with n
  exact exhaustion.schwartzHeightZeroWindowSum_eq_energy n f

end SchwartzHeightZeroSide

end RiemannHypothesisProject
