import RiemannHypothesisProject.CompactZetaZeroWindow
import Mathlib.Topology.DiscreteSubset

/-!
# Cofinite zeta-zero windows

This file packages Mathlib's cocompact/cofinite theorem for the zeta zero set
into forms that are convenient for the explicit-formula track.

The key input is `tendsto_riemannZeta_cofinite_cocompact`: the inclusion map
from the subtype of zeta zeroes to `ℂ` tends to the cocompact filter along the
cofinite filter. Equivalently, every compact subset of `ℂ` contains only
finitely many zeta zeroes.
-/

namespace RiemannHypothesisProject

open Filter

/-- The subtype of actual Riemann zeta zeroes. -/
abbrev ZetaZeroSubtype := riemannZetaZeros

/-- Mathlib's zeta-zero discreteness theorem in the project's local vocabulary. -/
theorem zetaZeroSubtype_tendsto_cofinite_cocompact :
    Tendsto ((↑) : ZetaZeroSubtype → ℂ) cofinite (cocompact ℂ) :=
  tendsto_riemannZeta_cofinite_cocompact

/-- The zeta zeroes lying over any compact subset of `ℂ` form a finite subtype set. -/
theorem zetaZeroSubtype_compact_preimage_finite
    (K : Set ℂ) (hK : IsCompact K) :
    ((fun z : ZetaZeroSubtype => (z : ℂ)) ⁻¹' K).Finite :=
  tendsto_cofinite_cocompact_iff.mp
    zetaZeroSubtype_tendsto_cofinite_cocompact K hK

/-- Cofinitely many zeta zeroes lie outside any fixed compact subset of `ℂ`. -/
theorem eventually_zetaZeroSubtype_not_mem_compact
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ z : ZetaZeroSubtype in cofinite, (z : ℂ) ∉ K := by
  simpa [Set.preimage] using
    (zetaZeroSubtype_compact_preimage_finite K hK).eventually_cofinite_notMem

/-- The preimage of the complement of a compact set is cofinite on zeta zeroes. -/
theorem zetaZeroSubtype_preimage_compl_compact_mem_cofinite
    (K : Set ℂ) (hK : IsCompact K) :
    {z : ZetaZeroSubtype | (z : ℂ) ∉ K} ∈ cofinite := by
  simpa [Set.preimage] using
    zetaZeroSubtype_tendsto_cofinite_cocompact hK.compl_mem_cocompact

/-- The finite subtype of zeta zeroes lying over a compact subset of `ℂ`. -/
noncomputable def compactZetaZeroSubtypeFinset
    (K : Set ℂ) (hK : IsCompact K) : Finset ZetaZeroSubtype :=
  (zetaZeroSubtype_compact_preimage_finite K hK).toFinset

/-- Membership in the compact zeta-zero subtype finset. -/
theorem mem_compactZetaZeroSubtypeFinset
    {K : Set ℂ} (hK : IsCompact K) {z : ZetaZeroSubtype} :
    z ∈ compactZetaZeroSubtypeFinset K hK ↔ (z : ℂ) ∈ K := by
  rw [compactZetaZeroSubtypeFinset]
  rw [(zetaZeroSubtype_compact_preimage_finite K hK).mem_toFinset]
  rfl

/-- A weight on zeta zeroes is supported in a compact subset of `ℂ`. -/
def ZetaZeroWeightSupportedInCompact
    (K : Set ℂ) (weight : ZetaZeroSubtype → ℝ) : Prop :=
  ∀ z : ZetaZeroSubtype, (z : ℂ) ∉ K → weight z = 0

/-- A compactly supported weight on zeta zeroes has finite support. -/
theorem zetaZeroWeight_hasFiniteSupport_of_supportedInCompact
    (K : Set ℂ) (hK : IsCompact K) {weight : ZetaZeroSubtype → ℝ}
    (hweight : ZetaZeroWeightSupportedInCompact K weight) :
    weight.HasFiniteSupport := by
  unfold Function.HasFiniteSupport
  refine (zetaZeroSubtype_compact_preimage_finite K hK).subset ?_
  intro z hz_support
  by_contra hz_not_mem
  exact hz_support (hweight z hz_not_mem)

/-- A compactly supported weight on zeta zeroes is summable. -/
theorem zetaZeroWeight_summable_of_supportedInCompact
    (K : Set ℂ) (hK : IsCompact K) {weight : ZetaZeroSubtype → ℝ}
    (hweight : ZetaZeroWeightSupportedInCompact K weight) :
    Summable weight :=
  summable_of_hasFiniteSupport
    (zetaZeroWeight_hasFiniteSupport_of_supportedInCompact K hK hweight)

/--
The `tsum` of a compactly supported zero weight is the finite sum over the
compact zeta-zero subtype window.
-/
theorem zetaZeroWeight_tsum_eq_sum_compact_of_supportedInCompact
    (K : Set ℂ) (hK : IsCompact K) {weight : ZetaZeroSubtype → ℝ}
    (hweight : ZetaZeroWeightSupportedInCompact K weight) :
    (∑' z : ZetaZeroSubtype, weight z) =
      (compactZetaZeroSubtypeFinset K hK).sum weight := by
  classical
  refine tsum_eq_sum (s := compactZetaZeroSubtypeFinset K hK) ?_
  intro z hz_not_mem
  apply hweight z
  by_contra hz_mem
  exact hz_not_mem ((mem_compactZetaZeroSubtypeFinset hK).mpr hz_mem)

/--
A compact exhaustion of the complex plane.

This interface is intentionally abstract: concrete examples can be closed balls,
rectangles, or other compact windows. The fields say that the windows are
compact, increasing, and eventually contain every fixed complex point.
-/
structure ComplexCompactExhaustion where
  window : ℕ → Set ℂ
  compact_window : ∀ n : ℕ, IsCompact (window n)
  monotone_window : Monotone window
  eventually_mem : ∀ z : ℂ, ∀ᶠ n in atTop, z ∈ window n

/-- The finite set of actual zeta zeroes in the `n`th compact exhaustion window. -/
noncomputable def ComplexCompactExhaustion.zetaZeroFinset
    (exhaustion : ComplexCompactExhaustion) (n : ℕ) : Finset ℂ :=
  compactZetaZeroFinset (exhaustion.window n) (exhaustion.compact_window n)

/-- The finite subtype of actual zeta zeroes in the `n`th compact exhaustion window. -/
noncomputable def ComplexCompactExhaustion.zetaZeroSubtypeFinset
    (exhaustion : ComplexCompactExhaustion) (n : ℕ) : Finset ZetaZeroSubtype :=
  compactZetaZeroSubtypeFinset
    (exhaustion.window n) (exhaustion.compact_window n)

/-- Membership in an exhaustion zeta-zero finset. -/
theorem ComplexCompactExhaustion.mem_zetaZeroFinset_iff
    (exhaustion : ComplexCompactExhaustion) (n : ℕ) {s : ℂ} :
    s ∈ exhaustion.zetaZeroFinset n ↔
      s ∈ exhaustion.window n ∧ IsZetaZero s :=
  mem_compactZetaZeroFinset (exhaustion.compact_window n)

/-- Membership in an exhaustion zeta-zero subtype finset. -/
theorem ComplexCompactExhaustion.mem_zetaZeroSubtypeFinset_iff
    (exhaustion : ComplexCompactExhaustion) (n : ℕ) {z : ZetaZeroSubtype} :
    z ∈ exhaustion.zetaZeroSubtypeFinset n ↔ (z : ℂ) ∈ exhaustion.window n :=
  mem_compactZetaZeroSubtypeFinset (exhaustion.compact_window n)

/-- The compact-exhaustion zeta-zero finsets are monotone. -/
theorem ComplexCompactExhaustion.zetaZeroFinset_mono
    (exhaustion : ComplexCompactExhaustion) {m n : ℕ} (hmn : m ≤ n) :
    exhaustion.zetaZeroFinset m ⊆ exhaustion.zetaZeroFinset n := by
  intro s hs
  have hs_data :=
    (exhaustion.mem_zetaZeroFinset_iff m).mp hs
  exact (exhaustion.mem_zetaZeroFinset_iff n).mpr
    ⟨exhaustion.monotone_window hmn hs_data.1, hs_data.2⟩

/-- The compact-exhaustion zeta-zero subtype finsets are monotone. -/
theorem ComplexCompactExhaustion.zetaZeroSubtypeFinset_mono
    (exhaustion : ComplexCompactExhaustion) {m n : ℕ} (hmn : m ≤ n) :
    exhaustion.zetaZeroSubtypeFinset m ⊆ exhaustion.zetaZeroSubtypeFinset n := by
  intro z hz
  have hz_window :=
    (exhaustion.mem_zetaZeroSubtypeFinset_iff m).mp hz
  exact (exhaustion.mem_zetaZeroSubtypeFinset_iff n).mpr
    (exhaustion.monotone_window hmn hz_window)

/-- Every fixed zeta zero eventually belongs to the exhaustion finite windows. -/
theorem ComplexCompactExhaustion.eventually_mem_zetaZeroFinset
    (exhaustion : ComplexCompactExhaustion) (s : ℂ) (hs : IsZetaZero s) :
    ∀ᶠ n in atTop, s ∈ exhaustion.zetaZeroFinset n := by
  filter_upwards [exhaustion.eventually_mem s] with n hn
  exact (exhaustion.mem_zetaZeroFinset_iff n).mpr ⟨hn, hs⟩

/-- Every fixed zeta-zero subtype point eventually belongs to the exhaustion subtype windows. -/
theorem ComplexCompactExhaustion.eventually_mem_zetaZeroSubtypeFinset
    (exhaustion : ComplexCompactExhaustion) (z : ZetaZeroSubtype) :
    ∀ᶠ n in atTop, z ∈ exhaustion.zetaZeroSubtypeFinset n := by
  filter_upwards [exhaustion.eventually_mem (z : ℂ)] with n hn
  exact (exhaustion.mem_zetaZeroSubtypeFinset_iff n).mpr hn

/-- Schwartz zero-window energy along a compact exhaustion. -/
noncomputable def ComplexCompactExhaustion.schwartzZetaZeroWindowEnergy
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (f : SchwartzLineTestFunction) : ℝ :=
  schwartzCompactZetaZeroWindowEnergy
    (exhaustion.window n) (exhaustion.compact_window n) f

/-- Exhaustion-window Schwartz zero energy is nonnegative. -/
theorem ComplexCompactExhaustion.schwartzZetaZeroWindowEnergy_nonneg
    (exhaustion : ComplexCompactExhaustion)
    (n : ℕ) (f : SchwartzLineTestFunction) :
    0 ≤ exhaustion.schwartzZetaZeroWindowEnergy n f := by
  unfold ComplexCompactExhaustion.schwartzZetaZeroWindowEnergy
  exact schwartzCompactZetaZeroWindowEnergy_nonneg
    (exhaustion.window n) (exhaustion.compact_window n) f

end RiemannHypothesisProject
