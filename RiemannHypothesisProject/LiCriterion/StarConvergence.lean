import RiemannHypothesisProject.LiCriterion.ZeroMultiset
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityCount
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Canonical radial star convergence

The canonical exact positive-ordinate zeta-zero window gives a distinguished
height cutoff.  This module transports that window to the positive subtype and
proves that its natural-number cutoffs are cofinal in finite subsets.  Hence
every summable positive-zero family converges along the canonical radial
cutoffs, without invoking an arbitrary enumeration or rearrangement.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Filter

open scoped Topology

noncomputable section

/-- Embed the canonical zeta-zero window into the positive-ordinate subtype. -/
noncomputable def canonicalPositiveOrdinateWindowEmbedding (T : Real) :
    {rho : ZetaZeroSubtype //
      rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window T} ↪
      PositiveOrdinateZetaZeroSubtype where
  toFun rho :=
    ⟨rho.1,
      ((canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff T rho.1).mp
        rho.2).1⟩
  inj' := by
    intro rho sigma h
    apply Subtype.ext
    exact congrArg (fun z : PositiveOrdinateZetaZeroSubtype => z.1) h

/-- The canonical finite window of positive-ordinate zeta zeroes at height
`T`, now as a finset of the positive subtype. -/
noncomputable def canonicalPositiveOrdinateWindow (T : Real) :
    Finset PositiveOrdinateZetaZeroSubtype :=
  (canonicalExactPositiveOrdinateZetaZeroWindow.window T).attach.map
    (canonicalPositiveOrdinateWindowEmbedding T)

/-- Membership in the transported window is exactly the upper height bound. -/
theorem mem_canonicalPositiveOrdinateWindow_iff
    (T : Real) (rho : PositiveOrdinateZetaZeroSubtype) :
    rho ∈ canonicalPositiveOrdinateWindow T ↔
      Complex.im (rho : Complex) <= T := by
  classical
  constructor
  · intro hrho
    rw [canonicalPositiveOrdinateWindow] at hrho
    rcases Finset.mem_map.mp hrho with ⟨sigma, _hsigma, hvalue⟩
    have hbase : sigma.1 = rho.1 :=
      congrArg (fun z : PositiveOrdinateZetaZeroSubtype => z.1) hvalue
    have hsigma :=
      (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff T sigma.1).mp
        sigma.2
    simpa [hbase] using hsigma.2
  · intro hrho
    rw [canonicalPositiveOrdinateWindow]
    apply Finset.mem_map.mpr
    let sigma :
        {z : ZetaZeroSubtype //
          z ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window T} :=
      ⟨rho.1,
        (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff T rho.1).mpr
          ⟨rho.2, hrho⟩⟩
    refine ⟨sigma, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/-- Natural-height canonical windows eventually contain each positive zero. -/
theorem eventually_mem_canonicalPositiveOrdinateWindow
    (rho : PositiveOrdinateZetaZeroSubtype) :
    ∀ᶠ N : Nat in atTop,
      rho ∈ canonicalPositiveOrdinateWindow (N : Real) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Complex.im (rho : Complex))
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [mem_canonicalPositiveOrdinateWindow_iff]
  exact hN.trans (by exact_mod_cast hM)

/-- The natural-height canonical windows are cofinal among finite subsets of
the positive-ordinate zero subtype. -/
theorem tendsto_canonicalPositiveOrdinateWindow_atTop :
    Tendsto (fun N : Nat => canonicalPositiveOrdinateWindow (N : Real))
      atTop atTop := by
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro M N hMN rho hrho
    rw [mem_canonicalPositiveOrdinateWindow_iff] at hrho ⊢
    exact hrho.trans (by exact_mod_cast hMN)
  · intro rho
    exact (eventually_mem_canonicalPositiveOrdinateWindow rho).exists

/-- A family converges canonically in the radial-star sense when its sums over
the exact natural-height windows tend to the stated value. -/
def CanonicalRadialStarConverges
    {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (f : PositiveOrdinateZetaZeroSubtype -> M) (a : M) : Prop :=
  Tendsto
    (fun N : Nat =>
      (canonicalPositiveOrdinateWindow (N : Real)).sum f)
    atTop (𝓝 a)

/-- Unconditional summability implies convergence along the canonical radial
star cutoffs. -/
theorem HasSum.canonicalRadialStarConverges
    {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    {f : PositiveOrdinateZetaZeroSubtype -> M} {a : M}
    (h : HasSum f a) :
    CanonicalRadialStarConverges f a :=
  h.comp tendsto_canonicalPositiveOrdinateWindow_atTop

/-- A multiplicity-expanded radial sum, written as finite fibres over the
canonical distinct-zero window. -/
def multiplicityExpandedRadialSum
    {M : Type*} [AddCommMonoid M]
    (f : PositiveOrdinateZetaZeroSubtype -> M) (N : Nat) : M :=
  (canonicalPositiveOrdinateWindow (N : Real)).sum
    (fun rho =>
      Finset.univ.sum (fun _ : Fin (zetaZeroMultiplicity rho.1) => f rho))

/-- The expanded radial sum is exactly the multiplicity-weighted radial sum. -/
theorem multiplicityExpandedRadialSum_eq_weighted
    {M : Type*} [AddCommMonoid M]
    (f : PositiveOrdinateZetaZeroSubtype -> M) (N : Nat) :
    multiplicityExpandedRadialSum f N =
      (canonicalPositiveOrdinateWindow (N : Real)).sum
        (fun rho => zetaZeroMultiplicity rho.1 • f rho) := by
  simp [multiplicityExpandedRadialSum]

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
