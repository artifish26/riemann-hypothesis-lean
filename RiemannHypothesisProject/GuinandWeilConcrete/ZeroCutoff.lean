import RiemannHypothesisProject.GuinandWeilConcrete.Sides

/-!
# Zero-side cutoff facts for concrete Guinand-Weil formulae

This module contains zero-side convergence, compact zero-support summability,
and finite compact-window reduction facts for the concrete Guinand-Weil formula
route.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open Filter
open scoped BigOperators
open scoped Topology

noncomputable section

/--
For a summable zero-side weight, the concrete truncated zero side converges
along any compact exhaustion of the zeta-zero subtype.
-/
theorem tendsto_guinandWeilTruncatedZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    (hweight : Summable (system.weight f)) :
    Tendsto
      (fun cutoff : Nat =>
        guinandWeilTruncatedZeroSide system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f)
      atTop (𝓝 (guinandWeilZeroSide system f)) := by
  simpa [guinandWeilTruncatedZeroSide, guinandWeilZeroSide,
    ComplexCompactExhaustion.zetaZeroWindowSum] using
    exhaustion.tendsto_zetaZeroWindowSum (weight := system.weight f) hweight

/--
For a summable completed-zeta normalized zero-side weight, the normalized
truncated zero side converges along any compact exhaustion of the zeta-zero
subtype.
-/
theorem tendsto_guinandWeilTruncatedCompletedZetaNormalizedZeroSide
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    (hweight : Summable (completedZetaNormalizedZeroWeight system f)) :
    Tendsto
      (fun cutoff : Nat =>
        guinandWeilTruncatedCompletedZetaNormalizedZeroSide system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f)
      atTop (𝓝 (guinandWeilCompletedZetaNormalizedZeroSide system f)) := by
  simpa [guinandWeilTruncatedCompletedZetaNormalizedZeroSide,
    guinandWeilCompletedZetaNormalizedZeroSide,
    ComplexCompactExhaustion.zetaZeroWindowSum] using
    exhaustion.tendsto_zetaZeroWindowSum
      (weight := completedZetaNormalizedZeroWeight system f) hweight

/--
Compact support of the complex zero contribution implies compact support of
the real zero-side weight used by the concrete Guinand-Weil formula.
-/
theorem zetaZeroWeightSupportedInCompact_of_zeroValue_eq_zero_of_not_mem
    (system : SchwartzRiemannWeilExtensionSystem)
    (K : Set Complex)
    (f : SchwartzLineTestFunction)
    (hzeroValue :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) ∉ K -> system.zeroValue f rho = 0) :
    ZetaZeroWeightSupportedInCompact K (system.weight f) := by
  intro rho hrho
  unfold SchwartzRiemannWeilExtensionSystem.weight
  rw [hzeroValue rho hrho]
  simp

/--
A compact-support majorant for the complex zero contribution supplies compact
support of the concrete real zero-side weight.
-/
theorem zetaZeroWeightSupportedInCompact_of_compactSupportMajorant
    (system : SchwartzRiemannWeilExtensionSystem)
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (f : SchwartzLineTestFunction) :
    ZetaZeroWeightSupportedInCompact
      (certificate.support f) (system.weight f) :=
  zetaZeroWeightSupportedInCompact_of_zeroValue_eq_zero_of_not_mem
    system (certificate.support f) f
    (certificate.zeroValue_eq_zero_of_not_mem f)

/-- Compact support of the concrete zero weight gives zero-side summability. -/
theorem summable_guinandWeilZeroSide_weight_of_supportedInCompact
    (system : SchwartzRiemannWeilExtensionSystem)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hweight : ZetaZeroWeightSupportedInCompact K (system.weight f)) :
    Summable (system.weight f) :=
  zetaZeroWeight_summable_of_supportedInCompact K hK hweight

/--
Compact support of the complex zero contribution gives zero-side summability
for the concrete real formula weight.
-/
theorem summable_guinandWeilZeroSide_weight_of_zeroValue_supportedInCompact
    (system : SchwartzRiemannWeilExtensionSystem)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hzeroValue :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) ∉ K -> system.zeroValue f rho = 0) :
    Summable (system.weight f) :=
  summable_guinandWeilZeroSide_weight_of_supportedInCompact
    system K hK f
    (zetaZeroWeightSupportedInCompact_of_zeroValue_eq_zero_of_not_mem
      system K f hzeroValue)

/-- A compact-support majorant gives zero-side summability for the concrete weight. -/
theorem summable_guinandWeilZeroSide_weight_of_compactSupportMajorant
    (system : SchwartzRiemannWeilExtensionSystem)
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) :=
  summable_guinandWeilZeroSide_weight_of_supportedInCompact
    system (certificate.support f) (certificate.compact_support f) f
    (zetaZeroWeightSupportedInCompact_of_compactSupportMajorant
      system certificate f)

/--
For a compactly supported concrete zero weight, the zero side is the finite sum
over the compact zeta-zero window.
-/
theorem guinandWeilZeroSide_eq_sum_compact_of_supportedInCompact
    (system : SchwartzRiemannWeilExtensionSystem)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hweight : ZetaZeroWeightSupportedInCompact K (system.weight f)) :
    guinandWeilZeroSide system f =
      (compactZetaZeroSubtypeFinset K hK).sum (system.weight f) := by
  unfold guinandWeilZeroSide
  exact zetaZeroWeight_tsum_eq_sum_compact_of_supportedInCompact K hK hweight

/--
For a compactly supported complex zero contribution, the concrete zero side is
the finite sum over the compact zeta-zero window.
-/
theorem guinandWeilZeroSide_eq_sum_compact_of_zeroValue_supportedInCompact
    (system : SchwartzRiemannWeilExtensionSystem)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hzeroValue :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) ∉ K -> system.zeroValue f rho = 0) :
    guinandWeilZeroSide system f =
      (compactZetaZeroSubtypeFinset K hK).sum (system.weight f) :=
  guinandWeilZeroSide_eq_sum_compact_of_supportedInCompact
    system K hK f
    (zetaZeroWeightSupportedInCompact_of_zeroValue_eq_zero_of_not_mem
      system K f hzeroValue)

/--
A compact-support majorant reduces the concrete zero side to the corresponding
finite compact-window sum.
-/
theorem guinandWeilZeroSide_eq_sum_compact_of_compactSupportMajorant
    (system : SchwartzRiemannWeilExtensionSystem)
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (f : SchwartzLineTestFunction) :
    guinandWeilZeroSide system f =
      (compactZetaZeroSubtypeFinset
        (certificate.support f) (certificate.compact_support f)).sum
          (system.weight f) :=
  guinandWeilZeroSide_eq_sum_compact_of_supportedInCompact
    system (certificate.support f) (certificate.compact_support f) f
    (zetaZeroWeightSupportedInCompact_of_compactSupportMajorant
      system certificate f)

/--
Once a concrete zero cutoff contains the compact support window for the
zero-side weight, the truncated zero side is already equal to the limiting zero
side.
-/
theorem guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact_of_subset
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hweight : ZetaZeroWeightSupportedInCompact K (system.weight f))
    (cutoff : Nat)
    (hsubset :
      compactZetaZeroSubtypeFinset K hK ⊆
        exhaustion.zetaZeroSubtypeFinset cutoff) :
    guinandWeilTruncatedZeroSide system
        (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
      guinandWeilZeroSide system f := by
  have hzero_eq :=
    guinandWeilZeroSide_eq_sum_compact_of_supportedInCompact
      system K hK f hweight
  have hsum :
      (exhaustion.zetaZeroSubtypeFinset cutoff).sum (system.weight f) =
        (compactZetaZeroSubtypeFinset K hK).sum (system.weight f) := by
    exact (Finset.sum_subset hsubset (fun z _hz_big hz_small => by
      have hz_not_mem : (z : Complex) ∉ K := by
        by_contra hz_mem
        exact hz_small ((mem_compactZetaZeroSubtypeFinset hK).mpr hz_mem)
      exact hweight z hz_not_mem)).symm
  rw [guinandWeilTruncatedZeroSide, hsum, ← hzero_eq]

/--
A compactly supported complex zero contribution gives a concrete finite zero
cutoff equality as soon as the cutoff contains the compact zero window.
-/
theorem guinandWeilTruncatedZeroSide_eq_zeroSide_of_zeroValue_supportedInCompact_of_subset
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hzeroValue :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) ∉ K -> system.zeroValue f rho = 0)
    (cutoff : Nat)
    (hsubset :
      compactZetaZeroSubtypeFinset K hK ⊆
        exhaustion.zetaZeroSubtypeFinset cutoff) :
    guinandWeilTruncatedZeroSide system
        (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
      guinandWeilZeroSide system f :=
  guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact_of_subset
    system exhaustion K hK f
    (zetaZeroWeightSupportedInCompact_of_zeroValue_eq_zero_of_not_mem
      system K f hzeroValue)
    cutoff hsubset

/--
A compact-support majorant gives a concrete finite zero cutoff equality as soon
as the cutoff contains the certificate's compact zero window.
-/
theorem guinandWeilTruncatedZeroSide_eq_zeroSide_of_compactSupportMajorant_of_subset
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (f : SchwartzLineTestFunction)
    (cutoff : Nat)
    (hsubset :
      compactZetaZeroSubtypeFinset
          (certificate.support f) (certificate.compact_support f) ⊆
        exhaustion.zetaZeroSubtypeFinset cutoff) :
    guinandWeilTruncatedZeroSide system
        (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
      guinandWeilZeroSide system f :=
  guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact_of_subset
    system exhaustion (certificate.support f) (certificate.compact_support f) f
    (zetaZeroWeightSupportedInCompact_of_compactSupportMajorant
      system certificate f)
    cutoff hsubset

/--
Every compact zero window is eventually contained in the chosen compact
exhaustion of the zeta-zero subtype.
-/
theorem eventually_compactZetaZeroSubtypeFinset_subset_zetaZeroSubtypeFinset
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K) :
    ∀ᶠ cutoff : Nat in atTop,
      compactZetaZeroSubtypeFinset K hK ⊆
        exhaustion.zetaZeroSubtypeFinset cutoff := by
  have hcontains :
      ∀ᶠ cutoff : Nat in atTop,
        ∀ z ∈ compactZetaZeroSubtypeFinset K hK,
          z ∈ exhaustion.zetaZeroSubtypeFinset cutoff := by
    rw [Filter.eventually_all_finset]
    intro z _hz
    exact exhaustion.eventually_mem_zetaZeroSubtypeFinset z
  filter_upwards [hcontains] with cutoff hcontains_cutoff
  intro z hz
  exact hcontains_cutoff z hz

/--
If the concrete zero weight is supported in a compact set, then every compact
exhaustion eventually contains all nonzero zero-side terms, so the truncated
zero side stabilizes exactly to the limiting zero side.
-/
theorem eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hweight : ZetaZeroWeightSupportedInCompact K (system.weight f)) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedZeroSide system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
        guinandWeilZeroSide system f := by
  have hzero_eq :=
    guinandWeilZeroSide_eq_sum_compact_of_supportedInCompact
      system K hK f hweight
  have hcontains :
      ∀ᶠ cutoff : Nat in atTop,
        ∀ z ∈ compactZetaZeroSubtypeFinset K hK,
          z ∈ exhaustion.zetaZeroSubtypeFinset cutoff := by
    rw [Filter.eventually_all_finset]
    intro z _hz
    exact exhaustion.eventually_mem_zetaZeroSubtypeFinset z
  filter_upwards [hcontains] with cutoff hcontains_cutoff
  have hsubset :
      compactZetaZeroSubtypeFinset K hK ⊆
        exhaustion.zetaZeroSubtypeFinset cutoff := by
    intro z hz
    exact hcontains_cutoff z hz
  have hsum :
      (exhaustion.zetaZeroSubtypeFinset cutoff).sum (system.weight f) =
        (compactZetaZeroSubtypeFinset K hK).sum (system.weight f) := by
    exact (Finset.sum_subset hsubset (fun z _hz_big hz_small => by
      have hz_not_mem : (z : Complex) ∉ K := by
        by_contra hz_mem
        exact hz_small ((mem_compactZetaZeroSubtypeFinset hK).mpr hz_mem)
      exact hweight z hz_not_mem)).symm
  rw [guinandWeilTruncatedZeroSide, hsum, ← hzero_eq]

/--
If the complex zero contribution is supported in a compact set, then the
concrete zero cutoff eventually stabilizes exactly to the limiting zero side.
-/
theorem eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_zeroValue_supportedInCompact
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (K : Set Complex) (hK : IsCompact K)
    (f : SchwartzLineTestFunction)
    (hzeroValue :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) ∉ K -> system.zeroValue f rho = 0) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedZeroSide system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
        guinandWeilZeroSide system f :=
  eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact
    system exhaustion K hK f
    (zetaZeroWeightSupportedInCompact_of_zeroValue_eq_zero_of_not_mem
      system K f hzeroValue)

/--
A compact-support majorant for the complex zero contribution gives exact
eventual stabilization of the concrete zero cutoffs.
-/
theorem eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_compactSupportMajorant
    (system : SchwartzRiemannWeilExtensionSystem)
    (exhaustion : ComplexCompactExhaustion)
    (certificate : SchwartzRiemannWeilCompactSupportMajorant system)
    (f : SchwartzLineTestFunction) :
    ∀ᶠ cutoff : Nat in atTop,
      guinandWeilTruncatedZeroSide system
          (fun n => exhaustion.zetaZeroSubtypeFinset n) cutoff f =
        guinandWeilZeroSide system f :=
  eventually_guinandWeilTruncatedZeroSide_eq_zeroSide_of_supportedInCompact
    system exhaustion (certificate.support f) (certificate.compact_support f) f
    (zetaZeroWeightSupportedInCompact_of_compactSupportMajorant
      system certificate f)

end

end RiemannHypothesisProject
