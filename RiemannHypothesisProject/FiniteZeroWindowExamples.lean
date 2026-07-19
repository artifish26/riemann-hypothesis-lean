import RiemannHypothesisProject.FiniteZeroWindow

/-!
# Finite zero-window examples

This file gives concrete templates for using finite zero-window certificates.
The examples are intentionally modest: they exercise the certificate machinery
without making any numerical claim about actual zeta zeroes.
-/

namespace RiemannHypothesisProject

/-- The singleton family containing the critical-line point `1 / 2 + i * t`. -/
def singletonCriticalFamily (t : ℝ) : ℂ → Prop :=
  fun s => s = criticalLinePoint t

/--
A finite height certificate for the singleton critical-line family.

If any nontrivial zeta zero belongs to this singleton family, it is already the
critical-line point `1 / 2 + i * t`, so RH holds on the family.
-/
noncomputable def singletonCriticalWindowCertificate (t : ℝ) :
    FiniteWindowHeightCertificate (singletonCriticalFamily t) := by
  classical
  refine
    { zeroes := {criticalLinePoint t}
      covers_family_zeroes := ?_
      height := ?_
      realizes_zeroes := ?_ }
  · intro s hs_family _
    rw [hs_family]
    simp
  · intro _ _
    exact t
  · intro s hs_zeroes
    simp at hs_zeroes
    exact hs_zeroes.symm

/-- RH holds on any singleton critical-line family. -/
theorem RHOn_singletonCriticalFamily (t : ℝ) :
    RHOn (singletonCriticalFamily t) :=
  RHOn.of_finiteWindowHeightCertificate
    (singletonCriticalWindowCertificate t)

/--
The family of critical-line points whose heights belong to a finite set.

This is a template for finite windows: the finite set records the real heights
being considered, and the corresponding complex points are `1 / 2 + i * t`.
-/
def finiteCriticalFamily (heights : Finset ℝ) : ℂ → Prop :=
  fun s => ∃ t : ℝ, t ∈ heights ∧ s = criticalLinePoint t

/--
A finite height certificate for any finite family of critical-line heights.
-/
noncomputable def finiteCriticalWindowCertificate (heights : Finset ℝ) :
    FiniteWindowHeightCertificate (finiteCriticalFamily heights) := by
  classical
  refine
    { zeroes := heights.image criticalLinePoint
      covers_family_zeroes := ?_
      height := ?_
      realizes_zeroes := ?_ }
  · intro s hs_family _
    rcases hs_family with ⟨t, ht_heights, rfl⟩
    exact Finset.mem_image.mpr ⟨t, ht_heights, rfl⟩
  · intro s hs_zeroes
    exact Classical.choose (Finset.mem_image.mp hs_zeroes)
  · intro s hs_zeroes
    exact (Classical.choose_spec (Finset.mem_image.mp hs_zeroes)).2

/-- RH holds on any finite family of critical-line heights. -/
theorem RHOn_finiteCriticalFamily (heights : Finset ℝ) :
    RHOn (finiteCriticalFamily heights) :=
  RHOn.of_finiteWindowHeightCertificate
    (finiteCriticalWindowCertificate heights)

end RiemannHypothesisProject
