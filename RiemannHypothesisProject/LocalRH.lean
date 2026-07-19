import RiemannHypothesisProject.SpectralModel

/-!
# Local RH utilities

This file collects small lemmas about `RHOn`, the local version of RH for a
chosen family of complex numbers.
-/

namespace RiemannHypothesisProject

/-- `RHOn` is monotone under restriction of the family. -/
theorem RHOn.mono {larger smaller : ℂ → Prop}
    (h_larger : RHOn larger)
    (h_subset : ∀ s : ℂ, smaller s → larger s) :
    RHOn smaller := by
  intro s hs_smaller hs_zero
  exact h_larger s (h_subset s hs_smaller) hs_zero

/-- Global RH is equivalent to `RHOn` for the universal family. -/
theorem RHStatement_iff_RHOn_univ :
    RHStatement ↔ RHOn (fun _ : ℂ => True) := by
  constructor
  · intro h s _ hs_zero
    exact h s hs_zero
  · intro h s hs_zero
    exact h s True.intro hs_zero

/-- Global RH implies `RHOn` for every family. -/
theorem RHOn.of_RHStatement
    (hRH : RHStatement) (family : ℂ → Prop) : RHOn family := by
  intro s _ hs_zero
  exact hRH s hs_zero

/-- Mathlib's RH implies `RHOn` for every family. -/
theorem RHOn.of_mathlib_RH
    (hRH : RiemannHypothesis) (family : ℂ → Prop) : RHOn family :=
  RHOn.of_RHStatement (RHStatement_iff_mathlib.mpr hRH) family

/--
If every nontrivial zero lies in a family, then `RHOn family` implies global RH.
-/
theorem RHStatement.of_RHOn_of_covers_nontrivial_zeroes
    {family : ℂ → Prop}
    (h_local : RHOn family)
    (h_covers : ∀ s : ℂ, IsNontrivialZetaZero s → family s) :
    RHStatement := by
  intro s hs_zero
  exact h_local s (h_covers s hs_zero) hs_zero

/--
If a local RH result covers all nontrivial zeroes, it implies Mathlib's RH.
-/
theorem mathlib_RH_of_RHOn_of_covers_nontrivial_zeroes
    {family : ℂ → Prop}
    (h_local : RHOn family)
    (h_covers : ∀ s : ℂ, IsNontrivialZetaZero s → family s) :
    RiemannHypothesis := by
  exact RHStatement_iff_mathlib.mp
    (RHStatement.of_RHOn_of_covers_nontrivial_zeroes h_local h_covers)

end RiemannHypothesisProject
