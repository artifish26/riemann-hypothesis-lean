import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import RiemannHypothesisProject.ComplexAnalyticReflection
import RiemannHypothesisProject.ZetaSetup

open Filter

open scoped ComplexConjugate

/-!
# Zeta conjugation infrastructure

This module isolates the analytic conjugation infrastructure for the Riemann
zeta function from the classical counting adapters.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/--
The source-shaped analytic theorem that the Riemann zeta function respects
complex conjugation.

This is the preferred future target: it is a standard function-level statement,
and downstream adapters can derive zero-level conjugation symmetry from it.
-/
def RiemannZetaConjugationFormula : Prop :=
  forall s : Complex,
    riemannZeta (conj s) = conj (riemannZeta s)

/--
The source-shaped conjugation theorem on the regular domain of zeta.

This is the exact form needed for zero-conjugation: a zeta zero cannot occur at
the pole point `1`, so the regular-domain formula is enough for counting
mirrors even before the junk value at `1` is analyzed.
-/
def RiemannZetaConjugationFormulaOnRegularSet : Prop :=
  forall s : Complex,
    s ≠ 1 ->
      riemannZeta (conj s) = conj (riemannZeta s)

/--
The function-level zeta conjugation formula is already checked on the
absolutely convergent half-plane. The remaining source theorem is the analytic
continuation step extending this identity to the whole project domain.
-/
theorem riemannZetaConjugationFormula_on_one_lt_re :
    forall s : Complex,
      1 < s.re ->
        riemannZeta (conj s) = conj (riemannZeta s) := by
  intro s hs
  simpa using RiemannHypothesisProject.riemannZeta_conj_of_one_lt_re
    (s := s) hs

/--
The remaining analytic continuation input for global zeta conjugation.

The checked Dirichlet-series theorem proves the identity on `1 < re s`; this
field isolates the companion fact needed to extend the reflected side by the
analytic identity theorem.
-/
def RiemannZetaConjugationReflectionAnalytic : Prop :=
  AnalyticOnNhd ℂ
    (fun s : ℂ => conj (riemannZeta (conj s)))
    (({(1 : ℂ)} : Set ℂ)ᶜ)

/--
The reflected zeta side is analytic on the regular domain.

This follows from Mathlib's analyticity of `riemannZeta` on `{1}^c` and the
generic conjugated-power-series reflection lemma.
-/
theorem riemannZetaConjugationReflectionAnalytic :
    RiemannZetaConjugationReflectionAnalytic := by
  unfold RiemannZetaConjugationReflectionAnalytic
  refine analyticOnNhd_conj_comp_conj
    (s := (({(1 : ℂ)} : Set ℂ)ᶜ))
    (t := (({(1 : ℂ)} : Set ℂ)ᶜ))
    analyticOn_riemannZeta ?_
  intro z hz
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
  intro h
  exact hz (by simpa using congrArg conj h)

/--
If the reflected zeta side is analytic on the regular domain, the checked
half-plane conjugation theorem extends to the global source-shaped formula.
-/
theorem riemannZetaConjugationFormulaOnRegularSet_of_reflectionAnalytic
    (hreflect : RiemannZetaConjugationReflectionAnalytic) :
    RiemannZetaConjugationFormulaOnRegularSet := by
  have hf :
      AnalyticOnNhd ℂ riemannZeta (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    simpa using analyticOn_riemannZeta
  have hU : IsPreconnected (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    have hrank : 1 < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    exact (isConnected_compl_singleton_of_one_lt_rank
      (E := ℂ) hrank (1 : ℂ)).isPreconnected
  have htwo_mem : (2 : ℂ) ∈ (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    norm_num
  have hfg_eventually :
      Filter.EventuallyEq (nhds (2 : ℂ))
        (fun s : ℂ => riemannZeta s)
        (fun s : ℂ => conj (riemannZeta (conj s))) := by
    have hright :
        Filter.Eventually (fun s : ℂ => 1 < s.re) (nhds (2 : ℂ)) := by
      exact (Complex.continuous_re.tendsto (2 : ℂ)).eventually
        (lt_mem_nhds (show 1 < (2 : ℂ).re by norm_num))
    filter_upwards [hright] with s hs
    have hbase := riemannZetaConjugationFormula_on_one_lt_re s hs
    rw [hbase]
    simp
  have heqOn : Set.EqOn
      (fun s : ℂ => riemannZeta s)
      (fun s : ℂ => conj (riemannZeta (conj s)))
      (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    exact hf.eqOn_of_preconnected_of_eventuallyEq
      hreflect hU htwo_mem hfg_eventually
  intro s hs
  have hmem : s ∈ (({(1 : ℂ)} : Set ℂ)ᶜ) := by
    simpa using hs
  have h := heqOn hmem
  have hstar := congrArg (starRingEnd ℂ) h
  simpa using hstar.symm

/--
The zeta conjugation formula on the regular domain.

The proof combines the checked Dirichlet-series identity on `1 < re s`, the
generic reflection-analyticity theorem, and Mathlib's analytic identity theorem
on the punctured plane `{1}^c`.
-/
theorem riemannZetaConjugationFormulaOnRegularSet :
    RiemannZetaConjugationFormulaOnRegularSet :=
  riemannZetaConjugationFormulaOnRegularSet_of_reflectionAnalytic
    riemannZetaConjugationReflectionAnalytic

end ComplexCompactExhaustion

end RiemannHypothesisProject
