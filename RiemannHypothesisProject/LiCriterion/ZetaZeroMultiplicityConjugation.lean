import RiemannHypothesisProject.ComplexAnalyticReflection
import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicity

/-!
# Conjugation invariance of zeta-zero multiplicity

Complex conjugation reflects the local analytic factorization at a zero.  The
reflected nonvanishing factor remains analytic, so the analytic order—and
hence the natural-number multiplicity—is unchanged.
-/

namespace RiemannHypothesisProject

open Filter

open scoped ComplexConjugate
open scoped Topology

noncomputable section

/-- Finite analytic order is invariant under the reflected operation
`z ↦ conj (f (conj z))`. -/
theorem analyticOrderAt_conj_comp_conj_eq
    {f : Complex -> Complex} {z₀ : Complex}
    (hf : AnalyticAt Complex f z₀)
    (hfinite : analyticOrderAt f z₀ ≠ ⊤) :
    analyticOrderAt (fun z : Complex => conj (f (conj z))) (conj z₀) =
      analyticOrderAt f z₀ := by
  let n : Nat := analyticOrderNatAt f z₀
  have horder : analyticOrderAt f z₀ = (n : ENat) := by
    exact (Nat.cast_analyticOrderNatAt hfinite).symm
  rcases (hf.analyticOrderAt_eq_natCast).mp horder with
    ⟨g, hg, hg_ne, hfactor⟩
  let reflectedFactor : Complex -> Complex := fun z => conj (g (conj z))
  have hreflectedFactor :
      AnalyticAt Complex reflectedFactor (conj z₀) := by
    simpa [reflectedFactor] using
      (analyticAt_conj_comp_conj (by simpa using hg))
  have hreflectedFactor_ne : reflectedFactor (conj z₀) ≠ 0 := by
    simpa [reflectedFactor] using hg_ne
  have hfactor_pre :
      ∀ᶠ z in 𝓝 (conj z₀),
        f (conj z) = (conj z - z₀) ^ n * g (conj z) := by
    have htendsto : Tendsto conj (𝓝 (conj z₀)) (𝓝 z₀) := by
      simpa using Complex.continuous_conj.tendsto (conj z₀)
    exact htendsto.eventually hfactor
  have hreflectedOrder :
      analyticOrderAt (fun z : Complex => conj (f (conj z))) (conj z₀) =
        (n : ENat) := by
    apply
      (analyticAt_conj_comp_conj (by simpa using hf)).analyticOrderAt_eq_natCast.mpr
    refine ⟨reflectedFactor, hreflectedFactor, hreflectedFactor_ne, ?_⟩
    filter_upwards [hfactor_pre] with z hz
    rw [hz]
    simp [reflectedFactor, map_mul, map_pow]
  exact hreflectedOrder.trans horder.symm

namespace ComplexCompactExhaustion

/-- Analytic multiplicity of an actual zeta zero is unchanged by complex
conjugation. -/
theorem zetaZeroMultiplicity_conj (rho : ZetaZeroSubtype) :
    zetaZeroMultiplicity
        ⟨conj (rho : Complex),
          zetaZeroConjugationSymmetry (rho : Complex) rho.property⟩ =
      zetaZeroMultiplicity rho := by
  let reflectedZeta : Complex -> Complex :=
    fun z => conj (riemannZeta (conj z))
  have hrho_ne_one : (rho : Complex) ≠ 1 := by
    intro h
    have hz : IsZetaZero (rho : Complex) := by
      exact mem_riemannZetaZeros.mp rho.property
    have hre := hz.re_lt_one
    rw [h] at hre
    norm_num at hre
  have hconj_ne_one : conj (rho : Complex) ≠ 1 := by
    intro h
    apply hrho_ne_one
    have := congrArg conj h
    simpa using this
  have heventually :
      riemannZeta =ᶠ[𝓝 (conj (rho : Complex))] reflectedZeta := by
    filter_upwards [eventually_ne_nhds hconj_ne_one] with z hz
    have hconj_z_ne_one : conj z ≠ 1 := by
      intro h
      apply hz
      have := congrArg conj h
      simpa using this
    have hformula :=
      riemannZetaConjugationFormulaOnRegularSet (conj z) hconj_z_ne_one
    simpa [reflectedZeta] using hformula
  have hreflection := analyticOrderAt_conj_comp_conj_eq
    (analyticAt_riemannZeta_of_zetaZeroSubtype rho)
    (analyticOrderAt_riemannZeta_ne_top_of_zetaZeroSubtype rho)
  have horder :
      analyticOrderAt riemannZeta (conj (rho : Complex)) =
        analyticOrderAt riemannZeta (rho : Complex) := by
    calc
      analyticOrderAt riemannZeta (conj (rho : Complex)) =
          analyticOrderAt reflectedZeta (conj (rho : Complex)) :=
        analyticOrderAt_congr heventually
      _ = analyticOrderAt riemannZeta (rho : Complex) := by
        simpa [reflectedZeta] using hreflection
  unfold zetaZeroMultiplicity
  exact congrArg ENat.toNat horder

/-- Multiplicity equality in the positive-to-negative zero equivalence. -/
theorem zetaZeroMultiplicity_positiveNegativeConjEquiv
    (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaZeroMultiplicity
        (positiveNegativeOrdinateZetaZeroConjEquiv rho).1 =
      zetaZeroMultiplicity rho.1 := by
  simpa [positiveNegativeOrdinateZetaZeroConjEquiv] using
    zetaZeroMultiplicity_conj rho.1

end ComplexCompactExhaustion

end

end RiemannHypothesisProject
