import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic

/-!
# Complex analytic reflection

This file records a small reusable analytic fact: if `f` is complex analytic at
`conj z`, then `z ↦ conj (f (conj z))` is complex analytic at `z`.

The proof is by conjugating the local scalar power-series coefficients.
-/

namespace RiemannHypothesisProject

open Filter

open scoped ComplexConjugate

noncomputable section

/--
If `f` has a power series at `conj z₀`, then the reflected function
`z ↦ conj (f (conj z))` has the conjugated coefficient power series at `z₀`.
-/
theorem analyticAt_conj_comp_conj_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {z₀ : ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HasFPowerSeriesAt f p (conj z₀)) :
    AnalyticAt ℂ (fun z : ℂ => conj (f (conj z))) z₀ := by
  refine ⟨FormalMultilinearSeries.ofScalars ℂ (fun n => conj (p.coeff n)), ?_⟩
  rw [hasFPowerSeriesAt_iff]
  have hbase :
      ∀ᶠ w in nhds 0,
        HasSum (fun n : ℕ => w ^ n • p.coeff n) (f (conj z₀ + w)) := by
    simpa using (hasFPowerSeriesAt_iff.mp hf)
  have hpre :
      ∀ᶠ z in nhds 0,
        HasSum
          (fun n : ℕ => (conj z) ^ n • p.coeff n)
          (f (conj z₀ + conj z)) := by
    have hbase' :
        ∀ᶠ w in nhds (conj (0 : ℂ)),
          HasSum (fun n : ℕ => w ^ n • p.coeff n) (f (conj z₀ + w)) := by
      simpa using hbase
    exact (Complex.continuous_conj.tendsto (0 : ℂ)).eventually hbase'
  filter_upwards [hpre] with z hz
  have hconj :
      HasSum
        (fun n : ℕ => conj ((conj z) ^ n • p.coeff n))
        (conj (f (conj z₀ + conj z))) := by
    exact Complex.hasSum_conj'.mpr hz
  simpa [FormalMultilinearSeries.coeff_ofScalars] using hconj

/-- Analyticity is preserved by the reflected conjugation operation. -/
theorem analyticAt_conj_comp_conj
    {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f (conj z₀)) :
    AnalyticAt ℂ (fun z : ℂ => conj (f (conj z))) z₀ := by
  rcases hf with ⟨p, hp⟩
  exact analyticAt_conj_comp_conj_of_hasFPowerSeriesAt hp

/--
Set-level version of `analyticAt_conj_comp_conj`: if every conjugate point of
`s` lies in a domain where `f` is analytic, then the reflected function is
analytic on `s`.
-/
theorem analyticOnNhd_conj_comp_conj
    {f : ℂ → ℂ} {s t : Set ℂ}
    (hf : AnalyticOnNhd ℂ f t)
    (hst : ∀ z : ℂ, z ∈ s -> conj z ∈ t) :
    AnalyticOnNhd ℂ (fun z : ℂ => conj (f (conj z))) s := by
  intro z hz
  exact analyticAt_conj_comp_conj (hf (conj z) (hst z hz))

end

end RiemannHypothesisProject
