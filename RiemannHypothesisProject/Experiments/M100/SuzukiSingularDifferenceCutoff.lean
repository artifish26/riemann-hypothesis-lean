import RiemannHypothesisProject.Experiments.M100.SuzukiSingularBoundaryCutoff

/-!
# M100-DF6D2 singular-difference cutoff limit

This module isolates the diagonal cutoff in the finite-square singular term.
The Lipschitz removal estimate already proved for the exact Suzuki integrand
supplies an integrable majorant, while the diagonal itself is product-null.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

/-- The finite-square norm-difference quotient with an inner diagonal cutoff. -/
def suzukiCutoffSingularDifferenceIntegrand
    (ε : Real) (v : SchwartzLineTestFunction) (p : Real × Real) : Real :=
  if ε ≤ |p.1 - p.2| then
    ‖v p.1 - v p.2‖ ^ 2 / |p.1 - p.2|
  else 0

theorem measurable_suzukiCutoffSingularDifferenceIntegrand
    (ε : Real) (v : SchwartzLineTestFunction) :
    Measurable (suzukiCutoffSingularDifferenceIntegrand ε v) := by
  unfold suzukiCutoffSingularDifferenceIntegrand
  exact Measurable.ite
    (measurableSet_le measurable_const (by fun_prop))
    (by fun_prop) measurable_const

/-- When the outer cutoff contains `t`, the real reciprocal kernel is exactly
the inner-cutoff reciprocal indicator. -/
theorem re_suzukiReciprocalCutoffKernel_eq_innerCutoff
    {ε R t : Real} (htR : |t| ≤ R) :
    (suzukiReciprocalCutoffKernel ε R t).re =
      if ε ≤ |t| then |t|⁻¹ else 0 := by
  by_cases hεt : ε ≤ |t|
  · have htMem : t ∈ suzukiReciprocalCutoffSet ε R := by
      by_cases ht : 0 ≤ t
      · right
        constructor
        · simpa only [abs_of_nonneg ht] using hεt
        · simpa only [abs_of_nonneg ht] using htR
      · have ht' : t ≤ 0 := le_of_not_ge ht
        left
        rw [abs_of_nonpos ht'] at hεt htR
        constructor <;> linarith
    simp only [suzukiReciprocalCutoffKernel, Set.indicator_of_mem htMem,
      Complex.ofReal_re, if_pos hεt]
  · have htNotMem : t ∉ suzukiReciprocalCutoffSet ε R := by
      intro htMem
      exact hεt (le_abs_of_mem_suzukiReciprocalCutoffSet htMem)
    simp only [suzukiReciprocalCutoffKernel,
      Set.indicator_of_notMem htNotMem, Complex.zero_re, if_neg hεt]

/-- On a finite Suzuki square contained in the outer cutoff, the reciprocal
kernel times the norm difference is exactly the named cutoff integrand. -/
theorem re_suzukiReciprocalCutoffKernel_mul_normSq_eq_cutoff
    {ε R a : Real} (hR : 2 * a ≤ R) (v : SchwartzLineTestFunction)
    {p : Real × Real} (hp : p ∈ suzukiFiniteSquare a) :
    (suzukiReciprocalCutoffKernel ε R (p.1 - p.2)).re *
        ‖v p.1 - v p.2‖ ^ 2 =
      suzukiCutoffSingularDifferenceIntegrand ε v p := by
  have hdist : |p.1 - p.2| ≤ 2 * a := by
    rcases hp with ⟨⟨hp1l, hp1r⟩, ⟨hp2l, hp2r⟩⟩
    rw [abs_le]
    constructor <;> linarith
  rw [re_suzukiReciprocalCutoffKernel_eq_innerCutoff (hdist.trans hR)]
  by_cases hcut : ε ≤ |p.1 - p.2|
  · simp only [hcut, if_true, suzukiCutoffSingularDifferenceIntegrand]
    rw [inv_mul_eq_div]
  · simp [suzukiCutoffSingularDifferenceIntegrand, hcut]

/-- The uncut real diagonal difference quotient is integrable on each finite
Suzuki square. -/
theorem integrableOn_suzukiSingularDifferenceNormSq
    (a : Real) (v : SchwartzLineTestFunction) :
    IntegrableOn
      (fun p : Real × Real =>
        ‖v p.1 - v p.2‖ ^ 2 / |p.1 - p.2|)
      (suzukiFiniteSquare a) := by
  have hpolarized :=
    (integrableOn_suzukiSingularDifferencePolarization a v v).re
  apply hpolarized.congr
  filter_upwards with p
  exact suzukiSingularDifferencePolarization_self_re v p.1 p.2

/-- Dominated convergence removes the inner diagonal cutoff from the exact
finite-square norm-difference quotient. -/
theorem tendsto_integral_suzukiCutoffSingularDifferenceIntegrand
    (a : Real) (v : SchwartzLineTestFunction) :
    Tendsto
      (fun ε : Real =>
        ∫ p in suzukiFiniteSquare a,
          suzukiCutoffSingularDifferenceIntegrand ε v p)
      (𝓝[>] (0 : Real))
      (𝓝 (∫ p in suzukiFiniteSquare a,
        ‖v p.1 - v p.2‖ ^ 2 / |p.1 - p.2|)) := by
  let μ : Measure (Real × Real) :=
    volume.restrict (suzukiFiniteSquare a)
  let majorant : Real × Real → Real := fun p =>
    ‖v p.1 - v p.2‖ ^ 2 / |p.1 - p.2|
  have hdiagFull :
      ∀ᵐ p : Real × Real ∂volume, p.1 ≠ p.2 := by
    have hdiagMeas : MeasurableSet {p : Real × Real | p.1 ≠ p.2} :=
      (measurableSet_eq_fun measurable_fst measurable_snd).compl
    rw [Measure.volume_eq_prod,
      Measure.ae_prod_iff_ae_ae hdiagMeas]
    filter_upwards with x
    exact (volume.ae_ne x).mono fun y hy => Ne.symm hy
  have hdiag : ∀ᵐ p ∂μ, p.1 ≠ p.2 :=
    (ae_mono Measure.restrict_le_self) hdiagFull
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : Real),
      AEStronglyMeasurable
        (suzukiCutoffSingularDifferenceIntegrand ε v) μ := by
    filter_upwards with ε
    exact (measurable_suzukiCutoffSingularDifferenceIntegrand ε v)
      |>.aestronglyMeasurable
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : Real), ∀ᵐ p ∂μ,
      ‖suzukiCutoffSingularDifferenceIntegrand ε v p‖ ≤ majorant p := by
    filter_upwards with ε
    filter_upwards with p
    have hnonneg : 0 ≤ majorant p :=
      div_nonneg (sq_nonneg _) (abs_nonneg _)
    by_cases hcut : ε ≤ |p.1 - p.2|
    · simp [suzukiCutoffSingularDifferenceIntegrand, hcut, majorant,
        Real.norm_eq_abs]
    · simp [suzukiCutoffSingularDifferenceIntegrand, hcut, majorant, hnonneg]
  have hlimit : ∀ᵐ p ∂μ,
      Tendsto
        (fun ε : Real => suzukiCutoffSingularDifferenceIntegrand ε v p)
        (𝓝[>] (0 : Real)) (𝓝 (majorant p)) := by
    filter_upwards [hdiag] with p hp
    have hd : 0 < |p.1 - p.2| :=
      abs_pos.mpr (sub_ne_zero.mpr hp)
    have heventually :
        ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ |p.1 - p.2| := by
      have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < |p.1 - p.2| :=
        mem_inf_of_left (Iio_mem_nhds hd)
      exact hlt.mono fun ε hε => hε.le
    refine (tendsto_congr' (heventually.mono fun ε hε => ?_)).2
      tendsto_const_nhds
    simp [suzukiCutoffSingularDifferenceIntegrand, hε, majorant]
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound
    (integrableOn_suzukiSingularDifferenceNormSq a v) hlimit
  change Tendsto
    (fun ε : Real =>
      ∫ p in suzukiFiniteSquare a,
        suzukiCutoffSingularDifferenceIntegrand ε v p)
    (𝓝[>] (0 : Real))
    (𝓝 (∫ p in suzukiFiniteSquare a,
      ‖v p.1 - v p.2‖ ^ 2 / |p.1 - p.2|)) at hdct
  exact hdct

end

end M100
end Experiments
end RiemannHypothesisProject
