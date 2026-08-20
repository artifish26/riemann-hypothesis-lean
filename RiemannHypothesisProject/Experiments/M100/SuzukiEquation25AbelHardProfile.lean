import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25TailLimitReduction
import RiemannHypothesisProject.Experiments.M100.SuzukiCosineIntegralConstant

/-!
# Abel/hard-cutoff profile for Suzuki's equation (2.5)

The exponential soft cutoff differs from the reciprocal hard cutoff on the
scale `1 / lambda`.  After rescaling, that difference is one fixed integrable
profile.  Its total mass is Euler's constant, by the Gamma-integral
normalization already proved for DF6D2.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Topology

/-- The one-sided rescaled difference between exponential and hard
reciprocal cutoffs. -/
def suzukiEquation25AbelHardProfile (u : Real) : Real :=
  (Ioc (0 : Real) 1).indicator
      (fun t => (1 - Real.exp (-t)) / t) u -
    (Ioi (1 : Real)).indicator
      (fun t => Real.exp (-t) / t) u

theorem integrable_suzukiEquation25AbelHardProfile :
    Integrable suzukiEquation25AbelHardProfile := by
  have hlocal : IntegrableOn
      (fun t : Real => (1 - Real.exp (-t)) / t) (Ioc 0 1) := by
    have h := integrableOn_suzukiExponentialRegularPart
      (lam := (1 : Real)) zero_lt_one
    apply h.neg.congr
    filter_upwards with t
    simp only [suzukiExponentialRegularPart, one_mul, div_eq_mul_inv,
      Pi.neg_apply]
    ring
  have htail : IntegrableOn
      (fun t : Real => Real.exp (-t) / t) (Ioi 1) := by
    simpa only [one_mul, neg_one_mul] using
      (integrableOn_exp_neg_div_Ioi_one
        (lam := (1 : Real)) zero_lt_one)
  unfold suzukiEquation25AbelHardProfile
  exact (hlocal.integrable_indicator measurableSet_Ioc).sub
    (htail.integrable_indicator measurableSet_Ioi)

/-- The rescaled Abel/hard profile has total mass Euler's constant. -/
theorem integral_suzukiEquation25AbelHardProfile :
    (∫ u : Real, suzukiEquation25AbelHardProfile u) =
      Real.eulerMascheroniConstant := by
  have hlocal : IntegrableOn
      (fun t : Real => (1 - Real.exp (-t)) / t) (Ioc 0 1) := by
    have h := integrableOn_suzukiExponentialRegularPart
      (lam := (1 : Real)) zero_lt_one
    apply h.neg.congr
    filter_upwards with t
    simp only [suzukiExponentialRegularPart, one_mul, div_eq_mul_inv,
      Pi.neg_apply]
    ring
  have htail : IntegrableOn
      (fun t : Real => Real.exp (-t) / t) (Ioi 1) := by
    simpa only [one_mul, neg_one_mul] using
      (integrableOn_exp_neg_div_Ioi_one
        (lam := (1 : Real)) zero_lt_one)
  have hnormal :=
    suzukiExponentialNormalizedConstant_eq
      (lam := (1 : Real)) zero_lt_one
  unfold suzukiExponentialNormalizedConstant at hnormal
  rw [intervalIntegral.integral_of_le zero_le_one] at hnormal
  simp only [Real.log_one, sub_zero, neg_one_mul] at hnormal
  unfold suzukiEquation25AbelHardProfile
  rw [integral_sub
      (hlocal.integrable_indicator measurableSet_Ioc)
      (htail.integrable_indicator measurableSet_Ioi),
    integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioi]
  have hlocalNeg :
      (∫ t in Ioc (0 : Real) 1, (1 - Real.exp (-t)) / t) =
        -(∫ t in Ioc (0 : Real) 1,
          suzukiExponentialRegularPart 1 t) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _ht
    simp only [suzukiExponentialRegularPart, one_mul, div_eq_mul_inv,
      Pi.neg_apply]
    ring
  rw [hlocalNeg]
  linarith

/-- An integrable profile samples a bounded continuous function at the
origin under the large-dilation approximate identity. -/
theorem tendsto_integral_suzukiEquation25AbelHardProfile_mul_scale
    (g : Real → Real) (hg : Continuous g) (C : Real)
    (hC : ∀ x, |g x| ≤ C) :
    Tendsto
      (fun lam : Real => ∫ u : Real,
        suzukiEquation25AbelHardProfile u * g (u / lam))
      atTop
      (nhds (Real.eulerMascheroniConstant * g 0)) := by
  let majorant : Real → Real := fun u =>
    C * |suzukiEquation25AbelHardProfile u|
  have hCnonneg : 0 ≤ C := by
    have := hC 0
    exact le_trans (abs_nonneg (g 0)) this
  have hmajorant : Integrable majorant := by
    exact integrable_suzukiEquation25AbelHardProfile.norm.const_mul C
  have hmeas : ∀ lam : Real, AEStronglyMeasurable
      (fun u : Real =>
        suzukiEquation25AbelHardProfile u * g (u / lam)) := by
    intro lam
    exact integrable_suzukiEquation25AbelHardProfile.aestronglyMeasurable.mul
      ((hg.comp (by fun_prop : Continuous (fun u : Real => u / lam)))
        |>.aestronglyMeasurable)
  have hbound : ∀ lam : Real, ∀ᵐ u : Real,
      ‖suzukiEquation25AbelHardProfile u * g (u / lam)‖ ≤ majorant u := by
    intro lam
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_mul]
    simpa only [majorant, mul_comm] using
      (mul_le_mul_of_nonneg_left (hC (u / lam))
        (abs_nonneg (suzukiEquation25AbelHardProfile u)))
  have hpoint : ∀ᵐ u : Real,
      Tendsto
        (fun lam : Real =>
          suzukiEquation25AbelHardProfile u * g (u / lam))
        atTop
        (nhds (suzukiEquation25AbelHardProfile u * g 0)) := by
    filter_upwards with u
    have hdiv : Tendsto (fun lam : Real => u / lam) atTop (nhds 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using
        tendsto_inv_atTop_zero.const_mul u
    exact tendsto_const_nhds.mul (hg.continuousAt.tendsto.comp hdiv)
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant (Filter.Eventually.of_forall hmeas)
      (Filter.Eventually.of_forall hbound) hmajorant hpoint
  convert hdct using 1
  rw [integral_mul_const,
    integral_suzukiEquation25AbelHardProfile]

/-- The even whole-line version of the one-sided Abel/hard profile. -/
def suzukiEquation25SymmetricAbelHardProfile (u : Real) : Real :=
  (1 / 2) * (suzukiEquation25AbelHardProfile u +
    suzukiEquation25AbelHardProfile (-u))

theorem integrable_suzukiEquation25SymmetricAbelHardProfile :
    Integrable suzukiEquation25SymmetricAbelHardProfile := by
  unfold suzukiEquation25SymmetricAbelHardProfile
  exact (integrable_suzukiEquation25AbelHardProfile.add
    integrable_suzukiEquation25AbelHardProfile.comp_neg).const_mul (1 / 2)

theorem integral_suzukiEquation25SymmetricAbelHardProfile :
    (∫ u : Real, suzukiEquation25SymmetricAbelHardProfile u) =
      Real.eulerMascheroniConstant := by
  have hneg := integral_neg_eq_self suzukiEquation25AbelHardProfile volume
  unfold suzukiEquation25SymmetricAbelHardProfile
  rw [integral_const_mul,
    integral_add integrable_suzukiEquation25AbelHardProfile
      integrable_suzukiEquation25AbelHardProfile.comp_neg,
    hneg, integral_suzukiEquation25AbelHardProfile]
  ring

/-- For an even bounded continuous source, symmetrizing the cutoff profile
does not change the approximate-identity limit. -/
theorem tendsto_integral_suzukiEquation25SymmetricAbelHardProfile_mul_scale
    (g : Real → Real) (hg : Continuous g) (hgEven : ∀ x, g (-x) = g x)
    (C : Real) (hC : ∀ x, |g x| ≤ C) :
    Tendsto
      (fun lam : Real => ∫ u : Real,
        suzukiEquation25SymmetricAbelHardProfile u * g (u / lam))
      atTop
      (nhds (Real.eulerMascheroniConstant * g 0)) := by
  have hbase :=
    tendsto_integral_suzukiEquation25AbelHardProfile_mul_scale g hg C hC
  apply hbase.congr'
  filter_upwards with lam
  have hfactor : Integrable (fun u : Real =>
      suzukiEquation25AbelHardProfile u * g (u / lam)) := by
    apply integrable_suzukiEquation25AbelHardProfile.mul_bdd
    · exact (hg.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with u
      exact hC (u / lam)
  have hfactorNeg : Integrable (fun u : Real =>
      suzukiEquation25AbelHardProfile (-u) * g (u / lam)) := by
    have hcomp := hfactor.comp_neg
    apply hcomp.congr
    filter_upwards with u
    rw [show (-u) / lam = -(u / lam) by ring, hgEven]
  have hreflect := integral_neg_eq_self
    (fun u : Real =>
      suzukiEquation25AbelHardProfile u * g (u / lam)) volume
  have hnegIntegral :
      (∫ u : Real,
        suzukiEquation25AbelHardProfile (-u) * g (u / lam)) =
      ∫ u : Real,
        suzukiEquation25AbelHardProfile u * g (u / lam) := by
    rw [← hreflect]
    apply integral_congr_ae
    filter_upwards with u
    rw [show (-u) / lam = -(u / lam) by ring, hgEven]
  unfold suzukiEquation25SymmetricAbelHardProfile
  rw [show (fun u : Real =>
      (1 / 2) *
          (suzukiEquation25AbelHardProfile u +
            suzukiEquation25AbelHardProfile (-u)) * g (u / lam)) =
      fun u : Real => (1 / 2) *
        (suzukiEquation25AbelHardProfile u * g (u / lam) +
          suzukiEquation25AbelHardProfile (-u) * g (u / lam)) by
        funext u
        ring]
  rw [integral_const_mul, integral_add hfactor hfactorNeg,
    hnegIntegral]
  ring

end

end M100
end Experiments
end RiemannHypothesisProject
