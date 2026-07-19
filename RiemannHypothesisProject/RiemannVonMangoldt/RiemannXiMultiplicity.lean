import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicity
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalPositiveOrdinateCount
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiGrowth

/-!
# Xi divisor multiplicity at positive-ordinate zeta zeroes

This file identifies the analytic divisor order used by Jensen's formula with
the project's existing `zetaZeroMultiplicity`.  The bridge is local: away
from `0` and `1`, zeta is xi times a nonvanishing analytic factor built from
the entire reciprocal real Gamma factor.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Filter Topology
open scoped Topology

/-- The nonvanishing local factor converting xi back to zeta. -/
def xiToZetaFactor (s : Complex) : Complex :=
  2 * (Complex.Gammaℝ s)⁻¹ * (s * (s - 1))⁻¹

/-- At a positive-ordinate zero, the xi-to-zeta factor is analytic. -/
theorem analyticAt_xiToZetaFactor
    (rho : PositiveOrdinateZetaZeroSubtype) :
    AnalyticAt Complex xiToZetaFactor (rho : Complex) := by
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro h
    have him := rho.property
    rw [h] at him
    norm_num at him
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro h
    have hz : IsZetaZero (rho : Complex) :=
      mem_riemannZetaZeros.mp rho.1.property
    have hre := hz.re_lt_one
    rw [h] at hre
    norm_num at hre
  have hpoly : AnalyticAt Complex (fun s : Complex ↦ s * (s - 1)) (rho : Complex) := by
    fun_prop
  have hpoly_ne : (rho : Complex) * ((rho : Complex) - 1) ≠ 0 :=
    mul_ne_zero hrho0 (sub_ne_zero.mpr hrho1)
  have hgamma : AnalyticAt Complex (fun s : Complex ↦ (Complex.Gammaℝ s)⁻¹)
      (rho : Complex) :=
    Complex.differentiable_Gammaℝ_inv.analyticAt _
  unfold xiToZetaFactor
  exact ((analyticAt_const.mul hgamma).mul (hpoly.inv hpoly_ne))

/-- At a positive-ordinate zero, the xi-to-zeta factor does not vanish. -/
theorem xiToZetaFactor_ne_zero
    (rho : PositiveOrdinateZetaZeroSubtype) :
    xiToZetaFactor (rho : Complex) ≠ 0 := by
  have hz : IsZetaZero (rho : Complex) :=
    mem_riemannZetaZeros.mp rho.1.property
  have hre : 0 < (rho : Complex).re :=
    IsZetaZero.re_pos_of_im_pos hz rho.property
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro h
    rw [h] at hre
    norm_num at hre
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro h
    have hlt := hz.re_lt_one
    rw [h] at hlt
    norm_num at hlt
  unfold xiToZetaFactor
  exact mul_ne_zero
    (mul_ne_zero (by norm_num) (inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hre)))
    (inv_ne_zero (mul_ne_zero hrho0 (sub_ne_zero.mpr hrho1)))

/-- Zeta and xi differ by `xiToZetaFactor` throughout a neighborhood of any
positive-ordinate zeta zero. -/
theorem riemannZeta_eventuallyEq_xiToZetaFactor_mul_riemannXi
    (rho : PositiveOrdinateZetaZeroSubtype) :
    riemannZeta =ᶠ[𝓝 (rho : Complex)]
      fun s ↦ xiToZetaFactor s * riemannXi s := by
  have hrho0 : (rho : Complex) ≠ 0 := by
    intro h
    have him := rho.property
    rw [h] at him
    norm_num at him
  have hrho1 : (rho : Complex) ≠ 1 := by
    intro h
    have hz : IsZetaZero (rho : Complex) :=
      mem_riemannZetaZeros.mp rho.1.property
    have hre := hz.re_lt_one
    rw [h] at hre
    norm_num at hre
  have hz : IsZetaZero (rho : Complex) :=
    mem_riemannZetaZeros.mp rho.1.property
  have hrhore : 0 < (rho : Complex).re :=
    IsZetaZero.re_pos_of_im_pos hz rho.property
  have hright : ∀ᶠ s : Complex in 𝓝 (rho : Complex), 0 < s.re :=
    (Complex.continuous_re.tendsto (rho : Complex)).eventually (lt_mem_nhds hrhore)
  filter_upwards [eventually_ne_nhds hrho0, eventually_ne_nhds hrho1, hright]
    with s hs0 hs1 hsre
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1]
  rw [riemannZeta_def_of_ne_zero hs0]
  unfold xiToZetaFactor
  rw [div_eq_mul_inv]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hs0, hs1, hsub, Complex.Gammaℝ_ne_zero_of_re_pos hsre]

/-- Xi's analytic divisor order is exactly the project's zeta-zero
multiplicity at every positive-ordinate zero. -/
theorem analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity
    (rho : PositiveOrdinateZetaZeroSubtype) :
    analyticOrderAt riemannXi (rho : Complex) =
      zetaZeroMultiplicity rho.1 := by
  have hfactor := analyticAt_xiToZetaFactor rho
  have hxi : AnalyticAt Complex riemannXi (rho : Complex) :=
    differentiable_riemannXi.analyticAt _
  have hfactor_order :
      analyticOrderAt xiToZetaFactor (rho : Complex) = 0 :=
    hfactor.analyticOrderAt_eq_zero.mpr (xiToZetaFactor_ne_zero rho)
  have hcongr :
      analyticOrderAt riemannZeta (rho : Complex) =
        analyticOrderAt (xiToZetaFactor * riemannXi) (rho : Complex) := by
    exact analyticOrderAt_congr
      (riemannZeta_eventuallyEq_xiToZetaFactor_mul_riemannXi rho)
  rw [analyticOrderAt_mul hfactor hxi, hfactor_order, zero_add] at hcongr
  rw [← hcongr, analyticOrderAt_riemannZeta_eq_zetaZeroMultiplicity]

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
