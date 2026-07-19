import Mathlib.NumberTheory.LSeries.Dirichlet
import RiemannHypothesisProject.GuinandWeilConcrete.ArchimedeanLogDerivative
import RiemannHypothesisProject.GuinandWeilConcrete.XiRectangleIdentity

/-!
# Xi logarithmic derivative on the right half-plane

This module begins the right-vertical evaluation by proving the exact
factorization and logarithmic-derivative decomposition of Riemann xi on
`re s > 1`.  It then replaces the zeta logarithmic derivative by the
absolutely convergent von Mangoldt L-series and the Gamma factor by the
project's checked digamma normalization.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Complex Filter

/-- Classical xi product formula on the zero-free right half-plane. -/
theorem riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta
    {s : Complex} (hs : 1 < s.re) :
    riemannXi s =
      s * (s - 1) * Complex.Gammaℝ s * riemannZeta s / 2 := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro hone
    rw [hone] at hs
    norm_num at hs
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  field_simp [hgamma]

/-- The right-half-plane product formula holds throughout a neighborhood of
each point there, so its derivative may be transported to xi. -/
theorem riemannXi_eventuallyEq_polynomial_mul_GammaR_mul_riemannZeta
    {s : Complex} (hs : 1 < s.re) :
    riemannXi =ᶠ[nhds s]
      fun z => z * (z - 1) * Complex.Gammaℝ z * riemannZeta z / 2 := by
  have hright : ∀ᶠ z : Complex in nhds s, 1 < z.re :=
    (Complex.continuous_re.tendsto s).eventually (lt_mem_nhds hs)
  filter_upwards [hright] with z hz
  exact riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta hz

/-- Exact logarithmic derivative of xi on `re s > 1`, before replacing the
zeta and Gamma factors by their source-side normalizations. -/
theorem logDeriv_riemannXi_eq_rightHalfPlaneFactors
    {s : Complex} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) +
        deriv Complex.Gammaℝ s / Complex.Gammaℝ s +
        deriv riemannZeta s / riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro hone
    rw [hone] at hs
    norm_num at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hgamma : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have hgammaDiff : DifferentiableAt Complex Complex.Gammaℝ s := by
    have hinv := (Complex.differentiable_Gammaℝ_inv s).inv
      (inv_ne_zero hgamma)
    have hfun :
        (fun z : Complex => (Complex.Gammaℝ z)⁻¹)⁻¹ = Complex.Gammaℝ := by
      funext z
      simp
    rw [hfun] at hinv
    exact hinv
  have hzetaDiff : DifferentiableAt Complex riemannZeta s :=
    differentiableAt_riemannZeta hs1
  let A : Complex → Complex := fun z =>
    z * (z - 1) * Complex.Gammaℝ z * riemannZeta z
  have hproduct :=
    riemannXi_eventuallyEq_polynomial_mul_GammaR_mul_riemannZeta hs
  have hlogCongr :
      logDeriv riemannXi s = logDeriv (fun z => A z / 2) s := by
    rw [logDeriv_apply, logDeriv_apply, hproduct.deriv_eq,
      hproduct.self_of_nhds]
  have hscale : logDeriv (fun z => A z / 2) s = logDeriv A s := by
    simpa only [div_eq_mul_inv] using
      (logDeriv_mul_const (f := A) s (2 : Complex)⁻¹ (inv_ne_zero two_ne_zero))
  rw [hlogCongr, hscale]
  dsimp only [A]
  rw [logDeriv_mul
      (f := fun z => z * (z - 1) * Complex.Gammaℝ z)
      (g := riemannZeta) s
      (mul_ne_zero (mul_ne_zero hs0 hsub) hgamma) hzeta
      (((differentiableAt_id.mul
        (differentiableAt_id.sub_const 1)).mul hgammaDiff)) hzetaDiff,
    logDeriv_mul
      (f := fun z => z * (z - 1)) (g := Complex.Gammaℝ) s
      (mul_ne_zero hs0 hsub) hgamma
      (differentiableAt_id.mul (differentiableAt_id.sub_const 1)) hgammaDiff,
    logDeriv_mul
      (f := fun z => z) (g := fun z => z - 1) s
      hs0 hsub differentiableAt_id
      (differentiableAt_id.sub_const 1)]
  simp only [logDeriv_apply, deriv_id'', deriv_sub_const, one_div]

/-- Literature-shaped right-half-plane decomposition: rational pole terms,
Deligne Gamma/digamma term, and the von Mangoldt Dirichlet series. -/
theorem logDeriv_riemannXi_eq_rightHalfPlaneLiteratureTerms
    {s : Complex} (hs : 1 < s.re) :
    logDeriv riemannXi s =
      1 / s + 1 / (s - 1) -
        (Real.log Real.pi : Complex) / 2 +
        Complex.digamma (s / 2) / 2 -
        LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex)) s := by
  rw [logDeriv_riemannXi_eq_rightHalfPlaneFactors hs,
    deriv_GammaR_div_GammaR_eq_digamma (zero_lt_one.trans hs)]
  have hvon :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  change LSeries (fun n : Nat =>
    (ArithmeticFunction.vonMangoldt n : Complex)) s =
      -deriv riemannZeta s / riemannZeta s at hvon
  rw [hvon]
  ring

/-- Differentiated xi reflection law.  The logarithmic derivative changes
sign under `s ↦ 1 - s` away from xi's zeros. -/
theorem logDeriv_riemannXi_one_sub
    (s : Complex) (hxi : riemannXi s ≠ 0) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  have hreflected : riemannXi (1 - s) ≠ 0 := by
    simpa only [riemannXi_one_sub] using hxi
  have hfunctions :
      (fun z : Complex => riemannXi (1 - z)) = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  have hderiv :
      deriv (fun z : Complex => riemannXi (1 - z)) s =
        deriv riemannXi s := by
    rw [hfunctions]
  have hchain :
      deriv (fun z : Complex => riemannXi (1 - z)) s =
        -deriv riemannXi (1 - s) := by
    rw [show (fun z : Complex => riemannXi (1 - z)) =
      riemannXi ∘ (fun z : Complex => 1 - z) by rfl]
    rw [deriv_comp s differentiable_riemannXi.differentiableAt (by fun_prop)]
    simp
  rw [logDeriv_apply, logDeriv_apply, riemannXi_one_sub]
  rw [hchain] at hderiv
  rw [← neg_div]
  congr 1
  linear_combination -hderiv

/-- The complete weighted xi logarithmic-derivative integrand is odd under
reflection across the critical line. -/
theorem guinandWeilXiContourWeight_mul_logDeriv_one_sub
    (p : Polynomial Real) (s : Complex) (hxi : riemannXi s ≠ 0) :
    guinandWeilXiContourWeight p (1 - s) *
        logDeriv riemannXi (1 - s) =
      -(guinandWeilXiContourWeight p s * logDeriv riemannXi s) := by
  rw [guinandWeilXiContourWeight_one_sub,
    logDeriv_riemannXi_one_sub s hxi]
  ring

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
