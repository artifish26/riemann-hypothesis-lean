import RiemannHypothesisProject.GuinandWeilConcrete.LiteratureNormalization
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Archimedean logarithmic derivative

This module rewrites the logarithmic derivative of Deligne's real gamma
factor in the digamma normalization used in classical explicit formulae.
The identity is proved on the positive half-plane, which contains the full
critical line used by the concrete Guinand-Weil gamma side.
-/

namespace RiemannHypothesisProject

open MeasureTheory

noncomputable section

/-- The logarithmic derivative of Deligne's real gamma factor on the positive
half-plane, expressed using the classical digamma function. -/
theorem deriv_GammaR_div_GammaR_eq_digamma
    {s : Complex} (hs : 0 < s.re) :
    deriv Complex.Gammaℝ s / Complex.Gammaℝ s =
      -(Real.log Real.pi : Complex) / 2 + Complex.digamma (s / 2) / 2 := by
  have hpow :
      HasDerivAt (fun z : Complex => (Real.pi : Complex) ^ (-z / 2))
        ((Real.pi : Complex) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s :=
    ((hasDerivAt_id s).neg.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hs_half_re : 0 < (s / 2).re := by
    simpa using div_pos hs (by norm_num : (0 : Real) < 2)
  have hgamma_diff : DifferentiableAt Complex Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma (s / 2) (fun m hm => by
      have hre := congrArg Complex.re hm
      simp at hre
      linarith)
  have hgamma :
      HasDerivAt (fun z : Complex => Complex.Gamma (z / 2))
        (deriv Complex.Gamma (s / 2) / 2) s :=
    by
      simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
        hgamma_diff.hasDerivAt.comp s
          ((hasDerivAt_id s).div_const 2)
  have hderiv := (hpow.mul hgamma).deriv
  change
    deriv
        ((fun z : Complex => (Real.pi : Complex) ^ (-z / 2)) *
          fun z : Complex => Complex.Gamma (z / 2)) s /
      ((Real.pi : Complex) ^ (-s / 2) * Complex.Gamma (s / 2)) = _
  rw [hderiv, Complex.digamma_def, logDeriv_apply]
  have hpow_ne : (Real.pi : Complex) ^ (-s / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hgamma_ne : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hs_half_re
  rw [Complex.ofReal_log Real.pi_pos.le]
  field_simp [hpow_ne, hgamma_ne]

/-- On the critical line the project gamma logarithmic derivative is the
digamma value at `1/4 + i*t/2`, with the standard `-log pi / 2` correction. -/
theorem guinandWeilGammaLogDerivative_eq_digamma (t : Real) :
    guinandWeilGammaLogDerivative t =
      -(Real.log Real.pi : Complex) / 2 +
        Complex.digamma ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2 := by
  unfold guinandWeilGammaLogDerivative
  rw [deriv_GammaR_div_GammaR_eq_digamma (s := criticalLinePoint t)]
  · congr 2
    unfold criticalLinePoint
    push_cast
    ring_nf
  · simp [criticalLinePoint]

/-- Integrability of the Archimedean integrand is exactly integrability of
the corresponding critical-line digamma expression. -/
theorem integrable_guinandWeilGammaLogDerivative_iff_digamma
    (f : SchwartzLineTestFunction) :
    Integrable (fun t : Real =>
        ((f t) * guinandWeilGammaLogDerivative t).re) ↔
      Integrable (fun t : Real =>
        ((f t) *
          (-(Real.log Real.pi : Complex) / 2 +
            Complex.digamma
              ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2)).re) := by
  apply integrable_congr
  filter_upwards [] with t
  rw [guinandWeilGammaLogDerivative_eq_digamma]

/-- The literature Archimedean side in its standard critical-line digamma
normalization. -/
theorem guinandWeilLiteratureGammaSide_eq_digammaIntegral
    (f : SchwartzLineTestFunction) :
    guinandWeilLiteratureGammaSide f =
      (1 / Real.pi) *
        ∫ t : Real,
          ((f t) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) / 2)).re
          ∂volume := by
  unfold guinandWeilLiteratureGammaSide
  apply congrArg (fun x : Real => (1 / Real.pi) * x)
  apply integral_congr_ae
  filter_upwards [] with t
  rw [guinandWeilGammaLogDerivative_eq_digamma]

end

end RiemannHypothesisProject
