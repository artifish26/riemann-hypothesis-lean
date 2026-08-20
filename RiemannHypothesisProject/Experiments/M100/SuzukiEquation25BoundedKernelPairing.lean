import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25SoftCutoffKernel

/-!
# Bounded translation-kernel pairing bridge

This is the bounded continuous-kernel version of the exponential physical
bridge used in the finite Gamma cancellation.  It supplies the soft cutoff
with the same finite-square/autocorrelation identification.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set SchwartzLineTestFunction
open scoped ComplexConjugate

theorem integral_boundedEvenKernel_mul_autocorrelation_eq_pairing
    {kernel : Real → Real} {a C : Real} {v : SchwartzLineTestFunction}
    (hkernel : Continuous kernel)
    (hbound : ∀ t, ‖kernel t‖ ≤ C)
    (heven : ∀ t, kernel (-t) = kernel t)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    (∫ t : Real, (kernel t : Complex) * autocorrelation v t) =
      suzukiFiniteKernelPairingComplex kernel a v := by
  let F : Real → Real → Complex := fun x y =>
    (kernel (x - y) : Complex) * v y * conj (v x)
  let G : Real → Real → Complex := fun y t =>
    (kernel t : Complex) * v y * conj (v (t + y))
  have hv : Integrable v := v.integrable
  have hconj : Integrable (fun x : Real => conj (v x)) := by
    have hcomp := Complex.conjCLE.toContinuousLinearMap.integrable_comp hv
    change Integrable (fun x : Real => Complex.conjCLE (v x))
    exact hcomp
  have hseparable : Integrable (fun p : Real × Real =>
      v p.2 * conj (v p.1)) (volume.prod volume) := by
    have hprod := hconj.mul_prod hv
    apply hprod.congr
    filter_upwards with p
    ring
  have hFraw : Integrable (fun p : Real × Real =>
      (kernel (p.1 - p.2) : Complex) *
        (v p.2 * conj (v p.1))) (volume.prod volume) := by
    apply hseparable.bdd_mul
    · exact (Complex.continuous_ofReal.comp
        (hkernel.comp (by fun_prop : Continuous
          (fun p : Real × Real => p.1 - p.2)))).aestronglyMeasurable
    · filter_upwards with p
      simpa only [Complex.norm_real] using hbound (p.1 - p.2)
  have hF : Integrable (fun p : Real × Real => F p.1 p.2)
      (volume.prod volume) := by
    simpa only [F, mul_assoc] using hFraw
  have hcoupled : Integrable (fun p : Real × Real =>
      v p.1 * conj (v (p.2 + p.1))) (volume.prod volume) := by
    let H : Real × Real → Complex := fun p => v p.1 * conj (v p.2)
    have hH : Integrable H := hv.mul_prod hconj
    have hcomp :=
      (measurePreserving_prod_add_right
        (volume : Measure Real) (volume : Measure Real)).integrable_comp_of_integrable hH
    change Integrable (fun p : Real × Real =>
      v p.1 * conj (v (p.2 + p.1))) (volume.prod volume) at hcomp
    exact hcomp
  have hGraw : Integrable (fun p : Real × Real =>
      (kernel p.2 : Complex) *
        (v p.1 * conj (v (p.2 + p.1)))) (volume.prod volume) := by
    apply hcoupled.bdd_mul
    · exact (Complex.continuous_ofReal.comp
        (hkernel.comp (by fun_prop : Continuous
          (fun p : Real × Real => p.2)))).aestronglyMeasurable
    · filter_upwards with p
      simpa only [Complex.norm_real] using hbound p.2
  have hG : Integrable (fun p : Real × Real => G p.1 p.2)
      (volume.prod volume) := by
    simpa only [G, mul_assoc] using hGraw
  have hrestrict :
      (∫ p in suzukiFiniteSquare a, F p.1 p.2) =
        ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    by_cases hx : p.1 ∈ Set.Icc (-a) a
    · have hy : p.2 ∉ Set.Icc (-a) a := fun hy => hp ⟨hx, hy⟩
      have hvy : v p.2 = 0 := by
        by_contra hne
        exact hy (hsupport hne)
      simp [F, hvy]
    · have hvx : v p.1 = 0 := by
        by_contra hne
        exact hx (hsupport hne)
      simp [F, hvx]
  have hfiber (y : Real) :
      (∫ x : Real, F x y) = ∫ t : Real, G y t := by
    have htranslate := integral_sub_right_eq_self
      (fun t : Real => G y t) y (μ := volume)
    simpa only [F, G, sub_add_cancel] using htranslate
  have hphysicalNeg :
      (∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume)) =
        ∫ t : Real, (kernel t : Complex) * autocorrelation v (-t) := by
    rw [MeasureTheory.integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G]
    rw [show (fun x : Real =>
        (kernel t : Complex) * v x * conj (v (t + x))) =
          fun x : Real =>
            (kernel t : Complex) * (v x * conj (v (t + x))) by
        funext x
        ring]
    rw [integral_const_mul]
    apply congrArg (fun z : Complex => (kernel t : Complex) * z)
    rw [autocorrelation_apply, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [star_apply]
    congr 2
    ring
  have hreflect := integral_neg_eq_self
    (f := fun t : Real => (kernel t : Complex) * autocorrelation v t) volume
  have hphysical :
      (∫ t : Real, (kernel t : Complex) * autocorrelation v (-t)) =
        ∫ t : Real, (kernel t : Complex) * autocorrelation v t := by
    simpa only [heven, neg_neg] using hreflect
  calc
    (∫ t : Real, (kernel t : Complex) * autocorrelation v t) =
        ∫ t : Real, (kernel t : Complex) * autocorrelation v (-t) :=
      hphysical.symm
    _ = ∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume) :=
      hphysicalNeg.symm
    _ = ∫ y : Real, ∫ t : Real, G y t :=
      MeasureTheory.integral_prod (fun p : Real × Real => G p.1 p.2) hG
    _ = ∫ y : Real, ∫ x : Real, F x y := by
      apply integral_congr_ae
      filter_upwards with y
      exact (hfiber y).symm
    _ = ∫ x : Real, ∫ y : Real, F x y :=
      (MeasureTheory.integral_integral_swap hF).symm
    _ = ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) :=
      MeasureTheory.integral_integral hF
    _ = ∫ p in suzukiFiniteSquare a, F p.1 p.2 := hrestrict.symm
    _ = suzukiFiniteKernelPairingComplex kernel a v := by rfl

/-- The soft reciprocal finite-square pairing is its physical
autocorrelation pairing. -/
theorem integral_softReciprocalKernel_mul_autocorrelation_eq_pairing
    {lam a : Real} (hlam : 0 ≤ lam) (v : SuzukiSmoothCore a) :
    (∫ t : Real,
        (suzukiEquation25SoftReciprocalKernel lam t : Complex) *
          autocorrelation v.1 t) =
      suzukiFiniteKernelPairingComplex
        (suzukiEquation25SoftReciprocalKernel lam) a v.1 := by
  apply integral_boundedEvenKernel_mul_autocorrelation_eq_pairing
    (continuous_suzukiEquation25SoftReciprocalKernel lam)
    (fun t => norm_suzukiEquation25SoftReciprocalKernel_le hlam t)
    (suzukiEquation25SoftReciprocalKernel_neg lam)
  intro x hx
  exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩

end

end M100
end Experiments
end RiemannHypothesisProject
