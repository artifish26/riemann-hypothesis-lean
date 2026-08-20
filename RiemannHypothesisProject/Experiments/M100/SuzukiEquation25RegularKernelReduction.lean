import RiemannHypothesisProject.Experiments.M100.SuzukiQuarterDigammaValue

/-!
# Scalar-free regular-kernel reduction of Suzuki's equation (2.5)

This module removes the now-evaluated quarter-point Gamma scalar from
`SuzukiEquation25GammaCorrectionAt`.  The remaining proposition is a single
all-smooth-core pairing identity involving the cancellation-safe Lerch kernel,
the regular `r1''` kernel, and the logarithmic Fourier form.

No regular-kernel source theorem is assumed or proved here.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set SchwartzLineTestFunction
open scoped ComplexConjugate

/-- The cancellation-safe non-base part of Suzuki's Archimedean screw
kernel. -/
def suzukiEquation25LerchPhysicalKernel (x : Real) : Real :=
  -(1 / 4) * suzukiLerchDifference x

theorem continuous_suzukiEquation25LerchPhysicalKernel :
    Continuous suzukiEquation25LerchPhysicalKernel := by
  unfold suzukiEquation25LerchPhysicalKernel
  exact continuous_const.mul continuous_suzukiLerchDifference

/-- The elementary scalar restored when the quarter-point Gamma base kernel
is moved from the literature Gamma side to the project scalar. -/
def suzukiEquation25GammaRestorationScalar : Real :=
  Real.pi / 2 + 2 * Real.log 2

theorem suzukiProjectCompleteScalar_eq_gammaBase_add_restoration :
    suzukiProjectCompleteScalar =
      suzukiGammaBaseCoefficient +
        suzukiEquation25GammaRestorationScalar := by
  have h := suzukiGammaBaseCoefficient_sub_completeScalar
  unfold suzukiEquation25GammaRestorationScalar
  linarith

/-- The scalar-free analytic content of the regular Gamma correction.  The
Lerch pairing acts on the source derivative, while the removable `r1''`
pairing acts on the smooth core itself. -/
def SuzukiEquation25RegularKernelCorrectionAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    (suzukiFiniteKernelPairingComplex
        suzukiEquation25LerchPhysicalKernel a
        (SchwartzMap.derivCLM Complex Complex v.1)).re +
      (suzukiFiniteKernelPairingComplex
        suzukiR1SecondKernel a v.1).re =
      suzukiSourceLogFourierForm v.1 +
        suzukiEquation25GammaRestorationScalar *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2

private theorem suzukiGammaScrewKernel_eq_base_add_lerch :
    suzukiGammaScrewKernel = fun x =>
      suzukiGammaBaseKernel x + suzukiEquation25LerchPhysicalKernel x := by
  funext x
  unfold suzukiGammaScrewKernel suzukiEquation25LerchPhysicalKernel
  ring

private theorem suzukiFiniteKernelPairingComplex_gammaScrew_split
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiFiniteKernelPairingComplex suzukiGammaScrewKernel a
        (SchwartzMap.derivCLM Complex Complex v.1) =
      suzukiFiniteKernelPairingComplex suzukiGammaBaseKernel a
          (SchwartzMap.derivCLM Complex Complex v.1) +
        suzukiFiniteKernelPairingComplex
          suzukiEquation25LerchPhysicalKernel a
          (SchwartzMap.derivCLM Complex Complex v.1) := by
  rw [suzukiGammaScrewKernel_eq_base_add_lerch]
  exact suzukiFiniteKernelPairingComplex_add
    continuous_suzukiGammaBaseKernel
    continuous_suzukiEquation25LerchPhysicalKernel
    (SchwartzMap.derivCLM Complex Complex v.1).continuous

/-- The scalar-free regular-kernel identity implies the regular Gamma
correction. -/
theorem suzukiEquation25GammaCorrectionAt_of_regularKernelCorrection
    {a : Real} (hregular : SuzukiEquation25RegularKernelCorrectionAt a) :
    SuzukiEquation25GammaCorrectionAt a := by
  intro ha v
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hgamma :=
    guinandWeilLiteratureGammaSide_suzukiProjectBase_eq_kernelPairing
      ha hsupport
  have hbase := suzukiFiniteKernelPairingComplex_gammaBaseKernel_eq
    ha hsupport
  have hregular_v := hregular ha v
  have hscalar := suzukiProjectCompleteScalar_eq_gammaBase_add_restoration
  have hmass := norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re v
  unfold suzukiFiniteKernelPairing at hgamma
  rw [suzukiFiniteKernelPairingComplex_gammaScrew_split v,
    Complex.add_re, hbase, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← hmass] at hgamma
  rw [hgamma]
  linear_combination hregular_v -
    ‖suzukiSmoothCoreToL2 v‖ ^ 2 * hscalar

/-- Conversely, the regular Gamma correction contains exactly the
scalar-free regular-kernel identity after the checked Gamma base term is
cancelled. -/
theorem suzukiEquation25RegularKernelCorrectionAt_of_gammaCorrection
    {a : Real} (hgamma : SuzukiEquation25GammaCorrectionAt a) :
    SuzukiEquation25RegularKernelCorrectionAt a := by
  intro ha v
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hside :=
    guinandWeilLiteratureGammaSide_suzukiProjectBase_eq_kernelPairing
      ha hsupport
  have hbase := suzukiFiniteKernelPairingComplex_gammaBaseKernel_eq
    ha hsupport
  have hgamma_v := hgamma ha v
  have hscalar := suzukiProjectCompleteScalar_eq_gammaBase_add_restoration
  have hmass := norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re v
  unfold suzukiFiniteKernelPairing at hside
  rw [suzukiFiniteKernelPairingComplex_gammaScrew_split v,
    Complex.add_re, hbase, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, ← hmass] at hside
  rw [hside] at hgamma_v
  linear_combination hgamma_v +
    ‖suzukiSmoothCoreToL2 v‖ ^ 2 * hscalar

/-- The evaluated scalar removes no analytic content: the original regular
Gamma correction is equivalent to the single scalar-free regular-kernel
pairing identity. -/
theorem suzukiEquation25GammaCorrectionAt_iff_regularKernelCorrection :
    SuzukiEquation25GammaCorrectionAt a ↔
      SuzukiEquation25RegularKernelCorrectionAt a :=
  ⟨suzukiEquation25RegularKernelCorrectionAt_of_gammaCorrection,
    suzukiEquation25GammaCorrectionAt_of_regularKernelCorrection⟩

end

end M100
end Experiments
end RiemannHypothesisProject
