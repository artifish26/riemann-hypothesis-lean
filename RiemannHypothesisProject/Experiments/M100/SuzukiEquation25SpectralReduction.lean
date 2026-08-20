import RiemannHypothesisProject.Experiments.M100.SuzukiProjectFormNormalization

/-!
# Spectral reduction of Suzuki's equation (2.5)

This module removes the already checked prime and singular-local components
from the remaining equation-(2.5) source identity.  The resulting proposition
is only the pole/Gamma spectral correction: it compares the literature
pole-plus-Gamma side with the logarithmic Fourier form, the visible scalar,
and the exact `r''` source remainder.

No source theorem is assumed here.  The equivalence below shows that this
spectral correction is exactly the remaining analytic content of equation
(2.5), after the unconditional singular/Fourier identity.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set SchwartzLineTestFunction
open scoped ComplexConjugate FourierTransform

/-- The positive exponential kernel `-r₀''` contributed by the two pole
evaluations after integration by parts. -/
def suzukiEquation25PolePhysicalKernel (t : Real) : Real :=
  Real.exp (t / 2) + Real.exp (-t / 2)

theorem continuous_suzukiEquation25PolePhysicalKernel :
    Continuous suzukiEquation25PolePhysicalKernel := by
  unfold suzukiEquation25PolePhysicalKernel
  fun_prop

/-- The remaining pole/Gamma spectral correction after the prime block and
the singular-local/Fourier identity have been removed from equation (2.5). -/
def SuzukiEquation25SpectralCorrectionAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v.1) +
        guinandWeilLiteratureGammaSide
          (fourierAutocorrelation (suzukiProjectBase v.1)) =
      suzukiSourceLogFourierForm v.1 +
        suzukiProjectCompleteScalar * ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
        suzukiL2BoundedOperatorDiagonal
          (suzukiRSecondSourceRemainderOperator a)
          (suzukiSmoothCoreToL2 v)

/-- The singular-local term is unconditionally the logarithmic Fourier form
on every positive-radius Suzuki smooth core. -/
theorem suzukiSingularLocalForm_eq_sourceLogFourierForm
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    suzukiSingularLocalForm a v.1 =
      suzukiSourceLogFourierForm v.1 :=
  suzukiSingularFourierIdentityAt_of_constantIdentity
    suzukiCosineIntegralConstantIdentity ha v

private theorem setIntegral_suzukiEquation25FiniteSquare_separable
    (a : Real) (f g : Real → Complex) :
    (∫ p in suzukiFiniteSquare a, f p.1 * g p.2) =
      (∫ x in Icc (-a) a, f x) *
        ∫ y in Icc (-a) a, g y := by
  simpa [suzukiFiniteSquare, MeasureTheory.Measure.volume_eq_prod] using
    (MeasureTheory.setIntegral_prod_mul f g
      (Icc (-a) a) (Icc (-a) a))

/-- Double integration by parts for the elementary pole kernel: the pole
screw pairing on `v'` is the finite-square pairing of `-r₀''` on `v`. -/
theorem suzukiFiniteKernelPairingComplex_pole_deriv_eq_physical
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    suzukiFiniteKernelPairingComplex suzukiPoleScrewKernel a
        (SchwartzMap.derivCLM Complex Complex v.1) =
      suzukiFiniteKernelPairingComplex
        suzukiEquation25PolePhysicalKernel a v.1 := by
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  rw [suzukiFiniteKernelPairingComplex_pole_eq_weightedProducts
    ha hsupport]
  let plusTerm : Real × Real → Complex := fun p =>
    ((Real.exp ((1 / 2 : Real) * p.1) : Complex) * conj (v.1 p.1)) *
      ((Real.exp (-(1 / 2 : Real) * p.2) : Complex) * v.1 p.2)
  let minusTerm : Real × Real → Complex := fun p =>
    ((Real.exp (-(1 / 2 : Real) * p.1) : Complex) * conj (v.1 p.1)) *
      ((Real.exp ((1 / 2 : Real) * p.2) : Complex) * v.1 p.2)
  have hplus : IntegrableOn plusTerm (suzukiFiniteSquare a) :=
    (by fun_prop : Continuous plusTerm).continuousOn.integrableOn_compact
      (isCompact_suzukiFiniteSquare a)
  have hminus : IntegrableOn minusTerm (suzukiFiniteSquare a) :=
    (by fun_prop : Continuous minusTerm).continuousOn.integrableOn_compact
      (isCompact_suzukiFiniteSquare a)
  have hexpand :
      suzukiKernelPairingIntegrand
          suzukiEquation25PolePhysicalKernel v.1 =
        fun p => plusTerm p + minusTerm p := by
    funext p
    have hexpPlus :
        Real.exp ((p.1 - p.2) / 2) =
          Real.exp ((1 / 2 : Real) * p.1) *
            Real.exp (-(1 / 2 : Real) * p.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpMinus :
        Real.exp (-(p.1 - p.2) / 2) =
          Real.exp (-(1 / 2 : Real) * p.1) *
            Real.exp ((1 / 2 : Real) * p.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [suzukiKernelPairingIntegrand,
      suzukiEquation25PolePhysicalKernel, plusTerm, minusTerm,
      hexpPlus, hexpMinus]
    push_cast
    ring
  have hconj (c : Real) :
      (∫ x in Icc (-a) a,
          (Real.exp (c * x) : Complex) * conj (v.1 x)) =
        conj (∫ x in Icc (-a) a,
          (Real.exp (c * x) : Complex) * v.1 x) := by
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    change
      (Real.exp (c * x) : Complex) * conj (v.1 x) =
        conj ((Real.exp (c * x) : Complex) * v.1 x)
    rw [map_mul, Complex.conj_ofReal]
  rw [suzukiFiniteKernelPairingComplex, hexpand]
  rw [integral_add hplus hminus]
  rw [show (∫ p in suzukiFiniteSquare a, plusTerm p) =
      (∫ x in Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * conj (v.1 x)) *
        ∫ y in Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * y) : Complex) * v.1 y by
        simpa only [plusTerm] using
          setIntegral_suzukiEquation25FiniteSquare_separable a
            (fun x =>
              (Real.exp ((1 / 2 : Real) * x) : Complex) * conj (v.1 x))
            (fun y =>
              (Real.exp (-(1 / 2 : Real) * y) : Complex) * v.1 y),
    show (∫ p in suzukiFiniteSquare a, minusTerm p) =
      (∫ x in Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * conj (v.1 x)) *
        ∫ y in Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * y) : Complex) * v.1 y by
        simpa only [minusTerm] using
          setIntegral_suzukiEquation25FiniteSquare_separable a
            (fun x =>
              (Real.exp (-(1 / 2 : Real) * x) : Complex) * conj (v.1 x))
            (fun y =>
              (Real.exp ((1 / 2 : Real) * y) : Complex) * v.1 y),
    hconj (1 / 2 : Real), hconj (-(1 / 2 : Real))]
  ring

/-- The literature pole side is therefore exactly the real finite-square
pairing of the physical pole kernel on the undifferentiated source. -/
theorem guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase_eq_physical
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v.1) =
      (suzukiFiniteKernelPairingComplex
        suzukiEquation25PolePhysicalKernel a v.1).re := by
  rw [guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase_eq_kernelPairing
    ha (by
      intro x hx
      exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)]
  exact congrArg Complex.re
    (suzukiFiniteKernelPairingComplex_pole_deriv_eq_physical ha v)

/-- The source `r''` remainder splits into the positive physical pole kernel
and the negative regular Gamma kernel. -/
theorem suzukiRSecondSourceRemainderDiagonal_eq_pole_sub_r1
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiL2BoundedOperatorDiagonal
        (suzukiRSecondSourceRemainderOperator a)
        (suzukiSmoothCoreToL2 v) =
      (suzukiFiniteKernelPairingComplex
        suzukiEquation25PolePhysicalKernel a v.1).re -
        (suzukiFiniteKernelPairingComplex
          suzukiR1SecondKernel a v.1).re := by
  rw [suzukiRSecondSourceRemainderDiagonal_smoothCore]
  have hkernel : suzukiRSecondKernel = fun t =>
      (-1 : Real) * suzukiEquation25PolePhysicalKernel t +
        suzukiR1SecondKernel t := by
    funext t
    unfold suzukiRSecondKernel suzukiEquation25PolePhysicalKernel
    ring
  rw [hkernel]
  have hadd :
      suzukiFiniteKernelPairingComplex
          (fun t => (-1 : Real) * suzukiEquation25PolePhysicalKernel t +
            suzukiR1SecondKernel t) a v.1 =
        suzukiFiniteKernelPairingComplex
            (fun t => (-1 : Real) * suzukiEquation25PolePhysicalKernel t)
            a v.1 +
          suzukiFiniteKernelPairingComplex suzukiR1SecondKernel a v.1 :=
    suzukiFiniteKernelPairingComplex_add
      (continuous_const.mul continuous_suzukiEquation25PolePhysicalKernel)
      continuous_suzukiR1SecondKernel v.1.continuous
  rw [hadd, suzukiFiniteKernelPairingComplex_const_mul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, neg_mul, one_mul, zero_mul, sub_zero]
  ring

/-- The final regular-Gamma correction after both the prime and pole blocks,
and the singular-local identity, have been discharged. -/
def SuzukiEquation25GammaCorrectionAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    guinandWeilLiteratureGammaSide
        (fourierAutocorrelation (suzukiProjectBase v.1)) =
      suzukiSourceLogFourierForm v.1 +
        suzukiProjectCompleteScalar * ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
        (suzukiFiniteKernelPairingComplex
          suzukiR1SecondKernel a v.1).re

/-- The regular-Gamma correction implies the combined pole/Gamma correction;
the pole term itself is already an unconditional integration-by-parts
identity. -/
theorem suzukiEquation25SpectralCorrectionAt_of_gammaCorrection
    {a : Real} (hgamma : SuzukiEquation25GammaCorrectionAt a) :
    SuzukiEquation25SpectralCorrectionAt a := by
  intro ha v
  have hpole :=
    guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase_eq_physical ha v
  have hremainder :=
    suzukiRSecondSourceRemainderDiagonal_eq_pole_sub_r1 v
  have hgamma_v := hgamma ha v
  rw [hpole, hgamma_v, hremainder]
  ring

/-- Conversely, cancelling the checked physical pole term from the combined
correction leaves exactly the regular-Gamma identity. -/
theorem suzukiEquation25GammaCorrectionAt_of_spectralCorrection
    {a : Real} (hcorrection : SuzukiEquation25SpectralCorrectionAt a) :
    SuzukiEquation25GammaCorrectionAt a := by
  intro ha v
  have hpole :=
    guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase_eq_physical ha v
  have hremainder :=
    suzukiRSecondSourceRemainderDiagonal_eq_pole_sub_r1 v
  have hcorrection_v := hcorrection ha v
  rw [hpole, hremainder] at hcorrection_v
  linear_combination hcorrection_v

/-- The pole/Gamma correction, together with the already checked prime and
singular components, gives the complete project normalization. -/
theorem suzukiProjectCompleteFormNormalizationAt_of_spectralCorrection
    {a : Real} (hcorrection : SuzukiEquation25SpectralCorrectionAt a) :
    SuzukiProjectCompleteFormNormalizationAt a := by
  intro ha v
  have hprime :=
    guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_translation ha v
  have hcorrection_v := hcorrection ha v
  have hsingular :=
    suzukiSingularLocalForm_eq_sourceLogFourierForm ha v
  rw [suzukiProjectNormalizedCompleteCoreForm_eq_groupedComponents]
  unfold guinandWeilBurnolLiteratureResidualSide
  rw [hprime]
  linear_combination hcorrection_v - hsingular

/-- Conversely, complete project normalization contains no additional
analytic content after the prime and singular components are cancelled. -/
theorem suzukiEquation25SpectralCorrectionAt_of_projectNormalization
    {a : Real} (hproject : SuzukiProjectCompleteFormNormalizationAt a) :
    SuzukiEquation25SpectralCorrectionAt a := by
  intro ha v
  have hproject_v := hproject ha v
  have hprime :=
    guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_translation ha v
  have hcomplete :=
    suzukiProjectNormalizedCompleteCoreForm_eq_groupedComponents v
  have hsingular :=
    suzukiSingularLocalForm_eq_sourceLogFourierForm ha v
  unfold guinandWeilBurnolLiteratureResidualSide at hproject_v
  rw [hprime, hcomplete, hsingular] at hproject_v
  linear_combination hproject_v

/-- The narrowed pole/Gamma spectral correction is logically equivalent to
Suzuki's full equation-(2.5) source identity. -/
theorem suzukiEquation25SourceIdentityAt_iff_spectralCorrection
    (a : Real) :
    SuzukiEquation25SourceIdentityAt a ↔
      SuzukiEquation25SpectralCorrectionAt a := by
  constructor
  · intro hsource
    exact suzukiEquation25SpectralCorrectionAt_of_projectNormalization
      (suzukiProjectCompleteFormNormalizationAt_of_screwIdentity hsource)
  · intro hcorrection
    exact suzukiScrewCompleteFormIdentityAt_of_projectNormalization
      (suzukiProjectCompleteFormNormalizationAt_of_spectralCorrection
        hcorrection)

/-- Final reducer: equation (2.5) is equivalent to the regular-Gamma
correction alone.  Prime support, pole integration by parts, and the singular
Fourier identity no longer occur in the open proposition. -/
theorem suzukiEquation25SourceIdentityAt_iff_gammaCorrection
    (a : Real) :
    SuzukiEquation25SourceIdentityAt a ↔
      SuzukiEquation25GammaCorrectionAt a := by
  rw [suzukiEquation25SourceIdentityAt_iff_spectralCorrection]
  constructor
  · exact suzukiEquation25GammaCorrectionAt_of_spectralCorrection
  · exact suzukiEquation25SpectralCorrectionAt_of_gammaCorrection

end

end M100
end Experiments
end RiemannHypothesisProject
