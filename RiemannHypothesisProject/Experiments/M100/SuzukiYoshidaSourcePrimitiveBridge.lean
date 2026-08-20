import RiemannHypothesisProject.Experiments.M100.SuzukiProjectFormNormalization
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceOperatorBridge

/-!
# M100-DF6F source primitive bridge

This module identifies Suzuki's inverse-Neumann quadratic form on the smooth
source differential with the `L²` mass of its primitive.  It sits above both
the scalar-kernel calculation and the closed zero-mean operator construction,
so the lower operator module remains independent of project-form
normalization.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open SchwartzLineTestFunction
open scoped ENNReal InnerProductSpace ComplexConjugate Convolution

attribute [local instance] Measure.Subtype.measureSpace

/-- The smooth source differential, restricted to Suzuki's finite interval. -/
def suzukiSmoothCoreDifferentialFiniteIntervalContinuous
    {a : Real} (v : SuzukiSmoothCore a) :
    C(SuzukiFiniteInterval a, Complex) :=
  suzukiFiniteIntervalRestriction a (suzukiDifferential v.1)
    (suzukiDifferential v.1).continuous

/-- The restricted smooth differential has zero interval mean. -/
theorem integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    (∫ x : SuzukiFiniteInterval a,
      suzukiSmoothCoreDifferentialFiniteIntervalContinuous v x ∂volume) = 0 := by
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  rw [show (∫ x : SuzukiFiniteInterval a,
      suzukiSmoothCoreDifferentialFiniteIntervalContinuous v x ∂volume) =
        ∫ x in Icc (-a) a, suzukiDifferential v.1 x by
    exact MeasureTheory.integral_subtype measurableSet_Icc
      (fun x : Real => suzukiDifferential v.1 x)]
  exact setIntegral_suzukiDifferential_eq_zero ha hsupport

/-- The smooth differential bundled directly in the closed zero-mean source
space. -/
def suzukiSmoothCoreDifferentialZeroMeanL2
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalContinuousZeroMeanToL2 a
    (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
    (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
      ha v)

/-- The full inverse-Neumann pairing on `D v` is the zero-displacement source
autocorrelation.  The factor `i` in `D = i d/dx` cancels between the two
quadratic slots. -/
theorem suzukiFiniteIntervalNeumannPairingComplex_smoothCoreDifferential_eq
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    suzukiFiniteIntervalNeumannPairingComplex a
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v) =
      autocorrelation v.1 0 := by
  let u : C(SuzukiFiniteInterval a, Complex) :=
    suzukiSmoothCoreDifferentialFiniteIntervalContinuous v
  have hzero : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0 := by
    simpa only [u] using
      integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
        ha v
  have hsupport : Function.support v.1 ⊆ Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hkernel : suzukiNeumannTranslationKernel =
      fun t : Real => (-1 / 2 : Real) * |t| := by
    funext t
    unfold suzukiNeumannTranslationKernel
    ring
  calc
    suzukiFiniteIntervalNeumannPairingComplex a u u =
        suzukiFiniteIntervalContinuousOperatorPairingComplex
          suzukiNeumannTranslationKernel
          continuous_suzukiNeumannTranslationKernel a u u :=
      suzukiFiniteIntervalNeumannPairingComplex_eq_translation u u hzero hzero
    _ = suzukiFiniteIntervalCoreOperatorPairingComplex
          suzukiNeumannTranslationKernel a
          (suzukiDifferential v.1) (suzukiDifferential v.1) := by
      exact suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
        continuous_suzukiNeumannTranslationKernel
        (suzukiDifferential v.1).continuous
        (suzukiDifferential v.1).continuous
    _ = suzukiFiniteKernelPairingComplex suzukiNeumannTranslationKernel a
          (suzukiDifferential v.1) := by
      rw [suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
        continuous_suzukiNeumannTranslationKernel
        (suzukiDifferential v.1).continuous
        (suzukiDifferential v.1).continuous,
        suzukiFiniteKernelPolarizationComplex_self]
    _ = ((-1 / 2 : Real) : Complex) *
          suzukiFiniteKernelPairingComplex (fun t : Real => |t|) a
            (SchwartzMap.derivCLM Complex Complex v.1) := by
      rw [hkernel, suzukiFiniteKernelPairingComplex_const_mul,
        suzukiFiniteKernelPairingComplex_differential_eq_deriv]
    _ = autocorrelation v.1 0 := by
      rw [suzukiFiniteKernelPairingComplex_abs_eq_autocorrelation_zero
        ha hsupport]
      push_cast
      ring

/-- Zero-displacement autocorrelation is real. -/
theorem conj_autocorrelation_zero_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) :
    conj (autocorrelation v.1 0) = autocorrelation v.1 0 := by
  rw [autocorrelation_apply, MeasureTheory.convolution_def, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [star_apply]
  ring

/-- Suzuki's source-side primitive identity on the smooth core:
`⟨K_a Dv, Dv⟩ = ‖v‖²`. -/
theorem inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiSourceKOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a
            (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
            (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
              ha v)))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
          (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
            ha v)) =
      ((‖suzukiSmoothCoreToL2 v‖ ^ 2 : Real) : Complex) := by
  let u : C(SuzukiFiniteInterval a, Complex) :=
    suzukiSmoothCoreDifferentialFiniteIntervalContinuous v
  let hzero : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0 :=
    integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero ha v
  have hreal := conj_autocorrelation_zero_smoothCore v
  calc
    inner Complex
        (suzukiSourceKOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hzero))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hzero) =
        conj (suzukiFiniteIntervalNeumannPairingComplex a u u) :=
      inner_suzukiSourceKOperator_continuous a u u hzero hzero
    _ = conj (autocorrelation v.1 0) := by
      rw [suzukiFiniteIntervalNeumannPairingComplex_smoothCoreDifferential_eq
        ha v]
    _ = autocorrelation v.1 0 := hreal
    _ = ((autocorrelation v.1 0).re : Complex) :=
      (Complex.conj_eq_iff_re.mp hreal).symm
    _ = ((‖suzukiSmoothCoreToL2 v‖ ^ 2 : Real) : Complex) := by
      exact congrArg (fun r : Real => (r : Complex))
        (norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re v).symm

/-- Before using any source identity, the real diagonal of the compressed
`G_a` operator is exactly the checked finite screw-kernel form on `D v`. -/
theorem re_inner_suzukiSourceGOperator_smoothCoreDifferential_eq_pairing
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    (inner Complex
        (suzukiSourceGOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a
            (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
            (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
              ha v)))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
          (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
            ha v))).re =
      suzukiFiniteKernelPairing suzukiScrewFunction a
        (suzukiDifferential v.1) := by
  let u : C(SuzukiFiniteInterval a, Complex) :=
    suzukiSmoothCoreDifferentialFiniteIntervalContinuous v
  let hzero : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0 :=
    integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero ha v
  rw [inner_suzukiSourceGOperator_continuous a u u hzero hzero]
  simp only [Complex.conj_re]
  dsimp only [u, suzukiSmoothCoreDifferentialFiniteIntervalContinuous]
  rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
    continuous_suzukiScrewFunction
    (suzukiDifferential v.1).continuous
    (suzukiDifferential v.1).continuous,
    suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiScrewFunction
      (suzukiDifferential v.1).continuous
      (suzukiDifferential v.1).continuous,
    suzukiFiniteKernelPolarizationComplex_self]
  rfl

/-- The visible equation-(2.5) source premise identifies the compressed
`G_a` quadratic form on `D v` with the project-normalized complete core form.
This is the bounded source-form bridge; it does not assert the later
Friedrichs representation of `A_a`. -/
theorem inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completeForm
    {a : Real} (hsource : SuzukiEquation25SourceIdentityAt a)
    (ha : 0 < a) (v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiSourceGOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a
            (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
            (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
              ha v)))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
          (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
            ha v)) =
      (suzukiProjectNormalizedCompleteCoreForm v : Complex) := by
  let u : C(SuzukiFiniteInterval a, Complex) :=
    suzukiSmoothCoreDifferentialFiniteIntervalContinuous v
  let hzero : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0 :=
    integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero ha v
  let pairing : Complex :=
    suzukiFiniteIntervalContinuousOperatorPairingComplex
      suzukiScrewFunction continuous_suzukiScrewFunction a u u
  have hpairingRe : pairing.re =
      suzukiProjectNormalizedCompleteCoreForm v := by
    have hsourceV := hsource ha v
    change
      (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiScrewFunction continuous_suzukiScrewFunction a u u).re =
          suzukiProjectNormalizedCompleteCoreForm v
    dsimp only [u, suzukiSmoothCoreDifferentialFiniteIntervalContinuous]
    rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
      continuous_suzukiScrewFunction
      (suzukiDifferential v.1).continuous
      (suzukiDifferential v.1).continuous,
      suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
        continuous_suzukiScrewFunction
        (suzukiDifferential v.1).continuous
        (suzukiDifferential v.1).continuous,
      suzukiFiniteKernelPolarizationComplex_self]
    change suzukiFiniteKernelPairing suzukiScrewFunction a
      (suzukiDifferential v.1) =
        suzukiProjectNormalizedCompleteCoreForm v at hsourceV
    exact hsourceV
  have hpairingReal : conj pairing = pairing := by
    exact (suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm
      a u u).symm
  calc
    inner Complex
        (suzukiSourceGOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hzero))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hzero) =
        conj pairing :=
      inner_suzukiSourceGOperator_continuous a u u hzero hzero
    _ = pairing := hpairingReal
    _ = (pairing.re : Complex) :=
      (Complex.conj_eq_iff_re.mp hpairingReal).symm
    _ = (suzukiProjectNormalizedCompleteCoreForm v : Complex) := by
      exact congrArg (fun r : Real => (r : Complex)) hpairingRe

/-- Any project-form lower bound on the smooth source immediately becomes the
matching source-compatible comparison `G_a ≥ c K_a` on `D v`.  This theorem
isolates the last DF6F transport obligation from the already checked operator
normalizations. -/
theorem suzukiSource_core_coercive_of_projectCompleteForm
    {a c : Real} (hsource : SuzukiEquation25SourceIdentityAt a)
    (ha : 0 < a) (v : SuzukiSmoothCore a)
    (hcoercive :
      c * ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
        suzukiProjectNormalizedCompleteCoreForm v) :
    c * (inner Complex
        (suzukiSourceKOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a
            (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
            (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
              ha v)))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
          (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
            ha v))).re ≤
      (inner Complex
        (suzukiSourceGOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a
            (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
            (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
              ha v)))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
          (integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
            ha v))).re := by
  rw [inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq ha v,
    inner_suzukiSourceGOperator_smoothCoreDifferential_eq_completeForm
      hsource ha v]
  change c * ‖suzukiSmoothCoreToL2 v‖ ^ 2 ≤
    suzukiProjectNormalizedCompleteCoreForm v
  exact hcoercive

end

end RiemannHypothesisProject.Experiments.M100
