import RiemannHypothesisProject.Experiments.M100.SuzukiFiniteIntervalL2Operator
import RiemannHypothesisProject.Experiments.M100.SuzukiScalarKernelBridge
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# M100-DF6F zero-mean source-operator bridge

This module supplies the closed zero-mean finite-interval `L²` space used by
Suzuki's source operators.  It then compresses the already checked screw-kernel
operator to that space and identifies its pairing on the continuous zero-mean
core.  No inverse, positivity, or form/operator representation theorem is
asserted here.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiSourceFiniteIntervalIsFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

/-- The interval mean as a bounded complex-linear functional on finite-interval
`L²`. -/
def suzukiFiniteIntervalMeanCLM (a : Real) :
    SuzukiFiniteIntervalL2 a →L[Complex] Complex :=
  innerSL Complex (suzukiFiniteIntervalOneComplexL2 a)

@[simp]
theorem suzukiFiniteIntervalMeanCLM_apply
    (a : Real) (v : SuzukiFiniteIntervalL2 a) :
    suzukiFiniteIntervalMeanCLM a v =
      inner Complex (suzukiFiniteIntervalOneComplexL2 a) v :=
  rfl

/-- On the continuous core, the Hilbert-space mean is the ordinary interval
integral. -/
theorem suzukiFiniteIntervalMeanCLM_continuous
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalMeanCLM a
        (suzukiFiniteIntervalContinuousToL2 a u) =
      ∫ x : SuzukiFiniteInterval a, u x ∂volume := by
  rw [suzukiFiniteIntervalMeanCLM_apply,
    suzukiFiniteIntervalOneComplexL2,
    suzukiFiniteIntervalContinuousToL2,
    ContinuousMap.inner_toLp]
  apply integral_congr_ae
  filter_upwards with x
  simp

/-- Suzuki's closed zero-mean subspace on `[-a,a]`. -/
def SuzukiFiniteIntervalZeroMeanSubspace (a : Real) :
    Submodule Complex (SuzukiFiniteIntervalL2 a) :=
  (suzukiFiniteIntervalMeanCLM a).ker

/-- Suzuki's finite-interval zero-mean Hilbert space. -/
abbrev SuzukiFiniteIntervalZeroMeanL2 (a : Real) : Type :=
  SuzukiFiniteIntervalZeroMeanSubspace a

local instance suzukiFiniteIntervalZeroMeanCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

theorem mem_suzukiFiniteIntervalZeroMeanSubspace
    (a : Real) (v : SuzukiFiniteIntervalL2 a) :
    v ∈ SuzukiFiniteIntervalZeroMeanSubspace a ↔
      suzukiFiniteIntervalMeanCLM a v = 0 :=
  Iff.rfl

/-- A continuous interval function with zero integral enters the closed source
space. -/
def suzukiFiniteIntervalContinuousZeroMeanToL2
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex))
    (hu : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0) :
    SuzukiFiniteIntervalZeroMeanL2 a :=
  ⟨suzukiFiniteIntervalContinuousToL2 a u, by
    change suzukiFiniteIntervalMeanCLM a
      (suzukiFiniteIntervalContinuousToL2 a u) = 0
    rwa [suzukiFiniteIntervalMeanCLM_continuous]⟩

@[simp]
theorem suzukiFiniteIntervalContinuousZeroMeanToL2_coe
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex))
    (hu : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0) :
    (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hu :
      SuzukiFiniteIntervalL2 a) =
      suzukiFiniteIntervalContinuousToL2 a u :=
  rfl

/-- Orthogonal projection from the ambient interval `L²` space onto Suzuki's
zero-mean source space. -/
def suzukiFiniteIntervalZeroMeanProjection (a : Real) :
    SuzukiFiniteIntervalL2 a →L[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  (SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto

/-- Continuous interval functions mapped into the closed zero-mean source
space by orthogonal projection. -/
def suzukiFiniteIntervalContinuousToZeroMeanL2 (a : Real) :
    C(SuzukiFiniteInterval a, Complex) →L[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  (suzukiFiniteIntervalZeroMeanProjection a).comp
    (suzukiFiniteIntervalContinuousToL2 a)

theorem surjective_suzukiFiniteIntervalZeroMeanProjection (a : Real) :
    Function.Surjective (suzukiFiniteIntervalZeroMeanProjection a) := by
  intro v
  refine ⟨(v : SuzukiFiniteIntervalL2 a), ?_⟩
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v

/-- The projected continuous core is dense in Suzuki's closed zero-mean
finite-interval space. -/
theorem denseRange_suzukiFiniteIntervalContinuousToZeroMeanL2 (a : Real) :
    DenseRange (suzukiFiniteIntervalContinuousToZeroMeanL2 a) := by
  change DenseRange (fun u : C(SuzukiFiniteInterval a, Complex) =>
    suzukiFiniteIntervalZeroMeanProjection a
      (suzukiFiniteIntervalContinuousToL2 a u))
  exact (surjective_suzukiFiniteIntervalZeroMeanProjection a).denseRange.comp
    (denseRange_suzukiFiniteIntervalContinuousToL2 a)
    (suzukiFiniteIntervalZeroMeanProjection a).continuous

/-- Compression of an ambient interval operator to the zero-mean source
space.  Projection on output is necessary because a generic kernel operator
need not preserve zero mean. -/
def suzukiFiniteIntervalZeroMeanCompression
    (a : Real)
    (T : SuzukiFiniteIntervalL2 a →L[Complex]
      SuzukiFiniteIntervalL2 a) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  (suzukiFiniteIntervalZeroMeanProjection a).comp
    (T.comp (Submodule.subtypeL
      (SuzukiFiniteIntervalZeroMeanSubspace a)))

/-- Compression does not change pairings against zero-mean test vectors. -/
theorem inner_suzukiFiniteIntervalZeroMeanCompression
    (a : Real)
    (T : SuzukiFiniteIntervalL2 a →L[Complex]
      SuzukiFiniteIntervalL2 a)
    (u v : SuzukiFiniteIntervalZeroMeanL2 a) :
    inner Complex
        (suzukiFiniteIntervalZeroMeanCompression a T u) v =
      inner Complex (T (u : SuzukiFiniteIntervalL2 a))
        (v : SuzukiFiniteIntervalL2 a) := by
  change inner Complex
      ((SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
        (T (u : SuzukiFiniteIntervalL2 a))) v =
    inner Complex (T (u : SuzukiFiniteIntervalL2 a))
      (v : SuzukiFiniteIntervalL2 a)
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right v
    (T (u : SuzukiFiniteIntervalL2 a))

/-- Compressing a self-adjoint ambient operator to the closed zero-mean
subspace preserves self-adjointness. -/
theorem suzukiFiniteIntervalZeroMeanCompression_isSelfAdjoint
    (a : Real)
    (T : SuzukiFiniteIntervalL2 a →L[Complex]
      SuzukiFiniteIntervalL2 a)
    (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (suzukiFiniteIntervalZeroMeanCompression a T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  calc
    inner Complex (suzukiFiniteIntervalZeroMeanCompression a T u) v =
        inner Complex (T (u : SuzukiFiniteIntervalL2 a))
          (v : SuzukiFiniteIntervalL2 a) :=
      inner_suzukiFiniteIntervalZeroMeanCompression a T u v
    _ = inner Complex (u : SuzukiFiniteIntervalL2 a)
          (T (v : SuzukiFiniteIntervalL2 a)) :=
      hT.isSymmetric
        (u : SuzukiFiniteIntervalL2 a) (v : SuzukiFiniteIntervalL2 a)
    _ = conj (inner Complex
          (T (v : SuzukiFiniteIntervalL2 a))
          (u : SuzukiFiniteIntervalL2 a)) :=
      (inner_conj_symm (u : SuzukiFiniteIntervalL2 a)
        (T (v : SuzukiFiniteIntervalL2 a))).symm
    _ = conj (inner Complex
          (suzukiFiniteIntervalZeroMeanCompression a T v) u) := by
      rw [inner_suzukiFiniteIntervalZeroMeanCompression]
    _ = inner Complex u
          (suzukiFiniteIntervalZeroMeanCompression a T v) :=
      inner_conj_symm u
        (suzukiFiniteIntervalZeroMeanCompression a T v)

/-- Suzuki's `G_a`: the exact screw-kernel operator compressed to the
zero-mean finite-interval source space. -/
def suzukiSourceGOperator (a : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalZeroMeanCompression a
    (suzukiFiniteIntervalL2Operator suzukiScrewFunction
      continuous_suzukiScrewFunction a)

theorem suzukiSourceGOperator_isSelfAdjoint (a : Real) :
    IsSelfAdjoint (suzukiSourceGOperator a) := by
  exact suzukiFiniteIntervalZeroMeanCompression_isSelfAdjoint a _
    (suzukiFiniteIntervalL2Operator_isSelfAdjoint_of_even
      continuous_suzukiScrewFunction suzukiScrewFunction_neg a)

/-- On continuous zero-mean sources, the compressed `G_a` pairing is exactly
the checked finite screw-kernel pairing. -/
theorem inner_suzukiSourceGOperator_continuous
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex))
    (hu : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0)
    (hv : (∫ x : SuzukiFiniteInterval a, v x ∂volume) = 0) :
    inner Complex
        (suzukiSourceGOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hu))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a v hv) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiScrewFunction continuous_suzukiScrewFunction a u v) := by
  rw [suzukiSourceGOperator,
    inner_suzukiFiniteIntervalZeroMeanCompression]
  exact inner_suzukiFiniteIntervalL2Operator_continuous
    suzukiScrewFunction continuous_suzukiScrewFunction a u v

/-- The continuous kernel of Suzuki's inverse Neumann Laplacian
`K_a = (-Δ_N)⁻¹`, with the source normalization from Section 8.2. -/
def suzukiNeumannInverseKernel (a x y : Real) : Real :=
  (x ^ 2 + y ^ 2) / (4 * a) - |x - y| / 2 + a / 6

/-- The translation part of the inverse-Neumann kernel.  The remaining terms
are separable and disappear after zero-mean compression. -/
def suzukiNeumannTranslationKernel (t : Real) : Real :=
  -|t| / 2

theorem continuous_suzukiNeumannTranslationKernel :
    Continuous suzukiNeumannTranslationKernel := by
  unfold suzukiNeumannTranslationKernel
  fun_prop

theorem suzukiNeumannTranslationKernel_neg (t : Real) :
    suzukiNeumannTranslationKernel (-t) =
      suzukiNeumannTranslationKernel t := by
  simp [suzukiNeumannTranslationKernel]

/-- Exact decomposition of the source Neumann kernel into its translation and
separable parts. -/
theorem suzukiNeumannInverseKernel_decomposition
    (a x y : Real) :
    suzukiNeumannInverseKernel a x y =
      suzukiNeumannTranslationKernel (x - y) +
        x ^ 2 / (4 * a) + y ^ 2 / (4 * a) + a / 6 := by
  unfold suzukiNeumannInverseKernel suzukiNeumannTranslationKernel
  ring

/-- The full source-oriented pairing for the inverse-Neumann kernel. -/
def suzukiFiniteIntervalNeumannPairingComplex
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex)) : Complex :=
  ∫ x : SuzukiFiniteInterval a,
    (∫ y : SuzukiFiniteInterval a,
      (suzukiNeumannInverseKernel a x.1 y.1 : Complex) * u y ∂volume) *
      conj (v x) ∂volume

/-- On a zero-mean input, the full Neumann action is its translation action
plus a constant function.  The latter disappears when paired with a
zero-mean output. -/
theorem integral_suzukiNeumannInverseKernel_mul_eq
    {a : Real} (u : C(SuzukiFiniteInterval a, Complex))
    (hu : (∫ y : SuzukiFiniteInterval a, u y ∂volume) = 0)
    (x : SuzukiFiniteInterval a) :
    (∫ y : SuzukiFiniteInterval a,
        (suzukiNeumannInverseKernel a x.1 y.1 : Complex) * u y ∂volume) =
      (∫ y : SuzukiFiniteInterval a,
        (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) *
          u y ∂volume) +
      ∫ y : SuzukiFiniteInterval a,
        ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume := by
  have htranslation : Integrable (fun y : SuzukiFiniteInterval a =>
      (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y) := by
    rw [← integrableOn_univ]
    have hcont : Continuous (fun y : SuzukiFiniteInterval a =>
        (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y) := by
      simpa [suzukiNeumannTranslationKernel] using
        (show Continuous (fun y : SuzukiFiniteInterval a =>
          ((-|x.1 - y.1| / 2 : Real) : Complex) * u y) by fun_prop)
    exact hcont.continuousOn.integrableOn_compact isCompact_univ
  have hxpart : Integrable (fun y : SuzukiFiniteInterval a =>
      ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y) := by
    rw [← integrableOn_univ]
    exact (by fun_prop : Continuous (fun y : SuzukiFiniteInterval a =>
      ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y)).continuousOn
        |>.integrableOn_compact isCompact_univ
  have hypart : Integrable (fun y : SuzukiFiniteInterval a =>
      ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y) := by
    rw [← integrableOn_univ]
    exact (by fun_prop : Continuous (fun y : SuzukiFiniteInterval a =>
      ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y)).continuousOn
        |>.integrableOn_compact isCompact_univ
  have haconst : Integrable (fun y : SuzukiFiniteInterval a =>
      ((a / 6 : Real) : Complex) * u y) := by
    rw [← integrableOn_univ]
    exact (by fun_prop : Continuous (fun y : SuzukiFiniteInterval a =>
      ((a / 6 : Real) : Complex) * u y)).continuousOn
        |>.integrableOn_compact isCompact_univ
  calc
    (∫ y : SuzukiFiniteInterval a,
        (suzukiNeumannInverseKernel a x.1 y.1 : Complex) * u y ∂volume) =
        ∫ y : SuzukiFiniteInterval a,
          ((suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
            ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y +
            ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y +
            ((a / 6 : Real) : Complex) * u y) ∂volume := by
      apply integral_congr_ae
      filter_upwards with y
      rw [suzukiNeumannInverseKernel_decomposition]
      push_cast
      ring
    _ = (∫ y : SuzukiFiniteInterval a,
          (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y ∂volume) +
        (∫ y : SuzukiFiniteInterval a,
          ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
        (∫ y : SuzukiFiniteInterval a,
          ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
        ∫ y : SuzukiFiniteInterval a,
          ((a / 6 : Real) : Complex) * u y ∂volume := by
      calc
        (∫ y : SuzukiFiniteInterval a,
            ((suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
              ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y +
              ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y) +
              ((a / 6 : Real) : Complex) * u y ∂volume) =
            (∫ y : SuzukiFiniteInterval a,
              (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
                ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y +
                ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
              ∫ y : SuzukiFiniteInterval a,
                ((a / 6 : Real) : Complex) * u y ∂volume := by
          simpa only [Pi.add_apply] using
            integral_add ((htranslation.add hxpart).add hypart) haconst
        _ = ((∫ y : SuzukiFiniteInterval a,
              (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
                ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
              ∫ y : SuzukiFiniteInterval a,
                ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
              ∫ y : SuzukiFiniteInterval a,
                ((a / 6 : Real) : Complex) * u y ∂volume := by
          rw [show (∫ y : SuzukiFiniteInterval a,
              (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
                ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y +
                ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) =
              (∫ y : SuzukiFiniteInterval a,
                (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
                  ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
                ∫ y : SuzukiFiniteInterval a,
                  ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume by
            simpa only [Pi.add_apply] using
              integral_add (htranslation.add hxpart) hypart]
        _ = ((∫ y : SuzukiFiniteInterval a,
              (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y ∂volume) +
              (∫ y : SuzukiFiniteInterval a,
                ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
              ∫ y : SuzukiFiniteInterval a,
                ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) +
              ∫ y : SuzukiFiniteInterval a,
                ((a / 6 : Real) : Complex) * u y ∂volume := by
          rw [show (∫ y : SuzukiFiniteInterval a,
              (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y +
                ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume) =
              (∫ y : SuzukiFiniteInterval a,
                (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y ∂volume) +
                ∫ y : SuzukiFiniteInterval a,
                  ((x.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume by
            simpa only [Pi.add_apply] using integral_add htranslation hxpart]
    _ = (∫ y : SuzukiFiniteInterval a,
          (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) * u y ∂volume) +
        ∫ y : SuzukiFiniteInterval a,
          ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume := by
      rw [integral_const_mul, integral_const_mul, hu]
      simp

/-- The full inverse-Neumann pairing equals the translation-kernel pairing on
the continuous zero-mean source core. -/
theorem suzukiFiniteIntervalNeumannPairingComplex_eq_translation
    {a : Real} (u v : C(SuzukiFiniteInterval a, Complex))
    (hu : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0)
    (hv : (∫ x : SuzukiFiniteInterval a, v x ∂volume) = 0) :
    suzukiFiniteIntervalNeumannPairingComplex a u v =
      suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiNeumannTranslationKernel
        continuous_suzukiNeumannTranslationKernel a u v := by
  have hvconj :
      (∫ x : SuzukiFiniteInterval a, conj (v x) ∂volume) = 0 := by
    rw [integral_conj, hv]
    simp
  let c : Complex :=
    ∫ y : SuzukiFiniteInterval a,
      ((y.1 ^ 2 / (4 * a) : Real) : Complex) * u y ∂volume
  unfold suzukiFiniteIntervalNeumannPairingComplex
  unfold suzukiFiniteIntervalContinuousOperatorPairingComplex
  calc
    (∫ x : SuzukiFiniteInterval a,
        (∫ y : SuzukiFiniteInterval a,
          (suzukiNeumannInverseKernel a x.1 y.1 : Complex) * u y ∂volume) *
          conj (v x) ∂volume) =
        ∫ x : SuzukiFiniteInterval a,
          ((∫ y : SuzukiFiniteInterval a,
            (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) *
              u y ∂volume) * conj (v x) + c * conj (v x)) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_suzukiNeumannInverseKernel_mul_eq u hu x]
      dsimp only [c]
      ring
    _ = (∫ x : SuzukiFiniteInterval a,
          (∫ y : SuzukiFiniteInterval a,
            (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) *
              u y ∂volume) * conj (v x) ∂volume) +
        ∫ x : SuzukiFiniteInterval a, c * conj (v x) ∂volume := by
      rw [integral_add]
      · change Integrable (fun x : SuzukiFiniteInterval a =>
          suzukiFiniteIntervalContinuousOperatorCLM
              suzukiNeumannTranslationKernel
              continuous_suzukiNeumannTranslationKernel a u x * conj (v x))
        rw [← integrableOn_univ]
        exact (by fun_prop : Continuous (fun x : SuzukiFiniteInterval a =>
          suzukiFiniteIntervalContinuousOperatorCLM
              suzukiNeumannTranslationKernel
              continuous_suzukiNeumannTranslationKernel a u x *
            conj (v x))).continuousOn.integrableOn_compact isCompact_univ
      · rw [← integrableOn_univ]
        exact (by fun_prop : Continuous (fun x : SuzukiFiniteInterval a =>
          c * conj (v x))).continuousOn.integrableOn_compact isCompact_univ
    _ = (∫ x : SuzukiFiniteInterval a,
          (∫ y : SuzukiFiniteInterval a,
            (suzukiNeumannTranslationKernel (x.1 - y.1) : Complex) *
              u y ∂volume) * conj (v x) ∂volume) := by
      rw [integral_const_mul, hvconj]
      simp

/-- Suzuki's `K_a`, realized as the zero-mean compression of the translation
part of the inverse-Neumann kernel.  The preceding theorem checks equivalence
with the full source kernel on the continuous zero-mean core. -/
def suzukiSourceKOperator (a : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalZeroMeanCompression a
    (suzukiFiniteIntervalL2Operator suzukiNeumannTranslationKernel
      continuous_suzukiNeumannTranslationKernel a)

theorem suzukiSourceKOperator_isSelfAdjoint (a : Real) :
    IsSelfAdjoint (suzukiSourceKOperator a) := by
  exact suzukiFiniteIntervalZeroMeanCompression_isSelfAdjoint a _
    (suzukiFiniteIntervalL2Operator_isSelfAdjoint_of_even
      continuous_suzukiNeumannTranslationKernel
      suzukiNeumannTranslationKernel_neg a)

theorem inner_suzukiSourceKOperator_continuous
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex))
    (hu : (∫ x : SuzukiFiniteInterval a, u x ∂volume) = 0)
    (hv : (∫ x : SuzukiFiniteInterval a, v x ∂volume) = 0) :
    inner Complex
        (suzukiSourceKOperator a
          (suzukiFiniteIntervalContinuousZeroMeanToL2 a u hu))
        (suzukiFiniteIntervalContinuousZeroMeanToL2 a v hv) =
      conj (suzukiFiniteIntervalNeumannPairingComplex a u v) := by
  rw [suzukiSourceKOperator,
    inner_suzukiFiniteIntervalZeroMeanCompression]
  have h := inner_suzukiFiniteIntervalL2Operator_continuous
    suzukiNeumannTranslationKernel
    continuous_suzukiNeumannTranslationKernel a u v
  rw [← suzukiFiniteIntervalNeumannPairingComplex_eq_translation u v hu hv] at h
  simpa using h

/-- Suzuki's shifted compact source operator
`S_(a,λ) = G_a - λ K_a`. -/
def suzukiSourceShiftedOperator (a lambda : Real) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiSourceGOperator a -
    (lambda : Complex) • suzukiSourceKOperator a

theorem suzukiSourceShiftedOperator_isSelfAdjoint
    (a lambda : Real) :
    IsSelfAdjoint (suzukiSourceShiftedOperator a lambda) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  have hG := (suzukiSourceGOperator_isSelfAdjoint a).isSymmetric u v
  have hK := (suzukiSourceKOperator_isSelfAdjoint a).isSymmetric u v
  change inner Complex (suzukiSourceGOperator a u) v =
    inner Complex u (suzukiSourceGOperator a v) at hG
  change inner Complex (suzukiSourceKOperator a u) v =
    inner Complex u (suzukiSourceKOperator a v) at hK
  have hlambda :
      (starRingEnd Complex) (lambda : Complex) = (lambda : Complex) := by
    rw [starRingEnd_apply, RCLike.star_def, Complex.conj_ofReal]
  change inner Complex
      ((suzukiSourceGOperator a -
        (lambda : Complex) • suzukiSourceKOperator a) u) v =
    inner Complex u
      ((suzukiSourceGOperator a -
        (lambda : Complex) • suzukiSourceKOperator a) v)
  rw [sub_apply, smul_apply, sub_apply, smul_apply,
    inner_sub_left, inner_sub_right, hG,
    inner_smul_left, inner_smul_right, hlambda, hK]

/-- Diagonal form of the shifted source operator. -/
theorem re_inner_suzukiSourceShiftedOperator
    (a lambda : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re =
      (inner Complex (suzukiSourceGOperator a u) u).re -
        lambda * (inner Complex (suzukiSourceKOperator a u) u).re := by
  simp [suzukiSourceShiftedOperator, inner_sub_left]
  change
    (inner Complex
      ((lambda : Complex) •
        ((suzukiSourceKOperator a u : SuzukiFiniteIntervalZeroMeanL2 a) :
          SuzukiFiniteIntervalL2 a))
      (u : SuzukiFiniteIntervalL2 a)).re =
        lambda *
          (inner Complex
            ((suzukiSourceKOperator a u : SuzukiFiniteIntervalZeroMeanL2 a) :
              SuzukiFiniteIntervalL2 a)
            (u : SuzukiFiniteIntervalL2 a)).re
  rw [inner_smul_left]
  simp

end

end RiemannHypothesisProject.Experiments.M100
