import RiemannHypothesisProject.Experiments.M100.SuzukiScalarKernelIdentity
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.ContinuousMap.Compact

/-!
# M100-X15 Suzuki finite-interval core operator

This experimental module introduces the smallest operator-facing consumer of
the checked X14 scalar identity.  It bundles the finite-interval action as a
bounded operator on continuous functions and connects its Hermitian pairing
to the continuous zero-mean core containing `D v` for a compactly supported
Schwartz source.  No `L2` extension, compactness, positivity, self-adjoint
extension, zero carrier, or spectral completeness statement is asserted here.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open MeasureTheory
open SchwartzLineTestFunction
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Measure.Subtype.measureSpace

/-- The compact interval used as the receiving space for the bounded X15
operator. -/
abbrev SuzukiFiniteInterval (a : Real) := Set.Icc (-a) a

local instance suzukiFiniteIntervalIsFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

/-- The translation kernel, restricted to the compact finite square and
bundled as a continuous map. -/
def suzukiFiniteIntervalKernelContinuousMap
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    C(SuzukiFiniteInterval a × SuzukiFiniteInterval a, Complex) where
  toFun p := (kernel (p.1.1 - p.2.1) : Complex)
  continuous_toFun := by fun_prop

/-- The finite-interval integral action on the Banach space of continuous
complex functions on `[-a,a]`.  This is a bounded continuous-core model, not
yet the full `L2` extension. -/
def suzukiFiniteIntervalContinuousOperator
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u : C(SuzukiFiniteInterval a, Complex)) :
    C(SuzukiFiniteInterval a, Complex) where
  toFun x := ∫ y : SuzukiFiniteInterval a,
    (kernel (x.1 - y.1) : Complex) * u y
  continuous_toFun := by
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (s := Set.univ) (hs := isCompact_univ)
        (by fun_prop : Continuous (Function.uncurry fun x y : SuzukiFiniteInterval a =>
          (kernel (x.1 - y.1) : Complex) * u y))

theorem integrable_suzukiFiniteIntervalContinuousOperator_integrand
    {kernel : Real -> Real} (hkernel : Continuous kernel) {a : Real}
    (u : C(SuzukiFiniteInterval a, Complex))
    (x : SuzukiFiniteInterval a) :
    Integrable (fun y : SuzukiFiniteInterval a =>
      (kernel (x.1 - y.1) : Complex) * u y) := by
  rw [← integrableOn_univ]
  exact (by fun_prop : Continuous (fun y : SuzukiFiniteInterval a =>
    (kernel (x.1 - y.1) : Complex) * u y)).continuousOn
      |>.integrableOn_compact isCompact_univ

/-- The finite-interval continuous operator as a complex-linear map. -/
def suzukiFiniteIntervalContinuousOperatorLinearMap
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    C(SuzukiFiniteInterval a, Complex) →ₗ[Complex]
      C(SuzukiFiniteInterval a, Complex) where
  toFun := suzukiFiniteIntervalContinuousOperator kernel hkernel a
  map_add' u v := by
    ext x
    change (∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * (u y + v y)) =
      (∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * u y) +
      ∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * v y
    simp only [mul_add]
    rw [integral_add
      (integrable_suzukiFiniteIntervalContinuousOperator_integrand hkernel u x)
      (integrable_suzukiFiniteIntervalContinuousOperator_integrand hkernel v x)]
  map_smul' c u := by
    ext x
    change (∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * (c * u y)) =
      c * ∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * u y
    rw [← integral_const_mul]
    congr 1
    funext y
    ring

/-- Sup-norm bound for the continuous finite-interval operator. -/
theorem norm_suzukiFiniteIntervalContinuousOperator_le
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u : C(SuzukiFiniteInterval a, Complex)) :
    ‖suzukiFiniteIntervalContinuousOperator kernel hkernel a u‖ ≤
      (‖suzukiFiniteIntervalKernelContinuousMap kernel hkernel a‖ *
          (volume : Measure (SuzukiFiniteInterval a)).real Set.univ) * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).2
  intro x
  change ‖∫ y : SuzukiFiniteInterval a,
    (kernel (x.1 - y.1) : Complex) * u y‖ ≤ _
  calc
    ‖∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * u y‖ ≤
        (‖suzukiFiniteIntervalKernelContinuousMap kernel hkernel a‖ * ‖u‖) *
          (volume : Measure (SuzukiFiniteInterval a)).real Set.univ := by
      apply norm_integral_le_of_norm_le_const
      filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul
        (ContinuousMap.norm_coe_le_norm
          (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) (x, y))
        (ContinuousMap.norm_coe_le_norm u y)
        (norm_nonneg _) (norm_nonneg _)
    _ = (‖suzukiFiniteIntervalKernelContinuousMap kernel hkernel a‖ *
          (volume : Measure (SuzukiFiniteInterval a)).real Set.univ) * ‖u‖ := by
      ring

/-- The finite-interval continuous operator bundled as a bounded operator. -/
def suzukiFiniteIntervalContinuousOperatorCLM
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    C(SuzukiFiniteInterval a, Complex) →L[Complex]
      C(SuzukiFiniteInterval a, Complex) :=
  (suzukiFiniteIntervalContinuousOperatorLinearMap kernel hkernel a).mkContinuous
    (‖suzukiFiniteIntervalKernelContinuousMap kernel hkernel a‖ *
      (volume : Measure (SuzukiFiniteInterval a)).real Set.univ)
    (norm_suzukiFiniteIntervalContinuousOperator_le kernel hkernel a)

theorem suzukiFiniteIntervalContinuousOperatorCLM_apply
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u =
      suzukiFiniteIntervalContinuousOperator kernel hkernel a u := rfl

/-- The operator norm is bounded by the sup norm of the restricted kernel
times the volume of the compact interval. -/
theorem norm_suzukiFiniteIntervalContinuousOperatorCLM_le
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    ‖suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a‖ ≤
      ‖suzukiFiniteIntervalKernelContinuousMap kernel hkernel a‖ *
        (volume : Measure (SuzukiFiniteInterval a)).real Set.univ := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity)
    (norm_suzukiFiniteIntervalContinuousOperator_le kernel hkernel a)

/-- Restrict a globally continuous source to the compact finite interval. -/
def suzukiFiniteIntervalRestriction
    (a : Real) (u : Real -> Complex) (hu : Continuous u) :
    C(SuzukiFiniteInterval a, Complex) where
  toFun x := u x.1
  continuous_toFun := hu.comp continuous_subtype_val

/-- The diagonal/polarized pairing associated with the bounded continuous
operator, in Suzuki's convention linear in the first argument. -/
def suzukiFiniteIntervalContinuousOperatorPairingComplex
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u v : C(SuzukiFiniteInterval a, Complex)) : Complex :=
  ∫ x : SuzukiFiniteInterval a,
    suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u x * conj (v x)

/-- The continuous zero-mean core on the finite interval `[-a,a]`.

This is the classical source domain needed by the X14 consumer.  It is not a
claim that the integral operator has already been extended to the full
zero-mean `L2` space. -/
def SuzukiFiniteIntervalCoreSource
    (a : Real) (u : Real -> Complex) : Prop :=
  Continuous u /\ (∫ x in Set.Icc (-a) a, u x) = 0

/-- The uncompressed finite-interval integral action associated with a real
translation kernel.  Compression to the zero-mean core is expressed by the
source predicate above and by the diagonal pairing below. -/
def suzukiFiniteIntervalCoreOperator
    (kernel : Real -> Real) (a : Real)
    (u : Real -> Complex) (x : Real) : Complex :=
  ∫ y in Set.Icc (-a) a,
    (kernel (x - y) : Complex) * u y

/-- On restrictions of global continuous sources, the bounded compact-domain
operator is exactly the original finite-interval set-integral action. -/
theorem suzukiFiniteIntervalContinuousOperatorCLM_restriction_apply
    {kernel : Real -> Real} (hkernel : Continuous kernel) {a : Real}
    {u : Real -> Complex} (hu : Continuous u)
    (x : SuzukiFiniteInterval a) :
    suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a
        (suzukiFiniteIntervalRestriction a u hu) x =
      suzukiFiniteIntervalCoreOperator kernel a u x.1 := by
  change (∫ y : SuzukiFiniteInterval a,
      (kernel (x.1 - y.1) : Complex) * u y.1) =
    ∫ y in Set.Icc (-a) a,
      (kernel (x.1 - y) : Complex) * u y
  exact MeasureTheory.integral_subtype measurableSet_Icc
    (fun y : Real => (kernel (x.1 - y) : Complex) * u y)

/-- The operator action is continuous for a continuous kernel and source. -/
theorem continuous_suzukiFiniteIntervalCoreOperator
    {kernel : Real -> Real} {a : Real} {u : Real -> Complex}
    (hkernel : Continuous kernel) (hu : Continuous u) :
    Continuous (suzukiFiniteIntervalCoreOperator kernel a u) := by
  apply continuous_parametric_integral_of_continuous
    (s := Set.Icc (-a) a) (hs := isCompact_Icc)
  fun_prop

/-- The polarized finite-square kernel integrand.  X14's scalar integrand is
the diagonal specialization `u = v`. -/
def suzukiKernelPolarizationIntegrand
    (kernel : Real -> Real) (u v : Real -> Complex)
    (p : Real × Real) : Complex :=
  (kernel (p.1 - p.2) : Complex) * u p.2 * conj (v p.1)

/-- The polarized finite-square kernel form. -/
def suzukiFiniteKernelPolarizationComplex
    (kernel : Real -> Real) (a : Real)
    (u v : Real -> Complex) : Complex :=
  ∫ p in suzukiFiniteSquare a,
    suzukiKernelPolarizationIntegrand kernel u v p

/-- The ordinary operator pairing, in Suzuki's convention linear in the
first argument. -/
def suzukiFiniteIntervalCoreOperatorPairingComplex
    (kernel : Real -> Real) (a : Real)
    (u v : Real -> Complex) : Complex :=
  ∫ x in Set.Icc (-a) a,
    suzukiFiniteIntervalCoreOperator kernel a u x * conj (v x)

/-- The bounded-operator pairing agrees with the earlier core pairing on
restrictions of global continuous sources. -/
theorem suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
    {kernel : Real -> Real} (hkernel : Continuous kernel) {a : Real}
    {u v : Real -> Complex} (hu : Continuous u) (hv : Continuous v) :
    suzukiFiniteIntervalContinuousOperatorPairingComplex kernel hkernel a
        (suzukiFiniteIntervalRestriction a u hu)
        (suzukiFiniteIntervalRestriction a v hv) =
      suzukiFiniteIntervalCoreOperatorPairingComplex kernel a u v := by
  unfold suzukiFiniteIntervalContinuousOperatorPairingComplex
  calc
    (∫ x : SuzukiFiniteInterval a,
        suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a
            (suzukiFiniteIntervalRestriction a u hu) x *
          conj ((suzukiFiniteIntervalRestriction a v hv) x)) =
        ∫ x : SuzukiFiniteInterval a,
          suzukiFiniteIntervalCoreOperator kernel a u x.1 * conj (v x.1) := by
      apply integral_congr_ae
      filter_upwards with x
      change
        suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a
              (suzukiFiniteIntervalRestriction a u hu) x * conj (v x.1) =
          suzukiFiniteIntervalCoreOperator kernel a u x.1 * conj (v x.1)
      rw [suzukiFiniteIntervalContinuousOperatorCLM_restriction_apply
        hkernel hu x]
    _ = ∫ x in Set.Icc (-a) a,
          suzukiFiniteIntervalCoreOperator kernel a u x * conj (v x) := by
      exact MeasureTheory.integral_subtype measurableSet_Icc
        (fun x : Real =>
          suzukiFiniteIntervalCoreOperator kernel a u x * conj (v x))
    _ = suzukiFiniteIntervalCoreOperatorPairingComplex kernel a u v := rfl

theorem continuous_suzukiKernelPolarizationIntegrand
    {kernel : Real -> Real} {u v : Real -> Complex}
    (hkernel : Continuous kernel) (hu : Continuous u)
    (hv : Continuous v) :
    Continuous (suzukiKernelPolarizationIntegrand kernel u v) := by
  unfold suzukiKernelPolarizationIntegrand
  fun_prop

theorem integrableOn_suzukiKernelPolarizationIntegrand
    {kernel : Real -> Real} {u v : Real -> Complex} {a : Real}
    (hkernel : Continuous kernel) (hu : Continuous u)
    (hv : Continuous v) :
    IntegrableOn (suzukiKernelPolarizationIntegrand kernel u v)
      (suzukiFiniteSquare a) := by
  exact
    (continuous_suzukiKernelPolarizationIntegrand hkernel hu hv).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)

/-- Fubini identifies the pointwise integral action with the finite-square
polarized form. -/
theorem suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
    {kernel : Real -> Real} {a : Real} {u v : Real -> Complex}
    (hkernel : Continuous kernel) (hu : Continuous u)
    (hv : Continuous v) :
    suzukiFiniteIntervalCoreOperatorPairingComplex kernel a u v =
      suzukiFiniteKernelPolarizationComplex kernel a u v := by
  have hintegrable :=
    integrableOn_suzukiKernelPolarizationIntegrand
      (a := a) hkernel hu hv
  rw [suzukiFiniteIntervalCoreOperatorPairingComplex,
    suzukiFiniteKernelPolarizationComplex, suzukiFiniteSquare,
    MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.setIntegral_prod
      (suzukiKernelPolarizationIntegrand kernel u v) hintegrable]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  change
    (∫ y in Set.Icc (-a) a, (kernel (x - y) : Complex) * u y) *
        conj (v x) =
      ∫ y in Set.Icc (-a) a,
        (kernel (x - y) : Complex) * u y * conj (v x)
  rw [← integral_mul_const]

/-- X14's complex scalar pairing is the diagonal polarization. -/
theorem suzukiFiniteKernelPolarizationComplex_self
    (kernel : Real -> Real) (a : Real) (u : Real -> Complex) :
    suzukiFiniteKernelPolarizationComplex kernel a u u =
      suzukiFiniteKernelPairingComplex kernel a u := by
  unfold suzukiFiniteKernelPolarizationComplex
    suzukiFiniteKernelPairingComplex
    suzukiKernelPolarizationIntegrand suzukiKernelPairingIntegrand
  rfl

/-- A real-even kernel gives a Hermitian finite-interval polarized form.  The
proof uses only conjugation and invariance of the square under coordinate
exchange; it does not use a sign assumption. -/
theorem suzukiFiniteKernelPolarizationComplex_conj_symm
    {kernel : Real -> Real} (heven : forall t, kernel (-t) = kernel t)
    (a : Real) (u v : Real -> Complex) :
    suzukiFiniteKernelPolarizationComplex kernel a u v =
      conj (suzukiFiniteKernelPolarizationComplex kernel a v u) := by
  rw [suzukiFiniteKernelPolarizationComplex,
    suzukiFiniteKernelPolarizationComplex, suzukiFiniteSquare,
    MeasureTheory.Measure.volume_eq_prod]
  calc
    (∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
        suzukiKernelPolarizationIntegrand kernel u v p) =
        ∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          conj (suzukiKernelPolarizationIntegrand kernel v u p.swap) := by
      apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      intro p _
      unfold suzukiKernelPolarizationIntegrand
      simp only [Prod.fst_swap, Prod.snd_swap]
      have harg : p.2 - p.1 = -(p.1 - p.2) := by ring
      rw [harg, heven]
      simp [Complex.conj_ofReal]
      ring
    _ = ∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          conj (suzukiKernelPolarizationIntegrand kernel v u p) := by
      exact MeasureTheory.setIntegral_prod_swap
        (Set.Icc (-a) a) (Set.Icc (-a) a)
        (fun p => conj (suzukiKernelPolarizationIntegrand kernel v u p))
    _ = conj (∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          suzukiKernelPolarizationIntegrand kernel v u p) := by
      exact integral_conj

/-- The explicit Suzuki screw kernel therefore gives a Hermitian operator
pairing on the continuous finite-interval core. -/
theorem suzukiFiniteIntervalCoreOperatorPairingComplex_conj_symm
    {a : Real} {u v : Real -> Complex}
    (hu : Continuous u) (hv : Continuous v) :
    suzukiFiniteIntervalCoreOperatorPairingComplex
        suzukiScrewFunction a u v =
      conj (suzukiFiniteIntervalCoreOperatorPairingComplex
        suzukiScrewFunction a v u) := by
  rw [suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiScrewFunction hu hv,
    suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiScrewFunction hv hu]
  exact suzukiFiniteKernelPolarizationComplex_conj_symm
    suzukiScrewFunction_neg a u v

/-- A real-even kernel gives a Hermitian pairing on the whole continuous
finite-interval Banach space.  Tietze extension reduces arbitrary interval
functions to the global continuous-core pairing. -/
theorem suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm_of_even
    {kernel : Real -> Real} (hkernel : Continuous kernel)
    (heven : forall t, kernel (-t) = kernel t)
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a u v =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a v u) := by
  obtain ⟨U, hU⟩ := ContinuousMap.exists_restrict_eq
    (s := Set.Icc (-a) a) isClosed_Icc u
  obtain ⟨V, hV⟩ := ContinuousMap.exists_restrict_eq
    (s := Set.Icc (-a) a) isClosed_Icc v
  have hU' :
      suzukiFiniteIntervalRestriction a U U.continuous = u := by
    ext x
    simpa [suzukiFiniteIntervalRestriction] using
      congrArg (fun f : C(SuzukiFiniteInterval a, Complex) => f x) hU
  have hV' :
      suzukiFiniteIntervalRestriction a V V.continuous = v := by
    ext x
    simpa [suzukiFiniteIntervalRestriction] using
      congrArg (fun f : C(SuzukiFiniteInterval a, Complex) => f x) hV
  calc
    suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a u v =
        suzukiFiniteIntervalContinuousOperatorPairingComplex
          kernel hkernel a
          (suzukiFiniteIntervalRestriction a U U.continuous)
          (suzukiFiniteIntervalRestriction a V V.continuous) := by
      rw [hU', hV']
    _ = suzukiFiniteIntervalCoreOperatorPairingComplex
          kernel a U V :=
      suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
        hkernel U.continuous V.continuous
    _ = conj (suzukiFiniteIntervalCoreOperatorPairingComplex
          kernel a V U) := by
      rw [suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
          hkernel U.continuous V.continuous,
        suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
          hkernel V.continuous U.continuous]
      exact suzukiFiniteKernelPolarizationComplex_conj_symm heven a U V
    _ = conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
          kernel hkernel a
          (suzukiFiniteIntervalRestriction a V V.continuous)
          (suzukiFiniteIntervalRestriction a U U.continuous)) := by
      rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
        hkernel V.continuous U.continuous]
    _ = conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
          kernel hkernel a v u) := by
      rw [hV', hU']

/-- The bundled bounded Suzuki operator is Hermitian on the whole continuous
finite-interval Banach space. -/
theorem suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiScrewFunction continuous_suzukiScrewFunction a u v =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiScrewFunction continuous_suzukiScrewFunction a v u) := by
  exact suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm_of_even
    continuous_suzukiScrewFunction suzukiScrewFunction_neg a u v

/-- A compactly supported smooth source enters the X15 zero-mean core after
applying Suzuki's differential `D = i d/dx`. -/
theorem suzukiDifferential_mem_finiteIntervalCoreSource
    {a : Real} {v : SchwartzLineTestFunction}
    (ha : 0 < a)
    (hsupport : Function.support v <= Set.Icc (-a) a) :
    SuzukiFiniteIntervalCoreSource a (suzukiDifferential v) := by
  exact ⟨(suzukiDifferential v).continuous,
    setIntegral_suzukiDifferential_eq_zero ha hsupport⟩

/-- First X15 consumer: the genuine project residual from X14 is exactly the
diagonal pairing of the finite-interval core operator on `D v`. -/
theorem guinandWeilBurnolLiteratureResidualSide_suzukiProjectBase_eq_coreOperatorPairing
    {a : Real} {v : SchwartzLineTestFunction}
    (ha : 0 < a)
    (hsupport : Function.support v <= Set.Icc (-a) a) :
    guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v) =
      (suzukiFiniteIntervalCoreOperatorPairingComplex
        suzukiScrewFunction a (suzukiDifferential v)
          (suzukiDifferential v)).re := by
  have hidentity := suzukiScalarKernelIdentityAt_of_support ha hsupport
  unfold SuzukiScalarKernelIdentityAt at hidentity
  calc
    guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v) =
        suzukiFiniteKernelPairing suzukiScrewFunction a
          (SchwartzMap.derivCLM Complex Complex v) := hidentity
    _ = (suzukiFiniteKernelPairingComplex suzukiScrewFunction a
          (SchwartzMap.derivCLM Complex Complex v)).re := by rfl
    _ = (suzukiFiniteKernelPairingComplex suzukiScrewFunction a
          (suzukiDifferential v)).re := by
      rw [suzukiFiniteKernelPairingComplex_differential_eq_deriv]
    _ = (suzukiFiniteKernelPolarizationComplex suzukiScrewFunction a
          (suzukiDifferential v) (suzukiDifferential v)).re := by
      rw [suzukiFiniteKernelPolarizationComplex_self]
    _ = (suzukiFiniteIntervalCoreOperatorPairingComplex
          suzukiScrewFunction a (suzukiDifferential v)
            (suzukiDifferential v)).re := by
      rw [suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
        continuous_suzukiScrewFunction (suzukiDifferential v).continuous
          (suzukiDifferential v).continuous]

/-- Bounded-operator X15 consumer: the same genuine X14 residual is the
diagonal pairing of the bundled continuous finite-interval operator on the
restricted Suzuki differential. -/
theorem guinandWeilBurnolLiteratureResidualSide_suzukiProjectBase_eq_continuousOperatorPairing
    {a : Real} {v : SchwartzLineTestFunction}
    (ha : 0 < a)
    (hsupport : Function.support v <= Set.Icc (-a) a) :
    guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v) =
      (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiScrewFunction continuous_suzukiScrewFunction a
        (suzukiFiniteIntervalRestriction a (suzukiDifferential v)
          (suzukiDifferential v).continuous)
        (suzukiFiniteIntervalRestriction a (suzukiDifferential v)
          (suzukiDifferential v).continuous)).re := by
  rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
    continuous_suzukiScrewFunction (suzukiDifferential v).continuous
      (suzukiDifferential v).continuous]
  exact
    guinandWeilBurnolLiteratureResidualSide_suzukiProjectBase_eq_coreOperatorPairing
      ha hsupport

end

end M100
end Experiments
end RiemannHypothesisProject
