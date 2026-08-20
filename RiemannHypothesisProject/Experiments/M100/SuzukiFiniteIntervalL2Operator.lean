import RiemannHypothesisProject.Experiments.M100.SuzukiFiniteIntervalOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# M100-DF6D2 finite-interval kernel operators on L2

This module upgrades the continuous finite-interval integral operator to the
actual `L2` space.  The extension is obtained from the dense continuous core
and an explicit Hilbert-space bound; no source-form or positivity assumption
is used.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiFiniteIntervalL2IsFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

/-- Complex `L2` on Suzuki's compact interval. -/
abbrev SuzukiFiniteIntervalL2 (a : Real) : Type :=
  Lp Complex 2 (volume : Measure (SuzukiFiniteInterval a))

/-- The dense inclusion of continuous interval functions into interval `L2`. -/
def suzukiFiniteIntervalContinuousToL2 (a : Real) :
    C(SuzukiFiniteInterval a, Complex) →L[Complex]
      SuzukiFiniteIntervalL2 a :=
  ContinuousMap.toLp 2 (volume : Measure (SuzukiFiniteInterval a)) Complex

/-- The real constant-one vector used in the finite-measure Cauchy--Schwarz
bound. -/
def suzukiFiniteIntervalOneRealL2 (a : Real) :
  Lp Real 2 (volume : Measure (SuzukiFiniteInterval a)) :=
  ContinuousMap.toLp 2 (volume : Measure (SuzukiFiniteInterval a)) Real
    (1 : C(SuzukiFiniteInterval a, Real))

/-- The complex constant-one vector used to bound a uniformly bounded output
in interval `L2`. -/
def suzukiFiniteIntervalOneComplexL2 (a : Real) :
    SuzukiFiniteIntervalL2 a :=
  suzukiFiniteIntervalContinuousToL2 a
    (1 : C(SuzukiFiniteInterval a, Complex))

/-- The explicit constant in the `L2` kernel-operator estimate. -/
def suzukiFiniteIntervalKernelL2Bound
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) : Real :=
  norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
    norm (suzukiFiniteIntervalOneRealL2 a) *
      norm (suzukiFiniteIntervalOneComplexL2 a)

/-- Taking pointwise norms of a continuous complex function preserves its
`L2` norm. -/
theorem norm_suzukiFiniteIntervalContinuousToL2_norm_le
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex)) :
    norm (ContinuousMap.toLp 2
      (volume : Measure (SuzukiFiniteInterval a)) Real
      ⟨fun x => norm (u x), u.continuous.norm⟩) <=
      norm (suzukiFiniteIntervalContinuousToL2 a u) := by
  have h :
      norm (ContinuousMap.toLp 2
        (volume : Measure (SuzukiFiniteInterval a)) Real
        ⟨fun x => norm (u x), u.continuous.norm⟩) <=
        1 * norm (suzukiFiniteIntervalContinuousToL2 a u) := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (c := 1)
      (f := ContinuousMap.toLp 2
        (volume : Measure (SuzukiFiniteInterval a)) Real
        ⟨fun x => norm (u x), u.continuous.norm⟩)
      (g := suzukiFiniteIntervalContinuousToL2 a u)
    filter_upwards [
      ContinuousMap.coeFn_toLp
        (𝕜 := Real)
        (p := (2 : ENNReal))
        (volume : Measure (SuzukiFiniteInterval a))
        (⟨fun x => norm (u x), u.continuous.norm⟩ :
          C(SuzukiFiniteInterval a, Real)),
      ContinuousMap.coeFn_toLp
        (𝕜 := Complex)
        (p := (2 : ENNReal))
        (volume : Measure (SuzukiFiniteInterval a)) u] with x hx hu
    rw [one_mul]
    change
      norm ((ContinuousMap.toLp 2
        (volume : Measure (SuzukiFiniteInterval a)) Real
        ⟨fun x => norm (u x), u.continuous.norm⟩) x) <=
        norm ((ContinuousMap.toLp 2
          (volume : Measure (SuzukiFiniteInterval a)) Complex u) x)
    rw [hx, hu]
    simp
  simpa only [one_mul] using h

/-- On the finite interval, the `L1` norm of a continuous function is bounded
by its `L2` norm times the `L2` norm of the constant-one function. -/
theorem integral_norm_suzukiFiniteInterval_le
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex)) :
    (∫ x : SuzukiFiniteInterval a, norm (u x) ∂volume) <=
      norm (suzukiFiniteIntervalOneRealL2 a) *
        norm (suzukiFiniteIntervalContinuousToL2 a u) := by
  let normU : C(SuzukiFiniteInterval a, Real) :=
    ⟨fun x => norm (u x), u.continuous.norm⟩
  have hinner :
      inner Real
          (ContinuousMap.toLp 2 volume Real normU)
          (suzukiFiniteIntervalOneRealL2 a) =
        ∫ x : SuzukiFiniteInterval a, norm (u x) ∂volume := by
    rw [suzukiFiniteIntervalOneRealL2,
      ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards with x
    simp [normU]
  calc
    (∫ x : SuzukiFiniteInterval a, norm (u x) ∂volume) =
        inner Real
          (ContinuousMap.toLp 2 volume Real normU)
          (suzukiFiniteIntervalOneRealL2 a) := hinner.symm
    _ <= norm (ContinuousMap.toLp 2 volume Real normU) *
          norm (suzukiFiniteIntervalOneRealL2 a) :=
      real_inner_le_norm _ _
    _ <= norm (suzukiFiniteIntervalContinuousToL2 a u) *
          norm (suzukiFiniteIntervalOneRealL2 a) := by
      exact mul_le_mul_of_nonneg_right
        (norm_suzukiFiniteIntervalContinuousToL2_norm_le a u)
        (norm_nonneg _)
    _ = norm (suzukiFiniteIntervalOneRealL2 a) *
          norm (suzukiFiniteIntervalContinuousToL2 a u) := by
      ring

/-- The continuous kernel action, viewed as an interval `L2` vector. -/
def suzukiFiniteIntervalCoreOperatorToL2
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    C(SuzukiFiniteInterval a, Complex) →L[Complex]
      SuzukiFiniteIntervalL2 a :=
  (suzukiFiniteIntervalContinuousToL2 a).comp
    (suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a)

/-- Pointwise kernel action is controlled by the kernel sup norm and the
finite-interval `L1` norm of the input. -/
theorem norm_suzukiFiniteIntervalContinuousOperator_apply_le_L1
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u : C(SuzukiFiniteInterval a, Complex))
    (x : SuzukiFiniteInterval a) :
    norm (suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u x) <=
      norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
        (∫ y : SuzukiFiniteInterval a, norm (u y) ∂volume) := by
  calc
    norm (suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u x) <=
        ∫ y : SuzukiFiniteInterval a,
          norm ((kernel (x.1 - y.1) : Complex) * u y) ∂volume := by
      exact norm_integral_le_integral_norm _
    _ <= ∫ y : SuzukiFiniteInterval a,
          norm (suzukiFiniteIntervalKernelContinuousMap
            kernel hkernel a) * norm (u y) ∂volume := by
      apply integral_mono
      · exact (integrable_suzukiFiniteIntervalContinuousOperator_integrand
          hkernel u x).norm
      · rw [← integrableOn_univ]
        exact (by fun_prop : Continuous (fun y : SuzukiFiniteInterval a =>
          norm (suzukiFiniteIntervalKernelContinuousMap
            kernel hkernel a) * norm (u y))).continuousOn
            |>.integrableOn_compact isCompact_univ
      · intro y
        change
          norm ((kernel (x.1 - y.1) : Complex) * u y) <=
            norm (suzukiFiniteIntervalKernelContinuousMap
              kernel hkernel a) * norm (u y)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right
          ((suzukiFiniteIntervalKernelContinuousMap
            kernel hkernel a).norm_coe_le_norm (x, y))
          (norm_nonneg (u y))
    _ = norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
          (∫ y : SuzukiFiniteInterval a, norm (u y) ∂volume) := by
      rw [integral_const_mul]

/-- The continuous-core operator satisfies an `L2 -> L2` estimate whose
constant depends only on the compact kernel and interval volume. -/
theorem norm_suzukiFiniteIntervalCoreOperatorToL2_le
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u : C(SuzukiFiniteInterval a, Complex)) :
    norm (suzukiFiniteIntervalCoreOperatorToL2 kernel hkernel a u) <=
      suzukiFiniteIntervalKernelL2Bound kernel hkernel a *
        norm (suzukiFiniteIntervalContinuousToL2 a u) := by
  let pointBound : Real :=
    norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
      (∫ y : SuzukiFiniteInterval a, norm (u y) ∂volume)
  have hpoint : forall x : SuzukiFiniteInterval a,
      norm (suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u x) <=
        pointBound := by
    intro x
    exact norm_suzukiFiniteIntervalContinuousOperator_apply_le_L1
      kernel hkernel a u x
  have hout :
      norm (suzukiFiniteIntervalCoreOperatorToL2 kernel hkernel a u) <=
        pointBound * norm (suzukiFiniteIntervalOneComplexL2 a) := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (E := Complex)
      (F := Complex)
      (p := (2 : ENNReal))
      (μ := (volume : Measure (SuzukiFiniteInterval a)))
      (c := pointBound)
      (f := suzukiFiniteIntervalCoreOperatorToL2 kernel hkernel a u)
      (g := suzukiFiniteIntervalOneComplexL2 a)
    filter_upwards [
      ContinuousMap.coeFn_toLp
        (𝕜 := Complex) (p := (2 : ENNReal)) volume
        (suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u),
      ContinuousMap.coeFn_toLp
        (𝕜 := Complex) (p := (2 : ENNReal)) volume
        (1 : C(SuzukiFiniteInterval a, Complex))] with x hx hOne
    rw [suzukiFiniteIntervalCoreOperatorToL2,
      ContinuousLinearMap.comp_apply,
      suzukiFiniteIntervalContinuousToL2,
      suzukiFiniteIntervalOneComplexL2,
      suzukiFiniteIntervalContinuousToL2]
    rw [hx, hOne]
    simpa using hpoint x
  have hL1 := integral_norm_suzukiFiniteInterval_le a u
  unfold suzukiFiniteIntervalKernelL2Bound
  dsimp only [pointBound] at hout
  calc
    norm (suzukiFiniteIntervalCoreOperatorToL2 kernel hkernel a u) <=
        (norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
          (∫ y : SuzukiFiniteInterval a, norm (u y) ∂volume)) *
            norm (suzukiFiniteIntervalOneComplexL2 a) := hout
    _ <= (norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
          (norm (suzukiFiniteIntervalOneRealL2 a) *
            norm (suzukiFiniteIntervalContinuousToL2 a u))) *
          norm (suzukiFiniteIntervalOneComplexL2 a) := by
      gcongr
    _ = (norm (suzukiFiniteIntervalKernelContinuousMap kernel hkernel a) *
          norm (suzukiFiniteIntervalOneRealL2 a) *
            norm (suzukiFiniteIntervalOneComplexL2 a)) *
          norm (suzukiFiniteIntervalContinuousToL2 a u) := by ring

/-- Continuous functions are dense in the compact interval `L2` space. -/
theorem denseRange_suzukiFiniteIntervalContinuousToL2 (a : Real) :
    DenseRange (suzukiFiniteIntervalContinuousToL2 a) := by
  exact ContinuousMap.toLp_denseRange Complex volume Complex
    ENNReal.ofNat_ne_top

/-- The bounded `L2` integral operator obtained by extending the continuous
kernel action from its dense core. -/
def suzukiFiniteIntervalL2Operator
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    SuzukiFiniteIntervalL2 a →L[Complex] SuzukiFiniteIntervalL2 a :=
  (suzukiFiniteIntervalCoreOperatorToL2 kernel hkernel a).toLinearMap.extendOfNorm
    (suzukiFiniteIntervalContinuousToL2 a).toLinearMap

/-- The `L2` extension agrees with the integral operator on every continuous
interval function. -/
theorem suzukiFiniteIntervalL2Operator_apply_continuous
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalL2Operator kernel hkernel a
        (suzukiFiniteIntervalContinuousToL2 a u) =
      suzukiFiniteIntervalCoreOperatorToL2 kernel hkernel a u := by
  apply LinearMap.extendOfNorm_eq
    (denseRange_suzukiFiniteIntervalContinuousToL2 a)
  exact ⟨suzukiFiniteIntervalKernelL2Bound kernel hkernel a,
    norm_suzukiFiniteIntervalCoreOperatorToL2_le kernel hkernel a⟩

/-- Operator-norm estimate for the extended finite-interval kernel action. -/
theorem norm_suzukiFiniteIntervalL2Operator_le
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real) :
    norm (suzukiFiniteIntervalL2Operator kernel hkernel a) <=
      suzukiFiniteIntervalKernelL2Bound kernel hkernel a := by
  apply LinearMap.opNorm_extendOfNorm_le
    (denseRange_suzukiFiniteIntervalContinuousToL2 a)
  · unfold suzukiFiniteIntervalKernelL2Bound
    positivity
  · exact norm_suzukiFiniteIntervalCoreOperatorToL2_le kernel hkernel a

/-- On the continuous core, the Hilbert pairing of the `L2` extension is the
complex conjugate of the source-oriented kernel pairing. -/
theorem inner_suzukiFiniteIntervalL2Operator_continuous
    (kernel : Real -> Real) (hkernel : Continuous kernel) (a : Real)
    (u v : C(SuzukiFiniteInterval a, Complex)) :
    inner Complex
        (suzukiFiniteIntervalL2Operator kernel hkernel a
          (suzukiFiniteIntervalContinuousToL2 a u))
        (suzukiFiniteIntervalContinuousToL2 a v) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a u v) := by
  rw [suzukiFiniteIntervalL2Operator_apply_continuous]
  rw [L2.inner_def]
  rw [suzukiFiniteIntervalCoreOperatorToL2,
    ContinuousLinearMap.comp_apply,
    suzukiFiniteIntervalContinuousToL2]
  rw [show conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
      kernel hkernel a u v) =
      (∫ x : SuzukiFiniteInterval a,
        conj (suzukiFiniteIntervalContinuousOperatorCLM
          kernel hkernel a u x) * v x ∂volume) by
    rw [suzukiFiniteIntervalContinuousOperatorPairingComplex,
      ← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    simp [mul_comm]]
  apply integral_congr_ae
  filter_upwards [
    ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal)) volume
      (suzukiFiniteIntervalContinuousOperatorCLM kernel hkernel a u),
    ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal)) volume v] with x hx hv
  rw [hx, hv]
  simp [RCLike.inner_apply, mul_comm]

/-- The `L2` extension of a continuous real-even kernel is self-adjoint.  The
Hermitian identity is proved on the dense continuous core and then extended
separately in both variables. -/
theorem suzukiFiniteIntervalL2Operator_isSelfAdjoint_of_even
    {kernel : Real -> Real} (hkernel : Continuous kernel)
    (heven : forall t, kernel (-t) = kernel t) (a : Real) :
    IsSelfAdjoint (suzukiFiniteIntervalL2Operator kernel hkernel a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  let e := suzukiFiniteIntervalContinuousToL2 a
  let A := suzukiFiniteIntervalL2Operator kernel hkernel a
  have hdense : DenseRange e :=
    denseRange_suzukiFiniteIntervalContinuousToL2 a
  have hcore (x y : C(SuzukiFiniteInterval a, Complex)) :
      inner Complex (A (e x)) (e y) =
        inner Complex (e x) (A (e y)) := by
    have hpair :=
      suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm_of_even
        hkernel heven a x y
    calc
      inner Complex (A (e x)) (e y) =
          conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
            kernel hkernel a x y) :=
        inner_suzukiFiniteIntervalL2Operator_continuous
          kernel hkernel a x y
      _ = suzukiFiniteIntervalContinuousOperatorPairingComplex
            kernel hkernel a y x := by
        rw [hpair]
        simp
      _ = conj (inner Complex (A (e y)) (e x)) := by
        rw [inner_suzukiFiniteIntervalL2Operator_continuous
          kernel hkernel a y x]
        simp
      _ = inner Complex (e x) (A (e y)) :=
        inner_conj_symm (e x) (A (e y))
  have hdenseRight
      (x : C(SuzukiFiniteInterval a, Complex)) :
      (fun y => inner Complex (A (e x)) y) =
        fun y => inner Complex (e x) (A y) := by
    apply hdense.equalizer <;> try fun_prop
    funext y
    exact hcore x y
  have hdenseLeft :
      (fun x => fun y => inner Complex (A x) y) =
        fun x => fun y => inner Complex x (A y) := by
    apply hdense.equalizer <;> try fun_prop
    funext x
    exact hdenseRight x
  intro x y
  exact congrFun (congrFun hdenseLeft x) y

end

end M100
end Experiments
end RiemannHypothesisProject
