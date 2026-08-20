import RiemannHypothesisProject.Experiments.M100.SuzukiLogRadiusScalarParity
import RiemannHypothesisProject.Experiments.M100.SuzukiRSecondKernel

/-!
# M100-DF6D5B1R concrete reflection equivariance

This module proves the operator and form equivariance needed to make the
reflection-parity split of `SuzukiLogRadiusScalarParity` unconditional for
Suzuki's concrete complete form.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory
open scoped ComplexConjugate InnerProductSpace

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiConcreteReflectionFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

private theorem lp_compMeasurePreserving_congr_apply
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] {p : ENNReal}
    {μ : Measure α} {ν : Measure β}
    {f g : α → β} (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g μ ν) (hfg : ∀ x, f x = g x)
    (v : Lp E p ν) :
    Lp.compMeasurePreserving f hf v =
      Lp.compMeasurePreserving g hg v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving v hf,
    Lp.coeFn_compMeasurePreserving v hg] with x hfx hgx
  rw [hfx, hgx, Function.comp_apply, Function.comp_apply, hfg]

@[simp]
theorem suzukiL2Translate_add (s t : Real) (v : SuzukiL2) :
    suzukiL2Translate s (suzukiL2Translate t v) =
      suzukiL2Translate (s + t) v := by
  calc
    suzukiL2Translate s (suzukiL2Translate t v) =
        Lp.compMeasurePreserving
          ((fun x : Real => x + t) ∘ fun x : Real => x + s)
          ((measurePreserving_add_right (volume : Measure Real) t).comp
            (measurePreserving_add_right (volume : Measure Real) s)) v := by
      exact (Lp.compMeasurePreserving_comp_apply v
        (measurePreserving_add_right (volume : Measure Real) t)
        (measurePreserving_add_right (volume : Measure Real) s)).symm
    _ = suzukiL2Translate (s + t) v := by
      unfold suzukiL2Translate
      apply lp_compMeasurePreserving_congr_apply
      intro x
      dsimp [Function.comp]
      ring

@[simp]
theorem suzukiL2Translate_zero (v : SuzukiL2) :
    suzukiL2Translate 0 v = v := by
  unfold suzukiL2Translate
  calc
    Lp.compMeasurePreserving (fun x : Real => x + 0)
        (measurePreserving_add_right (volume : Measure Real) 0) v =
      Lp.compMeasurePreserving id (MeasurePreserving.id volume) v := by
        apply lp_compMeasurePreserving_congr_apply
        simp
    _ = v := Lp.compMeasurePreserving_id_apply v

@[simp]
theorem suzukiL2Translate_neg (t : Real) (v : SuzukiL2) :
    suzukiL2Translate t (suzukiL2Translate (-t) v) = v := by
  rw [suzukiL2Translate_add]
  simp

theorem suzukiL2Translate_adjoint (t : Real) :
    (suzukiL2TranslateCLM t).adjoint = suzukiL2TranslateCLM (-t) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (suzukiL2TranslateCLM (-t)) (suzukiL2TranslateCLM t)).2
  intro u v
  calc
    inner Complex (suzukiL2TranslateCLM (-t) u) v =
        inner Complex
          (suzukiL2TranslateCLM t
            (suzukiL2TranslateCLM (-t) u))
          (suzukiL2TranslateCLM t v) := by
      exact (suzukiL2TranslateLI t).inner_map_map
        (suzukiL2TranslateCLM (-t) u) v |>.symm
    _ = inner Complex u (suzukiL2TranslateCLM t v) := by
      rw [suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply,
        suzukiL2Translate_neg]

theorem suzukiL2Reflection_translate_reflection
    (t : Real) (v : SuzukiL2) :
    suzukiL2Reflection
        (suzukiL2Translate t (suzukiL2Reflection v)) =
      suzukiL2Translate (-t) v := by
  calc
    suzukiL2Reflection
        (suzukiL2Translate t (suzukiL2Reflection v)) =
      Lp.compMeasurePreserving
        ((fun x : Real => x + t) ∘ Neg.neg)
        ((measurePreserving_add_right (volume : Measure Real) t).comp
          (Measure.measurePreserving_neg (volume : Measure Real)))
        (suzukiL2Reflection v) := by
      exact (Lp.compMeasurePreserving_comp_apply
        (suzukiL2Reflection v)
        (measurePreserving_add_right (volume : Measure Real) t)
        (Measure.measurePreserving_neg (volume : Measure Real))).symm
    _ = Lp.compMeasurePreserving
        (Neg.neg ∘ (fun x : Real => x + t) ∘ Neg.neg)
        ((Measure.measurePreserving_neg (volume : Measure Real)).comp
          ((measurePreserving_add_right (volume : Measure Real) t).comp
            (Measure.measurePreserving_neg (volume : Measure Real)))) v := by
      exact (Lp.compMeasurePreserving_comp_apply v
        (Measure.measurePreserving_neg (volume : Measure Real))
        ((measurePreserving_add_right (volume : Measure Real) t).comp
          (Measure.measurePreserving_neg (volume : Measure Real)))).symm
    _ = suzukiL2Translate (-t) v := by
      unfold suzukiL2Translate
      apply lp_compMeasurePreserving_congr_apply
      intro x
      dsimp [Function.comp]
      ring

theorem suzukiL2Translate_reflection
    (t : Real) (v : SuzukiL2) :
    suzukiL2Translate t (suzukiL2Reflection v) =
      suzukiL2Reflection (suzukiL2Translate (-t) v) := by
  have h := congrArg suzukiL2Reflection
    (suzukiL2Reflection_translate_reflection t v)
  simpa only [suzukiL2Reflection_involution] using h

theorem suzukiL2SymmetricTranslationEnergy_reflection
    (t : Real) (u v : SuzukiL2) :
    suzukiL2SymmetricTranslationEnergy t
        (suzukiL2Reflection u) (suzukiL2Reflection v) =
      suzukiL2SymmetricTranslationEnergy t u v := by
  unfold suzukiL2SymmetricTranslationEnergy
  rw [suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply]
  rw [suzukiL2Translate_reflection, suzukiL2Translate_reflection]
  have hfirst := suzukiL2Reflection.inner_map_map
    (suzukiL2Translate (-t) u) v
  have hsecond := suzukiL2Reflection.inner_map_map
    u (suzukiL2Translate (-t) v)
  rw [hfirst, hsecond]
  rw [← suzukiL2TranslateCLM_apply]
  rw [← suzukiL2Translate_adjoint, ContinuousLinearMap.adjoint_inner_left]
  rw [← suzukiL2TranslateCLM_apply]
  rw [← suzukiL2Translate_adjoint, ContinuousLinearMap.adjoint_inner_right]
  ring

theorem suzukiL2FiniteTranslationEnergy_reflection
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u v : SuzukiL2) :
    suzukiL2FiniteTranslationEnergy s coefficient shift
        (suzukiL2Reflection u) (suzukiL2Reflection v) =
      suzukiL2FiniteTranslationEnergy s coefficient shift u v := by
  unfold suzukiL2FiniteTranslationEnergy
  apply Finset.sum_congr rfl
  intro i hi
  rw [suzukiL2SymmetricTranslationEnergy_reflection]

private theorem
    suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm_of_even_local
    {kernel : Real → Real} (hkernel : Continuous kernel)
    (heven : ∀ t, kernel (-t) = kernel t)
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
    _ = suzukiFiniteKernelPolarizationComplex kernel a U V := by
      rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
        hkernel U.continuous V.continuous,
        suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
          hkernel U.continuous V.continuous]
    _ = conj (suzukiFiniteKernelPolarizationComplex kernel a V U) :=
      suzukiFiniteKernelPolarizationComplex_conj_symm heven a U V
    _ = conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a
        (suzukiFiniteIntervalRestriction a V V.continuous)
        (suzukiFiniteIntervalRestriction a U U.continuous)) := by
      rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
        hkernel V.continuous U.continuous,
        suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
          hkernel V.continuous U.continuous]
    _ = conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a v u) := by rw [hV', hU']

theorem suzukiRSecondFiniteIntervalL2Operator_isSelfAdjoint (a : Real) :
    IsSelfAdjoint (suzukiRSecondFiniteIntervalL2Operator a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  let e := suzukiFiniteIntervalContinuousToL2 a
  let A := suzukiRSecondFiniteIntervalL2Operator a
  have hdense : DenseRange e :=
    denseRange_suzukiFiniteIntervalContinuousToL2 a
  have hcore (x y : C(SuzukiFiniteInterval a, Complex)) :
      inner Complex (A (e x)) (e y) =
        inner Complex (e x) (A (e y)) := by
    have hpair :=
      suzukiFiniteIntervalContinuousOperatorPairingComplex_conj_symm_of_even_local
        continuous_suzukiRSecondKernel suzukiRSecondKernel_neg a x y
    calc
      inner Complex (A (e x)) (e y) =
          conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
            suzukiRSecondKernel continuous_suzukiRSecondKernel a x y) :=
        inner_suzukiRSecondFiniteIntervalL2Operator_continuous a x y
      _ = suzukiFiniteIntervalContinuousOperatorPairingComplex
            suzukiRSecondKernel continuous_suzukiRSecondKernel a y x := by
        rw [hpair]
        simp
      _ = conj (inner Complex (A (e y)) (e x)) := by
        rw [inner_suzukiRSecondFiniteIntervalL2Operator_continuous a y x]
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

def suzukiFiniteIntervalNeg (a : Real) :
    SuzukiFiniteInterval a → SuzukiFiniteInterval a :=
  fun x => ⟨-x.1, by
    constructor
    · linarith [x.2.2]
    · linarith [x.2.1]⟩

private theorem suzukiFiniteIntervalNeg_preimage (a : Real) :
    Neg.neg ⁻¹' Set.Icc (-a) a = Set.Icc (-a) a := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc]
  constructor <;> intro hx
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩

private theorem measurable_suzukiFiniteIntervalNeg (a : Real) :
    Measurable (suzukiFiniteIntervalNeg a) :=
  (Continuous.subtype_mk
    (continuous_neg.comp continuous_subtype_val) _).measurable

private theorem measurePreserving_suzukiFiniteIntervalNeg (a : Real) :
    MeasurePreserving (suzukiFiniteIntervalNeg a)
      (volume : Measure (SuzukiFiniteInterval a))
      (volume : Measure (SuzukiFiniteInterval a)) := by
  have hnegRestricted :
      MeasurePreserving Neg.neg
        ((volume : Measure Real).restrict (Set.Icc (-a) a))
        ((volume : Measure Real).restrict (Set.Icc (-a) a)) := by
    have h := (Measure.measurePreserving_neg
      (volume : Measure Real)).restrict_preimage
        (s := Set.Icc (-a) a) measurableSet_Icc
    rw [suzukiFiniteIntervalNeg_preimage] at h
    exact h
  have hcoe :
      Measure.map Subtype.val
          (volume : Measure (SuzukiFiniteInterval a)) =
        (volume : Measure Real).restrict (Set.Icc (-a) a) := by
    rw [Measure.Subtype.volume_def,
      map_comap_subtype_coe measurableSet_Icc]
  refine ⟨measurable_suzukiFiniteIntervalNeg a, ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe
    (measurable_suzukiFiniteIntervalNeg a)]
  change Measure.map (Neg.neg ∘ Subtype.val)
      (volume : Measure (SuzukiFiniteInterval a)) =
    Measure.map Subtype.val (volume : Measure (SuzukiFiniteInterval a))
  calc
    Measure.map (Neg.neg ∘ Subtype.val)
        (volume : Measure (SuzukiFiniteInterval a)) =
      Measure.map Neg.neg
        (Measure.map Subtype.val
          (volume : Measure (SuzukiFiniteInterval a))) := by
            rw [Measure.map_map
              hnegRestricted.measurable measurable_subtype_coe]
    _ = Measure.map Neg.neg
        ((volume : Measure Real).restrict (Set.Icc (-a) a)) := by
          rw [hcoe]
    _ = (volume : Measure Real).restrict (Set.Icc (-a) a) :=
      hnegRestricted.map_eq
    _ = Measure.map Subtype.val
        (volume : Measure (SuzukiFiniteInterval a)) := hcoe.symm

def suzukiFiniteIntervalL2Reflection (a : Real) :
    SuzukiFiniteIntervalL2 a →ₗᵢ[Complex] SuzukiFiniteIntervalL2 a :=
  Lp.compMeasurePreservingₗᵢ Complex (suzukiFiniteIntervalNeg a)
    (measurePreserving_suzukiFiniteIntervalNeg a)

@[simp]
theorem suzukiFiniteIntervalNeg_involution
    (a : Real) (x : SuzukiFiniteInterval a) :
    suzukiFiniteIntervalNeg a (suzukiFiniteIntervalNeg a x) = x := by
  apply Subtype.ext
  simp [suzukiFiniteIntervalNeg]

def suzukiFiniteIntervalNegMeasurableEquiv (a : Real) :
    SuzukiFiniteInterval a ≃ᵐ SuzukiFiniteInterval a where
  toEquiv :=
    { toFun := suzukiFiniteIntervalNeg a
      invFun := suzukiFiniteIntervalNeg a
      left_inv := suzukiFiniteIntervalNeg_involution a
      right_inv := suzukiFiniteIntervalNeg_involution a }
  measurable_toFun := measurable_suzukiFiniteIntervalNeg a
  measurable_invFun := measurable_suzukiFiniteIntervalNeg a

def suzukiFiniteIntervalContinuousReflection
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex)) :
    C(SuzukiFiniteInterval a, Complex) where
  toFun x := u (suzukiFiniteIntervalNeg a x)
  continuous_toFun := u.continuous.comp
    (Continuous.subtype_mk
      (continuous_neg.comp continuous_subtype_val) _)

theorem
    suzukiFiniteIntervalContinuousOperatorPairingComplex_reflection_of_even
    {kernel : Real → Real} (hkernel : Continuous kernel)
    (heven : ∀ t, kernel (-t) = kernel t)
    (a : Real) (u v : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalContinuousOperatorPairingComplex kernel hkernel a
        (suzukiFiniteIntervalContinuousReflection a u)
        (suzukiFiniteIntervalContinuousReflection a v) =
      suzukiFiniteIntervalContinuousOperatorPairingComplex
        kernel hkernel a u v := by
  let N := suzukiFiniteIntervalNeg a
  let hN := measurePreserving_suzukiFiniteIntervalNeg a
  let eN := suzukiFiniteIntervalNegMeasurableEquiv a
  have hNe : MeasurePreserving eN
      (volume : Measure (SuzukiFiniteInterval a))
      (volume : Measure (SuzukiFiniteInterval a)) := by
    apply hN.congr eN.measurable
    filter_upwards with x
    rfl
  have hinner (x : SuzukiFiniteInterval a) :
      (∫ y : SuzukiFiniteInterval a,
          (kernel ((N x).1 - y.1) : Complex) * u (N y)) =
        ∫ y : SuzukiFiniteInterval a,
          (kernel (x.1 - y.1) : Complex) * u y := by
    calc
      (∫ y : SuzukiFiniteInterval a,
          (kernel ((N x).1 - y.1) : Complex) * u (N y)) =
        ∫ y : SuzukiFiniteInterval a,
          (kernel ((N x).1 - (N y).1) : Complex) *
            u (N (N y)) := by
              exact (hNe.integral_comp'
                (fun y : SuzukiFiniteInterval a =>
                  (kernel ((N x).1 - y.1) : Complex) * u (N y))).symm
      _ = ∫ y : SuzukiFiniteInterval a,
          (kernel (x.1 - y.1) : Complex) * u y := by
        apply integral_congr_ae
        filter_upwards with y
        simp only [N, suzukiFiniteIntervalNeg_involution]
        change (kernel (-x.1 - -y.1) : Complex) * u y =
          (kernel (x.1 - y.1) : Complex) * u y
        have harg : -x.1 - -y.1 = -(x.1 - y.1) := by ring
        rw [harg, heven]
  change
    (∫ x : SuzukiFiniteInterval a,
      (∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * u (N y)) *
          conj (v (N x))) =
    ∫ x : SuzukiFiniteInterval a,
      (∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * u y) * conj (v x)
  calc
    (∫ x : SuzukiFiniteInterval a,
      (∫ y : SuzukiFiniteInterval a,
        (kernel (x.1 - y.1) : Complex) * u (N y)) *
          conj (v (N x))) =
      ∫ x : SuzukiFiniteInterval a,
        (∫ y : SuzukiFiniteInterval a,
          (kernel ((N x).1 - y.1) : Complex) * u (N y)) *
            conj (v (N (N x))) := by
              exact (hNe.integral_comp'
                (fun x : SuzukiFiniteInterval a =>
                  (∫ y : SuzukiFiniteInterval a,
                    (kernel (x.1 - y.1) : Complex) * u (N y)) *
                      conj (v (N x)))).symm
    _ = ∫ x : SuzukiFiniteInterval a,
        (∫ y : SuzukiFiniteInterval a,
          (kernel (x.1 - y.1) : Complex) * u y) * conj (v x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [N, suzukiFiniteIntervalNeg_involution]
      rw [hinner]

theorem suzukiFiniteIntervalContinuousToL2_reflection
    (a : Real) (u : C(SuzukiFiniteInterval a, Complex)) :
    suzukiFiniteIntervalL2Reflection a
        (suzukiFiniteIntervalContinuousToL2 a u) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFiniteIntervalContinuousReflection a u) := by
  let N := suzukiFiniteIntervalNeg a
  let hN := measurePreserving_suzukiFiniteIntervalNeg a
  have hcomp :
      (suzukiFiniteIntervalL2Reflection a
          (suzukiFiniteIntervalContinuousToL2 a u) :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      (suzukiFiniteIntervalContinuousToL2 a u :
          SuzukiFiniteInterval a → Complex) ∘ N := by
    exact Lp.coeFn_compMeasurePreserving
      (suzukiFiniteIntervalContinuousToL2 a u) hN
  have hcontinuous :
      (suzukiFiniteIntervalContinuousToL2 a u :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume] u := by
    simpa only [suzukiFiniteIntervalContinuousToL2] using
      (ContinuousMap.coeFn_toLp
        (𝕜 := Complex) (p := (2 : ENNReal))
        (volume : Measure (SuzukiFiniteInterval a)) u)
  have hcontinuousComp :
      (fun x => (suzukiFiniteIntervalContinuousToL2 a u) (N x))
          =ᵐ[volume]
        fun x => u (N x) :=
    hN.quasiMeasurePreserving.ae_eq_comp hcontinuous
  have hreflected :
      (suzukiFiniteIntervalContinuousToL2 a
          (suzukiFiniteIntervalContinuousReflection a u) :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      suzukiFiniteIntervalContinuousReflection a u := by
    simpa only [suzukiFiniteIntervalContinuousToL2] using
      (ContinuousMap.coeFn_toLp
        (𝕜 := Complex) (p := (2 : ENNReal))
        (volume : Measure (SuzukiFiniteInterval a))
        (suzukiFiniteIntervalContinuousReflection a u))
  apply Lp.ext
  filter_upwards [hcomp, hcontinuousComp, hreflected] with
    x hxComp hxContinuous hxReflected
  exact hxComp.trans (hxContinuous.trans hxReflected.symm)

@[simp]
theorem suzukiFiniteIntervalL2Reflection_involution
    (a : Real) (v : SuzukiFiniteIntervalL2 a) :
    suzukiFiniteIntervalL2Reflection a
        (suzukiFiniteIntervalL2Reflection a v) = v := by
  let N := suzukiFiniteIntervalNeg a
  let hN := measurePreserving_suzukiFiniteIntervalNeg a
  calc
    suzukiFiniteIntervalL2Reflection a
        (suzukiFiniteIntervalL2Reflection a v) =
      Lp.compMeasurePreserving (N ∘ N) (hN.comp hN) v := by
        exact (Lp.compMeasurePreserving_comp_apply v hN hN).symm
    _ = Lp.compMeasurePreserving id (MeasurePreserving.id volume) v := by
      apply lp_compMeasurePreserving_congr_apply
      exact suzukiFiniteIntervalNeg_involution a
    _ = v := Lp.compMeasurePreserving_id_apply v

theorem inner_suzukiRSecondFiniteIntervalL2Operator_reflection
    (a : Real) (u v : SuzukiFiniteIntervalL2 a) :
    inner Complex
        (suzukiRSecondFiniteIntervalL2Operator a
          (suzukiFiniteIntervalL2Reflection a u))
        (suzukiFiniteIntervalL2Reflection a v) =
      inner Complex
        (suzukiRSecondFiniteIntervalL2Operator a u) v := by
  let e := suzukiFiniteIntervalContinuousToL2 a
  let A := suzukiRSecondFiniteIntervalL2Operator a
  let R := suzukiFiniteIntervalL2Reflection a
  have hdense : DenseRange e :=
    denseRange_suzukiFiniteIntervalContinuousToL2 a
  have hcore (x y : C(SuzukiFiniteInterval a, Complex)) :
      inner Complex (A (R (e x))) (R (e y)) =
        inner Complex (A (e x)) (e y) := by
    rw [suzukiFiniteIntervalContinuousToL2_reflection,
      suzukiFiniteIntervalContinuousToL2_reflection,
      inner_suzukiRSecondFiniteIntervalL2Operator_continuous,
      inner_suzukiRSecondFiniteIntervalL2Operator_continuous,
      suzukiFiniteIntervalContinuousOperatorPairingComplex_reflection_of_even
        continuous_suzukiRSecondKernel suzukiRSecondKernel_neg]
  have hdenseRight
      (x : C(SuzukiFiniteInterval a, Complex)) :
      (fun y => inner Complex (A (R (e x))) (R y)) =
        fun y => inner Complex (A (e x)) y := by
    apply hdense.equalizer <;> try fun_prop
    funext y
    exact hcore x y
  have hdenseLeft :
      (fun x => fun y => inner Complex (A (R x)) (R y)) =
        fun x => fun y => inner Complex (A x) y := by
    apply hdense.equalizer <;> try fun_prop
    funext x
    exact hdenseRight x
  exact congrFun (congrFun hdenseLeft u) v

theorem suzukiRSecondFiniteIntervalL2Operator_reflection
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    suzukiRSecondFiniteIntervalL2Operator a
        (suzukiFiniteIntervalL2Reflection a u) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiRSecondFiniteIntervalL2Operator a u) := by
  apply ext_inner_right Complex
  intro v
  have hform :=
    inner_suzukiRSecondFiniteIntervalL2Operator_reflection
      a u (suzukiFiniteIntervalL2Reflection a v)
  have hisometry :=
    (suzukiFiniteIntervalL2Reflection a).inner_map_map
      (suzukiRSecondFiniteIntervalL2Operator a u)
      (suzukiFiniteIntervalL2Reflection a v)
  simpa only [suzukiFiniteIntervalL2Reflection_involution] using
    hform.trans hisometry.symm

/-- Every finite-interval convolution operator with a real even kernel
commutes with reflection.  This is the kernel-independent form of the
specialized `RSecond` equivariance above. -/
theorem suzukiFiniteIntervalL2Operator_reflection_of_even
    {kernel : Real → Real} (hkernel : Continuous kernel)
    (heven : ∀ t, kernel (-t) = kernel t)
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    suzukiFiniteIntervalL2Operator kernel hkernel a
        (suzukiFiniteIntervalL2Reflection a u) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiFiniteIntervalL2Operator kernel hkernel a u) := by
  let e := suzukiFiniteIntervalContinuousToL2 a
  let A := suzukiFiniteIntervalL2Operator kernel hkernel a
  let R := suzukiFiniteIntervalL2Reflection a
  have hdense : DenseRange e :=
    denseRange_suzukiFiniteIntervalContinuousToL2 a
  have hcore (x y : C(SuzukiFiniteInterval a, Complex)) :
      inner Complex (A (R (e x))) (R (e y)) =
        inner Complex (A (e x)) (e y) := by
    rw [suzukiFiniteIntervalContinuousToL2_reflection,
      suzukiFiniteIntervalContinuousToL2_reflection,
      inner_suzukiFiniteIntervalL2Operator_continuous,
      inner_suzukiFiniteIntervalL2Operator_continuous,
      suzukiFiniteIntervalContinuousOperatorPairingComplex_reflection_of_even
        hkernel heven]
  have hdenseRight
      (x : C(SuzukiFiniteInterval a, Complex)) :
      (fun y => inner Complex (A (R (e x))) (R y)) =
        fun y => inner Complex (A (e x)) y := by
    apply hdense.equalizer <;> try fun_prop
    funext y
    exact hcore x y
  have hdenseLeft :
      (fun x => fun y => inner Complex (A (R x)) (R y)) =
        fun x => fun y => inner Complex (A x) y := by
    apply hdense.equalizer <;> try fun_prop
    funext x
    exact hdenseRight x
  apply ext_inner_right Complex
  intro v
  have hform := congrFun (congrFun hdenseLeft u) (R v)
  have hisometry := R.inner_map_map (A u) (R v)
  dsimp only [A, R] at hform hisometry ⊢
  simpa only [suzukiFiniteIntervalL2Reflection_involution] using
    hform.trans hisometry.symm

private theorem suzukiL2RestrictToFiniteInterval_coeFn
    (a : Real) (v : SuzukiL2) :
    (suzukiL2RestrictToFiniteInterval a v :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      fun x => v x.1 := by
  let s : Set Real := Icc (-a) a
  let restricted : Lp Complex 2 ((volume : Measure Real).restrict s) :=
    LpToLpRestrictCLM Real Complex Complex
      (volume : Measure Real) 2 s v
  have hmp : MeasurePreserving
      (fun x : SuzukiFiniteInterval a => (x : Real))
      (volume : Measure (SuzukiFiniteInterval a))
      ((volume : Measure Real).restrict s) := by
    rw [Measure.Subtype.volume_def]
    simpa only [s] using
      (measurePreserving_subtype_coe measurableSet_Icc :
        MeasurePreserving
          (fun x : SuzukiFiniteInterval a => (x : Real))
          ((volume : Measure Real).comap Subtype.val)
          ((volume : Measure Real).restrict (Icc (-a) a)))
  have hcomp :
      Lp.compMeasurePreserving
          (fun x : SuzukiFiniteInterval a => (x : Real)) hmp restricted
        =ᵐ[volume]
      (restricted : Real → Complex) ∘
        fun x : SuzukiFiniteInterval a => (x : Real) :=
    Lp.coeFn_compMeasurePreserving restricted hmp
  have hrestrict :
      restricted =ᵐ[(volume : Measure Real).restrict s] v := by
    simpa only [restricted] using
      (LpToLpRestrictCLM_coeFn
        (p := (2 : ENNReal)) (μ := (volume : Measure Real))
        Complex s v)
  have hrestrictComp :
      (fun x : SuzukiFiniteInterval a => restricted x.1) =ᵐ[volume]
        fun x => v x.1 :=
    hmp.quasiMeasurePreserving.ae_eq_comp hrestrict
  filter_upwards [hcomp, hrestrictComp] with x hxComp hxRestrict
  rw [suzukiL2RestrictToFiniteInterval,
    ContinuousLinearMap.comp_apply]
  exact hxComp.trans hxRestrict

theorem suzukiL2RestrictToFiniteInterval_reflection
    (a : Real) (v : SuzukiL2) :
    suzukiL2RestrictToFiniteInterval a (suzukiL2Reflection v) =
      suzukiFiniteIntervalL2Reflection a
        (suzukiL2RestrictToFiniteInterval a v) := by
  let N := suzukiFiniteIntervalNeg a
  let hN := measurePreserving_suzukiFiniteIntervalNeg a
  have hsubtype : MeasurePreserving
      (fun x : SuzukiFiniteInterval a => (x : Real))
      (volume : Measure (SuzukiFiniteInterval a))
      ((volume : Measure Real).restrict (Icc (-a) a)) := by
    rw [Measure.Subtype.volume_def]
    exact measurePreserving_subtype_coe measurableSet_Icc
  have hleft :=
    suzukiL2RestrictToFiniteInterval_coeFn a (suzukiL2Reflection v)
  have hglobal :
      (suzukiL2Reflection v : Real → Complex) =ᵐ[volume]
        (v : Real → Complex) ∘ Neg.neg :=
    Lp.coeFn_compMeasurePreserving v
      (Measure.measurePreserving_neg (volume : Measure Real))
  have hglobalRestricted :
      (fun x : SuzukiFiniteInterval a => (suzukiL2Reflection v) x.1)
          =ᵐ[volume]
        fun x => v (-x.1) :=
    hsubtype.quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae hglobal)
  have hfinite :
      (suzukiFiniteIntervalL2Reflection a
          (suzukiL2RestrictToFiniteInterval a v) :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      (suzukiL2RestrictToFiniteInterval a v :
          SuzukiFiniteInterval a → Complex) ∘ N :=
    Lp.coeFn_compMeasurePreserving
      (suzukiL2RestrictToFiniteInterval a v) hN
  have hrestricted :=
    suzukiL2RestrictToFiniteInterval_coeFn a v
  have hrestrictedComp :
      (fun x => (suzukiL2RestrictToFiniteInterval a v) (N x))
          =ᵐ[volume]
        fun x => v ((N x).1) :=
    hN.quasiMeasurePreserving.ae_eq_comp hrestricted
  apply Lp.ext
  filter_upwards [hleft, hglobalRestricted, hfinite,
    hrestrictedComp] with x hxLeft hxGlobal hxFinite hxRestricted
  rw [hxLeft, hxGlobal, hxFinite]
  change v (-x.1) =
    (suzukiL2RestrictToFiniteInterval a v) (N x)
  rw [hxRestricted]
  rfl

theorem suzukiRSecondGlobalL2Operator_isSelfAdjoint (a : Real) :
    IsSelfAdjoint (suzukiRSecondGlobalL2Operator a) := by
  simpa only [suzukiRSecondGlobalL2Operator] using
    (suzukiRSecondFiniteIntervalL2Operator_isSelfAdjoint a).adjoint_conj
      (suzukiL2RestrictToFiniteInterval a)

theorem suzukiRSecondSourceRemainderOperator_isSelfAdjoint (a : Real) :
    IsSelfAdjoint (suzukiRSecondSourceRemainderOperator a) := by
  simpa only [suzukiRSecondSourceRemainderOperator] using
    (suzukiRSecondGlobalL2Operator_isSelfAdjoint a).neg

theorem inner_suzukiRSecondGlobalL2Operator_reflection
    (a : Real) (u v : SuzukiL2) :
    inner Complex
        (suzukiRSecondGlobalL2Operator a (suzukiL2Reflection u))
        (suzukiL2Reflection v) =
      inner Complex (suzukiRSecondGlobalL2Operator a u) v := by
  rw [inner_suzukiRSecondGlobalL2Operator,
    suzukiL2RestrictToFiniteInterval_reflection,
    suzukiL2RestrictToFiniteInterval_reflection,
    inner_suzukiRSecondFiniteIntervalL2Operator_reflection,
    ← inner_suzukiRSecondGlobalL2Operator]

theorem suzukiRSecondGlobalL2Operator_reflection
    (a : Real) (u : SuzukiL2) :
    suzukiRSecondGlobalL2Operator a (suzukiL2Reflection u) =
      suzukiL2Reflection (suzukiRSecondGlobalL2Operator a u) := by
  apply ext_inner_right Complex
  intro v
  have hform :=
    inner_suzukiRSecondGlobalL2Operator_reflection
      a u (suzukiL2Reflection v)
  have hisometry :=
    suzukiL2Reflection.inner_map_map
      (suzukiRSecondGlobalL2Operator a u)
      (suzukiL2Reflection v)
  simpa only [suzukiL2Reflection_involution] using
    hform.trans hisometry.symm

theorem inner_suzukiRSecondSourceRemainderOperator_reflection
    (a : Real) (u v : SuzukiL2) :
    inner Complex
        (suzukiRSecondSourceRemainderOperator a
          (suzukiL2Reflection u))
        (suzukiL2Reflection v) =
      inner Complex (suzukiRSecondSourceRemainderOperator a u) v := by
  rw [suzukiRSecondSourceRemainderOperator,
    neg_apply, neg_apply,
    inner_neg_left, inner_neg_left,
    inner_suzukiRSecondGlobalL2Operator_reflection]

theorem suzukiRSecondSourceRemainderOperator_reflection
    (a : Real) (u : SuzukiL2) :
    suzukiRSecondSourceRemainderOperator a (suzukiL2Reflection u) =
      suzukiL2Reflection
        (suzukiRSecondSourceRemainderOperator a u) := by
  rw [suzukiRSecondSourceRemainderOperator,
    neg_apply,
    suzukiRSecondGlobalL2Operator_reflection]
  change -suzukiL2Reflection (suzukiRSecondGlobalL2Operator a u) =
    suzukiL2Reflection (-(suzukiRSecondGlobalL2Operator a u))
  exact (map_neg suzukiL2Reflection
    (suzukiRSecondGlobalL2Operator a u)).symm

theorem suzukiL2SymmetricTranslationEnergy_conj_symm
    (t : Real) (u v : SuzukiL2) :
    suzukiL2SymmetricTranslationEnergy t u v =
      conj (suzukiL2SymmetricTranslationEnergy t v u) := by
  unfold suzukiL2SymmetricTranslationEnergy
  rw [map_add]
  have hfirst :=
    inner_conj_symm (𝕜 := Complex)
      (suzukiL2TranslateCLM t u) v
  have hsecond :=
    inner_conj_symm (𝕜 := Complex)
      u (suzukiL2TranslateCLM t v)
  rw [hfirst, hsecond]
  ring

theorem suzukiL2FiniteTranslationEnergy_conj_symm
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u v : SuzukiL2) :
    suzukiL2FiniteTranslationEnergy s coefficient shift u v =
      conj (suzukiL2FiniteTranslationEnergy
        s coefficient shift v u) := by
  unfold suzukiL2FiniteTranslationEnergy
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, ← suzukiL2SymmetricTranslationEnergy_conj_symm]
  simp

theorem suzukiL2BoundedOperatorEnergy_conj_symm_of_isSelfAdjoint
    {K : SuzukiL2 →L[Complex] SuzukiL2} (hK : IsSelfAdjoint K)
    (u v : SuzukiL2) :
    suzukiL2BoundedOperatorEnergy K u v =
      conj (suzukiL2BoundedOperatorEnergy K v u) := by
  unfold suzukiL2BoundedOperatorEnergy
  calc
    inner Complex (K u) v = inner Complex u (K v) :=
      hK.isSymmetric u v
    _ = conj (inner Complex (K v) u) :=
      (inner_conj_symm (𝕜 := Complex) u (K v)).symm

theorem suzukiL2BoundedOperatorEnergy_reflection
    (a : Real) (u v : SuzukiL2) :
    suzukiL2BoundedOperatorEnergy
        (suzukiRSecondSourceRemainderOperator a)
        (suzukiL2Reflection u) (suzukiL2Reflection v) =
      suzukiL2BoundedOperatorEnergy
        (suzukiRSecondSourceRemainderOperator a) u v := by
  unfold suzukiL2BoundedOperatorEnergy
  rw [suzukiRSecondSourceRemainderOperator_reflection]
  exact suzukiL2Reflection.inner_map_map
    (suzukiRSecondSourceRemainderOperator a u) v

theorem suzukiRSecondFiniteRadiusRemainderEnergy_conj_symm
    {I : Type*} [DecidableEq I] (s : Finset I)
    (a scalar : Real) (coefficient shift : I → Real)
    (u v : SuzukiL2) :
    suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) u v =
      conj (suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) v u) := by
  unfold suzukiL2FiniteRadiusRemainderEnergy
  rw [map_add, map_add, map_mul,
    ← suzukiL2FiniteTranslationEnergy_conj_symm,
    ← suzukiL2BoundedOperatorEnergy_conj_symm_of_isSelfAdjoint
      (suzukiRSecondSourceRemainderOperator_isSelfAdjoint a)]
  have hinner := inner_conj_symm (𝕜 := Complex) u v
  rw [← hinner]
  simp

theorem suzukiRSecondFiniteRadiusRemainderEnergy_reflection
    {I : Type*} [DecidableEq I] (s : Finset I)
    (a scalar : Real) (coefficient shift : I → Real)
    (u v : SuzukiL2) :
    suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a)
        (suzukiL2Reflection u) (suzukiL2Reflection v) =
      suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) u v := by
  unfold suzukiL2FiniteRadiusRemainderEnergy
  rw [suzukiL2Reflection.inner_map_map,
    suzukiL2FiniteTranslationEnergy_reflection,
    suzukiL2BoundedOperatorEnergy_reflection]

theorem suzukiRSecondLogRadiusLinearCompleteEnergy_conj_symm
    {I : Type*} [DecidableEq I] (a : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (u v : SuzukiLogRadiusLinearCompletion a) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) u v =
      conj (suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) v u) := by
  unfold suzukiLogRadiusLinearCompleteEnergy
  rw [map_add, ← suzukiRSecondFiniteRadiusRemainderEnergy_conj_symm]
  exact congrArg
    (fun z => z +
      suzukiL2FiniteRadiusRemainderEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a)
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v))
    (inner_conj_symm (𝕜 := Complex) u v).symm

theorem suzukiRSecondLogRadiusLinearCompleteEnergy_reflection
    {I : Type*} [DecidableEq I] (a : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (u v : SuzukiLogRadiusLinearCompletion a) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a)
        (suzukiLogRadiusLinearReflection a u)
        (suzukiLogRadiusLinearReflection a v) =
      suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) u v := by
  unfold suzukiLogRadiusLinearCompleteEnergy
  rw [suzukiLogRadiusLinearReflection_inner_map_map,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiLogRadiusLinearCompletionToL2_reflection,
    suzukiRSecondFiniteRadiusRemainderEnergy_reflection]

theorem suzukiRSecondLogRadiusLinearCompleteEnergy_even_odd_split
    {I : Type*} [DecidableEq I] (a : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (v : SuzukiLogRadiusLinearCompletion a) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift
        (suzukiRSecondSourceRemainderOperator a) v v =
      suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift
          (suzukiRSecondSourceRemainderOperator a)
          (suzukiLogRadiusLinearEvenProjector a v)
          (suzukiLogRadiusLinearEvenProjector a v) +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift
          (suzukiRSecondSourceRemainderOperator a)
          (suzukiLogRadiusLinearOddProjector a v)
          (suzukiLogRadiusLinearOddProjector a v) := by
  exact
    suzukiLogRadiusLinearCompleteEnergy_even_odd_split_of_reflectionInvariant
      a s scalar coefficient shift
      (suzukiRSecondSourceRemainderOperator a)
      (suzukiRSecondLogRadiusLinearCompleteEnergy_reflection
        a s scalar coefficient shift) v

end

end M100
end Experiments
end RiemannHypothesisProject
