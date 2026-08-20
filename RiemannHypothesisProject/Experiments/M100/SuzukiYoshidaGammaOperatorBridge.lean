import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointParityEvaluation
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDirichletIntegral

/-!
# Endpoint Yoshida modes in the finite-interval Gamma operator

This module removes the completion and restriction layers from the remaining
equation-(2.5) Gamma component.  The ambient endpoint `L²` classes restrict to
their literal normalized cosine, sine, and constant representatives on the
finite interval, so the global `r''` operator pairing is the corresponding
continuous finite-interval kernel pairing.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter Set MeasureTheory
open scoped ComplexConjugate ENNReal Topology

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiYoshidaGammaFiniteIntervalIsFiniteMeasureOnCompacts
    (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

/-- The normalized even Yoshida mode as a continuous function on `[-r,r]`.
The constant mode keeps its exceptional `1 / sqrt (2r)` normalization. -/
def suzukiYoshidaEvenFiniteIntervalContinuous
    (r : Real) (mode : Nat) : C(SuzukiFiniteInterval r, Complex) where
  toFun x :=
    if mode = 0 then
      ((Real.sqrt (2 * r))⁻¹ : Complex)
    else
      ((Real.sqrt r)⁻¹ : Complex) *
        (Real.cos ((mode : Real) * Real.pi * x.1 / r) : Complex)
  continuous_toFun := by
    by_cases hmode : mode = 0
    · simp only [hmode, ↓reduceIte]
      fun_prop
    · simp only [hmode, ↓reduceIte]
      fun_prop

/-- The normalized odd Yoshida mode as a continuous function on `[-r,r]`. -/
def suzukiYoshidaOddFiniteIntervalContinuous
    (r : Real) (mode : Nat) : C(SuzukiFiniteInterval r, Complex) where
  toFun x :=
    ((Real.sqrt r)⁻¹ : Complex) *
      (Real.sin ((mode : Real) * Real.pi * x.1 / r) : Complex)
  continuous_toFun := by
    fun_prop

/-- A general representative bridge for the restriction map.  It is useful
when the global representative has jump discontinuities at the endpoints but
its literal restriction to the closed interval is continuous. -/
theorem suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
    {a : Real} (u : SuzukiL2) (g : Real → Complex)
    (f : C(SuzukiFiniteInterval a, Complex))
    (hu : (u : Real → Complex) =ᵐ[volume] g)
    (hfg : ∀ x : SuzukiFiniteInterval a, g x.1 = f x) :
    suzukiL2RestrictToFiniteInterval a u =
      suzukiFiniteIntervalContinuousToL2 a f := by
  let s : Set Real := Icc (-a) a
  let restricted : Lp Complex 2 ((volume : Measure Real).restrict s) :=
    LpToLpRestrictCLM Real Complex Complex
      (volume : Measure Real) 2 s u
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
      restricted =ᵐ[(volume : Measure Real).restrict s] u := by
    simpa only [restricted] using
      (LpToLpRestrictCLM_coeFn
        (p := (2 : ENNReal)) (μ := (volume : Measure Real))
        Complex s u)
  have hrestrictComp :
      (fun x : SuzukiFiniteInterval a => restricted x.1) =ᵐ[volume]
        fun x => (u : Real → Complex) x.1 := by
    exact hmp.quasiMeasurePreserving.ae_eq_comp hrestrict
  have huRestricted :
      (fun x : SuzukiFiniteInterval a => (u : Real → Complex) x.1) =ᵐ[volume]
        fun x => g x.1 := by
    exact hmp.quasiMeasurePreserving.ae_eq_comp
      (ae_restrict_of_ae hu)
  have hf :
      (suzukiFiniteIntervalContinuousToL2 a f :
        SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      (f : SuzukiFiniteInterval a → Complex) := by
    simpa only [suzukiFiniteIntervalContinuousToL2] using
      (ContinuousMap.coeFn_toLp
        (𝕜 := Complex) (p := (2 : ENNReal))
        (volume : Measure (SuzukiFiniteInterval a)) f)
  apply Lp.ext
  filter_upwards [hcomp, hrestrictComp, huRestricted, hf] with
      x hxComp hxRestrict hxU hxF
  rw [suzukiL2RestrictToFiniteInterval,
    ContinuousLinearMap.comp_apply]
  exact hxComp.trans
    (hxRestrict.trans (hxU.trans ((hfg x).trans hxF.symm)))

theorem suzukiL2RestrictToFiniteInterval_yoshidaEven
    {r : Real} (hr : 0 < r) (mode : Nat) :
    suzukiL2RestrictToFiniteInterval r
        (suzukiYoshidaEvenL2 r hr mode) =
      suzukiFiniteIntervalContinuousToL2 r
        (suzukiYoshidaEvenFiniteIntervalContinuous r mode) := by
  by_cases hmode : mode = 0
  · subst mode
    apply suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
      (u := suzukiYoshidaEvenL2 r hr 0)
      (g := suzukiYoshidaEvenZeroFunction r)
      (f := suzukiYoshidaEvenFiniteIntervalContinuous r 0)
      (suzukiYoshidaEvenL2_coeFn_zero hr)
    intro x
    unfold suzukiYoshidaEvenZeroFunction
      suzukiYoshidaEvenFiniteIntervalContinuous
    simp [x.2]
  · apply suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
      (u := suzukiYoshidaEvenL2 r hr mode)
      (g := suzukiYoshidaEvenPositiveFunction r mode)
      (f := suzukiYoshidaEvenFiniteIntervalContinuous r mode)
      (suzukiYoshidaEvenL2_coeFn_of_pos hr (Nat.pos_of_ne_zero hmode))
    intro x
    unfold suzukiYoshidaEvenPositiveFunction
      suzukiYoshidaEvenFiniteIntervalContinuous
    simp [x.2, hmode]

theorem suzukiL2RestrictToFiniteInterval_yoshidaOdd
    {r : Real} (hr : 0 < r) (mode : Nat) :
    suzukiL2RestrictToFiniteInterval r
        (suzukiYoshidaOddL2 r hr mode) =
      suzukiFiniteIntervalContinuousToL2 r
        (suzukiYoshidaOddFiniteIntervalContinuous r mode) := by
  apply suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
    (u := suzukiYoshidaOddL2 r hr mode)
    (g := suzukiYoshidaOddFunction r mode)
    (f := suzukiYoshidaOddFiniteIntervalContinuous r mode)
    (suzukiYoshidaOddL2_coeFn hr mode)
  intro x
  unfold suzukiYoshidaOddFunction
    suzukiYoshidaOddFiniteIntervalContinuous
  simp [x.2]

/-- The global even-mode `r''` pairing is the literal finite-interval
continuous kernel pairing. -/
theorem inner_suzukiRSecondGlobalL2Operator_yoshidaEven
    {r : Real} (hr : 0 < r) (left right : Nat) :
    inner Complex
        (suzukiRSecondGlobalL2Operator r
          (suzukiYoshidaEvenL2 r hr left))
        (suzukiYoshidaEvenL2 r hr right) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiRSecondKernel continuous_suzukiRSecondKernel r
        (suzukiYoshidaEvenFiniteIntervalContinuous r left)
        (suzukiYoshidaEvenFiniteIntervalContinuous r right)) := by
  rw [inner_suzukiRSecondGlobalL2Operator,
    suzukiL2RestrictToFiniteInterval_yoshidaEven hr,
    suzukiL2RestrictToFiniteInterval_yoshidaEven hr,
    inner_suzukiRSecondFiniteIntervalL2Operator_continuous]

/-- The global odd-mode `r''` pairing is the literal finite-interval
continuous kernel pairing. -/
theorem inner_suzukiRSecondGlobalL2Operator_yoshidaOdd
    {r : Real} (hr : 0 < r) (left right : Nat) :
    inner Complex
        (suzukiRSecondGlobalL2Operator r
          (suzukiYoshidaOddL2 r hr left))
        (suzukiYoshidaOddL2 r hr right) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiRSecondKernel continuous_suzukiRSecondKernel r
        (suzukiYoshidaOddFiniteIntervalContinuous r left)
        (suzukiYoshidaOddFiniteIntervalContinuous r right)) := by
  rw [inner_suzukiRSecondGlobalL2Operator,
    suzukiL2RestrictToFiniteInterval_yoshidaOdd hr,
    suzukiL2RestrictToFiniteInterval_yoshidaOdd hr,
    inner_suzukiRSecondFiniteIntervalL2Operator_continuous]

theorem suzukiYoshidaGammaRemainderForm_even_eq_finiteIntervalPairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiRSecondKernel continuous_suzukiRSecondKernel
        suzukiProjectAStar
        (suzukiYoshidaEvenFiniteIntervalContinuous
          suzukiProjectAStar left)
        (suzukiYoshidaEvenFiniteIntervalContinuous
          suzukiProjectAStar right)) := by
  unfold suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  rw [suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  exact inner_suzukiRSecondGlobalL2Operator_yoshidaEven
    suzukiProjectAStar_pos left right

theorem suzukiYoshidaGammaRemainderForm_odd_eq_finiteIntervalPairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      conj (suzukiFiniteIntervalContinuousOperatorPairingComplex
        suzukiRSecondKernel continuous_suzukiRSecondKernel
        suzukiProjectAStar
        (suzukiYoshidaOddFiniteIntervalContinuous
          suzukiProjectAStar left)
        (suzukiYoshidaOddFiniteIntervalContinuous
          suzukiProjectAStar right)) := by
  unfold suzukiYoshidaGammaRemainderForm
    suzukiL2BoundedOperatorEnergy
  rw [suzukiYoshidaOddLinearCompletionOfSource_toL2,
    suzukiYoshidaOddLinearCompletionOfSource_toL2]
  exact inner_suzukiRSecondGlobalL2Operator_yoshidaOdd
    suzukiProjectAStar_pos left right

/-! ## Compact physical correlation model -/

/-- The `r''` kernel truncated to the difference set of `[-a,a]²`. -/
def suzukiRSecondCompactKernel (a t : Real) : Complex :=
  Set.indicator (Set.Icc (-(2 * a)) (2 * a))
    (fun s => (suzukiRSecondKernel s : Complex)) t

/-- Continuous kernel map used only to expose a uniform compact bound. -/
def suzukiRSecondCompactKernelContinuousMap (a : Real) :
    C(Set.Icc (-(2 * a)) (2 * a), Complex) where
  toFun t := (suzukiRSecondKernel t.1 : Complex)
  continuous_toFun :=
    Complex.continuous_ofReal.comp
      (continuous_suzukiRSecondKernel.comp continuous_subtype_val)

theorem norm_suzukiRSecondCompactKernel_le (a t : Real) :
    ‖suzukiRSecondCompactKernel a t‖ ≤
      ‖suzukiRSecondCompactKernelContinuousMap a‖ := by
  by_cases ht : t ∈ Set.Icc (-(2 * a)) (2 * a)
  · simp only [suzukiRSecondCompactKernel, Set.indicator_of_mem ht]
    exact ContinuousMap.norm_coe_le_norm
      (suzukiRSecondCompactKernelContinuousMap a) ⟨t, ht⟩
  · rw [suzukiRSecondCompactKernel, Set.indicator_of_notMem ht, norm_zero]
    exact norm_nonneg _

theorem integrable_suzukiRSecondCompactKernel (a : Real) :
    Integrable (suzukiRSecondCompactKernel a) := by
  change Integrable (Set.indicator (Set.Icc (-(2 * a)) (2 * a))
    (fun s => (suzukiRSecondKernel s : Complex)))
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (Complex.continuous_ofReal.comp continuous_suzukiRSecondKernel)
    |>.continuousOn.integrableOn_compact isCompact_Icc

theorem measurable_suzukiRSecondCompactKernel (a : Real) :
    Measurable (suzukiRSecondCompactKernel a) := by
  unfold suzukiRSecondCompactKernel
  exact (Complex.continuous_ofReal.comp continuous_suzukiRSecondKernel)
    |>.measurable.indicator measurableSet_Icc

theorem suzukiRSecondCompactKernel_neg (a t : Real) :
    suzukiRSecondCompactKernel a (-t) =
      suzukiRSecondCompactKernel a t := by
  have hmem :
      -t ∈ Set.Icc (-(2 * a)) (2 * a) ↔
        t ∈ Set.Icc (-(2 * a)) (2 * a) := by
    constructor <;> intro h
    · exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · exact ⟨by linarith [h.2], by linarith [h.1]⟩
  unfold suzukiRSecondCompactKernel
  by_cases ht : t ∈ Set.Icc (-(2 * a)) (2 * a)
  · rw [Set.indicator_of_mem (hmem.mpr ht), Set.indicator_of_mem ht]
    push_cast
    rw [suzukiRSecondKernel_neg]
  · have hnt : -t ∉ Set.Icc (-(2 * a)) (2 * a) :=
      fun h => ht (hmem.mp h)
    simp [ht, hnt]

theorem suzukiRSecondCompactKernel_sub_eq
    {a : Real} (_ha : 0 ≤ a)
    {x y : Real} (hx : x ∈ Set.Icc (-a) a)
    (hy : y ∈ Set.Icc (-a) a) :
    suzukiRSecondCompactKernel a (x - y) =
      (suzukiRSecondKernel (x - y) : Complex) := by
  rw [suzukiRSecondCompactKernel, Set.indicator_of_mem]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- Ordered physical `r''` pairing, written in the same endpoint translation
convention as the checked reciprocal-cutoff argument. -/
def suzukiRSecondCompactL2CrossCorrelationPairing
    (a : Real) (u v : SuzukiL2) : Complex :=
  ∫ t : Real, suzukiRSecondCompactKernel a t *
    conj (inner Complex (suzukiL2Translate t u) v)

theorem integrable_suzukiRSecondCompactL2CrossCorrelationIntegrand
    (a : Real) (u v : SuzukiL2) :
    Integrable (fun t : Real => suzukiRSecondCompactKernel a t *
      conj (inner Complex (suzukiL2Translate t u) v)) := by
  have hk := integrable_suzukiRSecondCompactKernel a
  have hfactor : AEStronglyMeasurable (fun t : Real =>
      conj (inner Complex (suzukiL2Translate t u) v)) :=
    (continuous_suzukiReciprocalCutoffL2CrossCorrelationFactor u v)
      |>.aestronglyMeasurable
  have hmul := hk.bdd_mul (c := ‖u‖ * ‖v‖) hfactor (by
    filter_upwards with t
    rw [Complex.norm_conj]
    exact (norm_inner_le_norm _ _).trans_eq
      (by rw [suzukiL2Translate_norm]))
  apply hmul.congr
  filter_upwards with t
  ring

/-- The compact physical pairing is jointly continuous along convergent
ambient `L²` sequences. -/
theorem tendsto_suzukiRSecondCompactL2CrossCorrelationPairing
    {a : Real} {uSeq vSeq : Nat → SuzukiL2} {u v : SuzukiL2}
    (hu : Tendsto uSeq atTop (𝓝 u))
    (hv : Tendsto vSeq atTop (𝓝 v)) :
    Tendsto
      (fun k => suzukiRSecondCompactL2CrossCorrelationPairing
        a (uSeq k) (vSeq k))
      atTop
      (𝓝 (suzukiRSecondCompactL2CrossCorrelationPairing a u v)) := by
  let U : Real := ‖u‖ + 1
  let V : Real := ‖v‖ + 1
  let majorant : Real → Real := fun t =>
    U * V * ‖suzukiRSecondCompactKernel a t‖
  have huBound : ∀ᶠ k in atTop, ‖uSeq k‖ ≤ U := by
    have hmem : Set.Iio U ∈ 𝓝 ‖u‖ := Iio_mem_nhds (by simp [U])
    exact hu.norm.eventually hmem |>.mono fun k hk => hk.le
  have hvBound : ∀ᶠ k in atTop, ‖vSeq k‖ ≤ V := by
    have hmem : Set.Iio V ∈ 𝓝 ‖v‖ := Iio_mem_nhds (by simp [V])
    exact hv.norm.eventually hmem |>.mono fun k hk => hk.le
  have hmajorant : Integrable majorant := by
    have hk := (integrable_suzukiRSecondCompactKernel a).norm.const_mul (U * V)
    simpa only [majorant, mul_assoc] using hk
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable
      (fun t : Real => suzukiRSecondCompactKernel a t *
        conj (inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k))) :=
    Filter.Eventually.of_forall fun k =>
      (integrable_suzukiRSecondCompactL2CrossCorrelationIntegrand
        a (uSeq k) (vSeq k)).aestronglyMeasurable
  have hbound : ∀ᶠ k in atTop, ∀ᵐ t ∂volume,
      ‖suzukiRSecondCompactKernel a t *
          conj (inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k))‖ ≤
        majorant t := by
    filter_upwards [huBound, hvBound] with k huk hvk
    filter_upwards with t
    rw [norm_mul, Complex.norm_conj]
    have hinner :
        ‖inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)‖ ≤
          U * V := by
      calc
        _ ≤ ‖suzukiL2Translate t (uSeq k)‖ * ‖vSeq k‖ :=
          norm_inner_le_norm _ _
        _ = ‖uSeq k‖ * ‖vSeq k‖ := by rw [suzukiL2Translate_norm]
        _ ≤ U * V := mul_le_mul huk hvk (norm_nonneg _)
          (add_nonneg (norm_nonneg _) zero_le_one)
    dsimp only [majorant]
    calc
      ‖suzukiRSecondCompactKernel a t‖ *
          ‖inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)‖ =
        ‖inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)‖ *
          ‖suzukiRSecondCompactKernel a t‖ := mul_comm _ _
      _ ≤ (U * V) * ‖suzukiRSecondCompactKernel a t‖ :=
        mul_le_mul_of_nonneg_right hinner (norm_nonneg _)
  have hlimit : ∀ᵐ t ∂volume,
      Tendsto
        (fun k => suzukiRSecondCompactKernel a t *
          conj (inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)))
        atTop
        (𝓝 (suzukiRSecondCompactKernel a t *
          conj (inner Complex (suzukiL2Translate t u) v))) := by
    filter_upwards with t
    have htu : Tendsto (fun k => suzukiL2Translate t (uSeq k))
        atTop (𝓝 (suzukiL2Translate t u)) :=
      (suzukiL2TranslateCLM t).continuous.tendsto u |>.comp hu
    have hinner : Tendsto
        (fun k => inner Complex
          (suzukiL2Translate t (uSeq k)) (vSeq k))
        atTop
        (𝓝 (inner Complex (suzukiL2Translate t u) v)) :=
      htu.inner hv
    exact tendsto_const_nhds.mul
      ((Complex.continuous_conj.tendsto _).comp hinner)
  unfold suzukiRSecondCompactL2CrossCorrelationPairing
  exact tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hlimit

/-- On a compactly supported smooth-core pair, the physical correlation
pairing is exactly the finite-square `r''(x-y)` polarization. -/
theorem suzukiRSecondCompactL2CrossCorrelationPairing_smoothCore
    {a : Real} (ha : 0 ≤ a) (u v : SuzukiSmoothCore a) :
    suzukiRSecondCompactL2CrossCorrelationPairing a
        (suzukiSmoothCoreToL2 u) (suzukiSmoothCoreToL2 v) =
      suzukiFiniteKernelPolarizationComplex
        suzukiRSecondKernel a u.1 v.1 := by
  let F : Real → Real → Complex := fun x y =>
    suzukiRSecondCompactKernel a (x - y) *
      u.1 y * conj (v.1 x)
  let G : Real → Real → Complex := fun y t =>
    suzukiRSecondCompactKernel a t *
      u.1 y * conj (v.1 (t + y))
  have hu : Integrable (u.1 : Real → Complex) := u.1.integrable
  have hv : Integrable (v.1 : Real → Complex) := v.1.integrable
  have hconjV : Integrable (fun x : Real => conj (v.1 x)) := by
    have hcomp := Complex.conjCLE.toContinuousLinearMap.integrable_comp hv
    change Integrable (fun x : Real => Complex.conjCLE (v.1 x))
    exact hcomp
  have hseparable : Integrable (fun p : Real × Real =>
      u.1 p.2 * conj (v.1 p.1)) (volume.prod volume) := by
    have hprod := hconjV.mul_prod hu
    apply hprod.congr
    filter_upwards with p
    ring
  have hFraw : Integrable (fun p : Real × Real =>
      suzukiRSecondCompactKernel a (p.1 - p.2) *
        (u.1 p.2 * conj (v.1 p.1))) (volume.prod volume) := by
    apply hseparable.bdd_mul
        (c := ‖suzukiRSecondCompactKernelContinuousMap a‖)
    · exact ((measurable_suzukiRSecondCompactKernel a).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.1 - p.2)))
          |>.aestronglyMeasurable
    · filter_upwards with p
      exact norm_suzukiRSecondCompactKernel_le a (p.1 - p.2)
  have hF : Integrable (fun p : Real × Real => F p.1 p.2)
      (volume.prod volume) := by
    simpa only [F, mul_assoc] using hFraw
  have hcoupled : Integrable (fun p : Real × Real =>
      u.1 p.1 * conj (v.1 (p.2 + p.1))) (volume.prod volume) := by
    let H : Real × Real → Complex := fun p => u.1 p.1 * conj (v.1 p.2)
    have hH : Integrable H := hu.mul_prod hconjV
    have hcomp :=
      (measurePreserving_prod_add_right
        (volume : Measure Real) (volume : Measure Real))
          |>.integrable_comp_of_integrable hH
    change Integrable (fun p : Real × Real =>
      u.1 p.1 * conj (v.1 (p.2 + p.1))) (volume.prod volume) at hcomp
    exact hcomp
  have hGraw : Integrable (fun p : Real × Real =>
      suzukiRSecondCompactKernel a p.2 *
        (u.1 p.1 * conj (v.1 (p.2 + p.1))))
      (volume.prod volume) := by
    apply hcoupled.bdd_mul
        (c := ‖suzukiRSecondCompactKernelContinuousMap a‖)
    · exact ((measurable_suzukiRSecondCompactKernel a).comp
        (by fun_prop : Measurable (fun p : Real × Real => p.2)))
          |>.aestronglyMeasurable
    · filter_upwards with p
      exact norm_suzukiRSecondCompactKernel_le a p.2
  have hG : Integrable (fun p : Real × Real => G p.1 p.2)
      (volume.prod volume) := by
    simpa only [G, mul_assoc] using hGraw
  have hsupportU : Function.support u.1 ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨(u.2 hx).1.le, (u.2 hx).2.le⟩
  have hsupportV : Function.support v.1 ⊆ Set.Icc (-a) a := by
    intro x hx
    exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hrestrict :
      (∫ p in suzukiFiniteSquare a, F p.1 p.2) =
        ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    by_cases hx : p.1 ∈ Set.Icc (-a) a
    · have hy : p.2 ∉ Set.Icc (-a) a := fun hy => hp ⟨hx, hy⟩
      have huy : u.1 p.2 = 0 := by
        by_contra hne
        exact hy (hsupportU hne)
      simp [F, huy]
    · have hvx : v.1 p.1 = 0 := by
        by_contra hne
        exact hx (hsupportV hne)
      simp [F, hvx]
  have hfiber (y : Real) :
      (∫ x : Real, F x y) = ∫ t : Real, G y t := by
    have htranslate := integral_sub_right_eq_self
      (fun t : Real => G y t) y (μ := volume)
    simpa only [F, G, sub_add_cancel] using htranslate
  have hphysicalNeg :
      (∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume)) =
        ∫ t : Real, suzukiRSecondCompactKernel a t *
          schwartzCrossCorrelation u.1 v.1 (-t) := by
    rw [MeasureTheory.integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G]
    rw [show (fun y : Real =>
        suzukiRSecondCompactKernel a t * u.1 y * conj (v.1 (t + y))) =
          fun y : Real => suzukiRSecondCompactKernel a t *
            (u.1 y * conj (v.1 (t + y))) by
        funext y
        ring]
    rw [integral_const_mul]
    apply congrArg (fun z : Complex => suzukiRSecondCompactKernel a t * z)
    unfold schwartzCrossCorrelation
    rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with y
    simp only [SchwartzLineTestFunction.star_apply]
    congr 2
    ring
  have hreflect := integral_neg_eq_self
    (f := fun t : Real => suzukiRSecondCompactKernel a t *
      schwartzCrossCorrelation u.1 v.1 t) volume
  have hphysical :
      (∫ t : Real, suzukiRSecondCompactKernel a t *
          schwartzCrossCorrelation u.1 v.1 (-t)) =
        ∫ t : Real, suzukiRSecondCompactKernel a t *
          schwartzCrossCorrelation u.1 v.1 t := by
    simpa only [suzukiRSecondCompactKernel_neg, neg_neg] using hreflect
  unfold suzukiRSecondCompactL2CrossCorrelationPairing
  calc
    (∫ t : Real, suzukiRSecondCompactKernel a t *
        conj (inner Complex
          (suzukiL2Translate t (suzukiSmoothCoreToL2 u))
          (suzukiSmoothCoreToL2 v))) =
        ∫ t : Real, suzukiRSecondCompactKernel a t *
          schwartzCrossCorrelation u.1 v.1 t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [schwartzCrossCorrelation_eq_conj_inner_suzukiL2Translate]
    _ = ∫ t : Real, suzukiRSecondCompactKernel a t *
          schwartzCrossCorrelation u.1 v.1 (-t) := hphysical.symm
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
    _ = suzukiFiniteKernelPolarizationComplex
        suzukiRSecondKernel a u.1 v.1 := by
      unfold suzukiFiniteKernelPolarizationComplex
      apply setIntegral_congr_fun
        (isCompact_suzukiFiniteSquare a).measurableSet
      intro p hp
      change F p.1 p.2 =
        (suzukiRSecondKernel (p.1 - p.2) : Complex) *
          u.1 p.2 * conj (v.1 p.1)
      dsimp only [F]
      rw [suzukiRSecondCompactKernel_sub_eq ha hp.1 hp.2]

/-- The canonical completed-form approximation converges in the physical
`L²` coordinate as well as in the graph completion. -/
theorem suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto_L2
    (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    Tendsto
      (fun k => suzukiSmoothCoreToL2
        (suzukiSmoothCoreLinearSubmoduleAsCore
          (suzukiYoshidaCorrectedSmoothCoreApproximation u k)))
      atTop
      (𝓝 (suzukiLogRadiusLinearCompletionToL2 u)) := by
  have hcompletion :=
    suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto u
  have hmapped :=
    (suzukiLogRadiusLinearCompletionToL2.continuous.tendsto u).comp
      hcompletion
  apply hmapped.congr'
  filter_upwards with k
  rw [Function.comp_apply,
    suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_toL2]

/-- On the full corrected completion, the bounded `r''` operator is the
continuous extension of the compact physical cross-correlation pairing. -/
theorem suzukiYoshidaGammaOperatorEnergy_eq_compactCorrelation
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v) =
      conj (suzukiRSecondCompactL2CrossCorrelationPairing
        suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v)) := by
  let uSeq : Nat → SuzukiL2 := fun k =>
    suzukiSmoothCoreToL2
      (suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiYoshidaCorrectedSmoothCoreApproximation u k))
  let vSeq : Nat → SuzukiL2 := fun k =>
    suzukiSmoothCoreToL2
      (suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiYoshidaCorrectedSmoothCoreApproximation v k))
  have hu : Tendsto uSeq atTop
      (𝓝 (suzukiLogRadiusLinearCompletionToL2 u)) := by
    simpa only [uSeq] using
      suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto_L2 u
  have hv : Tendsto vSeq atTop
      (𝓝 (suzukiLogRadiusLinearCompletionToL2 v)) := by
    simpa only [vSeq] using
      suzukiYoshidaCorrectedSmoothCoreApproximation_tendsto_L2 v
  have hoperator : Tendsto
      (fun k => suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (uSeq k) (vSeq k))
      atTop
      (𝓝 (suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v))) := by
    unfold suzukiL2BoundedOperatorEnergy
    exact ((suzukiRSecondGlobalL2Operator suzukiProjectAStar).continuous
      |>.tendsto (suzukiLogRadiusLinearCompletionToL2 u) |>.comp hu).inner hv
  have hcorrelation :=
    tendsto_suzukiRSecondCompactL2CrossCorrelationPairing
      (a := suzukiProjectAStar) hu hv
  have hconjCorrelation : Tendsto
      (fun k => conj (suzukiRSecondCompactL2CrossCorrelationPairing
        suzukiProjectAStar (uSeq k) (vSeq k)))
      atTop
      (𝓝 (conj (suzukiRSecondCompactL2CrossCorrelationPairing
        suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v)))) :=
    (Complex.continuous_conj.tendsto _).comp hcorrelation
  have hpointwise : ∀ k,
      suzukiL2BoundedOperatorEnergy
          (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
          (uSeq k) (vSeq k) =
        conj (suzukiRSecondCompactL2CrossCorrelationPairing
          suzukiProjectAStar (uSeq k) (vSeq k)) := by
    intro k
    let uk : SuzukiSmoothCore suzukiProjectAStar :=
      suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiYoshidaCorrectedSmoothCoreApproximation u k)
    let vk : SuzukiSmoothCore suzukiProjectAStar :=
      suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiYoshidaCorrectedSmoothCoreApproximation v k)
    change suzukiL2BoundedOperatorEnergy
        (suzukiRSecondGlobalL2Operator suzukiProjectAStar)
        (suzukiSmoothCoreToL2 uk) (suzukiSmoothCoreToL2 vk) =
      conj (suzukiRSecondCompactL2CrossCorrelationPairing
        suzukiProjectAStar (suzukiSmoothCoreToL2 uk)
          (suzukiSmoothCoreToL2 vk))
    unfold suzukiL2BoundedOperatorEnergy
    rw [inner_suzukiRSecondGlobalL2Operator_smoothCore,
      suzukiRSecondCompactL2CrossCorrelationPairing_smoothCore
        suzukiProjectAStar_pos.le]
  exact tendsto_nhds_unique hoperator
    (hconjCorrelation.congr'
      (Filter.Eventually.of_forall fun k => (hpointwise k).symm))

theorem suzukiYoshidaGammaRemainderForm_eq_compactCorrelation
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaGammaRemainderForm u v =
      conj (suzukiRSecondCompactL2CrossCorrelationPairing
        suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToL2 u)
        (suzukiLogRadiusLinearCompletionToL2 v)) := by
  unfold suzukiYoshidaGammaRemainderForm
  exact suzukiYoshidaGammaOperatorEnergy_eq_compactCorrelation u v

/-! ## Symmetric positive-interval reduction -/

theorem conj_suzukiRSecondCompactKernel (a t : Real) :
    conj (suzukiRSecondCompactKernel a t) =
      suzukiRSecondCompactKernel a t := by
  unfold suzukiRSecondCompactKernel
  by_cases ht : t ∈ Set.Icc (-(2 * a)) (2 * a)
  · simp [Set.indicator_of_mem ht]
  · simp [Set.indicator_of_notMem ht]

theorem suzukiL2SymmetricTranslationEnergy_eq_inner_add_neg
    (t : Real) (u v : SuzukiL2) :
    suzukiL2SymmetricTranslationEnergy t u v =
      inner Complex (suzukiL2Translate t u) v +
        inner Complex (suzukiL2Translate (-t) u) v := by
  unfold suzukiL2SymmetricTranslationEnergy
  rw [suzukiL2TranslateCLM_apply, suzukiL2TranslateCLM_apply,
    inner_suzukiL2Translate_neg_eq_inner_translate_right]

/-- A continuous even factor against the compact `r''` kernel reduces from
the whole line to twice the positive difference interval. -/
theorem integral_suzukiRSecondCompactKernel_mul_even
    {a : Real} (ha : 0 ≤ a) (g : Real → Complex)
    (hg : Continuous g) (hgEven : ∀ t, g (-t) = g t) :
    (∫ t : Real, suzukiRSecondCompactKernel a t * g t) =
      2 * ∫ t in (0 : Real)..2 * a,
        (suzukiRSecondKernel t : Complex) * g t := by
  let f : Real → Complex := fun t =>
    (suzukiRSecondKernel t : Complex) * g t
  have hf : Continuous f :=
    (Complex.continuous_ofReal.comp continuous_suzukiRSecondKernel).mul hg
  have hleft : IntervalIntegrable f volume (-(2 * a)) 0 :=
    hf.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume 0 (2 * a) :=
    hf.intervalIntegrable _ _
  have hcompact :
      (∫ t : Real, suzukiRSecondCompactKernel a t * g t) =
        ∫ t in Set.Icc (-(2 * a)) (2 * a), f t := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    unfold f suzukiRSecondCompactKernel
    by_cases ht : t ∈ Set.Icc (-(2 * a)) (2 * a)
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  have hsetInterval :
      (∫ t in Set.Icc (-(2 * a)) (2 * a), f t) =
        ∫ t in (-(2 * a))..(2 * a), f t := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith)]
  have hneg :
      (∫ t in (-(2 * a))..0, f t) =
        ∫ t in (0 : Real)..2 * a, f t := by
    have hcomp := intervalIntegral.integral_comp_neg
      (f := f) (a := (0 : Real)) (b := 2 * a)
    calc
      (∫ t in (-(2 * a))..0, f t) =
          ∫ t in (0 : Real)..2 * a, f (-t) := by
        simpa only [neg_zero] using hcomp.symm
      _ = ∫ t in (0 : Real)..2 * a, f t := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [f]
        rw [suzukiRSecondKernel_neg, hgEven]
  rw [hcompact, hsetInterval,
    ← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hneg]
  dsimp only [f]
  ring

/-- Conjugating the ordered physical pairing produces the positive-interval
`r''` pairing against the symmetric translation energy. -/
theorem conj_suzukiRSecondCompactL2CrossCorrelationPairing_eq_interval
    (u v : SuzukiL2) :
    conj (suzukiRSecondCompactL2CrossCorrelationPairing
      suzukiProjectAStar u v) =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t u v := by
  let A : Real → Complex := fun t =>
    suzukiRSecondCompactKernel suzukiProjectAStar t *
      conj (inner Complex (suzukiL2Translate t u) v)
  let B : Real → Complex := fun t =>
    suzukiRSecondCompactKernel suzukiProjectAStar t *
      suzukiL2SymmetricTranslationEnergy t u v
  have hA : Integrable A := by
    simpa only [A] using
      integrable_suzukiRSecondCompactL2CrossCorrelationIntegrand
        suzukiProjectAStar u v
  have hAneg : Integrable (fun t : Real => A (-t)) := hA.comp_neg
  have hconjA : Integrable (fun t : Real => conj (A t)) := by
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hA
  have hconjAneg : Integrable (fun t : Real => conj (A (-t))) := by
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hAneg
  have hnegIntegral : (∫ t : Real, A (-t)) = ∫ t : Real, A t :=
    integral_neg_eq_self A volume
  have hBpointwise : ∀ t, B t = conj (A t) + conj (A (-t)) := by
    intro t
    unfold A B
    simp only [map_mul, Complex.conj_conj]
    rw [
      conj_suzukiRSecondCompactKernel,
      conj_suzukiRSecondCompactKernel,
      suzukiRSecondCompactKernel_neg,
      suzukiL2SymmetricTranslationEnergy_eq_inner_add_neg]
    ring
  have hBIntegral :
      (∫ t : Real, B t) =
        2 * conj (∫ t : Real, A t) := by
    calc
      (∫ t : Real, B t) =
          ∫ t : Real, (conj (A t) + conj (A (-t))) := by
        apply integral_congr_ae
        filter_upwards with t
        exact hBpointwise t
      _ = (∫ t : Real, conj (A t)) +
          ∫ t : Real, conj (A (-t)) :=
        integral_add hconjA hconjAneg
      _ = conj (∫ t : Real, A t) +
          conj (∫ t : Real, A (-t)) := by
        rw [integral_conj, integral_conj]
      _ = 2 * conj (∫ t : Real, A t) := by
        rw [hnegIntegral]
        ring
  have hEvenIntegral := integral_suzukiRSecondCompactKernel_mul_even
    suzukiProjectAStar_pos.le
    (fun t => suzukiL2SymmetricTranslationEnergy t u v)
    (continuous_suzukiL2SymmetricTranslationEnergy_orbit u v)
    (fun t => suzukiL2SymmetricTranslationEnergy_neg t u v)
  change conj (∫ t : Real, A t) = _
  change (∫ t : Real, B t) = _ at hEvenIntegral
  rw [hBIntegral] at hEvenIntegral
  linear_combination (1 / 2 : Complex) * hEvenIntegral

theorem suzukiYoshidaGammaRemainderForm_eq_symmetricInterval
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaGammaRemainderForm u v =
      ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (suzukiLogRadiusLinearCompletionToL2 u)
            (suzukiLogRadiusLinearCompletionToL2 v) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_compactCorrelation,
    conj_suzukiRSecondCompactL2CrossCorrelationPairing_eq_interval]

/-! ## Endpoint parity correlations -/

theorem suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_even
    {t : Real} {u v : SuzukiL2} {c : Real}
    (hu : SuzukiL2Even u) (hv : SuzukiL2Even v)
    (hinner : inner Complex (suzukiL2Translate t u) v = (c : Complex)) :
    suzukiL2SymmetricTranslationEnergy t u v =
      ((2 * c : Real) : Complex) := by
  have hreverse :
      inner Complex u (suzukiL2Translate t v) = (c : Complex) := by
    calc
      _ = inner Complex (suzukiL2Translate (-t) u) v := by
        change inner Complex u (suzukiL2TranslateCLM t v) =
          inner Complex (suzukiL2TranslateCLM (-t) u) v
        rw [← suzukiL2Translate_adjoint,
          ContinuousLinearMap.adjoint_inner_left]
      _ = inner Complex
          (suzukiL2Reflection
            (suzukiL2Translate t (suzukiL2Reflection u))) v := by
        rw [suzukiL2Reflection_translate_reflection]
      _ = inner Complex
          (suzukiL2Reflection (suzukiL2Translate t u))
          (suzukiL2Reflection v) := by rw [hu, hv]
      _ = inner Complex (suzukiL2Translate t u) v :=
        suzukiL2Reflection.inner_map_map _ _
      _ = (c : Complex) := hinner
  unfold suzukiL2SymmetricTranslationEnergy
  simp only [suzukiL2TranslateCLM_apply]
  rw [hinner, hreverse]
  push_cast
  ring

theorem suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_odd
    {t : Real} {u v : SuzukiL2} {c : Real}
    (hu : SuzukiL2Odd u) (hv : SuzukiL2Odd v)
    (hinner : inner Complex (suzukiL2Translate t u) v = (c : Complex)) :
    suzukiL2SymmetricTranslationEnergy t u v =
      ((2 * c : Real) : Complex) := by
  have hreverse :
      inner Complex u (suzukiL2Translate t v) = (c : Complex) := by
    have htranslateNeg :
        suzukiL2Translate t (-u) = -suzukiL2Translate t u := by
      change suzukiL2TranslateCLM t (-u) = -suzukiL2TranslateCLM t u
      exact map_neg (suzukiL2TranslateCLM t) u
    calc
      _ = inner Complex (suzukiL2Translate (-t) u) v := by
        change inner Complex u (suzukiL2TranslateCLM t v) =
          inner Complex (suzukiL2TranslateCLM (-t) u) v
        rw [← suzukiL2Translate_adjoint,
          ContinuousLinearMap.adjoint_inner_left]
      _ = inner Complex
          (suzukiL2Reflection
            (suzukiL2Translate t (suzukiL2Reflection u))) v := by
        rw [suzukiL2Reflection_translate_reflection]
      _ = inner Complex
          (suzukiL2Reflection (suzukiL2Translate t u))
          (suzukiL2Reflection v) := by
        rw [hu, hv, htranslateNeg, map_neg]
        simp
      _ = inner Complex (suzukiL2Translate t u) v :=
        suzukiL2Reflection.inner_map_map _ _
      _ = (c : Complex) := hinner
  unfold suzukiL2SymmetricTranslationEnergy
  simp only [suzukiL2TranslateCLM_apply]
  rw [hinner, hreverse]
  push_cast
  ring

theorem suzukiL2SymmetricTranslationEnergy_yoshidaEvenPositive_offDiagonal
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - left
    let total := left + right
    suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaEvenL2 r hr left)
        (suzukiYoshidaEvenL2 r hr right) =
      ((2 * (1 / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference +
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total)) : Real) : Complex) := by
  dsimp only
  exact suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_even
    (suzukiYoshidaEvenL2_even hr left)
    (suzukiYoshidaEvenL2_even hr right)
    (inner_suzukiL2Translate_evenPositive_offDiagonal_eq_correlation
      hr ht0 ht left right hleft hlt)

theorem suzukiL2SymmetricTranslationEnergy_yoshidaEvenZero_offDiagonal
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (right : Nat) (hright : 0 < right) :
    let leftFrequency := (0 : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - 0
    let total := 0 + right
    suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaEvenL2 r hr 0)
        (suzukiYoshidaEvenL2 r hr right) =
      ((2 * ((Real.sqrt 2)⁻¹ * (1 / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference +
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total))) : Real) : Complex) := by
  dsimp only
  exact suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_even
    (suzukiYoshidaEvenL2_even hr 0)
    (suzukiYoshidaEvenL2_even hr right)
    (inner_suzukiL2Translate_evenZero_offDiagonal_eq_correlation
      hr ht0 ht right hright)

theorem suzukiL2SymmetricTranslationEnergy_yoshidaOdd_offDiagonal
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - left
    let total := left + right
    suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaOddL2 r hr left)
        (suzukiYoshidaOddL2 r hr right) =
      ((2 * (1 / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference -
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total)) : Real) : Complex) := by
  dsimp only
  exact suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_odd
    (suzukiYoshidaOddL2_odd hr left)
    (suzukiYoshidaOddL2_odd hr right)
    (inner_suzukiL2Translate_odd_offDiagonal_eq_correlation
      hr ht0 ht left right hleft hlt)

theorem suzukiL2SymmetricTranslationEnergy_yoshidaEvenPositive_diagonal
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (mode : Nat) (hmode : 0 < mode) :
    let w := (mode : Real) * Real.pi / r
    suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaEvenL2 r hr mode)
        (suzukiYoshidaEvenL2 r hr mode) =
      ((2 * (((2 * r - t) * Real.cos (w * t) -
        Real.sin (w * t) / w) / (2 * r)) : Real) : Complex) := by
  dsimp only
  exact suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_even
    (suzukiYoshidaEvenL2_even hr mode)
    (suzukiYoshidaEvenL2_even hr mode)
    (inner_suzukiL2Translate_evenPositive_eq_correlation
      hr ht0 ht mode hmode)

theorem suzukiL2SymmetricTranslationEnergy_yoshidaEvenZero_diagonal
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r) :
    suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaEvenL2 r hr 0)
        (suzukiYoshidaEvenL2 r hr 0) =
      ((2 * (1 - t / (2 * r)) : Real) : Complex) := by
  exact suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_even
    (suzukiYoshidaEvenL2_even hr 0)
    (suzukiYoshidaEvenL2_even hr 0)
    (inner_suzukiL2Translate_evenZero_eq_correlation hr ht0 ht)

theorem suzukiL2SymmetricTranslationEnergy_yoshidaOdd_diagonal
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (mode : Nat) (hmode : 0 < mode) :
    let w := (mode : Real) * Real.pi / r
    suzukiL2SymmetricTranslationEnergy t
        (suzukiYoshidaOddL2 r hr mode)
        (suzukiYoshidaOddL2 r hr mode) =
      ((2 * (((2 * r - t) * Real.cos (w * t) +
        Real.sin (w * t) / w) / (2 * r)) : Real) : Complex) := by
  dsimp only
  exact suzukiL2SymmetricTranslationEnergy_eq_twice_of_real_inner_of_odd
    (suzukiYoshidaOddL2_odd hr mode)
    (suzukiYoshidaOddL2_odd hr mode)
    (inner_suzukiL2Translate_odd_eq_correlation
      hr ht0 ht mode hmode)

private theorem inner_yoshidaExponential_suzukiL2Translate_eq_zero_of_two_mul_lt
    {r t : Real} (hr : 0 < r) (ht : 2 * r < t) (m n : Int) :
    inner Complex
      (suzukiYoshidaExponentialL2 r hr m)
      (suzukiL2Translate t (suzukiYoshidaExponentialL2 r hr n)) = 0 := by
  rw [← inner_conj_symm,
    inner_suzukiL2Translate_yoshidaExponential_eq_zero_of_two_mul_lt
      hr ht n m]
  simp

theorem suzukiL2SymmetricTranslationEnergy_yoshidaEven_eq_zero_of_two_mul_lt
    {r t : Real} (hr : 0 < r) (ht : 2 * r < t) (mode : Nat) :
    suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaEvenL2 r hr mode)
      (suzukiYoshidaEvenL2 r hr mode) = 0 := by
  unfold suzukiYoshidaEvenL2
  split_ifs with hmode
  · exact suzukiL2SymmetricTranslationEnergy_yoshidaExponential_eq_zero_of_two_mul_lt
      hr ht 0 0
  · unfold suzukiL2SymmetricTranslationEnergy
    simp only [suzukiL2TranslateCLM_apply, map_smul, map_add,
      inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    simp_rw [inner_suzukiL2Translate_yoshidaExponential_eq_zero_of_two_mul_lt
      hr ht,
      inner_yoshidaExponential_suzukiL2Translate_eq_zero_of_two_mul_lt
        hr ht]
    simp

theorem suzukiL2SymmetricTranslationEnergy_yoshidaOdd_eq_zero_of_two_mul_lt
    {r t : Real} (hr : 0 < r) (ht : 2 * r < t) (mode : Nat) :
    suzukiL2SymmetricTranslationEnergy t
      (suzukiYoshidaOddL2 r hr mode)
      (suzukiYoshidaOddL2 r hr mode) = 0 := by
  unfold suzukiYoshidaOddL2 suzukiL2SymmetricTranslationEnergy
  simp only [suzukiL2TranslateCLM_apply, map_smul, map_sub,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  simp_rw [inner_suzukiL2Translate_yoshidaExponential_eq_zero_of_two_mul_lt
    hr ht,
    inner_yoshidaExponential_suzukiL2Translate_eq_zero_of_two_mul_lt
      hr ht]
  simp

/-! ## Smooth-transform convolution identities -/

/-- The positive-interval sine transform of Suzuki's smooth `r''` kernel. -/
def suzukiDF6D4RSecondSineIntegral (mode : Nat) : Real :=
  ∫ t in (0 : Real)..2 * suzukiProjectAStar,
    suzukiRSecondKernel t *
      Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t)

/-- On every positive mode, the comparison-plus-prime transform differs from
the complete DF6D4 transform by twice the smooth `r''` sine integral. -/
theorem suzukiDF6D4Comparison_add_prime_sub_complete_eq_rSecond
    (mode : Nat) (hmode : 0 < mode) :
    suzukiDF6D4ComparisonSineTransform mode +
        suzukiDF6D4PrimeSineTransform mode -
      suzukiDF6D4CompleteSineTransform mode =
        2 * suzukiDF6D4RSecondSineIntegral mode := by
  have hsmooth := suzukiDF6D4SmoothTransformDifference_eq_integral mode hmode
  unfold suzukiDF6D4SmoothTransformDifference at hsmooth
  unfold suzukiDF6D4RSecondSineIntegral
  linear_combination -hsmooth

theorem intervalIntegrable_suzukiDF6D4RSecondSineIntegral (mode : Nat) :
    IntervalIntegrable
      (fun t : Real => suzukiRSecondKernel t *
        Real.sin (((mode : Real) * Real.pi / suzukiProjectAStar) * t))
      volume 0 (2 * suzukiProjectAStar) := by
  exact (continuous_suzukiRSecondKernel.mul
    (Real.continuous_sin.comp
      (continuous_const.mul continuous_id))).intervalIntegrable
        (μ := volume) 0 (2 * suzukiProjectAStar)

/-- Linearity formula used to turn the endpoint translation correlations into
the independent DF6D4 convolution coefficients. -/
theorem integral_suzukiRSecondKernel_mul_linear_sines
    (left right : Nat) (differenceCoefficient totalCoefficient : Real) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      suzukiRSecondKernel t *
        (differenceCoefficient *
            (Real.sin (((right : Real) * Real.pi / suzukiProjectAStar) * t) -
              Real.sin (((left : Real) * Real.pi / suzukiProjectAStar) * t)) +
          totalCoefficient *
            (Real.sin (((left : Real) * Real.pi / suzukiProjectAStar) * t) +
              Real.sin (((right : Real) * Real.pi / suzukiProjectAStar) * t)))) =
      differenceCoefficient *
          (suzukiDF6D4RSecondSineIntegral right -
            suzukiDF6D4RSecondSineIntegral left) +
        totalCoefficient *
          (suzukiDF6D4RSecondSineIntegral left +
            suzukiDF6D4RSecondSineIntegral right) := by
  have hleft := intervalIntegrable_suzukiDF6D4RSecondSineIntegral left
  have hright := intervalIntegrable_suzukiDF6D4RSecondSineIntegral right
  calc
    _ = ∫ t in (0 : Real)..2 * suzukiProjectAStar,
        differenceCoefficient *
            (suzukiRSecondKernel t *
                Real.sin (((right : Real) * Real.pi / suzukiProjectAStar) * t) -
              suzukiRSecondKernel t *
                Real.sin (((left : Real) * Real.pi / suzukiProjectAStar) * t)) +
          totalCoefficient *
            (suzukiRSecondKernel t *
                Real.sin (((left : Real) * Real.pi / suzukiProjectAStar) * t) +
              suzukiRSecondKernel t *
                Real.sin (((right : Real) * Real.pi / suzukiProjectAStar) * t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = differenceCoefficient *
          ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
              suzukiRSecondKernel t *
                Real.sin (((right : Real) * Real.pi / suzukiProjectAStar) * t)) -
            ∫ t in (0 : Real)..2 * suzukiProjectAStar,
              suzukiRSecondKernel t *
                Real.sin (((left : Real) * Real.pi / suzukiProjectAStar) * t)) +
        totalCoefficient *
          ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
              suzukiRSecondKernel t *
                Real.sin (((left : Real) * Real.pi / suzukiProjectAStar) * t)) +
            ∫ t in (0 : Real)..2 * suzukiProjectAStar,
              suzukiRSecondKernel t *
                Real.sin (((right : Real) * Real.pi / suzukiProjectAStar) * t)) := by
      rw [intervalIntegral.integral_add
          ((hright.sub hleft).const_mul differenceCoefficient)
          ((hleft.add hright).const_mul totalCoefficient),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub hright hleft,
        intervalIntegral.integral_add hleft hright]
    _ = _ := by rfl

theorem suzuki_linearConvolution_difference
    (complete comparison prime smooth : Nat → Real)
    (prefactor differenceCoefficient totalCoefficient : Real)
    (left right : Nat)
    (hleft : comparison left + prime left - complete left = 2 * smooth left)
    (hright : comparison right + prime right - complete right = 2 * smooth right) :
    prefactor *
          (differenceCoefficient * (comparison right - comparison left) +
            totalCoefficient * (comparison left + comparison right)) +
        prefactor *
          (differenceCoefficient * (prime right - prime left) +
            totalCoefficient * (prime left + prime right)) -
      prefactor *
          (differenceCoefficient * (complete right - complete left) +
            totalCoefficient * (complete left + complete right)) =
        prefactor *
          (differenceCoefficient * (2 * smooth right - 2 * smooth left) +
            totalCoefficient * (2 * smooth left + 2 * smooth right)) := by
  linear_combination
    prefactor * (differenceCoefficient + totalCoefficient) * hright +
      prefactor * (-differenceCoefficient + totalCoefficient) * hleft

theorem suzukiDF6D4EvenOffDiagonalGammaCombination_eq_rSecond
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    suzukiDF6D4ComparisonEvenOffDiagonal left right +
        suzukiDF6D4EvenOffDiagonalPrimeTerm left right -
      suzukiDF6D4EvenOffDiagonal left right =
    ((1 / 2 : Real) * suzukiDF6D4EvenModeScale left *
        suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
      ((((suzukiDF6D4AlternatingSign (right - left) /
          ((right - left : Nat) : Rat) : Rat) : Real) *
          (2 * suzukiDF6D4RSecondSineIntegral right -
            2 * suzukiDF6D4RSecondSineIntegral left)) +
        (((suzukiDF6D4AlternatingSign (left + right) /
          ((left : Rat) + (right : Rat)) : Rat) : Real) *
          (2 * suzukiDF6D4RSecondSineIntegral left +
            2 * suzukiDF6D4RSecondSineIntegral right))) := by
  unfold suzukiDF6D4ComparisonEvenOffDiagonal
    suzukiDF6D4EvenOffDiagonalPrimeTerm suzukiDF6D4EvenOffDiagonal
  dsimp only
  exact suzuki_linearConvolution_difference
    suzukiDF6D4CompleteSineTransform
    suzukiDF6D4ComparisonSineTransform
    suzukiDF6D4PrimeSineTransform
    suzukiDF6D4RSecondSineIntegral _ _ _ left right
    (suzukiDF6D4Comparison_add_prime_sub_complete_eq_rSecond left hleft)
    (suzukiDF6D4Comparison_add_prime_sub_complete_eq_rSecond right
      (hleft.trans hlt))

theorem suzukiDF6D4EvenZeroOffDiagonalGammaCombination_eq_rSecond
    (right : Nat) (hright : 0 < right) :
    suzukiDF6D4ComparisonEvenOffDiagonal 0 right +
        suzukiDF6D4EvenOffDiagonalPrimeTerm 0 right -
      suzukiDF6D4EvenOffDiagonal 0 right =
    ((1 / 2 : Real) * suzukiDF6D4EvenModeScale 0 *
        suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
      ((((suzukiDF6D4AlternatingSign right / (right : Rat) : Rat) : Real) *
          (2 * suzukiDF6D4RSecondSineIntegral right)) +
        (((suzukiDF6D4AlternatingSign right / (right : Rat) : Rat) : Real) *
          (2 * suzukiDF6D4RSecondSineIntegral right))) := by
  have hrightTransform :=
    suzukiDF6D4Comparison_add_prime_sub_complete_eq_rSecond right hright
  unfold suzukiDF6D4ComparisonEvenOffDiagonal
    suzukiDF6D4EvenOffDiagonalPrimeTerm suzukiDF6D4EvenOffDiagonal
  simp only [Nat.sub_zero, Nat.zero_add, Nat.cast_zero, zero_add]
  linear_combination
    ((1 / 2 : Real) * suzukiDF6D4EvenModeScale 0 *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
        (2 * (((suzukiDF6D4AlternatingSign right / (right : Rat) : Rat) : Real))) *
          hrightTransform

theorem suzukiDF6D4OddOffDiagonalGammaCombination_eq_rSecond
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    suzukiDF6D4ComparisonOddOffDiagonal left right +
        suzukiDF6D4OddOffDiagonalPrimeTerm left right -
      suzukiDF6D4OddOffDiagonal left right =
    ((1 / 2 : Real) * Real.pi⁻¹) *
      ((((suzukiDF6D4AlternatingSign (right - left) /
          ((right - left : Nat) : Rat) : Rat) : Real) *
          (2 * suzukiDF6D4RSecondSineIntegral right -
            2 * suzukiDF6D4RSecondSineIntegral left)) +
        ((-(suzukiDF6D4AlternatingSign (left + right) /
          ((left : Rat) + (right : Rat))) : Rat) : Real) *
          (2 * suzukiDF6D4RSecondSineIntegral left +
            2 * suzukiDF6D4RSecondSineIntegral right)) := by
  unfold suzukiDF6D4ComparisonOddOffDiagonal
    suzukiDF6D4OddOffDiagonalPrimeTerm suzukiDF6D4OddOffDiagonal
  dsimp only
  exact suzuki_linearConvolution_difference
    suzukiDF6D4CompleteSineTransform
    suzukiDF6D4ComparisonSineTransform
    suzukiDF6D4PrimeSineTransform
    suzukiDF6D4RSecondSineIntegral _ _ _ left right
    (suzukiDF6D4Comparison_add_prime_sub_complete_eq_rSecond left hleft)
    (suzukiDF6D4Comparison_add_prime_sub_complete_eq_rSecond right
      (hleft.trans hlt))

/-! ## Off-diagonal Gamma component evaluations -/

theorem suzukiYoshidaGammaRemainderForm_evenPositive_offDiagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      ((suzukiDF6D4ComparisonEvenOffDiagonal left right +
        suzukiDF6D4EvenOffDiagonalPrimeTerm left right -
        suzukiDF6D4EvenOffDiagonal left right : Real) : Complex) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_symmetricInterval,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiDF6D4EvenOffDiagonalGammaCombination_eq_rSecond left right hleft hlt]
  unfold suzukiDF6D4EvenModeScale
  rw [if_neg hleft.ne', if_neg (hleft.trans hlt).ne']
  let differenceCoefficient : Real :=
    -((-1 : Real) ^ (right - left)) / (right - left)
  let totalCoefficient : Real :=
    -((-1 : Real) ^ (left + right)) / (left + right)
  calc
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos left)
            (suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos right)) =
      ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiRSecondKernel t *
          (2 * (1 / (2 * Real.pi) *
            (differenceCoefficient *
                (Real.sin (((right : Real) * Real.pi /
                    suzukiProjectAStar) * t) -
                  Real.sin (((left : Real) * Real.pi /
                    suzukiProjectAStar) * t)) +
              totalCoefficient *
                (Real.sin (((left : Real) * Real.pi /
                    suzukiProjectAStar) * t) +
                  Real.sin (((right : Real) * Real.pi /
                    suzukiProjectAStar) * t))))) : Real) : Complex) := by
        rw [← intervalIntegral.integral_ofReal]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le
          (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)] at ht
        dsimp only
        rw [suzukiL2SymmetricTranslationEnergy_yoshidaEvenPositive_offDiagonal
          suzukiProjectAStar_pos ht.1 ht.2 left right hleft hlt]
        unfold differenceCoefficient totalCoefficient
        push_cast
        rw [Nat.cast_sub hlt.le]
        ring
    _ = _ := by
      norm_cast
      calc
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t *
            (2 * (1 / (2 * Real.pi) *
              (differenceCoefficient *
                  (Real.sin (((right : Real) * Real.pi /
                      suzukiProjectAStar) * t) -
                    Real.sin (((left : Real) * Real.pi /
                      suzukiProjectAStar) * t)) +
                totalCoefficient *
                  (Real.sin (((left : Real) * Real.pi /
                      suzukiProjectAStar) * t) +
                    Real.sin (((right : Real) * Real.pi /
                      suzukiProjectAStar) * t)))))) =
            (2 * (1 / (2 * Real.pi))) *
              (∫ t in (0 : Real)..2 * suzukiProjectAStar,
                suzukiRSecondKernel t *
                  (differenceCoefficient *
                      (Real.sin (((right : Real) * Real.pi /
                          suzukiProjectAStar) * t) -
                        Real.sin (((left : Real) * Real.pi /
                          suzukiProjectAStar) * t)) +
                    totalCoefficient *
                      (Real.sin (((left : Real) * Real.pi /
                          suzukiProjectAStar) * t) +
                        Real.sin (((right : Real) * Real.pi /
                          suzukiProjectAStar) * t)))) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = _ := by
          rw [integral_suzukiRSecondKernel_mul_linear_sines]
          unfold differenceCoefficient totalCoefficient
          push_cast
          rw [suzukiDF6D4AlternatingSign_cast_real,
            suzukiDF6D4AlternatingSign_cast_real]
          rw [Nat.cast_sub hlt.le]
          ring

theorem suzukiYoshidaGammaRemainderForm_evenZero_offDiagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (right : Nat) (hright : 0 < right) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      ((suzukiDF6D4ComparisonEvenOffDiagonal 0 right +
        suzukiDF6D4EvenOffDiagonalPrimeTerm 0 right -
        suzukiDF6D4EvenOffDiagonal 0 right : Real) : Complex) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_symmetricInterval,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiDF6D4EvenZeroOffDiagonalGammaCombination_eq_rSecond right hright]
  unfold suzukiDF6D4EvenModeScale
  rw [if_pos rfl, if_neg hright.ne']
  let coefficient : Real := -((-1 : Real) ^ right) / right
  calc
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos 0)
            (suzukiYoshidaEvenL2 suzukiProjectAStar
              suzukiProjectAStar_pos right)) =
      ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiRSecondKernel t *
          (2 * ((Real.sqrt 2)⁻¹ * (1 / (2 * Real.pi) *
            (coefficient *
                (Real.sin (((right : Real) * Real.pi /
                    suzukiProjectAStar) * t) -
                  Real.sin (((0 : Real) * Real.pi /
                    suzukiProjectAStar) * t)) +
              coefficient *
                (Real.sin (((0 : Real) * Real.pi /
                    suzukiProjectAStar) * t) +
                  Real.sin (((right : Real) * Real.pi /
                    suzukiProjectAStar) * t)))))) : Real) : Complex) := by
        rw [← intervalIntegral.integral_ofReal]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le
          (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)] at ht
        dsimp only
        rw [suzukiL2SymmetricTranslationEnergy_yoshidaEvenZero_offDiagonal
          suzukiProjectAStar_pos ht.1 ht.2 right hright]
        simp only [Nat.sub_zero, Nat.zero_add]
        unfold coefficient
        push_cast
        ring
    _ = _ := by
      norm_cast
      calc
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t *
            (2 * ((Real.sqrt 2)⁻¹ * (1 / (2 * Real.pi) *
              (coefficient *
                  (Real.sin (((right : Real) * Real.pi /
                      suzukiProjectAStar) * t) -
                    Real.sin (((0 : Real) * Real.pi /
                      suzukiProjectAStar) * t)) +
                coefficient *
                  (Real.sin (((0 : Real) * Real.pi /
                      suzukiProjectAStar) * t) +
                    Real.sin (((right : Real) * Real.pi /
                      suzukiProjectAStar) * t)))))) =
            (2 * (Real.sqrt 2)⁻¹ * (1 / (2 * Real.pi))) *
              (∫ t in (0 : Real)..2 * suzukiProjectAStar,
                suzukiRSecondKernel t *
                  (coefficient *
                      (Real.sin (((right : Real) * Real.pi /
                          suzukiProjectAStar) * t) -
                        Real.sin (((0 : Real) * Real.pi /
                          suzukiProjectAStar) * t)) +
                    coefficient *
                      (Real.sin (((0 : Real) * Real.pi /
                          suzukiProjectAStar) * t) +
                        Real.sin (((right : Real) * Real.pi /
                          suzukiProjectAStar) * t))))) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = _ := by
          have hlinear := integral_suzukiRSecondKernel_mul_linear_sines
            0 right coefficient coefficient
          simp only [Nat.cast_zero] at hlinear
          rw [hlinear]
          unfold coefficient
          push_cast
          rw [suzukiDF6D4AlternatingSign_cast_real]
          ring

theorem suzukiYoshidaGammaRemainderForm_odd_offDiagonal
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      ((suzukiDF6D4ComparisonOddOffDiagonal left right +
        suzukiDF6D4OddOffDiagonalPrimeTerm left right -
        suzukiDF6D4OddOffDiagonal left right : Real) : Complex) := by
  rw [suzukiYoshidaGammaRemainderForm_eq_symmetricInterval,
    suzukiYoshidaOddLinearCompletionOfSource_toL2,
    suzukiYoshidaOddLinearCompletionOfSource_toL2,
    suzukiDF6D4OddOffDiagonalGammaCombination_eq_rSecond left right hleft hlt]
  let differenceCoefficient : Real :=
    -((-1 : Real) ^ (right - left)) / (right - left)
  let totalCoefficient : Real :=
    ((-1 : Real) ^ (left + right)) / (left + right)
  calc
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        (suzukiRSecondKernel t : Complex) *
          suzukiL2SymmetricTranslationEnergy t
            (suzukiYoshidaOddL2 suzukiProjectAStar
              suzukiProjectAStar_pos left)
            (suzukiYoshidaOddL2 suzukiProjectAStar
              suzukiProjectAStar_pos right)) =
      ((∫ t in (0 : Real)..2 * suzukiProjectAStar,
        suzukiRSecondKernel t *
          (2 * (1 / (2 * Real.pi) *
            (differenceCoefficient *
                (Real.sin (((right : Real) * Real.pi /
                    suzukiProjectAStar) * t) -
                  Real.sin (((left : Real) * Real.pi /
                    suzukiProjectAStar) * t)) +
              totalCoefficient *
                (Real.sin (((left : Real) * Real.pi /
                    suzukiProjectAStar) * t) +
                  Real.sin (((right : Real) * Real.pi /
                    suzukiProjectAStar) * t))))) : Real) : Complex) := by
        rw [← intervalIntegral.integral_ofReal]
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le
          (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)] at ht
        dsimp only
        rw [suzukiL2SymmetricTranslationEnergy_yoshidaOdd_offDiagonal
          suzukiProjectAStar_pos ht.1 ht.2 left right hleft hlt]
        unfold differenceCoefficient totalCoefficient
        push_cast
        rw [Nat.cast_sub hlt.le]
        ring
    _ = _ := by
      norm_cast
      calc
        (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiRSecondKernel t *
            (2 * (1 / (2 * Real.pi) *
              (differenceCoefficient *
                  (Real.sin (((right : Real) * Real.pi /
                      suzukiProjectAStar) * t) -
                    Real.sin (((left : Real) * Real.pi /
                      suzukiProjectAStar) * t)) +
                totalCoefficient *
                  (Real.sin (((left : Real) * Real.pi /
                      suzukiProjectAStar) * t) +
                    Real.sin (((right : Real) * Real.pi /
                      suzukiProjectAStar) * t)))))) =
            (2 * (1 / (2 * Real.pi))) *
              (∫ t in (0 : Real)..2 * suzukiProjectAStar,
                suzukiRSecondKernel t *
                  (differenceCoefficient *
                      (Real.sin (((right : Real) * Real.pi /
                          suzukiProjectAStar) * t) -
                        Real.sin (((left : Real) * Real.pi /
                          suzukiProjectAStar) * t)) +
                    totalCoefficient *
                      (Real.sin (((left : Real) * Real.pi /
                          suzukiProjectAStar) * t) +
                        Real.sin (((right : Real) * Real.pi /
                          suzukiProjectAStar) * t)))) := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          ring
        _ = _ := by
          rw [integral_suzukiRSecondKernel_mul_linear_sines]
          unfold differenceCoefficient totalCoefficient
          push_cast
          rw [suzukiDF6D4AlternatingSign_cast_real,
            suzukiDF6D4AlternatingSign_cast_real,
            Nat.cast_sub hlt.le]
          ring

theorem suzukiEquation25EvenOffDiagonalGammaEvaluation
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25EvenOffDiagonalGammaEvaluation hsource := by
  intro left right hlt
  by_cases hleft : left = 0
  · subst left
    exact suzukiYoshidaGammaRemainderForm_evenZero_offDiagonal
      hsource right hlt
  · exact suzukiYoshidaGammaRemainderForm_evenPositive_offDiagonal
      hsource left right (Nat.pos_of_ne_zero hleft) hlt

theorem suzukiEquation25OddOffDiagonalGammaEvaluation
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25OddOffDiagonalGammaEvaluation hsource := by
  intro left right hleft hlt
  exact suzukiYoshidaGammaRemainderForm_odd_offDiagonal
    hsource left right hleft hlt

end

end RiemannHypothesisProject.Experiments.M100
