import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmEquationObstruction

/-!
# M100-DF6F explicit Fredholm mean correction

This module identifies exactly what the zero-mean projection removes from
Suzuki's two printed Section 8 right-hand sides.  It is a normalization bridge,
not a proof that the source boundary-form transport selects the projected
equations.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiFredholmMeanCorrectionFiniteMeasureOnCompacts (a : Real) :
    IsFiniteMeasureOnCompacts
      (volume : Measure (SuzukiFiniteInterval a)) := by
  rw [Measure.Subtype.volume_def]
  exact IsFiniteMeasureOnCompacts.comap' (volume : Measure Real)
    continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Icc)

local instance suzukiFredholmMeanCorrectionCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

private theorem integrable_suzukiFredholmExponentialContinuous
    (a c : Real) : Integrable (fun x : SuzukiFiniteInterval a =>
      suzukiFredholmExponentialContinuous a c x) := by
  rw [← integrableOn_univ]
  exact (suzukiFredholmExponentialContinuous a c).continuous.continuousOn.integrableOn_compact
    isCompact_univ

private theorem integrable_suzukiFredholmPlusContinuous
    (a : Real) : Integrable (fun x : SuzukiFiniteInterval a =>
      suzukiFredholmPlusContinuous a x) := by
  rw [← integrableOn_univ]
  exact (suzukiFredholmPlusContinuous a).continuous.continuousOn.integrableOn_compact
    isCompact_univ

private theorem integrable_suzukiFredholmMinusContinuous
    (a : Real) : Integrable (fun x : SuzukiFiniteInterval a =>
      suzukiFredholmMinusContinuous a x) := by
  rw [← integrableOn_univ]
  exact (suzukiFredholmMinusContinuous a).continuous.continuousOn.integrableOn_compact
    isCompact_univ

private theorem integrable_suzukiFiniteIntervalConstantContinuous
    (a : Real) (z : Complex) : Integrable (fun x : SuzukiFiniteInterval a =>
      suzukiFiniteIntervalConstantContinuous a z x) := by
  rw [← integrableOn_univ]
  exact (suzukiFiniteIntervalConstantContinuous a z).continuous.continuousOn.integrableOn_compact
    isCompact_univ

/-- Both real exponentials occurring in the Fredholm right-hand sides have the
same interval integral. -/
theorem integral_suzukiFredholmExponentialContinuous_sign
    {a : Real} (ha : 0 < a) (c : Real) (hc : c = 1 ∨ c = -1) :
    (∫ x : SuzukiFiniteInterval a,
      suzukiFredholmExponentialContinuous a c x ∂volume) =
        ((Real.exp a - Real.exp (-a) : Real) : Complex) := by
  rcases hc with rfl | rfl
  · apply Complex.ext
    · calc
        (∫ x : SuzukiFiniteInterval a,
            suzukiFredholmExponentialContinuous a 1 x ∂volume).re =
            ∫ x : SuzukiFiniteInterval a,
              (suzukiFredholmExponentialContinuous a 1 x).re ∂volume :=
          (integral_re
            (integrable_suzukiFredholmExponentialContinuous a 1)).symm
        _ = ∫ x : SuzukiFiniteInterval a,
              (suzukiFredholmPlusContinuous a x).re ∂volume := by
          congr 1
          funext x
          simp [suzukiFredholmPlusContinuous,
            suzukiFiniteIntervalConstantContinuous]
        _ = (∫ x : SuzukiFiniteInterval a,
              suzukiFredholmPlusContinuous a x ∂volume).re := by
          exact integral_re (integrable_suzukiFredholmPlusContinuous a)
        _ = Real.exp a - Real.exp (-a) :=
          integral_suzukiFredholmPlusContinuous_re ha
        _ = ((Real.exp a - Real.exp (-a) : Real) : Complex).re := by
          simp [Complex.exp_ofReal_re]
          rw [← Complex.ofReal_neg, Complex.exp_ofReal_re]
    · calc
        (∫ x : SuzukiFiniteInterval a,
            suzukiFredholmExponentialContinuous a 1 x ∂volume).im =
            ∫ x : SuzukiFiniteInterval a,
              (suzukiFredholmExponentialContinuous a 1 x).im ∂volume :=
          (integral_im
            (integrable_suzukiFredholmExponentialContinuous a 1)).symm
        _ = 0 := by
          simp [suzukiFredholmExponentialContinuous,
            Complex.exp_ofReal_im]
        _ = ((Real.exp a - Real.exp (-a) : Real) : Complex).im := by
          simp [Complex.exp_ofReal_im]
          rw [← Complex.ofReal_neg, Complex.exp_ofReal_im]
  · apply Complex.ext
    · calc
        (∫ x : SuzukiFiniteInterval a,
            suzukiFredholmExponentialContinuous a (-1) x ∂volume).re =
            ∫ x : SuzukiFiniteInterval a,
              (suzukiFredholmExponentialContinuous a (-1) x).re ∂volume :=
          (integral_re
            (integrable_suzukiFredholmExponentialContinuous a (-1))).symm
        _ = ∫ x : SuzukiFiniteInterval a,
              (suzukiFredholmMinusContinuous a x).re ∂volume := by
          congr 1
          funext x
          simp [suzukiFredholmMinusContinuous,
            suzukiFiniteIntervalConstantContinuous]
        _ = (∫ x : SuzukiFiniteInterval a,
              suzukiFredholmMinusContinuous a x ∂volume).re := by
          exact integral_re (integrable_suzukiFredholmMinusContinuous a)
        _ = Real.exp a - Real.exp (-a) :=
          integral_suzukiFredholmMinusContinuous_re ha
        _ = ((Real.exp a - Real.exp (-a) : Real) : Complex).re := by
          simp [Complex.exp_ofReal_re]
          rw [← Complex.ofReal_neg, Complex.exp_ofReal_re]
    · calc
        (∫ x : SuzukiFiniteInterval a,
            suzukiFredholmExponentialContinuous a (-1) x ∂volume).im =
            ∫ x : SuzukiFiniteInterval a,
              (suzukiFredholmExponentialContinuous a (-1) x).im ∂volume :=
          (integral_im
            (integrable_suzukiFredholmExponentialContinuous a (-1))).symm
        _ = 0 := by
          apply integral_eq_zero_of_ae
          filter_upwards with x
          simp only [Pi.zero_apply]
          rw [suzukiFredholmExponentialContinuous_apply]
          norm_num
          rw [← Complex.ofReal_neg, Complex.exp_ofReal_im]
        _ = ((Real.exp a - Real.exp (-a) : Real) : Complex).im := by
          simp [Complex.exp_ofReal_im]
          rw [← Complex.ofReal_neg, Complex.exp_ofReal_im]

/-- The common real average of `exp(x)` and `exp(-x)` on `[-a,a]`. -/
def suzukiFredholmExponentialAverage (a : Real) : Real :=
  (Real.exp a - Real.exp (-a)) / (2 * a)

/-- Continuous centered exponential for either Fredholm sign. -/
def suzukiFredholmCenteredExponentialContinuous
    (a c : Real) : C(SuzukiFiniteInterval a, Complex) :=
  suzukiFredholmExponentialContinuous a c -
    suzukiFiniteIntervalConstantContinuous a
      (suzukiFredholmExponentialAverage a)

theorem integral_suzukiFredholmCenteredExponentialContinuous_eq_zero
    {a : Real} (ha : 0 < a) (c : Real) (hc : c = 1 ∨ c = -1) :
    (∫ x : SuzukiFiniteInterval a,
      suzukiFredholmCenteredExponentialContinuous a c x ∂volume) = 0 := by
  rw [show (∫ x : SuzukiFiniteInterval a,
      suzukiFredholmCenteredExponentialContinuous a c x ∂volume) =
      (∫ x : SuzukiFiniteInterval a,
        suzukiFredholmExponentialContinuous a c x ∂volume) -
      ∫ x : SuzukiFiniteInterval a,
        suzukiFiniteIntervalConstantContinuous a
          (suzukiFredholmExponentialAverage a) x ∂volume by
    rw [← integral_sub
      (integrable_suzukiFredholmExponentialContinuous a c)
      (integrable_suzukiFiniteIntervalConstantContinuous a
        (suzukiFredholmExponentialAverage a))]
    rfl]
  rw [integral_suzukiFredholmExponentialContinuous_sign ha c hc]
  simp only [suzukiFiniteIntervalConstantContinuous_apply, integral_const]
  have hmeasure :
      (volume : Measure (SuzukiFiniteInterval a)).real univ = 2 * a := by
    rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
      Real.volume_Icc]
    simp [sub_neg_eq_add, ha.le]
    ring
  unfold suzukiFredholmExponentialAverage
  rw [hmeasure]
  change ((Real.exp a - Real.exp (-a) : Real) : Complex) -
      ((2 * a : Real) : Complex) *
        (((Real.exp a - Real.exp (-a)) / (2 * a) : Real) : Complex) = 0
  push_cast
  have haC : (a : Complex) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp [haC]
  simp

/-- The projected sign exponential is exactly its literal `L²` representative
minus the explicit constant interval average. -/
theorem coe_suzukiFredholmExponentialForcing_eq_centered
    {a : Real} (ha : 0 < a) (c : Real) (hc : c = 1 ∨ c = -1) :
    (suzukiFredholmExponentialForcing a c :
        SuzukiFiniteIntervalL2 a) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmCenteredExponentialContinuous a c) := by
  let centered : SuzukiFiniteIntervalZeroMeanL2 a :=
    suzukiFiniteIntervalContinuousZeroMeanToL2 a
      (suzukiFredholmCenteredExponentialContinuous a c)
      (integral_suzukiFredholmCenteredExponentialContinuous_eq_zero ha c hc)
  have hsub : suzukiFredholmExponentialForcing a c = centered := by
    unfold suzukiFredholmExponentialForcing
      suzukiFiniteIntervalContinuousToZeroMeanL2
      suzukiFiniteIntervalZeroMeanProjection
    change (SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmExponentialContinuous a c)) = centered
    have hproject :
        (SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
            (centered : SuzukiFiniteIntervalL2 a) = centered :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self centered
    have hconstproject :
        (SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
            (suzukiFiniteIntervalContinuousToL2 a
              (suzukiFiniteIntervalConstantContinuous a
                (suzukiFredholmExponentialAverage a))) = 0 := by
      change suzukiFiniteIntervalContinuousToZeroMeanL2 a
          (suzukiFiniteIntervalConstantContinuous a
            (suzukiFredholmExponentialAverage a)) = 0
      exact suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero _ _
    rw [show suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmExponentialContinuous a c) =
        (centered : SuzukiFiniteIntervalL2 a) +
          suzukiFiniteIntervalContinuousToL2 a
            (suzukiFiniteIntervalConstantContinuous a
              (suzukiFredholmExponentialAverage a)) by
      change suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmExponentialContinuous a c) =
        suzukiFiniteIntervalContinuousToL2 a
            (suzukiFredholmCenteredExponentialContinuous a c) +
          suzukiFiniteIntervalContinuousToL2 a
            (suzukiFiniteIntervalConstantContinuous a
              (suzukiFredholmExponentialAverage a))
      rw [← map_add]
      congr 1
      unfold suzukiFredholmCenteredExponentialContinuous
      abel]
    rw [map_add, hproject, hconstproject, add_zero]
  exact congrArg Subtype.val hsub

/-- Exact zero-mode correction for the printed plus right-hand side. -/
theorem coe_suzukiFredholmPlusForcing_eq_literal_sub_mean
    {a : Real} (ha : 0 < a) :
    (suzukiFredholmPlusForcing a : SuzukiFiniteIntervalL2 a) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a -
          suzukiFiniteIntervalConstantContinuous a
            (suzukiFredholmExponentialAverage a + Complex.I)) := by
  rw [suzukiFredholmPlusForcing_eq_exponential,
    coe_suzukiFredholmExponentialForcing_eq_centered ha 1 (Or.inl rfl)]
  congr 1
  unfold suzukiFredholmCenteredExponentialContinuous
    suzukiFredholmPlusContinuous
  ext x
  simp [suzukiFiniteIntervalConstantContinuous]

/-- Exact zero-mode correction for the printed minus right-hand side. -/
theorem coe_suzukiFredholmMinusForcing_eq_literal_sub_mean
    {a : Real} (ha : 0 < a) :
    (suzukiFredholmMinusForcing a : SuzukiFiniteIntervalL2 a) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a -
          suzukiFiniteIntervalConstantContinuous a
            (suzukiFredholmExponentialAverage a - Complex.I)) := by
  rw [suzukiFredholmMinusForcing_eq_exponential,
    coe_suzukiFredholmExponentialForcing_eq_centered ha (-1) (Or.inr rfl)]
  congr 1
  unfold suzukiFredholmCenteredExponentialContinuous
    suzukiFredholmMinusContinuous
  ext x
  simp [suzukiFiniteIntervalConstantContinuous]

/-- Exact complex interval mean of Suzuki's printed plus right-hand side. -/
theorem suzukiFiniteIntervalMeanCLM_fredholmPlus_eq
    {a : Real} (ha : 0 < a) :
    suzukiFiniteIntervalMeanCLM a
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmPlusContinuous a)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I := by
  rw [suzukiFiniteIntervalMeanCLM_continuous]
  change (∫ x : SuzukiFiniteInterval a,
      (suzukiFredholmExponentialContinuous a 1 x + Complex.I) ∂volume) = _
  rw [integral_add
    (integrable_suzukiFredholmExponentialContinuous a 1)
    (integrable_const Complex.I),
    integral_suzukiFredholmExponentialContinuous_sign ha 1 (Or.inl rfl),
    integral_const]
  have hmeasure :
      (volume : Measure (SuzukiFiniteInterval a)).real univ = 2 * a := by
    rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
      Real.volume_Icc]
    simp [sub_neg_eq_add, ha.le]
    ring
  rw [hmeasure]
  rfl

/-- Exact complex interval mean of Suzuki's printed minus right-hand side. -/
theorem suzukiFiniteIntervalMeanCLM_fredholmMinus_eq
    {a : Real} (ha : 0 < a) :
    suzukiFiniteIntervalMeanCLM a
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmMinusContinuous a)) =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I := by
  rw [suzukiFiniteIntervalMeanCLM_continuous]
  change (∫ x : SuzukiFiniteInterval a,
      (suzukiFredholmExponentialContinuous a (-1) x - Complex.I) ∂volume) = _
  rw [integral_sub
    (integrable_suzukiFredholmExponentialContinuous a (-1))
    (integrable_const Complex.I),
    integral_suzukiFredholmExponentialContinuous_sign ha (-1) (Or.inr rfl),
    integral_const]
  have hmeasure :
      (volume : Measure (SuzukiFiniteInterval a)).real univ = 2 * a := by
    rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
      Real.volume_Icc]
    simp [sub_neg_eq_add, ha.le]
    ring
  rw [hmeasure]
  rfl

end

end RiemannHypothesisProject.Experiments.M100
