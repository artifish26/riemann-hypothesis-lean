import RiemannHypothesisProject.Experiments.M100.SuzukiFiniteRemainderBound

/-!
# Support-sharp translation bounds on global Suzuki L2

This module improves the generic two-translation estimate when the vector is
supported in a symmetric interval and the positive translation exceeds the
support radius.  Splitting the vector into its negative and nonnegative
halves identifies the correlation with one cross inner product.  Cauchy and
Pythagoras then give the sharp factor used by the endpoint prime-`2` term.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-- Restriction of a global `L²` class to the negative half-line. -/
def suzukiL2NegativePart (v : SuzukiL2) : SuzukiL2 :=
  ((Lp.memLp v).indicator measurableSet_Iio).toLp
    ((Set.Iio (0 : Real)).indicator v)

/-- Restriction of a global `L²` class to the nonnegative half-line. -/
def suzukiL2NonnegativePart (v : SuzukiL2) : SuzukiL2 :=
  ((Lp.memLp v).indicator measurableSet_Ici).toLp
    ((Set.Ici (0 : Real)).indicator v)

theorem suzukiL2NegativePart_coeFn (v : SuzukiL2) :
    suzukiL2NegativePart v =ᵐ[volume]
      (Set.Iio (0 : Real)).indicator v := by
  exact (((Lp.memLp v).indicator measurableSet_Iio).coeFn_toLp)

theorem suzukiL2NonnegativePart_coeFn (v : SuzukiL2) :
    suzukiL2NonnegativePart v =ᵐ[volume]
      (Set.Ici (0 : Real)).indicator v := by
  exact (((Lp.memLp v).indicator measurableSet_Ici).coeFn_toLp)

theorem suzukiL2NegativePart_add_nonnegativePart (v : SuzukiL2) :
    suzukiL2NegativePart v + suzukiL2NonnegativePart v = v := by
  apply Lp.ext
  filter_upwards
    [Lp.coeFn_add (suzukiL2NegativePart v) (suzukiL2NonnegativePart v),
      suzukiL2NegativePart_coeFn v,
      suzukiL2NonnegativePart_coeFn v] with x hadd hn hp
  rw [hadd]
  change suzukiL2NegativePart v x + suzukiL2NonnegativePart v x = v x
  rw [hn, hp]
  by_cases hx : x < 0
  · simp [Set.indicator, hx, not_le_of_gt hx]
  · simp [Set.indicator, hx, le_of_not_gt hx]

theorem inner_suzukiL2NegativePart_nonnegativePart (v : SuzukiL2) :
    inner Complex (suzukiL2NegativePart v)
      (suzukiL2NonnegativePart v) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards
    [suzukiL2NegativePart_coeFn v,
      suzukiL2NonnegativePart_coeFn v] with x hn hp
  rw [hn, hp]
  by_cases hx : x < 0
  · simp [Set.indicator, hx, not_le_of_gt hx]
  · simp [Set.indicator, hx, le_of_not_gt hx]

theorem suzukiL2NegativePart_norm_sq_add_nonnegativePart_norm_sq
    (v : SuzukiL2) :
    ‖suzukiL2NegativePart v‖ ^ 2 +
        ‖suzukiL2NonnegativePart v‖ ^ 2 = ‖v‖ ^ 2 := by
  calc
    ‖suzukiL2NegativePart v‖ ^ 2 +
        ‖suzukiL2NonnegativePart v‖ ^ 2 =
        ‖suzukiL2NegativePart v + suzukiL2NonnegativePart v‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          (suzukiL2NegativePart v) (suzukiL2NonnegativePart v)
          (inner_suzukiL2NegativePart_nonnegativePart v)).symm
    _ = ‖v‖ ^ 2 := by
      rw [suzukiL2NegativePart_add_nonnegativePart]

private theorem inner_suzukiL2Translate_eq_halves
    {r t : Real} (hrt : r < t) {v : SuzukiL2}
    (hv : suzukiL2SupportedAt r v) :
    inner Complex (suzukiL2Translate t v) v =
      inner Complex
        (suzukiL2Translate t (suzukiL2NonnegativePart v))
        (suzukiL2NegativePart v) := by
  have hvShift :
      ∀ᵐ x ∂(volume : Measure Real),
        x + t ∉ Set.Icc (-r) r → v (x + t) = 0 :=
    (measurePreserving_add_right
      (volume : Measure Real) t).quasiMeasurePreserving.ae hv
  have htranslateV :
      (suzukiL2Translate t v : Real → Complex) =ᵐ[volume]
        (v : Real → Complex) ∘ fun x ↦ x + t := by
    simpa only [suzukiL2Translate] using
      (Lp.coeFn_compMeasurePreserving v
        (measurePreserving_add_right (volume : Measure Real) t))
  have htranslatePositive :
      (suzukiL2Translate t (suzukiL2NonnegativePart v) :
          Real → Complex) =ᵐ[volume]
        (suzukiL2NonnegativePart v : Real → Complex) ∘
          fun x ↦ x + t := by
    simpa only [suzukiL2Translate] using
      (Lp.coeFn_compMeasurePreserving (suzukiL2NonnegativePart v)
        (measurePreserving_add_right (volume : Measure Real) t))
  have hpositiveShift :
      (fun x : Real ↦ suzukiL2NonnegativePart v (x + t)) =ᵐ[volume]
        fun x ↦ (Set.Ici (0 : Real)).indicator v (x + t) :=
    (measurePreserving_add_right
      (volume : Measure Real) t).quasiMeasurePreserving.ae_eq_comp
        (suzukiL2NonnegativePart_coeFn v)
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [hv, hvShift, htranslateV, htranslatePositive,
      hpositiveShift, suzukiL2NegativePart_coeFn v] with
      x hx hxShift htV htPositive hpShift hn
  rw [htV, htPositive, hn]
  simp only [Function.comp_apply]
  rw [hpShift]
  by_cases hx0 : x < 0
  · by_cases hxt0 : x + t < 0
    · have hxOut : x ∉ Set.Icc (-r) r := by
        intro hxIn
        linarith [hxIn.1]
      rw [hx hxOut]
      simp [Set.indicator, hx0, hxt0]
    · simp [Set.indicator, hx0, le_of_not_gt hxt0]
  · have hxtOut : x + t ∉ Set.Icc (-r) r := by
      intro hxtIn
      linarith [hxtIn.2, le_of_not_gt hx0]
    rw [hxShift hxtOut]
    simp [Set.indicator, hx0]

/-- Support-sharp symmetric translation estimate.  The generic global bound
has coefficient `2`; support separation improves it to coefficient `1`. -/
theorem suzukiL2SymmetricTranslationDiagonal_abs_le_of_supportedAt
    {r t : Real} (hrt : r < t) {v : SuzukiL2}
    (hv : suzukiL2SupportedAt r v) :
    abs (suzukiL2SymmetricTranslationDiagonal t v) ≤ ‖v‖ ^ 2 := by
  have hcorrelation := inner_suzukiL2Translate_eq_halves hrt hv
  have hinner :
      norm (inner Complex
        (suzukiL2Translate t (suzukiL2NonnegativePart v))
        (suzukiL2NegativePart v)) ≤
        ‖suzukiL2NonnegativePart v‖ * ‖suzukiL2NegativePart v‖ := by
    calc
      norm (inner Complex
          (suzukiL2Translate t (suzukiL2NonnegativePart v))
          (suzukiL2NegativePart v)) ≤
          ‖suzukiL2Translate t (suzukiL2NonnegativePart v)‖ *
            ‖suzukiL2NegativePart v‖ := norm_inner_le_norm _ _
      _ = ‖suzukiL2NonnegativePart v‖ *
          ‖suzukiL2NegativePart v‖ := by
        rw [suzukiL2Translate_norm]
  have hparts :=
    suzukiL2NegativePart_norm_sq_add_nonnegativePart_norm_sq v
  unfold suzukiL2SymmetricTranslationDiagonal
    suzukiL2TranslationCorrelation
  rw [hcorrelation, abs_mul,
    abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  calc
    2 * abs (inner Complex
        (suzukiL2Translate t (suzukiL2NonnegativePart v))
        (suzukiL2NegativePart v)).re ≤
        2 * norm (inner Complex
          (suzukiL2Translate t (suzukiL2NonnegativePart v))
          (suzukiL2NegativePart v)) := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ ≤ 2 * (‖suzukiL2NonnegativePart v‖ *
        ‖suzukiL2NegativePart v‖) := by
      gcongr
    _ ≤ ‖v‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖suzukiL2NonnegativePart v‖ - ‖suzukiL2NegativePart v‖)]

end

end RiemannHypothesisProject.Experiments.M100
