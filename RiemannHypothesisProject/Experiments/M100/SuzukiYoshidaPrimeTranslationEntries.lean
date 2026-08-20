import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEquation25ComponentEntryReduction

/-!
# Prime-translation entries for the B3Q-G source evaluation

At the frozen endpoint the complete prime set is the singleton `{2}`.  This
module evaluates that one symmetric translation on the normalized endpoint
cosine and sine modes.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

theorem log_two_lt_two_mul_suzukiProjectAStar :
    Real.log 2 < 2 * suzukiProjectAStar := by
  unfold suzukiProjectAStar
  let L : Real := Real.log 2
  let z : Real := L ^ 2 + 4 * Real.exp (-2 * Real.sqrt 2 * L)
  have hL : 0 < L := Real.log_pos (by norm_num)
  have hz : 0 < z := by
    dsimp only [z]
    positivity
  have hsqrt : L < Real.sqrt z := by
    have hsquare : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz.le
    have hsqrt0 : 0 ≤ Real.sqrt z := Real.sqrt_nonneg z
    dsimp only [z] at hsquare
    nlinarith [Real.exp_pos (-2 * Real.sqrt 2 * L)]
  dsimp only [L, z] at hsqrt ⊢
  linarith

private theorem yoshida_sqrt_normalization
    {r : Real} (hr : 0 < r) :
    (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * r))⁻¹ * 2 =
      (Real.sqrt r)⁻¹ := by
  have hsqrtR : Real.sqrt r ≠ 0 := by positivity
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  field_simp [hsqrtR, hsqrtTwo]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]

private theorem yoshida_sqrt_normalization_complex
    {r : Real} (hr : 0 < r) :
    ((Real.sqrt 2 : Real) : Complex)⁻¹ *
          ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ * 2 =
      ((Real.sqrt r : Real) : Complex)⁻¹ := by
  exact_mod_cast yoshida_sqrt_normalization hr

private theorem yoshida_odd_sqrt_normalization_complex
    {r : Real} (hr : 0 < r) :
    (Complex.I * ((Real.sqrt 2 : Real) : Complex))⁻¹ *
          ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ *
          (2 * Complex.I) =
      ((Real.sqrt r : Real) : Complex)⁻¹ := by
  rw [mul_inv_rev, Complex.inv_I]
  have hIcancel : (-Complex.I) * (2 * Complex.I) = 2 := by
    calc
      _ = -2 * (Complex.I * Complex.I) := by ring
      _ = 2 := by rw [Complex.I_mul_I]; ring
  calc
    ((Real.sqrt 2 : Real) : Complex)⁻¹ *
          (-Complex.I) *
          ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ *
          (2 * Complex.I) =
        ((Real.sqrt 2 : Real) : Complex)⁻¹ *
          ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ * 2 := by
      calc
        _ = ((Real.sqrt 2 : Real) : Complex)⁻¹ *
              ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ *
              ((-Complex.I) * (2 * Complex.I)) := by ring
        _ = _ := by rw [hIcancel]
    _ = ((Real.sqrt r : Real) : Complex)⁻¹ :=
      yoshida_sqrt_normalization_complex hr

/-- The positive Yoshida cosine mode as an explicit function. -/
def suzukiYoshidaEvenPositiveFunction
    (r : Real) (mode : Nat) (x : Real) : Complex :=
  Set.indicator (Set.Icc (-r) r)
    (fun x =>
      ((Real.sqrt r)⁻¹ : Complex) *
        (Real.cos ((mode : Real) * Real.pi * x / r) : Complex)) x

/-- The Yoshida sine mode as an explicit function. -/
def suzukiYoshidaOddFunction
    (r : Real) (mode : Nat) (x : Real) : Complex :=
  Set.indicator (Set.Icc (-r) r)
    (fun x =>
      ((Real.sqrt r)⁻¹ : Complex) *
        (Real.sin ((mode : Real) * Real.pi * x / r) : Complex)) x

/-- The normalized constant Yoshida mode as an explicit function. -/
def suzukiYoshidaEvenZeroFunction
    (r : Real) (x : Real) : Complex :=
  Set.indicator (Set.Icc (-r) r)
    (fun _ => ((Real.sqrt (2 * r))⁻¹ : Complex)) x

theorem inner_suzukiL2Translate_eq_integral_of_ae
    (t : Real) (v : SuzukiL2) (f : Real → Complex)
    (hv : (v : Real → Complex) =ᵐ[volume] f) :
    inner Complex (suzukiL2Translate t v) v =
      ∫ x : Real, f x * conj (f (x + t)) := by
  have htranslate :
      (suzukiL2Translate t v : Real → Complex) =ᵐ[volume]
        (v : Real → Complex) ∘ fun x : Real => x + t := by
    simpa only [suzukiL2Translate] using
      (Lp.coeFn_compMeasurePreserving v
        (measurePreserving_add_right (volume : Measure Real) t))
  have hvShift :
      (fun x : Real => (v : Real → Complex) (x + t)) =ᵐ[volume]
        fun x => f (x + t) :=
    (measurePreserving_add_right
      (volume : Measure Real) t).quasiMeasurePreserving.ae_eq_comp hv
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htranslate, hv, hvShift] with x hxTranslate hx hxShift
  rw [hxTranslate, Function.comp_apply, hx, hxShift]
  simp [inner]

theorem inner_suzukiL2Translate_eq_integral_of_ae_two
    (t : Real) (u v : SuzukiL2) (f g : Real → Complex)
    (hu : (u : Real → Complex) =ᵐ[volume] f)
    (hv : (v : Real → Complex) =ᵐ[volume] g) :
    inner Complex (suzukiL2Translate t u) v =
      ∫ x : Real, g x * conj (f (x + t)) := by
  have htranslate :
      (suzukiL2Translate t u : Real → Complex) =ᵐ[volume]
        (u : Real → Complex) ∘ fun x : Real => x + t := by
    simpa only [suzukiL2Translate] using
      (Lp.coeFn_compMeasurePreserving u
        (measurePreserving_add_right (volume : Measure Real) t))
  have huShift :
      (fun x : Real => (u : Real → Complex) (x + t)) =ᵐ[volume]
        fun x => f (x + t) :=
    (measurePreserving_add_right
      (volume : Measure Real) t).quasiMeasurePreserving.ae_eq_comp hu
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htranslate, hv, huShift] with x hxTranslate hxv huShift
  rw [hxTranslate, Function.comp_apply, hxv, huShift]
  simp [inner]

theorem integral_symmetric_indicator_overlap
    {r t : Real} (ht0 : 0 ≤ t)
    (g : Real → Complex) :
    (∫ x : Real,
        Set.indicator (Set.Icc (-r) r) g x *
          conj (Set.indicator (Set.Icc (-r) r) g (x + t))) =
      ∫ x in Set.Icc (-r) (r - t), g x * conj (g (x + t)) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  have hmem :
      x ∈ Set.Icc (-r) (r - t) ↔
        x ∈ Set.Icc (-r) r ∧ x + t ∈ Set.Icc (-r) r := by
    constructor
    · intro hx
      constructor
      · constructor
        · exact hx.1
        · linarith [hx.2]
      · constructor <;> linarith [hx.1, hx.2]
    · rintro ⟨hx, hxShift⟩
      constructor
      · exact hx.1
      · linarith [hxShift.2]
  by_cases hx : x ∈ Set.Icc (-r) (r - t)
  · have hxBoth := hmem.mp hx
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxBoth.1,
      Set.indicator_of_mem hxBoth.2]
  · have hxNotBoth : ¬
        (x ∈ Set.Icc (-r) r ∧ x + t ∈ Set.Icc (-r) r) := by
      exact fun h => hx (hmem.mpr h)
    rcases not_and_or.mp hxNotBoth with hxLeft | hxRight
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxLeft]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxRight]

theorem integral_symmetric_indicator_overlap_two
    {r t : Real} (ht0 : 0 ≤ t)
    (f g : Real → Complex) :
    (∫ x : Real,
        Set.indicator (Set.Icc (-r) r) g x *
          conj (Set.indicator (Set.Icc (-r) r) f (x + t))) =
      ∫ x in Set.Icc (-r) (r - t), g x * conj (f (x + t)) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  have hmem :
      x ∈ Set.Icc (-r) (r - t) ↔
        x ∈ Set.Icc (-r) r ∧ x + t ∈ Set.Icc (-r) r := by
    constructor
    · intro hx
      constructor
      · constructor
        · exact hx.1
        · linarith [hx.2]
      · constructor <;> linarith [hx.1, hx.2]
    · rintro ⟨hx, hxShift⟩
      constructor
      · exact hx.1
      · linarith [hxShift.2]
  by_cases hx : x ∈ Set.Icc (-r) (r - t)
  · have hxBoth := hmem.mp hx
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxBoth.1,
      Set.indicator_of_mem hxBoth.2]
  · have hxNotBoth : ¬
        (x ∈ Set.Icc (-r) r ∧ x + t ∈ Set.Icc (-r) r) := by
      exact fun h => hx (hmem.mpr h)
    rcases not_and_or.mp hxNotBoth with hxLeft | hxRight
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxLeft]
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxRight]

private def yoshidaCosineCorrelationPrimitive
    (w t x : Real) : Real :=
  Real.cos (w * t) * x / 2 +
    Real.sin (2 * w * x + w * t) / (4 * w)

private def yoshidaSineCorrelationPrimitive
    (w t x : Real) : Real :=
  Real.cos (w * t) * x / 2 -
    Real.sin (2 * w * x + w * t) / (4 * w)

private theorem yoshida_cosine_product_to_sum
    (w t x : Real) :
    Real.cos (w * (x + t)) * Real.cos (w * x) =
      (Real.cos (w * t) + Real.cos (2 * w * x + w * t)) / 2 := by
  have htrig := Real.two_mul_cos_mul_cos (w * (x + t)) (w * x)
  rw [show w * (x + t) - w * x = w * t by ring,
    show w * (x + t) + w * x = 2 * w * x + w * t by ring] at htrig
  linarith

private theorem yoshida_sine_product_to_sum
    (w t x : Real) :
    Real.sin (w * (x + t)) * Real.sin (w * x) =
      (Real.cos (w * t) - Real.cos (2 * w * x + w * t)) / 2 := by
  have htrig := Real.two_mul_sin_mul_sin (w * (x + t)) (w * x)
  rw [show w * (x + t) - w * x = w * t by ring,
    show w * (x + t) + w * x = 2 * w * x + w * t by ring] at htrig
  linarith

private def yoshidaCosineCrossCorrelationPrimitive
    (leftFrequency rightFrequency t x : Real) : Real :=
  Real.sin ((leftFrequency - rightFrequency) * x + leftFrequency * t) /
      (2 * (leftFrequency - rightFrequency)) +
    Real.sin ((leftFrequency + rightFrequency) * x + leftFrequency * t) /
      (2 * (leftFrequency + rightFrequency))

private def yoshidaSineCrossCorrelationPrimitive
    (leftFrequency rightFrequency t x : Real) : Real :=
  Real.sin ((leftFrequency - rightFrequency) * x + leftFrequency * t) /
      (2 * (leftFrequency - rightFrequency)) -
    Real.sin ((leftFrequency + rightFrequency) * x + leftFrequency * t) /
      (2 * (leftFrequency + rightFrequency))

private theorem yoshida_cosine_cross_product_to_sum
    (leftFrequency rightFrequency t x : Real) :
    Real.cos (leftFrequency * (x + t)) * Real.cos (rightFrequency * x) =
      (Real.cos ((leftFrequency - rightFrequency) * x + leftFrequency * t) +
        Real.cos ((leftFrequency + rightFrequency) * x + leftFrequency * t)) / 2 := by
  have htrig := Real.two_mul_cos_mul_cos
    (leftFrequency * (x + t)) (rightFrequency * x)
  rw [show leftFrequency * (x + t) - rightFrequency * x =
      (leftFrequency - rightFrequency) * x + leftFrequency * t by ring,
    show leftFrequency * (x + t) + rightFrequency * x =
      (leftFrequency + rightFrequency) * x + leftFrequency * t by ring] at htrig
  linarith

private theorem yoshida_sine_cross_product_to_sum
    (leftFrequency rightFrequency t x : Real) :
    Real.sin (leftFrequency * (x + t)) * Real.sin (rightFrequency * x) =
      (Real.cos ((leftFrequency - rightFrequency) * x + leftFrequency * t) -
        Real.cos ((leftFrequency + rightFrequency) * x + leftFrequency * t)) / 2 := by
  have htrig := Real.two_mul_sin_mul_sin
    (leftFrequency * (x + t)) (rightFrequency * x)
  rw [show leftFrequency * (x + t) - rightFrequency * x =
      (leftFrequency - rightFrequency) * x + leftFrequency * t by ring,
    show leftFrequency * (x + t) + rightFrequency * x =
      (leftFrequency + rightFrequency) * x + leftFrequency * t by ring] at htrig
  linarith

private theorem hasDerivAt_yoshidaCosineCrossCorrelationPrimitive
    {leftFrequency rightFrequency t x : Real}
    (hdifference : leftFrequency - rightFrequency ≠ 0)
    (htotal : leftFrequency + rightFrequency ≠ 0) :
    HasDerivAt
      (yoshidaCosineCrossCorrelationPrimitive leftFrequency rightFrequency t)
      (Real.cos (leftFrequency * (x + t)) * Real.cos (rightFrequency * x)) x := by
  have hdifferenceLinear :
      HasDerivAt
        (fun y : Real =>
          (leftFrequency - rightFrequency) * y + leftFrequency * t)
        (leftFrequency - rightFrequency) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul
        (leftFrequency - rightFrequency)).add_const (leftFrequency * t)
  have htotalLinear :
      HasDerivAt
        (fun y : Real =>
          (leftFrequency + rightFrequency) * y + leftFrequency * t)
        (leftFrequency + rightFrequency) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul
        (leftFrequency + rightFrequency)).add_const (leftFrequency * t)
  have hfirst := hdifferenceLinear.sin.div_const
    (2 * (leftFrequency - rightFrequency))
  have hsecond := htotalLinear.sin.div_const
    (2 * (leftFrequency + rightFrequency))
  have hderiv :
      HasDerivAt
        (yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t)
        ((Real.cos
            ((leftFrequency - rightFrequency) * x + leftFrequency * t) +
          Real.cos
            ((leftFrequency + rightFrequency) * x + leftFrequency * t)) / 2) x := by
    unfold yoshidaCosineCrossCorrelationPrimitive
    convert hfirst.add hsecond using 1 <;> try rfl
    field_simp [hdifference, htotal]
  simpa only [yoshida_cosine_cross_product_to_sum] using hderiv

private theorem hasDerivAt_yoshidaSineCrossCorrelationPrimitive
    {leftFrequency rightFrequency t x : Real}
    (hdifference : leftFrequency - rightFrequency ≠ 0)
    (htotal : leftFrequency + rightFrequency ≠ 0) :
    HasDerivAt
      (yoshidaSineCrossCorrelationPrimitive leftFrequency rightFrequency t)
      (Real.sin (leftFrequency * (x + t)) * Real.sin (rightFrequency * x)) x := by
  have hdifferenceLinear :
      HasDerivAt
        (fun y : Real =>
          (leftFrequency - rightFrequency) * y + leftFrequency * t)
        (leftFrequency - rightFrequency) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul
        (leftFrequency - rightFrequency)).add_const (leftFrequency * t)
  have htotalLinear :
      HasDerivAt
        (fun y : Real =>
          (leftFrequency + rightFrequency) * y + leftFrequency * t)
        (leftFrequency + rightFrequency) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul
        (leftFrequency + rightFrequency)).add_const (leftFrequency * t)
  have hfirst := hdifferenceLinear.sin.div_const
    (2 * (leftFrequency - rightFrequency))
  have hsecond := htotalLinear.sin.div_const
    (2 * (leftFrequency + rightFrequency))
  have hderiv :
      HasDerivAt
        (yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t)
        ((Real.cos
            ((leftFrequency - rightFrequency) * x + leftFrequency * t) -
          Real.cos
            ((leftFrequency + rightFrequency) * x + leftFrequency * t)) / 2) x := by
    unfold yoshidaSineCrossCorrelationPrimitive
    convert hfirst.sub hsecond using 1 <;> try rfl
    field_simp [hdifference, htotal]
  simpa only [yoshida_sine_cross_product_to_sum] using hderiv

private theorem hasDerivAt_yoshidaCosineCorrelationPrimitive
    {w t x : Real} (hw : w ≠ 0) :
    HasDerivAt (yoshidaCosineCorrelationPrimitive w t)
      (Real.cos (w * (x + t)) * Real.cos (w * x)) x := by
  have hderiv :
      HasDerivAt (yoshidaCosineCorrelationPrimitive w t)
        ((Real.cos (w * t) + Real.cos (2 * w * x + w * t)) / 2) x := by
    unfold yoshidaCosineCorrelationPrimitive
    have hlinear :
        HasDerivAt (fun y : Real => 2 * w * y + w * t) (2 * w) x :=
      by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id x).const_mul (2 * w)).add_const (w * t)
    have hfirst :=
      ((hasDerivAt_id x).const_mul (Real.cos (w * t))).div_const 2
    have hsecond := hlinear.sin.div_const (4 * w)
    convert hfirst.add hsecond using 1 <;> try rfl
    field_simp [hw]
    ring
  simpa only [yoshida_cosine_product_to_sum] using hderiv

private theorem hasDerivAt_yoshidaSineCorrelationPrimitive
    {w t x : Real} (hw : w ≠ 0) :
    HasDerivAt (yoshidaSineCorrelationPrimitive w t)
      (Real.sin (w * (x + t)) * Real.sin (w * x)) x := by
  have hderiv :
      HasDerivAt (yoshidaSineCorrelationPrimitive w t)
        ((Real.cos (w * t) - Real.cos (2 * w * x + w * t)) / 2) x := by
    unfold yoshidaSineCorrelationPrimitive
    have hlinear :
        HasDerivAt (fun y : Real => 2 * w * y + w * t) (2 * w) x :=
      by
        simpa only [id_eq, mul_one] using
          ((hasDerivAt_id x).const_mul (2 * w)).add_const (w * t)
    have hfirst :=
      ((hasDerivAt_id x).const_mul (Real.cos (w * t))).div_const 2
    have hsecond := hlinear.sin.div_const (4 * w)
    convert hfirst.sub hsecond using 1 <;> try rfl
    field_simp [hw]
    ring
  simpa only [yoshida_sine_product_to_sum] using hderiv

theorem integral_Icc_yoshidaCosineCorrelation
    {a b w t : Real} (hab : a ≤ b) (hw : w ≠ 0) :
    (∫ x in Set.Icc a b,
        ((Real.cos (w * (x + t)) * Real.cos (w * x) : Real) : Complex)) =
      ((yoshidaCosineCorrelationPrimitive w t b -
        yoshidaCosineCorrelationPrimitive w t a : Real) : Complex) := by
  have hreal :
      (∫ x in a..b,
          Real.cos (w * (x + t)) * Real.cos (w * x)) =
        yoshidaCosineCorrelationPrimitive w t b -
          yoshidaCosineCorrelationPrimitive w t a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun _ _ => hasDerivAt_yoshidaCosineCorrelationPrimitive hw)
      (by
        exact (by fun_prop : Continuous fun x : Real =>
          Real.cos (w * (x + t)) * Real.cos (w * x)).intervalIntegrable a b)
  calc
    (∫ x in Set.Icc a b,
        ((Real.cos (w * (x + t)) * Real.cos (w * x) : Real) : Complex)) =
        ∫ x in a..b,
          ((Real.cos (w * (x + t)) * Real.cos (w * x) : Real) : Complex) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hab]
    _ = ((∫ x in a..b,
          Real.cos (w * (x + t)) * Real.cos (w * x)) : Real) :=
      intervalIntegral.integral_ofReal
    _ = ((yoshidaCosineCorrelationPrimitive w t b -
        yoshidaCosineCorrelationPrimitive w t a : Real) : Complex) := by
      rw [hreal]

theorem integral_Icc_yoshidaSineCorrelation
    {a b w t : Real} (hab : a ≤ b) (hw : w ≠ 0) :
    (∫ x in Set.Icc a b,
        ((Real.sin (w * (x + t)) * Real.sin (w * x) : Real) : Complex)) =
      ((yoshidaSineCorrelationPrimitive w t b -
        yoshidaSineCorrelationPrimitive w t a : Real) : Complex) := by
  have hreal :
      (∫ x in a..b,
          Real.sin (w * (x + t)) * Real.sin (w * x)) =
        yoshidaSineCorrelationPrimitive w t b -
          yoshidaSineCorrelationPrimitive w t a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun _ _ => hasDerivAt_yoshidaSineCorrelationPrimitive hw)
      (by
        exact (by fun_prop : Continuous fun x : Real =>
          Real.sin (w * (x + t)) * Real.sin (w * x)).intervalIntegrable a b)
  calc
    (∫ x in Set.Icc a b,
        ((Real.sin (w * (x + t)) * Real.sin (w * x) : Real) : Complex)) =
        ∫ x in a..b,
          ((Real.sin (w * (x + t)) * Real.sin (w * x) : Real) : Complex) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hab]
    _ = ((∫ x in a..b,
          Real.sin (w * (x + t)) * Real.sin (w * x)) : Real) :=
      intervalIntegral.integral_ofReal
    _ = ((yoshidaSineCorrelationPrimitive w t b -
        yoshidaSineCorrelationPrimitive w t a : Real) : Complex) := by
      rw [hreal]

theorem integral_Icc_yoshidaCosineCrossCorrelation
    {a b leftFrequency rightFrequency t : Real} (hab : a ≤ b)
    (hdifference : leftFrequency - rightFrequency ≠ 0)
    (htotal : leftFrequency + rightFrequency ≠ 0) :
    (∫ x in Set.Icc a b,
        ((Real.cos (leftFrequency * (x + t)) *
          Real.cos (rightFrequency * x) : Real) : Complex)) =
      ((yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t b -
        yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t a : Real) : Complex) := by
  have hreal :
      (∫ x in a..b,
          Real.cos (leftFrequency * (x + t)) *
            Real.cos (rightFrequency * x)) =
        yoshidaCosineCrossCorrelationPrimitive
            leftFrequency rightFrequency t b -
          yoshidaCosineCrossCorrelationPrimitive
            leftFrequency rightFrequency t a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun _ _ =>
        hasDerivAt_yoshidaCosineCrossCorrelationPrimitive
          hdifference htotal)
      (by
        exact (by fun_prop : Continuous fun x : Real =>
          Real.cos (leftFrequency * (x + t)) *
            Real.cos (rightFrequency * x)).intervalIntegrable a b)
  calc
    (∫ x in Set.Icc a b,
        ((Real.cos (leftFrequency * (x + t)) *
          Real.cos (rightFrequency * x) : Real) : Complex)) =
        ∫ x in a..b,
          ((Real.cos (leftFrequency * (x + t)) *
            Real.cos (rightFrequency * x) : Real) : Complex) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hab]
    _ = ((∫ x in a..b,
          Real.cos (leftFrequency * (x + t)) *
            Real.cos (rightFrequency * x)) : Real) :=
      intervalIntegral.integral_ofReal
    _ = ((yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t b -
        yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t a : Real) : Complex) := by
      rw [hreal]

theorem integral_Icc_yoshidaSineCrossCorrelation
    {a b leftFrequency rightFrequency t : Real} (hab : a ≤ b)
    (hdifference : leftFrequency - rightFrequency ≠ 0)
    (htotal : leftFrequency + rightFrequency ≠ 0) :
    (∫ x in Set.Icc a b,
        ((Real.sin (leftFrequency * (x + t)) *
          Real.sin (rightFrequency * x) : Real) : Complex)) =
      ((yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t b -
        yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t a : Real) : Complex) := by
  have hreal :
      (∫ x in a..b,
          Real.sin (leftFrequency * (x + t)) *
            Real.sin (rightFrequency * x)) =
        yoshidaSineCrossCorrelationPrimitive
            leftFrequency rightFrequency t b -
          yoshidaSineCrossCorrelationPrimitive
            leftFrequency rightFrequency t a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun _ _ =>
        hasDerivAt_yoshidaSineCrossCorrelationPrimitive
          hdifference htotal)
      (by
        exact (by fun_prop : Continuous fun x : Real =>
          Real.sin (leftFrequency * (x + t)) *
            Real.sin (rightFrequency * x)).intervalIntegrable a b)
  calc
    (∫ x in Set.Icc a b,
        ((Real.sin (leftFrequency * (x + t)) *
          Real.sin (rightFrequency * x) : Real) : Complex)) =
        ∫ x in a..b,
          ((Real.sin (leftFrequency * (x + t)) *
            Real.sin (rightFrequency * x) : Real) : Complex) := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hab]
    _ = ((∫ x in a..b,
          Real.sin (leftFrequency * (x + t)) *
            Real.sin (rightFrequency * x)) : Real) :=
      intervalIntegral.integral_ofReal
    _ = ((yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t b -
        yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t a : Real) : Complex) := by
      rw [hreal]

theorem suzukiDF6D4AlternatingSign_cast_real (mode : Nat) :
    ((suzukiDF6D4AlternatingSign mode : Rat) : Real) =
      -((-1 : Real) ^ mode) := by
  unfold suzukiDF6D4AlternatingSign
  rw [neg_one_pow_eq_pow_mod_two]
  have hmod : mode % 2 = 0 ∨ mode % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod]

/-- The prime-2 part of the independent even DF6D4 off-diagonal
convolution. -/
def suzukiDF6D4EvenOffDiagonalPrimeTerm (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  ((1 / 2 : Real) * suzukiDF6D4EvenModeScale left *
      suzukiDF6D4EvenModeScale right * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiDF6D4PrimeSineTransform right -
          suzukiDF6D4PrimeSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiDF6D4PrimeSineTransform left +
          suzukiDF6D4PrimeSineTransform right))

/-- The prime-2 part of the independent odd DF6D4 off-diagonal
convolution. -/
def suzukiDF6D4OddOffDiagonalPrimeTerm (left right : Nat) : Real :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    -(suzukiDF6D4AlternatingSign (left + right) / (left + right))
  ((1 / 2 : Real) * Real.pi⁻¹) *
    (((differenceCoefficient : Rat) : Real) *
        (suzukiDF6D4PrimeSineTransform right -
          suzukiDF6D4PrimeSineTransform left) +
      ((totalCoefficient : Rat) : Real) *
        (suzukiDF6D4PrimeSineTransform left +
          suzukiDF6D4PrimeSineTransform right))

private theorem yoshidaCosineCrossCorrelationPrimitive_endpoint_sub
    {r t : Real} (hr : 0 < r) (left right : Nat) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - left
    let total := left + right
    yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t (r - t) -
        yoshidaCosineCrossCorrelationPrimitive
          leftFrequency rightFrequency t (-r) =
      r / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference +
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total) := by
  dsimp only
  let leftFrequency : Real := (left : Real) * Real.pi / r
  let rightFrequency : Real := (right : Real) * Real.pi / r
  let difference : Nat := right - left
  let total : Nat := left + right
  have hdifference : 0 < difference := Nat.sub_pos_of_lt hlt
  have htotal : 0 < total := by
    dsimp only [total]
    omega
  have hdifferenceReal : (difference : Real) ≠ 0 := by
    exact_mod_cast hdifference.ne'
  have htotalReal : (total : Real) ≠ 0 := by
    exact_mod_cast htotal.ne'
  have hleftRadius : leftFrequency * r = (left : Real) * Real.pi := by
    dsimp only [leftFrequency]
    field_simp [hr.ne']
  have hrightRadius : rightFrequency * r = (right : Real) * Real.pi := by
    dsimp only [rightFrequency]
    field_simp [hr.ne']
  have hfrequencyDifference :
      leftFrequency - rightFrequency =
        -((difference : Real) * Real.pi / r) := by
    dsimp only [leftFrequency, rightFrequency, difference]
    rw [Nat.cast_sub hlt.le]
    ring
  have hfrequencyTotal :
      leftFrequency + rightFrequency =
        (total : Real) * Real.pi / r := by
    dsimp only [leftFrequency, rightFrequency, total]
    push_cast
    ring
  have hdifferenceUpperPhase :
      (leftFrequency - rightFrequency) * (r - t) + leftFrequency * t =
        rightFrequency * t - (difference : Real) * Real.pi := by
    calc
      _ = (leftFrequency - rightFrequency) * r + rightFrequency * t := by ring
      _ = leftFrequency * r - rightFrequency * r +
          rightFrequency * t := by ring
      _ = (left : Real) * Real.pi - (right : Real) * Real.pi +
          rightFrequency * t := by rw [hleftRadius, hrightRadius]
      _ = rightFrequency * t - (difference : Real) * Real.pi := by
        dsimp only [difference]
        rw [Nat.cast_sub hlt.le]
        ring
  have hdifferenceLowerPhase :
      (leftFrequency - rightFrequency) * (-r) + leftFrequency * t =
        leftFrequency * t + (difference : Real) * Real.pi := by
    calc
      _ = -(leftFrequency * r) + rightFrequency * r +
          leftFrequency * t := by ring
      _ = -(left : Real) * Real.pi + (right : Real) * Real.pi +
          leftFrequency * t := by rw [hleftRadius, hrightRadius]; ring
      _ = leftFrequency * t + (difference : Real) * Real.pi := by
        dsimp only [difference]
        rw [Nat.cast_sub hlt.le]
        ring
  have htotalUpperPhase :
      (leftFrequency + rightFrequency) * (r - t) + leftFrequency * t =
        (total : Real) * Real.pi - rightFrequency * t := by
    calc
      _ = (leftFrequency + rightFrequency) * r - rightFrequency * t := by ring
      _ = leftFrequency * r + rightFrequency * r - rightFrequency * t := by ring
      _ = (left : Real) * Real.pi + (right : Real) * Real.pi -
          rightFrequency * t := by rw [hleftRadius, hrightRadius]
      _ = (total : Real) * Real.pi - rightFrequency * t := by
        dsimp only [total]
        push_cast
        ring
  have htotalLowerPhase :
      (leftFrequency + rightFrequency) * (-r) + leftFrequency * t =
        leftFrequency * t - (total : Real) * Real.pi := by
    calc
      _ = leftFrequency * t -
          (leftFrequency * r + rightFrequency * r) := by ring
      _ = leftFrequency * t -
          ((left : Real) * Real.pi + (right : Real) * Real.pi) := by
        rw [hleftRadius, hrightRadius]
      _ = leftFrequency * t - (total : Real) * Real.pi := by
        dsimp only [total]
        push_cast
        ring
  have hdifferenceUpperSin :
      Real.sin
          ((leftFrequency - rightFrequency) * (r - t) + leftFrequency * t) =
        (-1 : Real) ^ difference * Real.sin (rightFrequency * t) := by
    rw [hdifferenceUpperPhase]
    exact Real.sin_sub_nat_mul_pi (rightFrequency * t) difference
  have hdifferenceLowerSin :
      Real.sin
          ((leftFrequency - rightFrequency) * (-r) + leftFrequency * t) =
        (-1 : Real) ^ difference * Real.sin (leftFrequency * t) := by
    rw [hdifferenceLowerPhase]
    exact Real.sin_add_nat_mul_pi (leftFrequency * t) difference
  have htotalUpperSin :
      Real.sin
          ((leftFrequency + rightFrequency) * (r - t) + leftFrequency * t) =
        -((-1 : Real) ^ total * Real.sin (rightFrequency * t)) := by
    rw [htotalUpperPhase]
    exact Real.sin_nat_mul_pi_sub (rightFrequency * t) total
  have htotalLowerSin :
      Real.sin
          ((leftFrequency + rightFrequency) * (-r) + leftFrequency * t) =
        (-1 : Real) ^ total * Real.sin (leftFrequency * t) := by
    rw [htotalLowerPhase]
    exact Real.sin_sub_nat_mul_pi (leftFrequency * t) total
  unfold yoshidaCosineCrossCorrelationPrimitive
  rw [hdifferenceUpperSin, hdifferenceLowerSin,
    htotalUpperSin, htotalLowerSin,
    hfrequencyDifference, hfrequencyTotal]
  dsimp only [leftFrequency, rightFrequency, difference, total] at *
  field_simp [hr.ne', Real.pi_ne_zero, hdifferenceReal, htotalReal]
  ring

private theorem yoshidaCrossTotalPrimitive_endpoint_sub
    {r t : Real} (hr : 0 < r) (left right : Nat) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let total := left + right
    Real.sin
          ((leftFrequency + rightFrequency) * (r - t) + leftFrequency * t) /
          (2 * (leftFrequency + rightFrequency)) -
        Real.sin
          ((leftFrequency + rightFrequency) * (-r) + leftFrequency * t) /
          (2 * (leftFrequency + rightFrequency)) =
      r / (2 * Real.pi) *
        (-((-1 : Real) ^ total) *
          (Real.sin (leftFrequency * t) +
            Real.sin (rightFrequency * t)) / total) := by
  dsimp only
  let leftFrequency : Real := (left : Real) * Real.pi / r
  let rightFrequency : Real := (right : Real) * Real.pi / r
  let total : Nat := left + right
  have htotal : 0 < total := by
    dsimp only [total]
    omega
  have htotalReal : (total : Real) ≠ 0 := by
    exact_mod_cast htotal.ne'
  have hleftRadius : leftFrequency * r = (left : Real) * Real.pi := by
    dsimp only [leftFrequency]
    field_simp [hr.ne']
  have hrightRadius : rightFrequency * r = (right : Real) * Real.pi := by
    dsimp only [rightFrequency]
    field_simp [hr.ne']
  have hfrequencyTotal :
      leftFrequency + rightFrequency =
        (total : Real) * Real.pi / r := by
    dsimp only [leftFrequency, rightFrequency, total]
    push_cast
    ring
  have hupperPhase :
      (leftFrequency + rightFrequency) * (r - t) + leftFrequency * t =
        (total : Real) * Real.pi - rightFrequency * t := by
    calc
      _ = (leftFrequency + rightFrequency) * r - rightFrequency * t := by ring
      _ = leftFrequency * r + rightFrequency * r - rightFrequency * t := by ring
      _ = (left : Real) * Real.pi + (right : Real) * Real.pi -
          rightFrequency * t := by rw [hleftRadius, hrightRadius]
      _ = (total : Real) * Real.pi - rightFrequency * t := by
        dsimp only [total]
        push_cast
        ring
  have hlowerPhase :
      (leftFrequency + rightFrequency) * (-r) + leftFrequency * t =
        leftFrequency * t - (total : Real) * Real.pi := by
    calc
      _ = leftFrequency * t -
          (leftFrequency * r + rightFrequency * r) := by ring
      _ = leftFrequency * t -
          ((left : Real) * Real.pi + (right : Real) * Real.pi) := by
        rw [hleftRadius, hrightRadius]
      _ = leftFrequency * t - (total : Real) * Real.pi := by
        dsimp only [total]
        push_cast
        ring
  have hupperSin :
      Real.sin
          ((leftFrequency + rightFrequency) * (r - t) + leftFrequency * t) =
        -((-1 : Real) ^ total * Real.sin (rightFrequency * t)) := by
    rw [hupperPhase]
    exact Real.sin_nat_mul_pi_sub (rightFrequency * t) total
  have hlowerSin :
      Real.sin
          ((leftFrequency + rightFrequency) * (-r) + leftFrequency * t) =
        (-1 : Real) ^ total * Real.sin (leftFrequency * t) := by
    rw [hlowerPhase]
    exact Real.sin_sub_nat_mul_pi (leftFrequency * t) total
  rw [hupperSin, hlowerSin, hfrequencyTotal]
  dsimp only [leftFrequency, rightFrequency, total] at *
  field_simp [hr.ne', Real.pi_ne_zero, htotalReal]
  ring

private theorem yoshidaSineCrossCorrelationPrimitive_endpoint_sub
    {r t : Real} (hr : 0 < r) (left right : Nat) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - left
    let total := left + right
    yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t (r - t) -
        yoshidaSineCrossCorrelationPrimitive
          leftFrequency rightFrequency t (-r) =
      r / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference -
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total) := by
  dsimp only
  have hcosine :=
    yoshidaCosineCrossCorrelationPrimitive_endpoint_sub
      (t := t) hr left right hlt
  have htotalTerm :=
    yoshidaCrossTotalPrimitive_endpoint_sub
      (t := t) hr left right hlt
  dsimp only at hcosine htotalTerm
  unfold yoshidaCosineCrossCorrelationPrimitive at hcosine
  unfold yoshidaSineCrossCorrelationPrimitive
  linear_combination hcosine - 2 * htotalTerm

private theorem inv_sqrt_mul_inv_sqrt
    {r : Real} (hr : 0 < r) :
    (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by
  have hsqrt : Real.sqrt r ≠ 0 := (Real.sqrt_pos.2 hr).ne'
  field_simp [hr.ne', hsqrt]
  exact (Real.sq_sqrt hr.le).symm

private theorem inv_sqrt_mul_inv_sqrt_complex
    {r : Real} (hr : 0 < r) :
    (((Real.sqrt r : Real) : Complex)⁻¹) *
        (((Real.sqrt r : Real) : Complex)⁻¹) =
      ((r⁻¹ : Real) : Complex) := by
  exact_mod_cast inv_sqrt_mul_inv_sqrt hr

private theorem inv_sqrt_two_mul_r_mul_inv_sqrt_r_complex
    {r : Real} (hr : 0 < r) :
    (((Real.sqrt (2 * r) : Real) : Complex)⁻¹) *
        (((Real.sqrt r : Real) : Complex)⁻¹) =
      (((Real.sqrt 2)⁻¹ * r⁻¹ : Real) : Complex) := by
  have hsqrtR : Real.sqrt r ≠ 0 := by positivity
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  norm_cast
  rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 2)]
  field_simp [hr.ne', hsqrtR, hsqrtTwo]
  nlinarith [Real.sq_sqrt hr.le]

private theorem yoshidaCosineCorrelationPrimitive_endpoint_sub
    {r t : Real} (hr : 0 < r) (mode : Nat) (hmode : 0 < mode) :
    let w := (mode : Real) * Real.pi / r
    yoshidaCosineCorrelationPrimitive w t (r - t) -
        yoshidaCosineCorrelationPrimitive w t (-r) =
      ((2 * r - t) * Real.cos (w * t) - Real.sin (w * t) / w) / 2 := by
  dsimp only
  let w : Real := (mode : Real) * Real.pi / r
  have hw : w ≠ 0 := by
    dsimp only [w]
    positivity
  have hwr : w * r = (mode : Real) * Real.pi := by
    dsimp only [w]
    field_simp [hr.ne']
  have hupperPhase :
      2 * w * (r - t) + w * t =
        (mode : Real) * (2 * Real.pi) - w * t := by
    calc
      _ = 2 * (w * r) - w * t := by ring
      _ = (mode : Real) * (2 * Real.pi) - w * t := by rw [hwr]; ring
  have hlowerPhase :
      2 * w * (-r) + w * t =
        w * t - (mode : Real) * (2 * Real.pi) := by
    calc
      _ = w * t - 2 * (w * r) := by ring
      _ = w * t - (mode : Real) * (2 * Real.pi) := by rw [hwr]; ring
  have hupperSin :
      Real.sin (2 * w * (r - t) + w * t) = -Real.sin (w * t) := by
    rw [hupperPhase]
    exact Real.sin_nat_mul_two_pi_sub (w * t) mode
  have hlowerSin :
      Real.sin (2 * w * (-r) + w * t) = Real.sin (w * t) := by
    rw [hlowerPhase]
    exact Real.sin_sub_nat_mul_two_pi (w * t) mode
  unfold yoshidaCosineCorrelationPrimitive
  rw [hupperSin, hlowerSin]
  ring

private theorem yoshidaSineCorrelationPrimitive_endpoint_sub
    {r t : Real} (hr : 0 < r) (mode : Nat) (hmode : 0 < mode) :
    let w := (mode : Real) * Real.pi / r
    yoshidaSineCorrelationPrimitive w t (r - t) -
        yoshidaSineCorrelationPrimitive w t (-r) =
      ((2 * r - t) * Real.cos (w * t) + Real.sin (w * t) / w) / 2 := by
  dsimp only
  let w : Real := (mode : Real) * Real.pi / r
  have hw : w ≠ 0 := by
    dsimp only [w]
    positivity
  have hwr : w * r = (mode : Real) * Real.pi := by
    dsimp only [w]
    field_simp [hr.ne']
  have hupperPhase :
      2 * w * (r - t) + w * t =
        (mode : Real) * (2 * Real.pi) - w * t := by
    calc
      _ = 2 * (w * r) - w * t := by ring
      _ = (mode : Real) * (2 * Real.pi) - w * t := by rw [hwr]; ring
  have hlowerPhase :
      2 * w * (-r) + w * t =
        w * t - (mode : Real) * (2 * Real.pi) := by
    calc
      _ = w * t - 2 * (w * r) := by ring
      _ = w * t - (mode : Real) * (2 * Real.pi) := by rw [hwr]; ring
  have hupperSin :
      Real.sin (2 * w * (r - t) + w * t) = -Real.sin (w * t) := by
    rw [hupperPhase]
    exact Real.sin_nat_mul_two_pi_sub (w * t) mode
  have hlowerSin :
      Real.sin (2 * w * (-r) + w * t) = Real.sin (w * t) := by
    rw [hlowerPhase]
    exact Real.sin_sub_nat_mul_two_pi (w * t) mode
  unfold yoshidaSineCorrelationPrimitive
  rw [hupperSin, hlowerSin]
  ring

theorem suzukiYoshidaEvenL2_coeFn_of_pos
    {r : Real} (hr : 0 < r) {mode : Nat} (hmode : 0 < mode) :
    (suzukiYoshidaEvenL2 r hr mode : Real → Complex) =ᵐ[volume]
      suzukiYoshidaEvenPositiveFunction r mode := by
  have hpos :=
    suzukiYoshidaExponentialL2_coeFn hr (mode : Int)
  have hneg :=
    suzukiYoshidaExponentialL2_coeFn hr (-(mode : Int))
  have hadd :=
    Lp.coeFn_add (suzukiYoshidaExponentialL2 r hr (mode : Int))
      (suzukiYoshidaExponentialL2 r hr (-(mode : Int)))
  have hsmul :=
    Lp.coeFn_smul ((Real.sqrt 2 : Complex)⁻¹)
      (suzukiYoshidaExponentialL2 r hr (mode : Int) +
        suzukiYoshidaExponentialL2 r hr (-(mode : Int)))
  filter_upwards [hpos, hneg, hadd, hsmul] with x hxpos hxneg hxadd hxsmul
  unfold suzukiYoshidaEvenL2
  rw [dif_neg hmode.ne']
  rw [hxsmul]
  simp only [Pi.smul_apply]
  rw [hxadd]
  simp only [Pi.add_apply]
  rw [hxpos, hxneg]
  unfold suzukiYoshidaExponentialFunction
    suzukiYoshidaEvenPositiveFunction
  by_cases hx : x ∈ Set.Icc (-r) r
  · simp only [Set.indicator_of_mem hx]
    let θ : Real := (mode : Real) * Real.pi * x / r
    have hphasePos :
        Complex.I *
            (((mode : Int) : Complex) * (Real.pi : Complex) /
              (r : Complex)) *
              (x : Complex) =
          (θ : Complex) * Complex.I := by
      dsimp only [θ]
      push_cast
      ring
    have hphaseNeg :
        Complex.I *
            (((-(mode : Int)) : Complex) * (Real.pi : Complex) /
              (r : Complex)) *
              (x : Complex) =
          (-θ : Real) * Complex.I := by
      dsimp only [θ]
      push_cast
      ring
    rw [hphasePos]
    rw [Int.cast_neg]
    rw [hphaseNeg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
      Real.cos_neg, Real.sin_neg]
    have htheta :
        θ = (mode : Real) * Real.pi * x / r := rfl
    rw [← htheta]
    push_cast
    simp only [smul_eq_mul]
    calc
      _ =
          (((Real.sqrt 2 : Real) : Complex)⁻¹ *
              ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ * 2) *
            Complex.cos (θ : Complex) := by ring
      _ = ((Real.sqrt r : Real) : Complex)⁻¹ *
            Complex.cos (θ : Complex) := by
        rw [yoshida_sqrt_normalization_complex hr]
  · simp [hx]

theorem suzukiYoshidaOddL2_coeFn
    {r : Real} (hr : 0 < r) (mode : Nat) :
    (suzukiYoshidaOddL2 r hr mode : Real → Complex) =ᵐ[volume]
      suzukiYoshidaOddFunction r mode := by
  have hpos :=
    suzukiYoshidaExponentialL2_coeFn hr (mode : Int)
  have hneg :=
    suzukiYoshidaExponentialL2_coeFn hr (-(mode : Int))
  have hsub :=
    Lp.coeFn_sub (suzukiYoshidaExponentialL2 r hr (mode : Int))
      (suzukiYoshidaExponentialL2 r hr (-(mode : Int)))
  have hsmul :=
    Lp.coeFn_smul ((Complex.I * (Real.sqrt 2 : Complex))⁻¹)
      (suzukiYoshidaExponentialL2 r hr (mode : Int) -
        suzukiYoshidaExponentialL2 r hr (-(mode : Int)))
  filter_upwards [hpos, hneg, hsub, hsmul] with x hxpos hxneg hxsub hxsmul
  unfold suzukiYoshidaOddL2
  rw [hxsmul]
  simp only [Pi.smul_apply]
  rw [hxsub]
  simp only [Pi.sub_apply]
  rw [hxpos, hxneg]
  unfold suzukiYoshidaExponentialFunction suzukiYoshidaOddFunction
  by_cases hx : x ∈ Set.Icc (-r) r
  · simp only [Set.indicator_of_mem hx]
    let θ : Real := (mode : Real) * Real.pi * x / r
    have hphasePos :
        Complex.I *
            (((mode : Int) : Complex) * (Real.pi : Complex) /
              (r : Complex)) *
              (x : Complex) =
          (θ : Complex) * Complex.I := by
      dsimp only [θ]
      push_cast
      ring
    have hphaseNeg :
        Complex.I *
            (((-(mode : Int)) : Complex) * (Real.pi : Complex) /
              (r : Complex)) *
              (x : Complex) =
          (-θ : Real) * Complex.I := by
      dsimp only [θ]
      push_cast
      ring
    rw [hphasePos]
    rw [Int.cast_neg]
    rw [hphaseNeg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
      Real.cos_neg, Real.sin_neg]
    have htheta :
        θ = (mode : Real) * Real.pi * x / r := rfl
    rw [← htheta]
    push_cast
    simp only [smul_eq_mul]
    calc
      _ =
          ((Complex.I * ((Real.sqrt 2 : Real) : Complex))⁻¹ *
              ((Real.sqrt (2 * r) : Real) : Complex)⁻¹ *
              (2 * Complex.I)) *
            Complex.sin (θ : Complex) := by ring
      _ = ((Real.sqrt r : Real) : Complex)⁻¹ *
            Complex.sin (θ : Complex) := by
        rw [yoshida_odd_sqrt_normalization_complex hr]
  · simp [hx]

theorem suzukiYoshidaEvenL2_coeFn_zero
    {r : Real} (hr : 0 < r) :
    (suzukiYoshidaEvenL2 r hr 0 : Real → Complex) =ᵐ[volume]
      suzukiYoshidaEvenZeroFunction r := by
  have hzero := suzukiYoshidaExponentialL2_coeFn hr 0
  filter_upwards [hzero] with x hx
  unfold suzukiYoshidaEvenL2
  rw [dif_pos rfl, hx]
  unfold suzukiYoshidaExponentialFunction suzukiYoshidaEvenZeroFunction
  by_cases hxmem : x ∈ Set.Icc (-r) r
  · simp [Set.indicator_of_mem hxmem]
  · simp [Set.indicator_of_notMem hxmem]

theorem inner_suzukiL2Translate_evenPositive_offDiagonal_eq_correlation
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - left
    let total := left + right
    inner Complex
        (suzukiL2Translate t (suzukiYoshidaEvenL2 r hr left))
        (suzukiYoshidaEvenL2 r hr right) =
      ((1 / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference +
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total) : Real) : Complex) := by
  dsimp only
  let leftFrequency : Real := (left : Real) * Real.pi / r
  let rightFrequency : Real := (right : Real) * Real.pi / r
  have hfrequencyDifference : leftFrequency - rightFrequency ≠ 0 := by
    have hfrequencyLt : leftFrequency < rightFrequency := by
      dsimp only [leftFrequency, rightFrequency]
      have hcast : (left : Real) < right := by exact_mod_cast hlt
      exact (div_lt_div_iff_of_pos_right hr).2
        (mul_lt_mul_of_pos_right hcast Real.pi_pos)
    exact sub_ne_zero.mpr (ne_of_lt hfrequencyLt)
  have hfrequencyTotal : leftFrequency + rightFrequency ≠ 0 := by
    have hright : 0 < right := hleft.trans hlt
    have hrightFrequency : 0 < rightFrequency := by
      dsimp only [rightFrequency]
      positivity
    have hleftFrequency : 0 ≤ leftFrequency := by
      dsimp only [leftFrequency]
      positivity
    positivity
  have hab : -r ≤ r - t := by linarith
  rw [inner_suzukiL2Translate_eq_integral_of_ae_two t
    (suzukiYoshidaEvenL2 r hr left)
    (suzukiYoshidaEvenL2 r hr right)
    (suzukiYoshidaEvenPositiveFunction r left)
    (suzukiYoshidaEvenPositiveFunction r right)
    (suzukiYoshidaEvenL2_coeFn_of_pos hr hleft)
    (suzukiYoshidaEvenL2_coeFn_of_pos hr (hleft.trans hlt))]
  unfold suzukiYoshidaEvenPositiveFunction
  rw [integral_symmetric_indicator_overlap_two ht0]
  have hpointwise :
      (∫ x in Set.Icc (-r) (r - t),
          (((Real.sqrt r)⁻¹ : Complex) *
              (Real.cos ((right : Real) * Real.pi * x / r) : Complex)) *
            conj (((Real.sqrt r)⁻¹ : Complex) *
              (Real.cos
                ((left : Real) * Real.pi * (x + t) / r) : Complex))) =
        ∫ x in Set.Icc (-r) (r - t),
          ((r⁻¹ : Real) : Complex) *
            ((Real.cos (leftFrequency * (x + t)) *
              Real.cos (rightFrequency * x) : Real) : Complex) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    calc
      _ = ((((Real.sqrt r : Real) : Complex)⁻¹) *
              (((Real.sqrt r : Real) : Complex)⁻¹)) *
            ((Real.cos
                ((left : Real) * Real.pi * (x + t) / r) : Complex) *
              (Real.cos
                ((right : Real) * Real.pi * x / r) : Complex)) := by ring
      _ = _ := by
        rw [inv_sqrt_mul_inv_sqrt_complex hr]
        dsimp only [leftFrequency, rightFrequency]
        push_cast
        ring
  rw [hpointwise, MeasureTheory.integral_const_mul,
    integral_Icc_yoshidaCosineCrossCorrelation hab
      hfrequencyDifference hfrequencyTotal,
    yoshidaCosineCrossCorrelationPrimitive_endpoint_sub hr left right hlt]
  norm_cast
  field_simp [hr.ne']

theorem inner_suzukiL2Translate_evenZero_offDiagonal_eq_correlation
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (right : Nat) (hright : 0 < right) :
    let leftFrequency := (0 : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - 0
    let total := 0 + right
    inner Complex
        (suzukiL2Translate t (suzukiYoshidaEvenL2 r hr 0))
        (suzukiYoshidaEvenL2 r hr right) =
      (((Real.sqrt 2)⁻¹ * (1 / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference +
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total)) : Real) : Complex) := by
  dsimp only
  let leftFrequency : Real := (0 : Real) * Real.pi / r
  let rightFrequency : Real := (right : Real) * Real.pi / r
  have hrightFrequency : rightFrequency ≠ 0 := by
    dsimp only [rightFrequency]
    positivity
  have hfrequencyDifference : leftFrequency - rightFrequency ≠ 0 := by
    simpa [leftFrequency] using (neg_ne_zero.mpr hrightFrequency)
  have hfrequencyTotal : leftFrequency + rightFrequency ≠ 0 := by
    simpa [leftFrequency] using hrightFrequency
  have hab : -r ≤ r - t := by linarith
  rw [inner_suzukiL2Translate_eq_integral_of_ae_two t
    (suzukiYoshidaEvenL2 r hr 0)
    (suzukiYoshidaEvenL2 r hr right)
    (suzukiYoshidaEvenZeroFunction r)
    (suzukiYoshidaEvenPositiveFunction r right)
    (suzukiYoshidaEvenL2_coeFn_zero hr)
    (suzukiYoshidaEvenL2_coeFn_of_pos hr hright)]
  unfold suzukiYoshidaEvenZeroFunction
    suzukiYoshidaEvenPositiveFunction
  rw [integral_symmetric_indicator_overlap_two ht0]
  have hpointwise :
      (∫ x in Set.Icc (-r) (r - t),
          (((Real.sqrt r)⁻¹ : Complex) *
              (Real.cos ((right : Real) * Real.pi * x / r) : Complex)) *
            conj (((Real.sqrt (2 * r))⁻¹ : Complex))) =
        ∫ x in Set.Icc (-r) (r - t),
          ((((Real.sqrt 2)⁻¹ * r⁻¹ : Real) : Complex)) *
            ((Real.cos (leftFrequency * (x + t)) *
              Real.cos (rightFrequency * x) : Real) : Complex) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp only [map_inv₀, Complex.conj_ofReal]
    calc
      _ = ((((Real.sqrt (2 * r) : Real) : Complex)⁻¹) *
              (((Real.sqrt r : Real) : Complex)⁻¹)) *
            (Real.cos ((right : Real) * Real.pi * x / r) : Complex) := by ring
      _ = _ := by
        rw [inv_sqrt_two_mul_r_mul_inv_sqrt_r_complex hr]
        dsimp only [leftFrequency, rightFrequency]
        simp only [zero_mul, zero_div, Real.cos_zero, one_mul]
        ring_nf
  rw [hpointwise, MeasureTheory.integral_const_mul,
    integral_Icc_yoshidaCosineCrossCorrelation hab
      hfrequencyDifference hfrequencyTotal]
  dsimp only [leftFrequency, rightFrequency]
  have hendpoint :=
    yoshidaCosineCrossCorrelationPrimitive_endpoint_sub
      (t := t) hr 0 right hright
  dsimp only at hendpoint
  simp only [Nat.cast_zero, zero_mul, zero_div] at hendpoint ⊢
  rw [hendpoint]
  norm_cast
  field_simp [hr.ne']

theorem inner_suzukiL2Translate_odd_offDiagonal_eq_correlation
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    let leftFrequency := (left : Real) * Real.pi / r
    let rightFrequency := (right : Real) * Real.pi / r
    let difference := right - left
    let total := left + right
    inner Complex
        (suzukiL2Translate t (suzukiYoshidaOddL2 r hr left))
        (suzukiYoshidaOddL2 r hr right) =
      ((1 / (2 * Real.pi) *
        (-((-1 : Real) ^ difference) *
            (Real.sin (rightFrequency * t) -
              Real.sin (leftFrequency * t)) / difference -
          -((-1 : Real) ^ total) *
            (Real.sin (leftFrequency * t) +
              Real.sin (rightFrequency * t)) / total) : Real) : Complex) := by
  dsimp only
  let leftFrequency : Real := (left : Real) * Real.pi / r
  let rightFrequency : Real := (right : Real) * Real.pi / r
  have hfrequencyDifference : leftFrequency - rightFrequency ≠ 0 := by
    have hfrequencyLt : leftFrequency < rightFrequency := by
      dsimp only [leftFrequency, rightFrequency]
      have hcast : (left : Real) < right := by exact_mod_cast hlt
      exact (div_lt_div_iff_of_pos_right hr).2
        (mul_lt_mul_of_pos_right hcast Real.pi_pos)
    exact sub_ne_zero.mpr (ne_of_lt hfrequencyLt)
  have hfrequencyTotal : leftFrequency + rightFrequency ≠ 0 := by
    have hright : 0 < right := hleft.trans hlt
    have hrightFrequency : 0 < rightFrequency := by
      dsimp only [rightFrequency]
      positivity
    have hleftFrequency : 0 ≤ leftFrequency := by
      dsimp only [leftFrequency]
      positivity
    positivity
  have hab : -r ≤ r - t := by linarith
  rw [inner_suzukiL2Translate_eq_integral_of_ae_two t
    (suzukiYoshidaOddL2 r hr left)
    (suzukiYoshidaOddL2 r hr right)
    (suzukiYoshidaOddFunction r left)
    (suzukiYoshidaOddFunction r right)
    (suzukiYoshidaOddL2_coeFn hr left)
    (suzukiYoshidaOddL2_coeFn hr right)]
  unfold suzukiYoshidaOddFunction
  rw [integral_symmetric_indicator_overlap_two ht0]
  have hpointwise :
      (∫ x in Set.Icc (-r) (r - t),
          (((Real.sqrt r)⁻¹ : Complex) *
              (Real.sin ((right : Real) * Real.pi * x / r) : Complex)) *
            conj (((Real.sqrt r)⁻¹ : Complex) *
              (Real.sin
                ((left : Real) * Real.pi * (x + t) / r) : Complex))) =
        ∫ x in Set.Icc (-r) (r - t),
          ((r⁻¹ : Real) : Complex) *
            ((Real.sin (leftFrequency * (x + t)) *
              Real.sin (rightFrequency * x) : Real) : Complex) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    calc
      _ = ((((Real.sqrt r : Real) : Complex)⁻¹) *
              (((Real.sqrt r : Real) : Complex)⁻¹)) *
            ((Real.sin
                ((left : Real) * Real.pi * (x + t) / r) : Complex) *
              (Real.sin
                ((right : Real) * Real.pi * x / r) : Complex)) := by ring
      _ = _ := by
        rw [inv_sqrt_mul_inv_sqrt_complex hr]
        dsimp only [leftFrequency, rightFrequency]
        push_cast
        ring
  rw [hpointwise, MeasureTheory.integral_const_mul,
    integral_Icc_yoshidaSineCrossCorrelation hab
      hfrequencyDifference hfrequencyTotal,
    yoshidaSineCrossCorrelationPrimitive_endpoint_sub hr left right hlt]
  norm_cast
  field_simp [hr.ne']

theorem inner_suzukiL2Translate_evenPositive_eq_correlation
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (mode : Nat) (hmode : 0 < mode) :
    let w := (mode : Real) * Real.pi / r
    inner Complex
        (suzukiL2Translate t (suzukiYoshidaEvenL2 r hr mode))
        (suzukiYoshidaEvenL2 r hr mode) =
      ((((2 * r - t) * Real.cos (w * t) - Real.sin (w * t) / w) /
        (2 * r) : Real) : Complex) := by
  dsimp only
  let w : Real := (mode : Real) * Real.pi / r
  have hw : w ≠ 0 := by
    dsimp only [w]
    positivity
  have hab : -r ≤ r - t := by linarith
  rw [inner_suzukiL2Translate_eq_integral_of_ae t
    (suzukiYoshidaEvenL2 r hr mode)
    (suzukiYoshidaEvenPositiveFunction r mode)
    (suzukiYoshidaEvenL2_coeFn_of_pos hr hmode)]
  unfold suzukiYoshidaEvenPositiveFunction
  rw [integral_symmetric_indicator_overlap ht0]
  have hpointwise :
      (∫ x in Set.Icc (-r) (r - t),
          (((Real.sqrt r)⁻¹ : Complex) *
              (Real.cos ((mode : Real) * Real.pi * x / r) : Complex)) *
            conj (((Real.sqrt r)⁻¹ : Complex) *
              (Real.cos ((mode : Real) * Real.pi * (x + t) / r) : Complex))) =
        ∫ x in Set.Icc (-r) (r - t),
          ((r⁻¹ : Real) : Complex) *
            ((Real.cos (w * (x + t)) * Real.cos (w * x) : Real) : Complex) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    change
      (((Real.sqrt r)⁻¹ : Complex) *
          (Real.cos ((mode : Real) * Real.pi * x / r) : Complex)) *
        conj (((Real.sqrt r)⁻¹ : Complex) *
          (Real.cos ((mode : Real) * Real.pi * (x + t) / r) : Complex)) =
      ((r⁻¹ : Real) : Complex) *
        ((Real.cos (w * (x + t)) * Real.cos (w * x) : Real) : Complex)
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    calc
      _ = ((((Real.sqrt r : Real) : Complex)⁻¹) *
              (((Real.sqrt r : Real) : Complex)⁻¹)) *
            ((Real.cos ((mode : Real) * Real.pi * x / r) : Complex) *
              (Real.cos ((mode : Real) * Real.pi * (x + t) / r) : Complex)) := by
          ring
      _ = _ := by
        rw [inv_sqrt_mul_inv_sqrt_complex hr]
        dsimp only [w]
        push_cast
        ring
  rw [hpointwise, MeasureTheory.integral_const_mul,
    integral_Icc_yoshidaCosineCorrelation hab hw,
    yoshidaCosineCorrelationPrimitive_endpoint_sub hr mode hmode]
  norm_cast
  field_simp [hr.ne']

theorem inner_suzukiL2Translate_odd_eq_correlation
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r)
    (mode : Nat) (hmode : 0 < mode) :
    let w := (mode : Real) * Real.pi / r
    inner Complex
        (suzukiL2Translate t (suzukiYoshidaOddL2 r hr mode))
        (suzukiYoshidaOddL2 r hr mode) =
      ((((2 * r - t) * Real.cos (w * t) + Real.sin (w * t) / w) /
        (2 * r) : Real) : Complex) := by
  dsimp only
  let w : Real := (mode : Real) * Real.pi / r
  have hw : w ≠ 0 := by
    dsimp only [w]
    positivity
  have hab : -r ≤ r - t := by linarith
  rw [inner_suzukiL2Translate_eq_integral_of_ae t
    (suzukiYoshidaOddL2 r hr mode)
    (suzukiYoshidaOddFunction r mode)
    (suzukiYoshidaOddL2_coeFn hr mode)]
  unfold suzukiYoshidaOddFunction
  rw [integral_symmetric_indicator_overlap ht0]
  have hpointwise :
      (∫ x in Set.Icc (-r) (r - t),
          (((Real.sqrt r)⁻¹ : Complex) *
              (Real.sin ((mode : Real) * Real.pi * x / r) : Complex)) *
            conj (((Real.sqrt r)⁻¹ : Complex) *
              (Real.sin ((mode : Real) * Real.pi * (x + t) / r) : Complex))) =
        ∫ x in Set.Icc (-r) (r - t),
          ((r⁻¹ : Real) : Complex) *
            ((Real.sin (w * (x + t)) * Real.sin (w * x) : Real) : Complex) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x _
    change
      (((Real.sqrt r)⁻¹ : Complex) *
          (Real.sin ((mode : Real) * Real.pi * x / r) : Complex)) *
        conj (((Real.sqrt r)⁻¹ : Complex) *
          (Real.sin ((mode : Real) * Real.pi * (x + t) / r) : Complex)) =
      ((r⁻¹ : Real) : Complex) *
        ((Real.sin (w * (x + t)) * Real.sin (w * x) : Real) : Complex)
    simp only [map_mul, map_inv₀, Complex.conj_ofReal]
    calc
      _ = ((((Real.sqrt r : Real) : Complex)⁻¹) *
              (((Real.sqrt r : Real) : Complex)⁻¹)) *
            ((Real.sin ((mode : Real) * Real.pi * x / r) : Complex) *
              (Real.sin ((mode : Real) * Real.pi * (x + t) / r) : Complex)) := by
          ring
      _ = _ := by
        rw [inv_sqrt_mul_inv_sqrt_complex hr]
        dsimp only [w]
        push_cast
        ring
  rw [hpointwise, MeasureTheory.integral_const_mul,
    integral_Icc_yoshidaSineCorrelation hab hw,
    yoshidaSineCorrelationPrimitive_endpoint_sub hr mode hmode]
  norm_cast
  field_simp [hr.ne']

private theorem suzukiL2SymmetricTranslationEnergy_eq_twice_of_inner_of_even
    {t : Real} {u v : SuzukiL2} {c : Real}
    (hu : SuzukiL2Even u) (hv : SuzukiL2Even v)
    (hinner : inner Complex (suzukiL2Translate t u) v = (c : Complex)) :
    suzukiL2SymmetricTranslationEnergy t u v = ((2 * c : Real) : Complex) := by
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

private theorem suzukiL2SymmetricTranslationEnergy_eq_twice_of_inner_of_odd
    {t : Real} {u v : SuzukiL2} {c : Real}
    (hu : SuzukiL2Odd u) (hv : SuzukiL2Odd v)
    (hinner : inner Complex (suzukiL2Translate t u) v = (c : Complex)) :
    suzukiL2SymmetricTranslationEnergy t u v = ((2 * c : Real) : Complex) := by
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

private theorem suzukiL2SymmetricTranslationEnergy_self_eq_twice_of_inner
    {t : Real} {v : SuzukiL2} {c : Real}
    (hinner : inner Complex (suzukiL2Translate t v) v = (c : Complex)) :
    suzukiL2SymmetricTranslationEnergy t v v = ((2 * c : Real) : Complex) := by
  have hreverse :
      inner Complex v (suzukiL2Translate t v) = (c : Complex) := by
    calc
      _ = conj (inner Complex (suzukiL2Translate t v) v) :=
        (inner_conj_symm (𝕜 := Complex) v (suzukiL2Translate t v)).symm
      _ = (c : Complex) := by rw [hinner, Complex.conj_ofReal]
  unfold suzukiL2SymmetricTranslationEnergy
  rw [suzukiL2TranslateCLM_apply, hinner, hreverse]
  push_cast
  ring

theorem inner_suzukiL2Translate_evenPositive_aStar_eq_DF6D4
    (mode : Nat) (hmode : 0 < mode) :
    inner Complex
        (suzukiL2Translate (Real.log 2)
          (suzukiYoshidaEvenL2
            suzukiProjectAStar suzukiProjectAStar_pos mode))
        (suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos mode) =
      (suzukiDF6D4EvenDiagonalPrimeCorrelation mode : Complex) := by
  rw [inner_suzukiL2Translate_evenPositive_eq_correlation
    suzukiProjectAStar_pos (Real.log_nonneg (by norm_num))
    (log_two_lt_two_mul_suzukiProjectAStar.le) mode hmode]
  norm_cast
  unfold suzukiDF6D4EvenDiagonalPrimeCorrelation
    suzukiDF6D4DiagonalPrimeDisplacement
    suzukiDF6D4DiagonalFrequency
  rw [if_neg hmode.ne']
  have hangle :
      (mode : Real) * Real.pi / suzukiProjectAStar * Real.log 2 =
        ((mode : Real) * Real.pi) *
          (Real.log 2 / suzukiProjectAStar) := by ring
  rw [hangle]
  have hmodeReal : (mode : Real) ≠ 0 := by exact_mod_cast hmode.ne'
  field_simp [suzukiProjectAStar_pos.ne', hmodeReal, Real.pi_ne_zero]

theorem inner_suzukiL2Translate_odd_aStar_eq_DF6D4
    (mode : Nat) (hmode : 0 < mode) :
    inner Complex
        (suzukiL2Translate (Real.log 2)
          (suzukiYoshidaOddL2
            suzukiProjectAStar suzukiProjectAStar_pos mode))
        (suzukiYoshidaOddL2
          suzukiProjectAStar suzukiProjectAStar_pos mode) =
      (suzukiDF6D4OddDiagonalPrimeCorrelation mode : Complex) := by
  rw [inner_suzukiL2Translate_odd_eq_correlation
    suzukiProjectAStar_pos (Real.log_nonneg (by norm_num))
    (log_two_lt_two_mul_suzukiProjectAStar.le) mode hmode]
  norm_cast
  unfold suzukiDF6D4OddDiagonalPrimeCorrelation
    suzukiDF6D4DiagonalPrimeDisplacement
    suzukiDF6D4DiagonalFrequency
  have hangle :
      (mode : Real) * Real.pi / suzukiProjectAStar * Real.log 2 =
        ((mode : Real) * Real.pi) *
          (Real.log 2 / suzukiProjectAStar) := by ring
  rw [hangle]
  have hmodeReal : (mode : Real) ≠ 0 := by exact_mod_cast hmode.ne'
  field_simp [suzukiProjectAStar_pos.ne', hmodeReal, Real.pi_ne_zero]

theorem suzukiL2SymmetricTranslationEnergy_evenPositive_aStar_eq_DF6D4
    (mode : Nat) (hmode : 0 < mode) :
    suzukiL2SymmetricTranslationEnergy (Real.log 2)
        (suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos mode)
        (suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos mode) =
      ((2 * suzukiDF6D4EvenDiagonalPrimeCorrelation mode : Real) : Complex) :=
  suzukiL2SymmetricTranslationEnergy_self_eq_twice_of_inner
    (inner_suzukiL2Translate_evenPositive_aStar_eq_DF6D4 mode hmode)

theorem suzukiL2SymmetricTranslationEnergy_odd_aStar_eq_DF6D4
    (mode : Nat) (hmode : 0 < mode) :
    suzukiL2SymmetricTranslationEnergy (Real.log 2)
        (suzukiYoshidaOddL2
          suzukiProjectAStar suzukiProjectAStar_pos mode)
        (suzukiYoshidaOddL2
          suzukiProjectAStar suzukiProjectAStar_pos mode) =
      ((2 * suzukiDF6D4OddDiagonalPrimeCorrelation mode : Real) : Complex) :=
  suzukiL2SymmetricTranslationEnergy_self_eq_twice_of_inner
    (inner_suzukiL2Translate_odd_aStar_eq_DF6D4 mode hmode)

theorem suzukiYoshidaPrimeTwoForm_evenPositiveDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      (suzukiDF6D4EvenDiagonalPrimeTerm mode : Complex) := by
  unfold suzukiYoshidaPrimeTwoForm suzukiL2FiniteTranslationEnergy
  rw [suzukiProjectPrimeIndexSet_at_aStar, Finset.sum_singleton,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  unfold suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
    suzukiDF6D4EvenDiagonalPrimeTerm
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  rw [suzukiL2SymmetricTranslationEnergy_evenPositive_aStar_eq_DF6D4
    mode hmode]
  norm_cast
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrtTwo]
  rw [hsquare]

theorem suzukiYoshidaPrimeTwoForm_oddDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      (suzukiDF6D4OddDiagonalPrimeTerm mode : Complex) := by
  unfold suzukiYoshidaPrimeTwoForm suzukiL2FiniteTranslationEnergy
  rw [suzukiProjectPrimeIndexSet_at_aStar, Finset.sum_singleton,
    suzukiYoshidaOddLinearCompletionOfSource_toL2]
  unfold suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
    suzukiDF6D4OddDiagonalPrimeTerm
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  rw [suzukiL2SymmetricTranslationEnergy_odd_aStar_eq_DF6D4 mode hmode]
  norm_cast
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrtTwo]
  rw [hsquare]

theorem inner_suzukiL2Translate_evenZero_eq_correlation
    {r t : Real} (hr : 0 < r) (ht0 : 0 ≤ t) (ht : t ≤ 2 * r) :
    inner Complex
        (suzukiL2Translate t (suzukiYoshidaEvenL2 r hr 0))
        (suzukiYoshidaEvenL2 r hr 0) =
      (((1 - t / (2 * r) : Real)) : Complex) := by
  have hab : -r ≤ r - t := by linarith
  rw [inner_suzukiL2Translate_eq_integral_of_ae t
    (suzukiYoshidaEvenL2 r hr 0)
    (suzukiYoshidaEvenZeroFunction r)
    (suzukiYoshidaEvenL2_coeFn_zero hr)]
  unfold suzukiYoshidaEvenZeroFunction
  rw [integral_symmetric_indicator_overlap ht0]
  have hpointwise :
      (∫ x in Set.Icc (-r) (r - t),
          (((Real.sqrt (2 * r))⁻¹ : Complex) *
            conj (((Real.sqrt (2 * r))⁻¹ : Complex)))) =
        ∫ _x in Set.Icc (-r) (r - t),
          (((2 * r)⁻¹ : Real) : Complex) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro _ _
    change
      (((Real.sqrt (2 * r) : Real) : Complex)⁻¹) *
          conj ((((Real.sqrt (2 * r) : Real) : Complex)⁻¹)) =
        (((2 * r)⁻¹ : Real) : Complex)
    rw [map_inv₀, Complex.conj_ofReal,
      inv_sqrt_mul_inv_sqrt_complex (mul_pos (by norm_num) hr)]
  rw [hpointwise, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab]
  simp only [intervalIntegral.integral_const, Complex.real_smul]
  norm_cast
  field_simp [hr.ne']; ring

theorem inner_suzukiL2Translate_evenZero_aStar_eq_DF6D4 :
    inner Complex
        (suzukiL2Translate (Real.log 2)
          (suzukiYoshidaEvenL2
            suzukiProjectAStar suzukiProjectAStar_pos 0))
        (suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos 0) =
      (suzukiDF6D4EvenDiagonalPrimeCorrelation 0 : Complex) := by
  rw [inner_suzukiL2Translate_evenZero_eq_correlation
    suzukiProjectAStar_pos (Real.log_nonneg (by norm_num))
    log_two_lt_two_mul_suzukiProjectAStar.le]
  norm_cast
  unfold suzukiDF6D4EvenDiagonalPrimeCorrelation
    suzukiDF6D4DiagonalPrimeDisplacement
  rw [if_pos rfl]
  ring

theorem suzukiL2SymmetricTranslationEnergy_evenZero_aStar_eq_DF6D4 :
    suzukiL2SymmetricTranslationEnergy (Real.log 2)
        (suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos 0)
        (suzukiYoshidaEvenL2
          suzukiProjectAStar suzukiProjectAStar_pos 0) =
      ((2 * suzukiDF6D4EvenDiagonalPrimeCorrelation 0 : Real) : Complex) :=
  suzukiL2SymmetricTranslationEnergy_self_eq_twice_of_inner
    inner_suzukiL2Translate_evenZero_aStar_eq_DF6D4

theorem suzukiYoshidaPrimeTwoForm_evenZeroDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0) =
      (suzukiDF6D4EvenDiagonalPrimeTerm 0 : Complex) := by
  unfold suzukiYoshidaPrimeTwoForm suzukiL2FiniteTranslationEnergy
  rw [suzukiProjectPrimeIndexSet_at_aStar, Finset.sum_singleton,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  unfold suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
    suzukiDF6D4EvenDiagonalPrimeTerm
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  rw [suzukiL2SymmetricTranslationEnergy_evenZero_aStar_eq_DF6D4]
  norm_cast
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrtTwo]
  rw [hsquare]

theorem suzukiEquation25EvenDiagonalPrimeEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25EvenDiagonalPrimeEvaluation hsource := by
  unfold SuzukiEquation25EvenDiagonalPrimeEvaluation
  intro mode
  by_cases hmode : mode = 0
  · subst mode
    exact suzukiYoshidaPrimeTwoForm_evenZeroDiagonal hsource
  · exact suzukiYoshidaPrimeTwoForm_evenPositiveDiagonal
      hsource mode (Nat.pos_of_ne_zero hmode)

theorem suzukiEquation25OddDiagonalPrimeEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiEquation25OddDiagonalPrimeEvaluation hsource := by
  unfold SuzukiEquation25OddDiagonalPrimeEvaluation
  intro mode hmode
  exact suzukiYoshidaPrimeTwoForm_oddDiagonal hsource mode hmode

theorem suzukiYoshidaPrimeTwoForm_evenPositiveOffDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      (suzukiDF6D4EvenOffDiagonalPrimeTerm left right : Complex) := by
  unfold suzukiYoshidaPrimeTwoForm suzukiL2FiniteTranslationEnergy
  rw [suzukiProjectPrimeIndexSet_at_aStar, Finset.sum_singleton,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  unfold suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  have hinner :=
    inner_suzukiL2Translate_evenPositive_offDiagonal_eq_correlation
      suzukiProjectAStar_pos (Real.log_nonneg (by norm_num))
      log_two_lt_two_mul_suzukiProjectAStar.le
      left right hleft hlt
  have henergy :=
    suzukiL2SymmetricTranslationEnergy_eq_twice_of_inner_of_even
      (suzukiYoshidaEvenL2_even suzukiProjectAStar_pos left)
      (suzukiYoshidaEvenL2_even suzukiProjectAStar_pos right)
      hinner
  rw [henergy]
  norm_cast
  unfold suzukiDF6D4EvenOffDiagonalPrimeTerm
    suzukiDF6D4PrimeSineTransform suzukiDF6D4EvenModeScale
  rw [if_neg hleft.ne', if_neg (hleft.trans hlt).ne']
  dsimp only
  push_cast
  rw [suzukiDF6D4AlternatingSign_cast_real,
    suzukiDF6D4AlternatingSign_cast_real]
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrtTwo, Real.pi_ne_zero]
  rw [hsquare]
  ring

theorem suzukiYoshidaPrimeTwoForm_evenZeroOffDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (right : Nat) (hright : 0 < right) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos 0)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      (suzukiDF6D4EvenOffDiagonalPrimeTerm 0 right : Complex) := by
  unfold suzukiYoshidaPrimeTwoForm suzukiL2FiniteTranslationEnergy
  rw [suzukiProjectPrimeIndexSet_at_aStar, Finset.sum_singleton,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  unfold suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  have hinner :=
    inner_suzukiL2Translate_evenZero_offDiagonal_eq_correlation
      suzukiProjectAStar_pos (Real.log_nonneg (by norm_num))
      log_two_lt_two_mul_suzukiProjectAStar.le right hright
  have henergy :=
    suzukiL2SymmetricTranslationEnergy_eq_twice_of_inner_of_even
      (suzukiYoshidaEvenL2_even suzukiProjectAStar_pos 0)
      (suzukiYoshidaEvenL2_even suzukiProjectAStar_pos right)
      hinner
  rw [henergy]
  norm_cast
  unfold suzukiDF6D4EvenOffDiagonalPrimeTerm
    suzukiDF6D4PrimeSineTransform suzukiDF6D4EvenModeScale
  rw [if_pos rfl, if_neg hright.ne']
  simp only [Nat.cast_zero, zero_mul, zero_add, Nat.sub_zero]
  push_cast
  simp only [zero_div, Real.sin_zero]
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrtTwo, Real.pi_ne_zero]
  rw [hsquare]
  rw [suzukiDF6D4AlternatingSign_cast_real]
  ring

theorem suzukiYoshidaPrimeTwoForm_evenOffDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) (hlt : left < right) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      (suzukiDF6D4EvenOffDiagonalPrimeTerm left right : Complex) := by
  by_cases hleft : left = 0
  · subst left
    exact suzukiYoshidaPrimeTwoForm_evenZeroOffDiagonal
      hsource right hlt
  · exact suzukiYoshidaPrimeTwoForm_evenPositiveOffDiagonal
      hsource left right (Nat.pos_of_ne_zero hleft) hlt

theorem suzukiYoshidaPrimeTwoForm_oddOffDiagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (left right : Nat) (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaPrimeTwoForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      (suzukiDF6D4OddOffDiagonalPrimeTerm left right : Complex) := by
  unfold suzukiYoshidaPrimeTwoForm suzukiL2FiniteTranslationEnergy
  rw [suzukiProjectPrimeIndexSet_at_aStar, Finset.sum_singleton,
    suzukiYoshidaOddLinearCompletionOfSource_toL2,
    suzukiYoshidaOddLinearCompletionOfSource_toL2]
  unfold suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  norm_num only [Nat.cast_ofNat]
  have hinner :=
    inner_suzukiL2Translate_odd_offDiagonal_eq_correlation
      suzukiProjectAStar_pos (Real.log_nonneg (by norm_num))
      log_two_lt_two_mul_suzukiProjectAStar.le
      left right hleft hlt
  have henergy :=
    suzukiL2SymmetricTranslationEnergy_eq_twice_of_inner_of_odd
      (suzukiYoshidaOddL2_odd suzukiProjectAStar_pos left)
      (suzukiYoshidaOddL2_odd suzukiProjectAStar_pos right)
      hinner
  rw [henergy]
  norm_cast
  unfold suzukiDF6D4OddOffDiagonalPrimeTerm
    suzukiDF6D4PrimeSineTransform
  dsimp only
  push_cast
  rw [suzukiDF6D4AlternatingSign_cast_real,
    suzukiDF6D4AlternatingSign_cast_real]
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := by positivity
  have hsquare : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp [hsqrtTwo, Real.pi_ne_zero]
  rw [hsquare]
  ring

/-- After the prime translation is evaluated, the even correction component
reduces to this Gamma-only identity. -/
def SuzukiEquation25EvenOffDiagonalGammaEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, left < right →
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      ((suzukiDF6D4ComparisonEvenOffDiagonal left right +
        suzukiDF6D4EvenOffDiagonalPrimeTerm left right -
        suzukiDF6D4EvenOffDiagonal left right : Real) : Complex)

/-- After the prime translation is evaluated, the odd correction component
reduces to this Gamma-only identity. -/
def SuzukiEquation25OddOffDiagonalGammaEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, 0 < left → left < right →
    suzukiYoshidaGammaRemainderForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos left)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos right) =
      ((suzukiDF6D4ComparisonOddOffDiagonal left right +
        suzukiDF6D4OddOffDiagonalPrimeTerm left right -
        suzukiDF6D4OddOffDiagonal left right : Real) : Complex)

theorem suzukiEquation25EvenOffDiagonalCorrectionEvaluation_of_gamma
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hgamma : SuzukiEquation25EvenOffDiagonalGammaEvaluation hsource) :
    SuzukiEquation25EvenOffDiagonalCorrectionEvaluation hsource := by
  unfold SuzukiEquation25EvenOffDiagonalCorrectionEvaluation
  intro left right hlt
  rw [suzukiYoshidaPrimeTwoForm_evenOffDiagonal hsource left right hlt,
    hgamma left right hlt]
  push_cast
  ring

theorem suzukiEquation25OddOffDiagonalCorrectionEvaluation_of_gamma
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hgamma : SuzukiEquation25OddOffDiagonalGammaEvaluation hsource) :
    SuzukiEquation25OddOffDiagonalCorrectionEvaluation hsource := by
  unfold SuzukiEquation25OddOffDiagonalCorrectionEvaluation
  intro left right hleft hlt
  rw [suzukiYoshidaPrimeTwoForm_oddOffDiagonal
      hsource left right hleft hlt,
    hgamma left right hleft hlt]
  push_cast
  ring

end

end RiemannHypothesisProject.Experiments.M100
