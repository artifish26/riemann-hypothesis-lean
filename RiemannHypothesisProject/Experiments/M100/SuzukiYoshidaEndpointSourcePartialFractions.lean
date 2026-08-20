import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointSourceVariable

/-!
# Partial fractions for endpoint source profiles

This module isolates the algebraic core of QF3.  Products of the positive
even and odd rational source profiles reduce to one paired-pole master family.
The paired poles have quadratic rather than linear decay at infinity.  The
finitely many removable mode poles are excluded only almost everywhere.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory

/-- Positive source frequency attached to a natural endpoint mode. -/
def suzukiYoshidaEndpointSourceModeFrequency
    (r : Real) (n : Nat) : Real :=
  (n : Real) * Real.pi / r

/-- Sum of the two source denominators, occurring in positive even modes. -/
def suzukiYoshidaEndpointSourceEvenRationalProfile
    (r : Real) (n : Nat) (z : Real) : Real :=
  (z + suzukiYoshidaEndpointSourceModeFrequency r n)⁻¹ +
    (z - suzukiYoshidaEndpointSourceModeFrequency r n)⁻¹

/-- Difference of the two source denominators, occurring in positive odd
modes and providing the quadratically decaying master profile. -/
def suzukiYoshidaEndpointSourceOddRationalProfile
    (r : Real) (n : Nat) (z : Real) : Real :=
  (z + suzukiYoshidaEndpointSourceModeFrequency r n)⁻¹ -
    (z - suzukiYoshidaEndpointSourceModeFrequency r n)⁻¹

/-- Common rational-log master integrand for one positive mode. -/
def suzukiYoshidaEndpointSourceModeMasterIntegrand
    (r : Real) (n : Nat) (z : Real) : Real :=
  suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
    suzukiYoshidaEndpointSourceOddRationalProfile r n z

/-- Rational-log product before the positive even parity normalization. -/
def suzukiYoshidaEndpointSourceEvenRationalProduct
    (r : Real) (left right : Nat) (z : Real) : Real :=
  suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
    (suzukiYoshidaEndpointSourceEvenRationalProfile r left z *
      suzukiYoshidaEndpointSourceEvenRationalProfile r right z)

/-- Rational-log product before the positive odd parity normalization. -/
def suzukiYoshidaEndpointSourceOddRationalProduct
    (r : Real) (left right : Nat) (z : Real) : Real :=
  suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
    (suzukiYoshidaEndpointSourceOddRationalProfile r left z *
      suzukiYoshidaEndpointSourceOddRationalProfile r right z)

theorem suzukiYoshidaEndpointSourceModeFrequency_pos
    {r : Real} (hr : 0 < r) {n : Nat} (hn : 0 < n) :
    0 < suzukiYoshidaEndpointSourceModeFrequency r n := by
  unfold suzukiYoshidaEndpointSourceModeFrequency
  positivity

theorem suzukiYoshidaEndpointSourceModeFrequency_strictMono
    {r : Real} (hr : 0 < r) {left right : Nat} (hlt : left < right) :
    suzukiYoshidaEndpointSourceModeFrequency r left <
      suzukiYoshidaEndpointSourceModeFrequency r right := by
  unfold suzukiYoshidaEndpointSourceModeFrequency
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right (by exact_mod_cast hlt) Real.pi_pos) hr

/-- Distinct positive even rational products reduce almost everywhere to a
difference-frequency and a sum-frequency combination of the master family. -/
theorem suzukiYoshidaEndpointSourceEvenRationalProduct_ae_eq_master
    {r : Real} (hr : 0 < r) {left right : Nat}
    (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaEndpointSourceEvenRationalProduct r left right =ᵐ[volume]
      fun z =>
        (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z -
            suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r right -
            suzukiYoshidaEndpointSourceModeFrequency r left) -
        (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z +
            suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r left +
            suzukiYoshidaEndpointSourceModeFrequency r right) := by
  let a := suzukiYoshidaEndpointSourceModeFrequency r left
  let b := suzukiYoshidaEndpointSourceModeFrequency r right
  have ha : 0 < a := suzukiYoshidaEndpointSourceModeFrequency_pos hr hleft
  have hb : 0 < b := suzukiYoshidaEndpointSourceModeFrequency_pos hr
    (hleft.trans hlt)
  have hab : a < b :=
    suzukiYoshidaEndpointSourceModeFrequency_strictMono hr hlt
  filter_upwards [volume.ae_ne (-a), volume.ae_ne a,
      volume.ae_ne (-b), volume.ae_ne b] with z hzna hza hznb hzb
  unfold suzukiYoshidaEndpointSourceEvenRationalProduct
    suzukiYoshidaEndpointSourceModeMasterIntegrand
    suzukiYoshidaEndpointSourceEvenRationalProfile
    suzukiYoshidaEndpointSourceOddRationalProfile
  change
    suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
        (((z + a)⁻¹ + (z - a)⁻¹) * ((z + b)⁻¹ + (z - b)⁻¹)) =
      (suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + a)⁻¹ - (z - a)⁻¹) -
          suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + b)⁻¹ - (z - b)⁻¹)) / (b - a) -
        (suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + a)⁻¹ - (z - a)⁻¹) +
          suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + b)⁻¹ - (z - b)⁻¹)) / (a + b)
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hsum : a + b ≠ 0 := (add_pos ha hb).ne'
  have hzpa : z + a ≠ 0 := by intro h; apply hzna; linarith
  have hzma : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hzpb : z + b ≠ 0 := by intro h; apply hznb; linarith
  have hzmb : z - b ≠ 0 := sub_ne_zero.mpr hzb
  field_simp [hba, hsum, hzpa, hzma, hzpb, hzmb]
  ring

/-- Distinct positive odd rational products reduce almost everywhere to the
same master family, with the opposite sign in the sum-frequency branch. -/
theorem suzukiYoshidaEndpointSourceOddRationalProduct_ae_eq_master
    {r : Real} (hr : 0 < r) {left right : Nat}
    (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaEndpointSourceOddRationalProduct r left right =ᵐ[volume]
      fun z =>
        (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z -
            suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r right -
            suzukiYoshidaEndpointSourceModeFrequency r left) +
        (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z +
            suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r left +
            suzukiYoshidaEndpointSourceModeFrequency r right) := by
  let a := suzukiYoshidaEndpointSourceModeFrequency r left
  let b := suzukiYoshidaEndpointSourceModeFrequency r right
  have ha : 0 < a := suzukiYoshidaEndpointSourceModeFrequency_pos hr hleft
  have hb : 0 < b := suzukiYoshidaEndpointSourceModeFrequency_pos hr
    (hleft.trans hlt)
  have hab : a < b :=
    suzukiYoshidaEndpointSourceModeFrequency_strictMono hr hlt
  filter_upwards [volume.ae_ne (-a), volume.ae_ne a,
      volume.ae_ne (-b), volume.ae_ne b] with z hzna hza hznb hzb
  unfold suzukiYoshidaEndpointSourceOddRationalProduct
    suzukiYoshidaEndpointSourceModeMasterIntegrand
    suzukiYoshidaEndpointSourceOddRationalProfile
  change
    suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
        (((z + a)⁻¹ - (z - a)⁻¹) * ((z + b)⁻¹ - (z - b)⁻¹)) =
      (suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + a)⁻¹ - (z - a)⁻¹) -
          suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + b)⁻¹ - (z - b)⁻¹)) / (b - a) +
        (suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + a)⁻¹ - (z - a)⁻¹) +
          suzukiYoshidaEndpointSourceVariableWeight z * Real.sin (r * z) ^ 2 *
            ((z + b)⁻¹ - (z - b)⁻¹)) / (a + b)
  have hba : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hsum : a + b ≠ 0 := (add_pos ha hb).ne'
  have hzpa : z + a ≠ 0 := by intro h; apply hzna; linarith
  have hzma : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hzpb : z + b ≠ 0 := by intro h; apply hznb; linarith
  have hzmb : z - b ≠ 0 := sub_ne_zero.mpr hzb
  field_simp [hba, hsum, hzpa, hzma, hzpb, hzmb]
  ring

/-! ## Integral assembly -/

/-- Combined master interface consumed by the rational-product assembly.  It
keeps integrability and the exact project-normalized evaluation visible;
the successor integrability module supplies the first field unconditionally. -/
def SuzukiYoshidaEndpointSourceModeMasterEvaluation : Prop :=
  ∀ n : Nat, 0 < n →
    Integrable
        (suzukiYoshidaEndpointSourceModeMasterIntegrand
          suzukiProjectAStar n) ∧
      (∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand
            suzukiProjectAStar n z) =
        Real.pi * suzukiYoshidaComparisonSourceSineTransform n

/-- The even rational product integral is an explicit linear combination of
two master integrals. -/
theorem suzukiYoshidaEndpointSourceEvenRationalProduct_integral_eq_master
    {r : Real} (hr : 0 < r) {left right : Nat}
    (hleft : 0 < left) (hlt : left < right)
    (hleftInt : Integrable
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r left))
    (hrightInt : Integrable
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r right)) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceEvenRationalProduct r left right z) =
      ((∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r left z) -
        (∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r right z)) /
          (suzukiYoshidaEndpointSourceModeFrequency r right -
            suzukiYoshidaEndpointSourceModeFrequency r left) -
      ((∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r left z) +
        (∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r right z)) /
          (suzukiYoshidaEndpointSourceModeFrequency r left +
            suzukiYoshidaEndpointSourceModeFrequency r right) := by
  have hdifferenceInt : Integrable (fun z : Real =>
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z -
        suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r right -
            suzukiYoshidaEndpointSourceModeFrequency r left)) := by
    simpa only [Pi.sub_apply] using
      (hleftInt.sub hrightInt).div_const
        (suzukiYoshidaEndpointSourceModeFrequency r right -
          suzukiYoshidaEndpointSourceModeFrequency r left)
  have hsumInt : Integrable (fun z : Real =>
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z +
        suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r left +
            suzukiYoshidaEndpointSourceModeFrequency r right)) := by
    simpa only [Pi.add_apply] using
      (hleftInt.add hrightInt).div_const
        (suzukiYoshidaEndpointSourceModeFrequency r left +
          suzukiYoshidaEndpointSourceModeFrequency r right)
  rw [integral_congr_ae
    (suzukiYoshidaEndpointSourceEvenRationalProduct_ae_eq_master
      hr hleft hlt)]
  rw [integral_sub hdifferenceInt hsumInt,
    integral_div, integral_div, integral_sub hleftInt hrightInt,
    integral_add hleftInt hrightInt]

/-- The odd rational product integral is the corresponding sum of the two
master branches. -/
theorem suzukiYoshidaEndpointSourceOddRationalProduct_integral_eq_master
    {r : Real} (hr : 0 < r) {left right : Nat}
    (hleft : 0 < left) (hlt : left < right)
    (hleftInt : Integrable
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r left))
    (hrightInt : Integrable
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r right)) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceOddRationalProduct r left right z) =
      ((∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r left z) -
        (∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r right z)) /
          (suzukiYoshidaEndpointSourceModeFrequency r right -
            suzukiYoshidaEndpointSourceModeFrequency r left) +
      ((∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r left z) +
        (∫ z : Real,
          suzukiYoshidaEndpointSourceModeMasterIntegrand r right z)) /
          (suzukiYoshidaEndpointSourceModeFrequency r left +
            suzukiYoshidaEndpointSourceModeFrequency r right) := by
  have hdifferenceInt : Integrable (fun z : Real =>
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z -
        suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r right -
            suzukiYoshidaEndpointSourceModeFrequency r left)) := by
    simpa only [Pi.sub_apply] using
      (hleftInt.sub hrightInt).div_const
        (suzukiYoshidaEndpointSourceModeFrequency r right -
          suzukiYoshidaEndpointSourceModeFrequency r left)
  have hsumInt : Integrable (fun z : Real =>
      (suzukiYoshidaEndpointSourceModeMasterIntegrand r left z +
        suzukiYoshidaEndpointSourceModeMasterIntegrand r right z) /
          (suzukiYoshidaEndpointSourceModeFrequency r left +
            suzukiYoshidaEndpointSourceModeFrequency r right)) := by
    simpa only [Pi.add_apply] using
      (hleftInt.add hrightInt).div_const
        (suzukiYoshidaEndpointSourceModeFrequency r left +
          suzukiYoshidaEndpointSourceModeFrequency r right)
  rw [integral_congr_ae
    (suzukiYoshidaEndpointSourceOddRationalProduct_ae_eq_master
      hr hleft hlt)]
  rw [integral_add hdifferenceInt hsumInt,
    integral_div, integral_div, integral_sub hleftInt hrightInt,
    integral_add hleftInt hrightInt]

/-- Once the master theorem is supplied, the even product integral is already
in the exact source-transform vocabulary used by the DF6D4 bridge. -/
theorem suzukiYoshidaEndpointSourceEvenRationalProduct_integral_eq_source
    (hmaster : SuzukiYoshidaEndpointSourceModeMasterEvaluation)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceEvenRationalProduct
          suzukiProjectAStar left right z) =
      (Real.pi * suzukiYoshidaComparisonSourceSineTransform left -
          Real.pi * suzukiYoshidaComparisonSourceSineTransform right) /
          (suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar right -
            suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar left) -
        (Real.pi * suzukiYoshidaComparisonSourceSineTransform left +
          Real.pi * suzukiYoshidaComparisonSourceSineTransform right) /
          (suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar left +
            suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar right) := by
  obtain ⟨hleftInt, hleftEval⟩ := hmaster left hleft
  obtain ⟨hrightInt, hrightEval⟩ := hmaster right (hleft.trans hlt)
  rw [suzukiYoshidaEndpointSourceEvenRationalProduct_integral_eq_master
    suzukiProjectAStar_pos hleft hlt hleftInt hrightInt,
    hleftEval, hrightEval]

/-- Once the master theorem is supplied, the odd product integral is already
in the exact source-transform vocabulary used by the DF6D4 bridge. -/
theorem suzukiYoshidaEndpointSourceOddRationalProduct_integral_eq_source
    (hmaster : SuzukiYoshidaEndpointSourceModeMasterEvaluation)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    (∫ z : Real,
        suzukiYoshidaEndpointSourceOddRationalProduct
          suzukiProjectAStar left right z) =
      (Real.pi * suzukiYoshidaComparisonSourceSineTransform left -
          Real.pi * suzukiYoshidaComparisonSourceSineTransform right) /
          (suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar right -
            suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar left) +
        (Real.pi * suzukiYoshidaComparisonSourceSineTransform left +
          Real.pi * suzukiYoshidaComparisonSourceSineTransform right) /
          (suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar left +
            suzukiYoshidaEndpointSourceModeFrequency suzukiProjectAStar right) := by
  obtain ⟨hleftInt, hleftEval⟩ := hmaster left hleft
  obtain ⟨hrightInt, hrightEval⟩ := hmaster right (hleft.trans hlt)
  rw [suzukiYoshidaEndpointSourceOddRationalProduct_integral_eq_master
    suzukiProjectAStar_pos hleft hlt hleftInt hrightInt,
    hleftEval, hrightEval]

end

end RiemannHypothesisProject.Experiments.M100
