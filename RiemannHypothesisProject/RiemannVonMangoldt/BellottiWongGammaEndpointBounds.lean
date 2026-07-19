import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaIntervalBoxes

/-!
# Certified endpoint bounds for Bennett's Gamma interval boxes

The archived source notebook evaluates arctangent and logarithm terms by
outward-rounded interval arithmetic.  These definitions provide a
kernel-checked rational analogue: arctangent uses direct or reciprocal Taylor
bounds, while logarithm uses power-of-two range reduction and the certified
mathlib enclosure of `log 2`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

def arctanSepticPolynomial (x : Real) : Real :=
  x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7

def arctanNonicPolynomial (x : Real) : Real :=
  x - x ^ 3 / 3 + x ^ 5 / 5 - x ^ 7 / 7 + x ^ 9 / 9

private theorem arctan_eq_pi_four_add_reduced
    {x : Real} (hx : 0 < x) :
    Real.arctan x = Real.pi / 4 + Real.arctan ((x - 1) / (x + 1)) := by
  let z : Real := (x - 1) / (x + 1)
  have hden : 0 < x + 1 := by linarith
  have hzlt : z * 1 < 1 := by
    dsimp [z]
    rw [mul_one]
    rw [div_lt_iff₀ hden]
    linarith
  have hadd := Real.arctan_add (x := z) (y := 1) hzlt
  have hfrac : (z + 1) / (1 - z * 1) = x := by
    dsimp [z]
    field_simp [hden.ne']
    ring
  rw [Real.arctan_one, hfrac] at hadd
  linarith

/-- Rational/`pi` lower evaluator for arctangent on the nonnegative axis. -/
def bennettGammaArctanEndpointLower (x : Real) : Real :=
  if x <= 1 / 2 then arctanSepticPolynomial x
  else if 2 <= x then Real.pi / 2 - arctanNonicPolynomial x⁻¹
  else if x <= 1 then
    Real.pi / 4 - arctanNonicPolynomial ((1 - x) / (1 + x))
  else Real.pi / 4 + arctanSepticPolynomial ((x - 1) / (x + 1))

/-- Rational/`pi` upper evaluator for arctangent on the nonnegative axis. -/
def bennettGammaArctanEndpointUpper (x : Real) : Real :=
  if x <= 1 / 2 then arctanNonicPolynomial x
  else if 2 <= x then Real.pi / 2 - arctanSepticPolynomial x⁻¹
  else if x <= 1 then
    Real.pi / 4 - arctanSepticPolynomial ((1 - x) / (1 + x))
  else Real.pi / 4 + arctanNonicPolynomial ((x - 1) / (x + 1))

theorem bennettGammaArctanEndpointLower_le
    {x : Real} (hx : 0 <= x) :
    bennettGammaArctanEndpointLower x <= Real.arctan x := by
  by_cases hxhalf : x <= 1 / 2
  · simp only [bennettGammaArctanEndpointLower, if_pos hxhalf]
    exact arctan_septic_lower hx
  · simp only [bennettGammaArctanEndpointLower, if_neg hxhalf]
    by_cases hxtwo : 2 <= x
    · simp only [if_pos hxtwo]
      exact arctan_reciprocal_nonic_lower (by linarith)
    · simp only [if_neg hxtwo]
      have hxpos : 0 < x := by linarith
      have hid := arctan_eq_pi_four_add_reduced hxpos
      by_cases hxone : x <= 1
      · simp only [if_pos hxone]
        let z : Real := (1 - x) / (1 + x)
        have hz : 0 <= z := by dsimp [z]; positivity
        have hupper := arctan_nonic_upper hz
        have hneg : (x - 1) / (x + 1) = -z := by
          dsimp [z]
          ring
        rw [hneg, Real.arctan_neg] at hid
        unfold arctanNonicPolynomial
        linarith
      · simp only [if_neg hxone]
        let z : Real := (x - 1) / (x + 1)
        have hz : 0 <= z := by
          dsimp [z]
          have hxone' : 1 <= x := (lt_of_not_ge hxone).le
          positivity
        have hlower := arctan_septic_lower hz
        dsimp [z] at hlower
        unfold arctanSepticPolynomial
        linarith

theorem bennettGammaArctanEndpoint_le_Upper
    {x : Real} (hx : 0 <= x) :
    Real.arctan x <= bennettGammaArctanEndpointUpper x := by
  by_cases hxhalf : x <= 1 / 2
  · simp only [bennettGammaArctanEndpointUpper, if_pos hxhalf]
    exact arctan_nonic_upper hx
  · simp only [bennettGammaArctanEndpointUpper, if_neg hxhalf]
    by_cases hxtwo : 2 <= x
    · simp only [if_pos hxtwo]
      exact arctan_reciprocal_septic_upper (by linarith)
    · simp only [if_neg hxtwo]
      have hxpos : 0 < x := by linarith
      have hid := arctan_eq_pi_four_add_reduced hxpos
      by_cases hxone : x <= 1
      · simp only [if_pos hxone]
        let z : Real := (1 - x) / (1 + x)
        have hz : 0 <= z := by dsimp [z]; positivity
        have hlower := arctan_septic_lower hz
        have hneg : (x - 1) / (x + 1) = -z := by
          dsimp [z]
          ring
        rw [hneg, Real.arctan_neg] at hid
        unfold arctanSepticPolynomial
        linarith
      · simp only [if_neg hxone]
        let z : Real := (x - 1) / (x + 1)
        have hz : 0 <= z := by
          dsimp [z]
          have hxone' : 1 <= x := (lt_of_not_ge hxone).le
          positivity
        have hupper := arctan_nonic_upper hz
        dsimp [z] at hupper
        unfold arctanNonicPolynomial
        linarith

def logQuarticPolynomial (x : Real) : Real :=
  x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4

def logQuinticPolynomial (x : Real) : Real :=
  x - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5

/-- Rational lower evaluator for `log y` after reduction by `2^n`. -/
def bennettGammaLogEndpointLower (n : Nat) (y : Real) : Real :=
  (n : Real) * 0.6931471803 +
    logQuarticPolynomial (y / (2 : Real) ^ n - 1)

/-- Rational upper evaluator for `log y` after reduction by `2^n`. -/
def bennettGammaLogEndpointUpper (n : Nat) (y : Real) : Real :=
  (n : Real) * 0.6931471808 +
    logQuinticPolynomial (y / (2 : Real) ^ n - 1)

/-- Mixed-base lower evaluator for `log y`. -/
def bennettGammaMixedLogEndpointLower (p q : Nat) (y : Real) : Real :=
  (p : Real) * 0.6931471803 + (q : Real) * 1.0986122885 +
    logQuarticPolynomial
      (y / ((2 : Real) ^ p * (3 : Real) ^ q) - 1)

/-- Mixed-base upper evaluator for `log y`. -/
def bennettGammaMixedLogEndpointUpper (p q : Nat) (y : Real) : Real :=
  (p : Real) * 0.6931471808 + (q : Real) * 1.0986122888 +
    logQuinticPolynomial
      (y / ((2 : Real) ^ p * (3 : Real) ^ q) - 1)

/-- Lower evaluator when the chosen mixed scale lies above `y`. -/
def bennettGammaMixedLogInverseEndpointLower (p q : Nat) (y : Real) : Real :=
  (p : Real) * 0.6931471803 + (q : Real) * 1.0986122885 -
    logQuinticPolynomial
      (((2 : Real) ^ p * (3 : Real) ^ q) / y - 1)

/-- Upper evaluator when the chosen mixed scale lies above `y`. -/
def bennettGammaMixedLogInverseEndpointUpper (p q : Nat) (y : Real) : Real :=
  (p : Real) * 0.6931471808 + (q : Real) * 1.0986122888 -
    logQuarticPolynomial
      (((2 : Real) ^ p * (3 : Real) ^ q) / y - 1)

theorem bennettGammaLogEndpointLower_le
    (n : Nat) {y : Real} (hy : (2 : Real) ^ n <= y) :
    bennettGammaLogEndpointLower n y <= Real.log y := by
  let z : Real := y / (2 : Real) ^ n - 1
  have hpow_pos : 0 < (2 : Real) ^ n := by positivity
  have hz : 0 <= z := by
    dsimp [z]
    rw [sub_nonneg, le_div_iff₀ hpow_pos]
    simpa [mul_comm] using hy
  have h := log_two_pow_mul_one_add_quartic_lower n hz
  have heq : (2 : Real) ^ n * (1 + z) = y := by
    dsimp [z]
    field_simp [hpow_pos.ne']
    ring
  rw [heq] at h
  simpa [bennettGammaLogEndpointLower, logQuarticPolynomial, z] using h

theorem bennettGammaLogEndpoint_le_Upper
    (n : Nat) {y : Real} (hy : (2 : Real) ^ n <= y) :
    Real.log y <= bennettGammaLogEndpointUpper n y := by
  let z : Real := y / (2 : Real) ^ n - 1
  have hpow_pos : 0 < (2 : Real) ^ n := by positivity
  have hz : 0 <= z := by
    dsimp [z]
    rw [sub_nonneg, le_div_iff₀ hpow_pos]
    simpa [mul_comm] using hy
  have h := log_two_pow_mul_one_add_quintic_upper n hz
  have heq : (2 : Real) ^ n * (1 + z) = y := by
    dsimp [z]
    field_simp [hpow_pos.ne']
    ring
  rw [heq] at h
  simpa [bennettGammaLogEndpointUpper, logQuinticPolynomial, z] using h

theorem bennettGammaMixedLogEndpointLower_le
    (p q : Nat) {y : Real}
    (hy : (2 : Real) ^ p * (3 : Real) ^ q <= y) :
    bennettGammaMixedLogEndpointLower p q y <= Real.log y := by
  let scale : Real := (2 : Real) ^ p * (3 : Real) ^ q
  let z : Real := y / scale - 1
  have hscale_pos : 0 < scale := by dsimp [scale]; positivity
  have hz : 0 <= z := by
    dsimp [z]
    rw [sub_nonneg, le_div_iff₀ hscale_pos]
    simpa [scale, mul_comm] using hy
  have h := log_two_pow_mul_three_pow_mul_one_add_quartic_lower p q hz
  have heq : ((2 : Real) ^ p * (3 : Real) ^ q) * (1 + z) = y := by
    dsimp [z, scale]
    field_simp
    ring
  rw [heq] at h
  simpa [bennettGammaMixedLogEndpointLower, logQuarticPolynomial, z, scale] using h

theorem bennettGammaMixedLogEndpoint_le_Upper
    (p q : Nat) {y : Real}
    (hy : (2 : Real) ^ p * (3 : Real) ^ q <= y) :
    Real.log y <= bennettGammaMixedLogEndpointUpper p q y := by
  let scale : Real := (2 : Real) ^ p * (3 : Real) ^ q
  let z : Real := y / scale - 1
  have hscale_pos : 0 < scale := by dsimp [scale]; positivity
  have hz : 0 <= z := by
    dsimp [z]
    rw [sub_nonneg, le_div_iff₀ hscale_pos]
    simpa [scale, mul_comm] using hy
  have h := log_two_pow_mul_three_pow_mul_one_add_quintic_upper p q hz
  have heq : ((2 : Real) ^ p * (3 : Real) ^ q) * (1 + z) = y := by
    dsimp [z, scale]
    field_simp
    ring
  rw [heq] at h
  simpa [bennettGammaMixedLogEndpointUpper, logQuinticPolynomial, z, scale] using h

theorem bennettGammaMixedLogInverseEndpointLower_le
    (p q : Nat) {y : Real} (hy : 0 < y)
    (hyScale : y <= (2 : Real) ^ p * (3 : Real) ^ q) :
    bennettGammaMixedLogInverseEndpointLower p q y <= Real.log y := by
  let scale : Real := (2 : Real) ^ p * (3 : Real) ^ q
  let z : Real := scale / y - 1
  have hscale_pos : 0 < scale := by dsimp [scale]; positivity
  have hz : 0 <= z := by
    dsimp [z]
    rw [sub_nonneg, le_div_iff₀ hy]
    simpa [scale] using hyScale
  have hlogUpper := log_one_add_quintic_upper hz
  have hscaleLower :
      (p : Real) * 0.6931471803 + (q : Real) * 1.0986122885 <=
        Real.log scale := by
    dsimp [scale]
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
      Real.log_pow, Real.log_pow]
    have hp : (0 : Real) <= p := by positivity
    have hq : (0 : Real) <= q := by positivity
    have htwo := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hp
    have hthree := mul_le_mul_of_nonneg_left Real.log_three_gt_d9.le hq
    linarith
  have heq : scale = y * (1 + z) := by
    dsimp [z]
    field_simp [hy.ne']
    ring
  have hlogeq : Real.log scale = Real.log y + Real.log (1 + z) := by
    rw [heq, Real.log_mul hy.ne' (by positivity)]
  unfold bennettGammaMixedLogInverseEndpointLower logQuinticPolynomial
  dsimp [z, scale] at hlogUpper hscaleLower hlogeq ⊢
  linarith

theorem bennettGammaMixedLogInverseEndpoint_le_Upper
    (p q : Nat) {y : Real} (hy : 0 < y)
    (hyScale : y <= (2 : Real) ^ p * (3 : Real) ^ q) :
    Real.log y <= bennettGammaMixedLogInverseEndpointUpper p q y := by
  let scale : Real := (2 : Real) ^ p * (3 : Real) ^ q
  let z : Real := scale / y - 1
  have hscale_pos : 0 < scale := by dsimp [scale]; positivity
  have hz : 0 <= z := by
    dsimp [z]
    rw [sub_nonneg, le_div_iff₀ hy]
    simpa [scale] using hyScale
  have hlogLower := log_one_add_quartic_lower hz
  have hscaleUpper : Real.log scale <=
      (p : Real) * 0.6931471808 + (q : Real) * 1.0986122888 := by
    dsimp [scale]
    rw [Real.log_mul (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)),
      Real.log_pow, Real.log_pow]
    have hp : (0 : Real) <= p := by positivity
    have hq : (0 : Real) <= q := by positivity
    have htwo := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le hp
    have hthree := mul_le_mul_of_nonneg_left Real.log_three_lt_d9.le hq
    linarith
  have heq : scale = y * (1 + z) := by
    dsimp [z]
    field_simp [hy.ne']
    ring
  have hlogeq : Real.log scale = Real.log y + Real.log (1 + z) := by
    rw [heq, Real.log_mul hy.ne' (by positivity)]
  unfold bennettGammaMixedLogInverseEndpointUpper logQuarticPolynomial
  dsimp [z, scale] at hlogLower hscaleUpper hlogeq ⊢
  linarith

/-- Chooses lower- or upper-side mixed logarithm range reduction. -/
def bennettGammaMixedLogEndpointLowerWithMode
    (inverse : Bool) (p q : Nat) (y : Real) : Real :=
  if inverse then bennettGammaMixedLogInverseEndpointLower p q y
  else bennettGammaMixedLogEndpointLower p q y

/-- Chooses lower- or upper-side mixed logarithm range reduction. -/
def bennettGammaMixedLogEndpointUpperWithMode
    (inverse : Bool) (p q : Nat) (y : Real) : Real :=
  if inverse then bennettGammaMixedLogInverseEndpointUpper p q y
  else bennettGammaMixedLogEndpointUpper p q y

/-- The direction condition associated with a logarithm range-reduction mode. -/
def BennettGammaMixedLogScaleValid
    (inverse : Bool) (p q : Nat) (y : Real) : Prop :=
  if inverse then y <= (2 : Real) ^ p * (3 : Real) ^ q
  else (2 : Real) ^ p * (3 : Real) ^ q <= y

theorem bennettGammaMixedLogEndpointLowerWithMode_le
    (inverse : Bool) (p q : Nat) {y : Real} (hy : 0 < y)
    (hrange : BennettGammaMixedLogScaleValid inverse p q y) :
    bennettGammaMixedLogEndpointLowerWithMode inverse p q y <= Real.log y := by
  cases inverse <;>
    simp [BennettGammaMixedLogScaleValid,
      bennettGammaMixedLogEndpointLowerWithMode] at hrange ⊢
  · exact bennettGammaMixedLogEndpointLower_le p q hrange
  · exact bennettGammaMixedLogInverseEndpointLower_le p q hy hrange

theorem bennettGammaMixedLogEndpointWithMode_le_Upper
    (inverse : Bool) (p q : Nat) {y : Real} (hy : 0 < y)
    (hrange : BennettGammaMixedLogScaleValid inverse p q y) :
    Real.log y <= bennettGammaMixedLogEndpointUpperWithMode inverse p q y := by
  cases inverse <;>
    simp [BennettGammaMixedLogScaleValid,
      bennettGammaMixedLogEndpointUpperWithMode] at hrange ⊢
  · exact bennettGammaMixedLogEndpoint_le_Upper p q hrange
  · exact bennettGammaMixedLogInverseEndpoint_le_Upper p q hy hrange

/-- Lower endpoint evaluator for the notebook component `T * arctan(c/T)`. -/
theorem bennettGammaIntervalArctanComponent_endpointLower
    {c T : Real} (hc : 0 <= c) (hT : 0 < T) :
    T * bennettGammaArctanEndpointLower (c / T) <=
      bennettGammaIntervalArctanComponent c T := by
  unfold bennettGammaIntervalArctanComponent
  exact mul_le_mul_of_nonneg_left
    (bennettGammaArctanEndpointLower_le (div_nonneg hc hT.le)) hT.le

/-- Upper endpoint evaluator for the notebook component `T * arctan(c/T)`. -/
theorem bennettGammaIntervalArctanComponent_endpointUpper
    {c T : Real} (hc : 0 <= c) (hT : 0 < T) :
    bennettGammaIntervalArctanComponent c T <=
      T * bennettGammaArctanEndpointUpper (c / T) := by
  unfold bennettGammaIntervalArctanComponent
  exact mul_le_mul_of_nonneg_left
    (bennettGammaArctanEndpoint_le_Upper (div_nonneg hc hT.le)) hT.le

/-- Lower range-reduced evaluator for the notebook logarithm component. -/
theorem bennettGammaIntervalLogComponent_endpointLower
    (n : Nat) {T : Real} (hT : 0 < T)
    (hrange : (2 : Real) ^ n <= 1 + 81 / (4 * T ^ 2)) :
    T ^ 2 * bennettGammaLogEndpointLower n (1 + 81 / (4 * T ^ 2)) <=
      bennettGammaIntervalLogComponent T := by
  unfold bennettGammaIntervalLogComponent
  exact mul_le_mul_of_nonneg_left
    (bennettGammaLogEndpointLower_le n hrange) (sq_nonneg T)

/-- Upper range-reduced evaluator for the notebook logarithm component. -/
theorem bennettGammaIntervalLogComponent_endpointUpper
    (n : Nat) {T : Real} (hT : 0 < T)
    (hrange : (2 : Real) ^ n <= 1 + 81 / (4 * T ^ 2)) :
    bennettGammaIntervalLogComponent T <=
      T ^ 2 * bennettGammaLogEndpointUpper n (1 + 81 / (4 * T ^ 2)) := by
  unfold bennettGammaIntervalLogComponent
  exact mul_le_mul_of_nonneg_left
    (bennettGammaLogEndpoint_le_Upper n hrange) (sq_nonneg T)

theorem bennettGammaIntervalLogComponent_mixedEndpointLower
    (p q : Nat) {T : Real} (hT : 0 < T)
    (hrange : (2 : Real) ^ p * (3 : Real) ^ q <= 1 + 81 / (4 * T ^ 2)) :
    T ^ 2 * bennettGammaMixedLogEndpointLower p q (1 + 81 / (4 * T ^ 2)) <=
      bennettGammaIntervalLogComponent T := by
  unfold bennettGammaIntervalLogComponent
  exact mul_le_mul_of_nonneg_left
    (bennettGammaMixedLogEndpointLower_le p q hrange) (sq_nonneg T)

theorem bennettGammaIntervalLogComponent_mixedEndpointUpper
    (p q : Nat) {T : Real} (hT : 0 < T)
    (hrange : (2 : Real) ^ p * (3 : Real) ^ q <= 1 + 81 / (4 * T ^ 2)) :
    bennettGammaIntervalLogComponent T <=
      T ^ 2 * bennettGammaMixedLogEndpointUpper p q (1 + 81 / (4 * T ^ 2)) := by
  unfold bennettGammaIntervalLogComponent
  exact mul_le_mul_of_nonneg_left
    (bennettGammaMixedLogEndpoint_le_Upper p q hrange) (sq_nonneg T)

/--
A rational squared inequality certifies a rational majorant for `g11`.
This is the leaf-level replacement for floating-point square-root evaluation.
-/
theorem bennettGammaIntervalRpowComponent_le_of_sq
    {T r : Real} (hT : 0 <= T) (hr : 0 <= r)
    (hsq : (32 * T) ^ 2 <= r ^ 2 * (81 + 4 * T ^ 2) ^ 3) :
    bennettGammaIntervalRpowComponent T <= r := by
  let B : Real := 81 + 4 * T ^ 2
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hden_pos : 0 < B ^ (3 / 2 : Real) := Real.rpow_pos_of_pos hB_pos _
  have hden_sq : (B ^ (3 / 2 : Real)) ^ 2 = B ^ 3 := by
    calc
      (B ^ (3 / 2 : Real)) ^ 2 =
          (B ^ (3 / 2 : Real)) ^ (2 : Real) := by rw [Real.rpow_two]
      _ = B ^ ((3 / 2 : Real) * 2) := (Real.rpow_mul hB_pos.le _ _).symm
      _ = B ^ (3 : Real) := by norm_num
      _ = B ^ 3 := Real.rpow_natCast B 3
  unfold bennettGammaIntervalRpowComponent
  rw [Real.rpow_neg hB_pos.le]
  change 32 * T / B ^ (3 / 2 : Real) <= r
  apply (div_le_iff₀ hden_pos).2
  apply (sq_le_sq₀ (by positivity) (mul_nonneg hr hden_pos.le)).mp
  simp only [mul_pow]
  rw [hden_sq]
  simpa [B, mul_pow] using hsq

/-- Fully evaluable upper majorant for an interval box. -/
def bennettGammaRationalUpperIntervalBox
    (r : Real) (inverseLog : Bool) (logTwoScale logThreeScale : Nat)
    (a b : Real) : Real :=
  ((1 / 120 : Real) + 1 / (90 * Real.pi)) * r -
    1 / (3 * Real.pi) * bennettGammaIntervalRationalComponent a +
    1 / Real.pi *
      (2 * (b * bennettGammaArctanEndpointUpper ((1 / 2) / b)) +
        2 * (b * bennettGammaArctanEndpointUpper ((5 / 2) / b)) -
          (7 / 2 : Real) *
            (a * bennettGammaArctanEndpointLower ((9 / 2) / a))) +
    1 / (2 * Real.pi) *
      (b ^ 2 * bennettGammaMixedLogEndpointUpperWithMode
        inverseLog logTwoScale logThreeScale
        (1 + 81 / (4 * b ^ 2)))

/-- Fully evaluable lower minorant for an interval box. -/
def bennettGammaRationalLowerIntervalBox
    (r : Real) (inverseLog : Bool) (logTwoScale logThreeScale : Nat)
    (a b : Real) : Real :=
  (-(1 / 120 : Real) - 1 / (90 * Real.pi)) * r -
    1 / (3 * Real.pi) * bennettGammaIntervalRationalComponent b +
    1 / Real.pi *
      (2 * (a * bennettGammaArctanEndpointLower ((1 / 2) / a)) +
        2 * (a * bennettGammaArctanEndpointLower ((5 / 2) / a)) -
          (7 / 2 : Real) *
            (b * bennettGammaArctanEndpointUpper ((9 / 2) / b))) +
    1 / (2 * Real.pi) *
      (a ^ 2 * bennettGammaMixedLogEndpointLowerWithMode
        inverseLog logTwoScale logThreeScale
        (1 + 81 / (4 * a ^ 2)))

theorem bennettGammaScaledUpperIntervalBox_le_rational
    {r a b : Real} (ha : 0 < a) (hb : 0 < b) (inverseLog : Bool)
    (logTwoScale logThreeScale : Nat)
    (hrange : BennettGammaMixedLogScaleValid inverseLog
      logTwoScale logThreeScale (1 + 81 / (4 * b ^ 2))) :
    bennettGammaScaledUpperIntervalBox r a b <=
      bennettGammaRationalUpperIntervalBox r inverseLog
        logTwoScale logThreeScale a b := by
  have hhalf := bennettGammaIntervalArctanComponent_endpointUpper
    (by norm_num : (0 : Real) <= 1 / 2) hb
  have hfive := bennettGammaIntervalArctanComponent_endpointUpper
    (by norm_num : (0 : Real) <= 5 / 2) hb
  have hnine := bennettGammaIntervalArctanComponent_endpointLower
    (by norm_num : (0 : Real) <= 9 / 2) ha
  have hy : 0 < (1 + 81 / (4 * b ^ 2) : Real) := by positivity
  have hlogRaw := bennettGammaMixedLogEndpointWithMode_le_Upper
    inverseLog logTwoScale logThreeScale hy hrange
  have hlog : bennettGammaIntervalLogComponent b <=
      b ^ 2 * bennettGammaMixedLogEndpointUpperWithMode inverseLog
        logTwoScale logThreeScale (1 + 81 / (4 * b ^ 2)) := by
    unfold bennettGammaIntervalLogComponent
    exact mul_le_mul_of_nonneg_left hlogRaw (sq_nonneg b)
  have hatan :
      2 * bennettGammaIntervalArctanComponent (1 / 2) b +
          2 * bennettGammaIntervalArctanComponent (5 / 2) b -
            (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) a <=
        2 * (b * bennettGammaArctanEndpointUpper ((1 / 2) / b)) +
          2 * (b * bennettGammaArctanEndpointUpper ((5 / 2) / b)) -
            (7 / 2 : Real) *
              (a * bennettGammaArctanEndpointLower ((9 / 2) / a)) := by
    linarith
  have hatanScaled := mul_le_mul_of_nonneg_left hatan
    (by positivity : (0 : Real) <= 1 / Real.pi)
  have hlogScaled := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : Real) <= 1 / (2 * Real.pi))
  unfold bennettGammaScaledUpperIntervalBox bennettGammaRationalUpperIntervalBox
  linarith

theorem bennettGammaRationalLowerIntervalBox_le_scaled
    {r a b : Real} (ha : 0 < a) (hb : 0 < b) (inverseLog : Bool)
    (logTwoScale logThreeScale : Nat)
    (hrange : BennettGammaMixedLogScaleValid inverseLog
      logTwoScale logThreeScale (1 + 81 / (4 * a ^ 2))) :
    bennettGammaRationalLowerIntervalBox r inverseLog
      logTwoScale logThreeScale a b <=
      bennettGammaScaledLowerIntervalBox r a b := by
  have hhalf := bennettGammaIntervalArctanComponent_endpointLower
    (by norm_num : (0 : Real) <= 1 / 2) ha
  have hfive := bennettGammaIntervalArctanComponent_endpointLower
    (by norm_num : (0 : Real) <= 5 / 2) ha
  have hnine := bennettGammaIntervalArctanComponent_endpointUpper
    (by norm_num : (0 : Real) <= 9 / 2) hb
  have hy : 0 < (1 + 81 / (4 * a ^ 2) : Real) := by positivity
  have hlogRaw := bennettGammaMixedLogEndpointLowerWithMode_le
    inverseLog logTwoScale logThreeScale hy hrange
  have hlog : a ^ 2 * bennettGammaMixedLogEndpointLowerWithMode inverseLog
      logTwoScale logThreeScale (1 + 81 / (4 * a ^ 2)) <=
      bennettGammaIntervalLogComponent a := by
    unfold bennettGammaIntervalLogComponent
    exact mul_le_mul_of_nonneg_left hlogRaw (sq_nonneg a)
  have hatan :
      2 * (a * bennettGammaArctanEndpointLower ((1 / 2) / a)) +
          2 * (a * bennettGammaArctanEndpointLower ((5 / 2) / a)) -
            (7 / 2 : Real) *
              (b * bennettGammaArctanEndpointUpper ((9 / 2) / b)) <=
        2 * bennettGammaIntervalArctanComponent (1 / 2) a +
          2 * bennettGammaIntervalArctanComponent (5 / 2) a -
            (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) b := by
    linarith
  have hatanScaled := mul_le_mul_of_nonneg_left hatan
    (by positivity : (0 : Real) <= 1 / Real.pi)
  have hlogScaled := mul_le_mul_of_nonneg_left hlog
    (by positivity : (0 : Real) <= 1 / (2 * Real.pi))
  unfold bennettGammaScaledLowerIntervalBox bennettGammaRationalLowerIntervalBox
  linarith

/-- The two rational endpoint inequalities sufficient for a valid box leaf. -/
def BennettGammaRationalIntervalBoxValid
    (r : Real) (lowerInverse upperInverse : Bool)
    (lowerTwoScale lowerThreeScale upperTwoScale upperThreeScale : Nat)
    (a b : Real) : Prop :=
  -(1 / 25 : Real) <=
      bennettGammaRationalLowerIntervalBox r lowerInverse
        lowerTwoScale lowerThreeScale a b ∧
    bennettGammaRationalUpperIntervalBox r upperInverse
      upperTwoScale upperThreeScale a b <= 1 / 25

theorem BennettGammaRationalIntervalBoxValid.toScaled
    {r a b : Real}
    {lowerInverse upperInverse : Bool}
    {lowerTwoScale lowerThreeScale upperTwoScale upperThreeScale : Nat}
    (valid : BennettGammaRationalIntervalBoxValid
      r lowerInverse upperInverse
        lowerTwoScale lowerThreeScale upperTwoScale upperThreeScale a b)
    (ha : 0 < a) (hb : 0 < b)
    (hlowerRange : BennettGammaMixedLogScaleValid lowerInverse
      lowerTwoScale lowerThreeScale (1 + 81 / (4 * a ^ 2)))
    (hupperRange : BennettGammaMixedLogScaleValid upperInverse
      upperTwoScale upperThreeScale (1 + 81 / (4 * b ^ 2))) :
    BennettGammaScaledIntervalBoxValid r a b := by
  exact ⟨valid.1.trans
      (bennettGammaRationalLowerIntervalBox_le_scaled ha hb _ _ _ hlowerRange),
    (bennettGammaScaledUpperIntervalBox_le_rational ha hb _ _ _ hupperRange).trans valid.2⟩

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
