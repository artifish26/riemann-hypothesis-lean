import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongGammaRemainder

/-!
# Monotonicity primitives for Bennett's Gamma interval certificate

The companion interval-analysis notebook for Bennett et al. Proposition 3.2
separates the elementary bound into four monotone or piecewise-monotone
components.  This module proves the nontrivial arctangent component monotonicity
used by that certificate.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The notebook's `g13(c,T) = T * arctan(c/T)` component. -/
def bennettGammaIntervalArctanComponent (c T : Real) : Real :=
  T * Real.arctan (c / T)

/-- Exact derivative of the arctangent interval component at positive height. -/
theorem hasDerivAt_bennettGammaIntervalArctanComponent
    {c T : Real} (hT : 0 < T) :
    HasDerivAt (bennettGammaIntervalArctanComponent c)
      (Real.arctan (c / T) - (c / T) / (1 + (c / T) ^ 2)) T := by
  have hquot : HasDerivAt (fun y : Real => c / y) (-c / T ^ 2) T := by
    have hraw := (hasDerivAt_const T c).div (hasDerivAt_id T) hT.ne'
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [id_eq]
      field_simp [hT.ne']
      ring
    · filter_upwards with y
      simp only [Pi.div_apply, id_eq]
  unfold bennettGammaIntervalArctanComponent
  have hraw := (hasDerivAt_id T).mul
    ((Real.hasDerivAt_arctan (c / T)).comp T hquot)
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [id_eq, Function.comp_apply]
    field_simp [hT.ne']
    ring
  · filter_upwards with y
    simp only [Pi.mul_apply, id_eq, Function.comp_apply]

/--
For `c >= 0`, the function `T * arctan(c/T)` is monotone on positive heights.
This kernel-checks the hard monotonicity assertion used by the published
interval notebook.
-/
theorem bennettGammaIntervalArctanComponent_monotoneOn
    {c : Real} (hc : 0 <= c) :
    MonotoneOn (bennettGammaIntervalArctanComponent c) (Set.Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi (0 : Real))
  · intro T hT
    exact (hasDerivAt_bennettGammaIntervalArctanComponent
      (Set.mem_Ioi.mp hT)).continuousAt.continuousWithinAt
  · intro T hT
    have hT_pos : 0 < T := by simpa using hT
    exact (hasDerivAt_bennettGammaIntervalArctanComponent hT_pos).hasDerivWithinAt
  · intro T hT
    have hT_pos : 0 < T := by simpa using hT
    have hx : 0 <= c / T := div_nonneg hc hT_pos.le
    exact sub_nonneg.mpr (arctan_rational_lower hx)

/-- The notebook's even-parity logarithm component `T^2 log(1+81/(4T^2))`. -/
def bennettGammaIntervalLogComponent (T : Real) : Real :=
  T ^ 2 * Real.log (1 + 81 / (4 * T ^ 2))

/-- Exact derivative of the logarithm interval component at positive height. -/
theorem hasDerivAt_bennettGammaIntervalLogComponent
    {T : Real} (hT : 0 < T) :
    HasDerivAt bennettGammaIntervalLogComponent
      (2 * T * (Real.log (1 + 81 / (4 * T ^ 2)) -
        (81 / (4 * T ^ 2)) / (1 + 81 / (4 * T ^ 2)))) T := by
  have hden : HasDerivAt (fun y : Real => 4 * y ^ 2) (8 * T) T := by
    have hraw := (hasDerivAt_const T 4).mul (hasDerivAt_pow 2 T)
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · ring
    · filter_upwards with y
      simp only [Pi.mul_apply, id_eq]
  have hden_ne : (4 * T ^ 2 : Real) ≠ 0 := by positivity
  have hfrac : HasDerivAt (fun y : Real => 81 / (4 * y ^ 2))
      (-81 / (2 * T ^ 3)) T := by
    have hraw := (hasDerivAt_const T 81).div hden hden_ne
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · field_simp [hT.ne']
      ring
    · filter_upwards with y
      simp only [Pi.div_apply]
  have hlog : HasDerivAt
      (fun y : Real => Real.log (1 + 81 / (4 * y ^ 2)))
      ((-81 / (2 * T ^ 3)) / (1 + 81 / (4 * T ^ 2))) T := by
    have hraw := (hfrac.const_add 1).log (by positivity)
    refine hraw.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp only [Pi.add_apply]
  unfold bennettGammaIntervalLogComponent
  have hraw := (hasDerivAt_pow 2 T).mul hlog
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
  · field_simp [hT.ne']
    ring
  · filter_upwards with y
    simp only [Pi.mul_apply, id_eq]

/-- The logarithm component is monotone on positive heights. -/
theorem bennettGammaIntervalLogComponent_monotoneOn :
    MonotoneOn bennettGammaIntervalLogComponent (Set.Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi (0 : Real))
  · intro T hT
    exact (hasDerivAt_bennettGammaIntervalLogComponent
      (Set.mem_Ioi.mp hT)).continuousAt.continuousWithinAt
  · intro T hT
    have hT_pos : 0 < T := by simpa using hT
    exact (hasDerivAt_bennettGammaIntervalLogComponent hT_pos).hasDerivWithinAt
  · intro T hT
    have hT_pos : 0 < T := by simpa using hT
    have hx : 0 <= 81 / (4 * T ^ 2) := by positivity
    have hgap :
        0 <= Real.log (1 + 81 / (4 * T ^ 2)) -
          (81 / (4 * T ^ 2)) / (1 + 81 / (4 * T ^ 2)) :=
      sub_nonneg.mpr (log_one_add_rational_lower hx)
    positivity

/-- The notebook's even-parity rational component `4*T^2/(81+4*T^2)`. -/
def bennettGammaIntervalRationalComponent (T : Real) : Real :=
  4 * T ^ 2 / (81 + 4 * T ^ 2)

/-- The rational component is monotone on nonnegative heights. -/
theorem bennettGammaIntervalRationalComponent_monotoneOn :
    MonotoneOn bennettGammaIntervalRationalComponent (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 <= x := Set.mem_Ici.mp hx
  have hy0 : 0 <= y := Set.mem_Ici.mp hy
  unfold bennettGammaIntervalRationalComponent
  rw [div_le_div_iff₀ (by positivity : 0 < (81 + 4 * x ^ 2 : Real))
    (by positivity : 0 < (81 + 4 * y ^ 2 : Real))]
  nlinarith [pow_le_pow_left₀ hx0 hxy 2]

/--
The notebook's even-parity `g11` component, rewritten using the project
denominator `81 + 4*T^2`.
-/
def bennettGammaIntervalRpowComponent (T : Real) : Real :=
  32 * T * (81 + 4 * T ^ 2) ^ (-(3 / 2 : Real))

/-- Exact derivative exposing the sole positive critical height of `g11`. -/
theorem hasDerivAt_bennettGammaIntervalRpowComponent (T : Real) :
    HasDerivAt bennettGammaIntervalRpowComponent
      (32 * (81 - 8 * T ^ 2) *
        (81 + 4 * T ^ 2) ^ (-(5 / 2 : Real))) T := by
  let B : Real := 81 + 4 * T ^ 2
  have hB_pos : 0 < B := by dsimp [B]; positivity
  have hB : HasDerivAt (fun y : Real => 81 + 4 * y ^ 2) (8 * T) T := by
    have hraw := (hasDerivAt_const T 81).add
      ((hasDerivAt_const T 4).mul (hasDerivAt_pow 2 T))
    refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · ring
    · filter_upwards with y
      simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  have hpow : HasDerivAt
      (fun y : Real => (81 + 4 * y ^ 2) ^ (-(3 / 2 : Real)))
      ((-(3 / 2 : Real)) * B ^ (-(5 / 2 : Real)) * (8 * T)) T := by
    apply (hB.rpow_const (Or.inl hB_pos.ne')).congr_deriv
    dsimp [B]
    ring
  have hrpow :
      B ^ (-(3 / 2 : Real)) = B * B ^ (-(5 / 2 : Real)) := by
    calc
      B ^ (-(3 / 2 : Real)) = B ^ ((1 : Real) + (-(5 / 2 : Real))) := by
        congr 1
        norm_num
      _ = B ^ (1 : Real) * B ^ (-(5 / 2 : Real)) :=
        Real.rpow_add hB_pos 1 (-(5 / 2 : Real))
      _ = B * B ^ (-(5 / 2 : Real)) := by rw [Real.rpow_one]
  unfold bennettGammaIntervalRpowComponent
  have hraw := ((hasDerivAt_const T 32).mul (hasDerivAt_id T)).mul hpow
  refine (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
  · dsimp [B] at hrpow ⊢
    rw [hrpow]
    ring
  · filter_upwards with y
    simp only [Pi.mul_apply, id_eq]

/-- `g11` is locally increasing below its critical height. -/
theorem bennettGammaIntervalRpowComponent_deriv_nonneg
    {T : Real} (hT : 8 * T ^ 2 <= 81) :
    0 <= 32 * (81 - 8 * T ^ 2) *
      (81 + 4 * T ^ 2) ^ (-(5 / 2 : Real)) := by
  positivity

/-- `g11` is locally decreasing above its critical height. -/
theorem bennettGammaIntervalRpowComponent_deriv_nonpos
    {T : Real} (hT : 81 <= 8 * T ^ 2) :
    32 * (81 - 8 * T ^ 2) *
      (81 + 4 * T ^ 2) ^ (-(5 / 2 : Real)) <= 0 := by
  have hfactor : 81 - 8 * T ^ 2 <= 0 := by linarith
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hfactor)
    (Real.rpow_nonneg (by positivity) _)

/-- `g11` is monotone up to any height below its positive critical point. -/
theorem bennettGammaIntervalRpowComponent_monotoneOn_Icc
    {b : Real} (hb : 0 <= b) (hcritical : 8 * b ^ 2 <= 81) :
    MonotoneOn bennettGammaIntervalRpowComponent (Set.Icc 0 b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0 : Real) b)
  · intro T hT
    exact (hasDerivAt_bennettGammaIntervalRpowComponent T).continuousAt.continuousWithinAt
  · intro T hT
    exact (hasDerivAt_bennettGammaIntervalRpowComponent T).hasDerivWithinAt
  · intro T hT
    have hT' : T ∈ Set.Icc (0 : Real) b := interior_subset hT
    have hT0 : 0 <= T := (Set.mem_Icc.mp hT').1
    have hTb : T <= b := (Set.mem_Icc.mp hT').2
    apply bennettGammaIntervalRpowComponent_deriv_nonneg
    nlinarith [sq_nonneg (b - T)]

/-- `g11` is antitone beyond any height above its positive critical point. -/
theorem bennettGammaIntervalRpowComponent_antitoneOn_Ici
    {a : Real} (ha : 0 <= a) (hcritical : 81 <= 8 * a ^ 2) :
    AntitoneOn bennettGammaIntervalRpowComponent (Set.Ici a) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici a)
  · intro T hT
    exact (hasDerivAt_bennettGammaIntervalRpowComponent T).continuousAt.continuousWithinAt
  · intro T hT
    exact (hasDerivAt_bennettGammaIntervalRpowComponent T).hasDerivWithinAt
  · intro T hT
    have hT' : T ∈ Set.Ici a := interior_subset hT
    have haT : a <= T := Set.mem_Ici.mp hT'
    apply bennettGammaIntervalRpowComponent_deriv_nonpos
    nlinarith [sq_nonneg (T - a)]

/-- The scaled upper Stirling envelope `gUpper(0,T)` from the source notebook. -/
def bennettGammaScaledUpperEnvelope (T : Real) : Real :=
  ((1 / 120 : Real) + 1 / (90 * Real.pi)) *
      bennettGammaIntervalRpowComponent T -
    1 / (3 * Real.pi) * bennettGammaIntervalRationalComponent T +
    1 / Real.pi *
      (2 * bennettGammaIntervalArctanComponent (1 / 2) T +
        2 * bennettGammaIntervalArctanComponent (5 / 2) T -
          (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) T) +
    1 / (2 * Real.pi) * bennettGammaIntervalLogComponent T

/-- The scaled lower Stirling envelope `gLower(0,T)` from the source notebook. -/
def bennettGammaScaledLowerEnvelope (T : Real) : Real :=
  (-(1 / 120 : Real) - 1 / (90 * Real.pi)) *
      bennettGammaIntervalRpowComponent T -
    1 / (3 * Real.pi) * bennettGammaIntervalRationalComponent T +
    1 / Real.pi *
      (2 * bennettGammaIntervalArctanComponent (1 / 2) T +
        2 * bennettGammaIntervalArctanComponent (5 / 2) T -
          (7 / 2 : Real) * bennettGammaIntervalArctanComponent (9 / 2) T) +
    1 / (2 * Real.pi) * bennettGammaIntervalLogComponent T

/-- The notebook's upper envelope is exactly `T` times the existing approximation. -/
theorem bennettGammaScaledUpperEnvelope_eq
    {T : Real} (hT : T ≠ 0) :
    bennettGammaScaledUpperEnvelope T = T * bennettGammaApproximation T := by
  have hB : 0 < (81 + 4 * T ^ 2 : Real) := by positivity
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hrpow_ne :
      (81 + 4 * T ^ 2) ^ (3 / 2 : Real) ≠ 0 :=
    (Real.rpow_pos_of_pos hB (3 / 2 : Real)).ne'
  have hrpow :
      (81 + 4 * T ^ 2) ^ (-(3 / 2 : Real)) =
        ((81 + 4 * T ^ 2) ^ (3 / 2 : Real))⁻¹ := by
    exact Real.rpow_neg hB.le (3 / 2 : Real)
  unfold bennettGammaScaledUpperEnvelope
    bennettGammaIntervalRpowComponent
    bennettGammaIntervalRationalComponent
    bennettGammaIntervalArctanComponent
    bennettGammaIntervalLogComponent
  unfold bennettGammaApproximation
  rw [bennettGammaStirlingTerm_eq]
  rw [hrpow]
  field_simp [hT, hpi, hrpow_ne]
  ring

/-- The width of the published scaled Stirling enclosure. -/
theorem bennettGammaScaledUpperEnvelope_sub_lower (T : Real) :
    bennettGammaScaledUpperEnvelope T - bennettGammaScaledLowerEnvelope T =
      2 * ((1 / 120 : Real) + 1 / (90 * Real.pi)) *
        bennettGammaIntervalRpowComponent T := by
  unfold bennettGammaScaledUpperEnvelope bennettGammaScaledLowerEnvelope
  ring

/-- The scaled Stirling-envelope width is tiny on the elementary tail. -/
theorem bennettGammaIntervalRpowComponent_le_one_sixteen
    {T : Real} (hT : 8 <= T) :
    bennettGammaIntervalRpowComponent T <= 1 / 16 := by
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hB : 0 < (81 + 4 * T ^ 2 : Real) := by positivity
  have hsqrt : 2 * T <= Real.sqrt (81 + 4 * T ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hrpow :
      (81 + 4 * T ^ 2) ^ (3 / 2 : Real) =
        (81 + 4 * T ^ 2) * Real.sqrt (81 + 4 * T ^ 2) := by
    calc
      (81 + 4 * T ^ 2) ^ (3 / 2 : Real) =
          (81 + 4 * T ^ 2) ^ ((1 : Real) + 1 / 2) := by norm_num
      _ = (81 + 4 * T ^ 2) ^ (1 : Real) *
          (81 + 4 * T ^ 2) ^ (1 / 2 : Real) :=
        Real.rpow_add hB 1 (1 / 2)
      _ = (81 + 4 * T ^ 2) * Real.sqrt (81 + 4 * T ^ 2) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
  have hden_pos :
      0 < (81 + 4 * T ^ 2) ^ (3 / 2 : Real) :=
    Real.rpow_pos_of_pos hB _
  have hden :
      8 * T ^ 3 <= (81 + 4 * T ^ 2) ^ (3 / 2 : Real) := by
    rw [hrpow]
    nlinarith [sq_nonneg T]
  unfold bennettGammaIntervalRpowComponent
  rw [Real.rpow_neg hB.le]
  change 32 * T / (81 + 4 * T ^ 2) ^ (3 / 2 : Real) <= 1 / 16
  apply (div_le_iff₀ hden_pos).2
  nlinarith [sq_nonneg (T - 8)]

/-- On `T >= 8`, the published upper and lower envelopes differ by at most `1/500`. -/
theorem bennettGammaScaledEnvelope_width_le
    {T : Real} (hT : 8 <= T) :
    bennettGammaScaledUpperEnvelope T - bennettGammaScaledLowerEnvelope T <=
      1 / 500 := by
  have hpi3 : (3 : Real) <= Real.pi := Real.pi_gt_three.le
  have hrecip :
      (1 : Real) / (90 * Real.pi) <= 1 / 270 := by
    rw [div_le_div_iff₀ (by positivity : (0 : Real) < 90 * Real.pi)
      (by norm_num : (0 : Real) < 270)]
    nlinarith
  have hcoeff :
      2 * ((1 / 120 : Real) + 1 / (90 * Real.pi)) <= 13 / 540 := by
    linarith
  have hcoeff_nonneg : (0 : Real) <= 13 / 540 := by norm_num
  have hcomponent_nonneg : 0 <= bennettGammaIntervalRpowComponent T := by
    unfold bennettGammaIntervalRpowComponent
    positivity
  rw [bennettGammaScaledUpperEnvelope_sub_lower]
  calc
    2 * ((1 / 120 : Real) + 1 / (90 * Real.pi)) *
          bennettGammaIntervalRpowComponent T <=
        (13 / 540 : Real) * (1 / 16) :=
      mul_le_mul hcoeff
        (bennettGammaIntervalRpowComponent_le_one_sixteen hT)
        hcomponent_nonneg hcoeff_nonneg
    _ <= 1 / 500 := by norm_num

/-- The notebook envelope bounds are automatic beyond its finite interval. -/
theorem bennettGammaScaledEnvelope_tail
    {T : Real} (hT : 8 <= T) :
    -(1 / 25 : Real) <= bennettGammaScaledLowerEnvelope T ∧
      bennettGammaScaledUpperEnvelope T <= 1 / 25 := by
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have happrox := abs_le.mp (bennettGammaApproximation_abs_le_of_eight_le hT)
  have hscale : T * (19 / (500 * T) : Real) = 19 / 500 := by
    field_simp [hT_pos.ne']
  have hupper_lower :
      -(19 / 500 : Real) <= bennettGammaScaledUpperEnvelope T := by
    rw [bennettGammaScaledUpperEnvelope_eq hT_pos.ne']
    calc
      -(19 / 500 : Real) = T * (-(19 / (500 * T) : Real)) := by
        rw [mul_neg, hscale]
      _ <= T * bennettGammaApproximation T :=
        mul_le_mul_of_nonneg_left happrox.1 hT_pos.le
  have hupper_upper :
      bennettGammaScaledUpperEnvelope T <= 19 / 500 := by
    rw [bennettGammaScaledUpperEnvelope_eq hT_pos.ne']
    calc
      T * bennettGammaApproximation T <= T * (19 / (500 * T) : Real) :=
        mul_le_mul_of_nonneg_left happrox.2 hT_pos.le
      _ = 19 / 500 := hscale
  have hwidth := bennettGammaScaledEnvelope_width_le hT
  have hwidth_eq := bennettGammaScaledUpperEnvelope_sub_lower T
  constructor <;> nlinarith

/-- The source-level asymmetric shifted-Stirling enclosure. -/
def BennettGammaScaledStirlingEnvelope : Prop :=
  ∀ T : Real,
    (5 : Real) / 7 <= T ->
      bennettGammaScaledLowerEnvelope T <= T * bellottiWongGammaRemainder T ∧
        T * bellottiWongGammaRemainder T <= bennettGammaScaledUpperEnvelope T

/-- The finite interval certificate exactly matching the source notebook. -/
def BennettGammaCompactScaledIntervalEstimate : Prop :=
  ∀ T : Real,
    (5 : Real) / 7 <= T ->
      T <= 8 ->
        -(1 / 25 : Real) <= bennettGammaScaledLowerEnvelope T ∧
          bennettGammaScaledUpperEnvelope T <= 1 / 25

/-- The global scaled interval estimate needed to remove the factor `T`. -/
def BennettGammaScaledIntervalEstimate : Prop :=
  ∀ T : Real,
    (5 : Real) / 7 <= T ->
      -(1 / 25 : Real) <= bennettGammaScaledLowerEnvelope T ∧
        bennettGammaScaledUpperEnvelope T <= 1 / 25

/-- The finite notebook certificate and elementary tail give the global estimate. -/
theorem bennettGammaScaledIntervalEstimate_of_compact
    (hCompact : BennettGammaCompactScaledIntervalEstimate) :
    BennettGammaScaledIntervalEstimate := by
  intro T hT
  by_cases hT8 : T <= 8
  · exact hCompact T hT hT8
  · exact bennettGammaScaledEnvelope_tail (le_of_lt (lt_of_not_ge hT8))

/-- The faithful asymmetric Stirling envelopes imply the required Gamma bound. -/
theorem bellottiWongGammaRemainder_abs_le_of_scaled_envelopes
    (hStirling : BennettGammaScaledStirlingEnvelope)
    (hInterval : BennettGammaScaledIntervalEstimate)
    {T : Real} (hT : (5 : Real) / 7 <= T) :
    |bellottiWongGammaRemainder T| <= 1 / (25 * T) := by
  have hT_pos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hStirlingT := hStirling T hT
  have hIntervalT := hInterval T hT
  have hscaled : |T * bellottiWongGammaRemainder T| <= 1 / 25 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hmul : T * |bellottiWongGammaRemainder T| <= 1 / 25 := by
    simpa [abs_mul, abs_of_pos hT_pos] using hscaled
  calc
    |bellottiWongGammaRemainder T| <= (1 / 25 : Real) / T := by
      exact (le_div_iff₀ hT_pos).mpr (by simpa [mul_comm] using hmul)
    _ = 1 / (25 * T) := by ring

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
