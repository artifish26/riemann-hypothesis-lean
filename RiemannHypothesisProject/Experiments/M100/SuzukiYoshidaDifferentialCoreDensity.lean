import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaIntervalSourceCoercivity
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaIntervalCompleteness
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# M100-DF6F differential-core density

This module starts the constructive proof of the remaining DF6F density gate.
It fixes a smooth scalar bump whose support is exactly the source interval and
promotes it to the project's compactly supported Schwartz core.  Later
boundary-cutoff approximants can therefore use one canonical object without
reopening support or Schwartz-decay bookkeeping.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace Nat ContDiff Topology

attribute [local instance] Measure.Subtype.measureSpace

/-- The normalized smooth exponential before restriction to `[-a,a]`. -/
def suzukiIntervalExponentialCore
    (a : Real) (m : Int) (x : Real) : Complex :=
  (((Real.sqrt (2 * a))⁻¹ : Real) : Complex) *
    Complex.exp
      (Complex.I *
        ((m : Complex) * (Real.pi : Complex) / (a : Complex)) *
          (x : Complex))

/-- The nonzero-mode frequency in the physical interval variable. -/
def suzukiIntervalModeFrequency (a : Real) (m : Int) : Complex :=
  Complex.I * ((m : Complex) * (Real.pi : Complex) / (a : Complex))

/-- Endpoint-zero primitive of a normalized nonzero interval exponential. -/
def suzukiIntervalExponentialPrimitive
    (a : Real) (m : Int) (x : Real) : Complex :=
  (suzukiIntervalModeFrequency a m)⁻¹ *
    (suzukiIntervalExponentialCore a m x -
      suzukiIntervalExponentialCore a m (-a))

theorem suzukiIntervalModeFrequency_ne_zero
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    suzukiIntervalModeFrequency a m ≠ 0 := by
  unfold suzukiIntervalModeFrequency
  exact mul_ne_zero Complex.I_ne_zero
    (div_ne_zero
      (mul_ne_zero (Int.cast_ne_zero.mpr hm)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr ha.ne'))

theorem hasDerivAt_suzukiIntervalExponentialPrimitive
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) (x : Real) :
    HasDerivAt (suzukiIntervalExponentialPrimitive a m)
      (suzukiIntervalExponentialCore a m x) x := by
  let c : Complex := suzukiIntervalModeFrequency a m
  have hc : c ≠ 0 := suzukiIntervalModeFrequency_ne_zero ha hm
  have hlin : HasDerivAt (fun y : Real => c * (y : Complex)) c x := by
    simpa using (((hasDerivAt_id (x : Complex)).const_mul c).comp_ofReal)
  have hexp : HasDerivAt (fun y : Real => Complex.exp (c * (y : Complex)))
      (Complex.exp (c * (x : Complex)) * c) x :=
    (Complex.hasDerivAt_exp (c * (x : Complex))).comp x hlin
  have hscaled := hexp.const_mul
    (((Real.sqrt (2 * a))⁻¹ : Real) : Complex)
  have hprimitive :=
    (hscaled.sub_const (suzukiIntervalExponentialCore a m (-a))).const_mul c⁻¹
  have hfactor : c⁻¹ *
        ((((Real.sqrt (2 * a))⁻¹ : Real) : Complex) *
          (Complex.exp (c * (x : Complex)) * c)) =
      suzukiIntervalExponentialCore a m x := by
    rw [show c⁻¹ *
        ((((Real.sqrt (2 * a))⁻¹ : Real) : Complex) *
          (Complex.exp (c * (x : Complex)) * c)) =
        ((((Real.sqrt (2 * a))⁻¹ : Real) : Complex) *
          Complex.exp (c * (x : Complex))) * (c⁻¹ * c) by ring]
    rw [inv_mul_cancel₀ hc, mul_one]
    rfl
  rw [hfactor] at hprimitive
  unfold suzukiIntervalExponentialPrimitive
  change HasDerivAt
    (fun y : Real => c⁻¹ *
      (suzukiIntervalExponentialCore a m y -
        suzukiIntervalExponentialCore a m (-a)))
    (suzukiIntervalExponentialCore a m x) x
  simpa only [suzukiIntervalExponentialCore,
    suzukiIntervalModeFrequency, c] using hprimitive

@[simp]
theorem suzukiIntervalExponentialPrimitive_left_endpoint
    (a : Real) (m : Int) :
    suzukiIntervalExponentialPrimitive a m (-a) = 0 := by
  simp [suzukiIntervalExponentialPrimitive]

theorem suzukiIntervalExponentialCore_endpoints_eq
    {a : Real} (ha : 0 < a) (m : Int) :
    suzukiIntervalExponentialCore a m a =
      suzukiIntervalExponentialCore a m (-a) := by
  let c : Complex := suzukiIntervalModeFrequency a m
  have hright : Complex.exp (c * (a : Complex)) =
      ((-1 : Complex) ^ m) := by
    calc
      Complex.exp (c * (a : Complex)) =
          Complex.exp ((m : Complex) *
            ((Real.pi : Complex) * Complex.I)) := by
        congr 1
        simp only [c, suzukiIntervalModeFrequency]
        field_simp [ha.ne']
      _ = Complex.exp ((Real.pi : Complex) * Complex.I) ^ m :=
        Complex.exp_int_mul _ _
      _ = ((-1 : Complex) ^ m) := by rw [Complex.exp_pi_mul_I]
  have hleft : Complex.exp (c * (-(a : Complex))) =
      ((-1 : Complex) ^ (-m)) := by
    calc
      Complex.exp (c * (-(a : Complex))) =
          Complex.exp ((-m : Complex) *
            ((Real.pi : Complex) * Complex.I)) := by
        congr 1
        simp only [c, suzukiIntervalModeFrequency]
        field_simp [ha.ne']
      _ = Complex.exp ((Real.pi : Complex) * Complex.I) ^ (-m) := by
        simpa using
          (Complex.exp_int_mul ((Real.pi : Complex) * Complex.I) (-m))
      _ = ((-1 : Complex) ^ (-m)) := by rw [Complex.exp_pi_mul_I]
  have hphase : ((-1 : Complex) ^ (-m)) = ((-1 : Complex) ^ m) := by
    rw [zpow_neg, ← inv_zpow]
    norm_num
  unfold suzukiIntervalExponentialCore
  rw [show (-a : Real) = -(a : Real) by rfl, Complex.ofReal_neg,
    show Complex.I * ((m : Complex) * (Real.pi : Complex) / (a : Complex)) = c
      by rfl,
    hright, hleft, hphase]

@[simp]
theorem suzukiIntervalExponentialPrimitive_right_endpoint
    {a : Real} (ha : 0 < a) (m : Int) :
    suzukiIntervalExponentialPrimitive a m a = 0 := by
  rw [suzukiIntervalExponentialPrimitive,
    suzukiIntervalExponentialCore_endpoints_eq ha, sub_self, mul_zero]

theorem contDiff_suzukiIntervalExponentialPrimitive
    (a : Real) (m : Int) :
    ContDiff Real (⊤ : ℕ∞) (suzukiIntervalExponentialPrimitive a m) := by
  have hcast : ContDiff Real (⊤ : ℕ∞) (fun x : Real => (x : Complex)) :=
    Complex.ofRealCLM.contDiff
  unfold suzukiIntervalExponentialPrimitive suzukiIntervalExponentialCore
    suzukiIntervalModeFrequency
  fun_prop

theorem contDiff_suzukiIntervalExponentialCore
    (a : Real) (m : Int) :
    ContDiff Real (⊤ : ℕ∞) (suzukiIntervalExponentialCore a m) := by
  have hcast : ContDiff Real (⊤ : ℕ∞) (fun x : Real => (x : Complex)) :=
    Complex.ofRealCLM.contDiff
  unfold suzukiIntervalExponentialCore
  fun_prop

/-- Common pointwise norm of the normalized interval exponentials. -/
def suzukiIntervalModeAmplitude (a : Real) : NNReal :=
  ⟨(Real.sqrt (2 * a))⁻¹,
    inv_nonneg.mpr (Real.sqrt_nonneg _)⟩

@[simp]
theorem norm_suzukiIntervalExponentialCore
    (a : Real) (m : Int) (x : Real) :
    ‖suzukiIntervalExponentialCore a m x‖ =
      (suzukiIntervalModeAmplitude a : Real) := by
  unfold suzukiIntervalExponentialCore
  rw [norm_mul, Complex.norm_exp]
  have hre : (Complex.I *
      ((m : Complex) * (Real.pi : Complex) / (a : Complex)) *
        (x : Complex)).re = 0 := by simp
  rw [hre, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rfl

theorem lipschitzWith_suzukiIntervalExponentialPrimitive
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    LipschitzWith (suzukiIntervalModeAmplitude a)
      (suzukiIntervalExponentialPrimitive a m) := by
  rw [← lipschitzOnWith_univ]
  apply convex_univ.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
  · intro x _
    exact (hasDerivAt_suzukiIntervalExponentialPrimitive ha hm x).hasDerivWithinAt
  · intro x _
    rw [← NNReal.coe_le_coe]
    change ‖suzukiIntervalExponentialCore a m x‖ ≤
      (suzukiIntervalModeAmplitude a : Real)
    rw [norm_suzukiIntervalExponentialCore]

/-- The derivative of the standard smooth transition is supported in its
transition interval.  This packages the constant tails of the mathlib
function into the compact-support fact needed for a uniform derivative
bound. -/
theorem hasCompactSupport_deriv_smoothTransition :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have heventually :
        Real.smoothTransition =ᶠ[𝓝 x] fun _ : Real => 0 := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos hy.le
    rw [Filter.EventuallyEq.deriv_eq heventually]
    simp
  · have heventually :
        Real.smoothTransition =ᶠ[𝓝 x] fun _ : Real => 1 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le hy.le
    rw [Filter.EventuallyEq.deriv_eq heventually]
    simp

theorem continuous_deriv_smoothTransition :
    Continuous (deriv Real.smoothTransition) :=
  (@Real.smoothTransition.contDiff (2 : ℕ∞)).continuous_deriv (by norm_num)

/-- A finite global bound for the derivative of mathlib's standard smooth
transition.  No numerical value is needed: scaling this bound gives the
explicit `O(1 / δ)` estimate for the interval boundary layer. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : Real, |deriv Real.smoothTransition x| ≤ C := by
  let g : Real → Real := fun x => |deriv Real.smoothTransition x|
  have hgContinuous : Continuous g := continuous_deriv_smoothTransition.abs
  have hgCompact : HasCompactSupport g :=
    hasCompactSupport_deriv_smoothTransition.abs
  obtain ⟨x₀, hx₀⟩ :=
    hgContinuous.exists_forall_ge_of_hasCompactSupport hgCompact
  exact ⟨g x₀, abs_nonneg _, hx₀⟩

/-- The canonical finite derivative bound used by the scaled cutoff family. -/
noncomputable def suzukiSmoothTransitionDerivativeBound : Real :=
  Classical.choose exists_smoothTransition_deriv_bound

theorem suzukiSmoothTransitionDerivativeBound_nonneg :
    0 ≤ suzukiSmoothTransitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_deriv_bound).1

theorem abs_deriv_smoothTransition_le (x : Real) :
    |deriv Real.smoothTransition x| ≤
      suzukiSmoothTransitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_deriv_bound).2 x

/-- A two-sided smooth cutoff with boundary-layer width `δ`.  It vanishes
outside `(-a,a)` and is identically one once both endpoints are at least
`δ` away. -/
def suzukiBoundaryLayerCutoff (a δ x : Real) : Real :=
  Real.smoothTransition ((x + a) / δ) *
    Real.smoothTransition ((a - x) / δ)

theorem contDiff_suzukiBoundaryLayerCutoff (a δ : Real) :
    ContDiff Real (⊤ : ℕ∞) (suzukiBoundaryLayerCutoff a δ) := by
  unfold suzukiBoundaryLayerCutoff
  fun_prop

theorem suzukiBoundaryLayerCutoff_nonneg (a δ x : Real) :
    0 ≤ suzukiBoundaryLayerCutoff a δ x := by
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

theorem suzukiBoundaryLayerCutoff_le_one (a δ x : Real) :
    suzukiBoundaryLayerCutoff a δ x ≤ 1 := by
  unfold suzukiBoundaryLayerCutoff
  nlinarith [Real.smoothTransition.nonneg ((x + a) / δ),
    Real.smoothTransition.le_one ((x + a) / δ),
    Real.smoothTransition.nonneg ((a - x) / δ),
    Real.smoothTransition.le_one ((a - x) / δ)]

theorem support_suzukiBoundaryLayerCutoff_subset
    {a δ : Real} (hδ : 0 < δ) :
    Function.support (suzukiBoundaryLayerCutoff a δ) ⊆ Ioo (-a) a := by
  intro x hx
  constructor
  · by_contra hleft
    have harg : (x + a) / δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    apply hx
    simp only [suzukiBoundaryLayerCutoff,
      Real.smoothTransition.zero_of_nonpos harg, zero_mul]
  · by_contra hright
    have harg : (a - x) / δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    apply hx
    simp only [suzukiBoundaryLayerCutoff,
      Real.smoothTransition.zero_of_nonpos harg, mul_zero]

theorem suzukiBoundaryLayerCutoff_eq_one
    {a δ x : Real} (hδ : 0 < δ)
    (hx : x ∈ Icc (-a + δ) (a - δ)) :
    suzukiBoundaryLayerCutoff a δ x = 1 := by
  have hleft : 1 ≤ (x + a) / δ :=
    (le_div_iff₀ hδ).2 (by linarith [hx.1])
  have hright : 1 ≤ (a - x) / δ :=
    (le_div_iff₀ hδ).2 (by linarith [hx.2])
  simp only [suzukiBoundaryLayerCutoff,
    Real.smoothTransition.one_of_one_le hleft,
    Real.smoothTransition.one_of_one_le hright, one_mul]

theorem hasDerivAt_suzukiBoundaryLayerCutoff
    {a δ x : Real} (hδ : δ ≠ 0) :
    HasDerivAt (suzukiBoundaryLayerCutoff a δ)
      (deriv Real.smoothTransition ((x + a) / δ) / δ *
          Real.smoothTransition ((a - x) / δ) -
        Real.smoothTransition ((x + a) / δ) *
          (deriv Real.smoothTransition ((a - x) / δ) / δ)) x := by
  unfold suzukiBoundaryLayerCutoff
  have htransition : Differentiable Real Real.smoothTransition :=
    (@Real.smoothTransition.contDiff 1).differentiable (by norm_num)
  have hleft := htransition.differentiableAt.hasDerivAt.comp x
    (((hasDerivAt_id x).add_const a).div_const δ)
  have hright := htransition.differentiableAt.hasDerivAt.comp x
    (((hasDerivAt_const x a).sub (hasDerivAt_id x)).div_const δ)
  have hproduct := hleft.mul hright
  change HasDerivAt
    (fun y => Real.smoothTransition ((y + a) / δ) *
      Real.smoothTransition ((a - y) / δ))
    (deriv Real.smoothTransition ((x + a) / δ) * (1 / δ) *
        Real.smoothTransition ((a - x) / δ) +
      Real.smoothTransition ((x + a) / δ) *
        (deriv Real.smoothTransition ((a - x) / δ) * ((0 - 1) / δ))) x
    at hproduct
  convert hproduct using 1
  field_simp
  ring

theorem deriv_suzukiBoundaryLayerCutoff
    {a δ x : Real} (hδ : δ ≠ 0) :
    deriv (suzukiBoundaryLayerCutoff a δ) x =
      deriv Real.smoothTransition ((x + a) / δ) / δ *
          Real.smoothTransition ((a - x) / δ) -
        Real.smoothTransition ((x + a) / δ) *
          (deriv Real.smoothTransition ((a - x) / δ) / δ) :=
  (hasDerivAt_suzukiBoundaryLayerCutoff hδ).deriv

/-- The scaled cutoff derivative has the expected inverse-width bound. -/
theorem abs_deriv_suzukiBoundaryLayerCutoff_le
    {a δ x : Real} (hδ : 0 < δ) :
    |deriv (suzukiBoundaryLayerCutoff a δ) x| ≤
      2 * suzukiSmoothTransitionDerivativeBound / δ := by
  rw [deriv_suzukiBoundaryLayerCutoff hδ.ne']
  let leftArg := (x + a) / δ
  let rightArg := (a - x) / δ
  have hleftDeriv : |deriv Real.smoothTransition leftArg| / δ ≤
      suzukiSmoothTransitionDerivativeBound / δ :=
    div_le_div_of_nonneg_right (abs_deriv_smoothTransition_le leftArg) hδ.le
  have hrightDeriv : |deriv Real.smoothTransition rightArg| / δ ≤
      suzukiSmoothTransitionDerivativeBound / δ :=
    div_le_div_of_nonneg_right (abs_deriv_smoothTransition_le rightArg) hδ.le
  have hleftValue : |Real.smoothTransition leftArg| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg leftArg)]
    exact Real.smoothTransition.le_one leftArg
  have hrightValue : |Real.smoothTransition rightArg| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg rightArg)]
    exact Real.smoothTransition.le_one rightArg
  calc
    |deriv Real.smoothTransition leftArg / δ *
          Real.smoothTransition rightArg -
        Real.smoothTransition leftArg *
          (deriv Real.smoothTransition rightArg / δ)|
        ≤ |deriv Real.smoothTransition leftArg / δ *
              Real.smoothTransition rightArg| +
            |Real.smoothTransition leftArg *
              (deriv Real.smoothTransition rightArg / δ)| := abs_sub _ _
    _ = (|deriv Real.smoothTransition leftArg| / δ) *
          |Real.smoothTransition rightArg| +
        |Real.smoothTransition leftArg| *
          (|deriv Real.smoothTransition rightArg| / δ) := by
      rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hδ]
    _ ≤ (suzukiSmoothTransitionDerivativeBound / δ) * 1 +
          1 * (suzukiSmoothTransitionDerivativeBound / δ) := by
      apply add_le_add
      · exact mul_le_mul hleftDeriv hrightValue (abs_nonneg _)
          (div_nonneg suzukiSmoothTransitionDerivativeBound_nonneg hδ.le)
      · exact mul_le_mul hleftValue hrightDeriv
          (div_nonneg (abs_nonneg _) hδ.le) zero_le_one
    _ = 2 * suzukiSmoothTransitionDerivativeBound / δ := by ring

theorem deriv_suzukiBoundaryLayerCutoff_eq_zero_of_mem_Ioo
    {a δ x : Real} (hδ : 0 < δ)
    (hx : x ∈ Ioo (-a + δ) (a - δ)) :
    deriv (suzukiBoundaryLayerCutoff a δ) x = 0 := by
  have heventually :
      suzukiBoundaryLayerCutoff a δ =ᶠ[𝓝 x] fun _ : Real => 1 := by
    filter_upwards [mem_nhds_iff.2 ⟨Ioo (-a + δ) (a - δ),
      subset_rfl, isOpen_Ioo, hx⟩] with y hy
    exact suzukiBoundaryLayerCutoff_eq_one hδ ⟨hy.1.le, hy.2.le⟩
  rw [Filter.EventuallyEq.deriv_eq heventually]
  simp

/-- Endpoint vanishing cancels the inverse-width derivative loss: wherever
the cutoff derivative is nonzero, a Lipschitz primitive is at most its
Lipschitz constant times the boundary width. -/
theorem norm_le_mul_width_of_deriv_boundaryLayerCutoff_ne_zero
    {a δ x : Real} {K : NNReal} {F : Real → Complex}
    (hδ : 0 < δ) (hF : LipschitzWith K F)
    (hleftEndpoint : F (-a) = 0) (hrightEndpoint : F a = 0)
    (hx : x ∈ Icc (-a) a)
    (hderiv : deriv (suzukiBoundaryLayerCutoff a δ) x ≠ 0) :
    ‖F x‖ ≤ (K : Real) * δ := by
  have hnotInterior : x ∉ Ioo (-a + δ) (a - δ) := by
    intro hinterior
    exact hderiv
      (deriv_suzukiBoundaryLayerCutoff_eq_zero_of_mem_Ioo hδ hinterior)
  simp only [mem_Ioo, not_and_or, not_lt] at hnotInterior
  rcases hnotInterior with hleft | hright
  · calc
      ‖F x‖ = dist (F x) (F (-a)) := by
        rw [hleftEndpoint, dist_zero_right]
      _ ≤ (K : Real) * dist x (-a) := hF.dist_le_mul x (-a)
      _ = (K : Real) * (x + a) := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hx.1])]
        ring
      _ ≤ (K : Real) * δ := by
        exact mul_le_mul_of_nonneg_left (by linarith) K.2
  · calc
      ‖F x‖ = dist (F x) (F a) := by
        rw [hrightEndpoint, dist_zero_right]
      _ ≤ (K : Real) * dist x a := hF.dist_le_mul x a
      _ = (K : Real) * (a - x) := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith [hx.2])]
        ring
      _ ≤ (K : Real) * δ := by
        exact mul_le_mul_of_nonneg_left (by linarith) K.2

/-- Uniform cancellation bound for the derivative-layer error.  Crucially,
the right-hand side is independent of the boundary width. -/
theorem norm_deriv_boundaryLayerCutoff_mul_le
    {a δ x : Real} {K : NNReal} {F : Real → Complex}
    (hδ : 0 < δ) (hF : LipschitzWith K F)
    (hleftEndpoint : F (-a) = 0) (hrightEndpoint : F a = 0)
    (hx : x ∈ Icc (-a) a) :
    ‖((deriv (suzukiBoundaryLayerCutoff a δ) x : Real) : Complex) * F x‖ ≤
      2 * suzukiSmoothTransitionDerivativeBound * (K : Real) := by
  by_cases hderiv : deriv (suzukiBoundaryLayerCutoff a δ) x = 0
  · rw [hderiv]
    simp only [Complex.ofReal_zero, zero_mul, norm_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        suzukiSmoothTransitionDerivativeBound_nonneg) K.2
  · have hprimitive :=
      norm_le_mul_width_of_deriv_boundaryLayerCutoff_ne_zero
        hδ hF hleftEndpoint hrightEndpoint hx hderiv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |deriv (suzukiBoundaryLayerCutoff a δ) x| * ‖F x‖ ≤
          (2 * suzukiSmoothTransitionDerivativeBound / δ) *
            ((K : Real) * δ) := by
        exact mul_le_mul (abs_deriv_suzukiBoundaryLayerCutoff_le hδ)
          hprimitive (norm_nonneg _)
          (div_nonneg
            (mul_nonneg (by norm_num)
              suzukiSmoothTransitionDerivativeBound_nonneg) hδ.le)
      _ = 2 * suzukiSmoothTransitionDerivativeBound * (K : Real) := by
        field_simp

/-- The quantitative boundary-layer cutoff as an element of the exact smooth
source core. -/
def suzukiBoundaryLayerCutoffSmoothCore
    {a δ : Real} (hδ : 0 < δ) : SuzukiSmoothCore a := by
  let f : Real → Complex := fun x => (suzukiBoundaryLayerCutoff a δ x : Complex)
  have hsupport : Function.support f ⊆ Ioo (-a) a := by
    intro x hx
    apply support_suzukiBoundaryLayerCutoff_subset hδ
    change (suzukiBoundaryLayerCutoff a δ x : Complex) ≠ 0 at hx
    exact Complex.ofReal_ne_zero.mp hx
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hopen := hsupport hne
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  refine ⟨hfCompact.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_suzukiBoundaryLayerCutoff a δ)), ?_⟩
  exact hsupport

@[simp]
theorem suzukiBoundaryLayerCutoffSmoothCore_apply
    {a δ : Real} (hδ : 0 < δ) (x : Real) :
    (suzukiBoundaryLayerCutoffSmoothCore (a := a) (δ := δ) hδ).1 x =
      (suzukiBoundaryLayerCutoff a δ x : Complex) := by
  rfl

/-- Canonical shrinking boundary width for the quantitative cutoff sequence. -/
def suzukiBoundaryLayerWidth (a : Real) (n : Nat) : Real :=
  a / ((n : Real) + 1)

theorem suzukiBoundaryLayerWidth_pos
    {a : Real} (ha : 0 < a) (n : Nat) :
    0 < suzukiBoundaryLayerWidth a n := by
  unfold suzukiBoundaryLayerWidth
  positivity

theorem tendsto_suzukiBoundaryLayerWidth_atTop (a : Real) :
    Filter.Tendsto (suzukiBoundaryLayerWidth a)
      Filter.atTop (𝓝 0) := by
  unfold suzukiBoundaryLayerWidth
  have h := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => a) Filter.atTop (𝓝 a)).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using h

/-- The canonical quantitative interval cutoff sequence. -/
def suzukiQuantitativeIntervalCutoff
    (a : Real) (n : Nat) : Real → Real :=
  suzukiBoundaryLayerCutoff a (suzukiBoundaryLayerWidth a n)

theorem support_suzukiQuantitativeIntervalCutoff_subset
    {a : Real} (ha : 0 < a) (n : Nat) :
    Function.support (suzukiQuantitativeIntervalCutoff a n) ⊆
      Ioo (-a) a :=
  support_suzukiBoundaryLayerCutoff_subset
    (suzukiBoundaryLayerWidth_pos ha n)

theorem abs_deriv_suzukiQuantitativeIntervalCutoff_le
    {a : Real} (ha : 0 < a) (n : Nat) (x : Real) :
    |deriv (suzukiQuantitativeIntervalCutoff a n) x| ≤
      2 * suzukiSmoothTransitionDerivativeBound /
        suzukiBoundaryLayerWidth a n :=
  abs_deriv_suzukiBoundaryLayerCutoff_le
    (suzukiBoundaryLayerWidth_pos ha n)

theorem tendsto_suzukiQuantitativeIntervalCutoff_atTop
    {a x : Real} (ha : 0 < a) (hx : x ∈ Ioo (-a) a) :
    Filter.Tendsto (fun n : Nat => suzukiQuantitativeIntervalCutoff a n x)
      Filter.atTop (𝓝 1) := by
  let d : Real := min (x + a) (a - x)
  have hd : 0 < d := by
    exact lt_min (by linarith [hx.1]) (by linarith [hx.2])
  have heventually : ∀ᶠ n : Nat in Filter.atTop,
      suzukiBoundaryLayerWidth a n < d :=
    (tendsto_suzukiBoundaryLayerWidth_atTop a).eventually
      (eventually_lt_nhds hd)
  apply tendsto_const_nhds.congr'
  filter_upwards [heventually] with n hn
  symm
  apply suzukiBoundaryLayerCutoff_eq_one
    (suzukiBoundaryLayerWidth_pos ha n)
  constructor <;> dsimp only [d] at hn <;>
    have hmin := min_le_left (x + a) (a - x) <;>
    have hmin' := min_le_right (x + a) (a - x) <;>
    linarith

theorem eventually_deriv_suzukiQuantitativeIntervalCutoff_eq_zero
    {a x : Real} (ha : 0 < a) (hx : x ∈ Ioo (-a) a) :
    ∀ᶠ n : Nat in Filter.atTop,
      deriv (suzukiQuantitativeIntervalCutoff a n) x = 0 := by
  let d : Real := min (x + a) (a - x)
  have hd : 0 < d := by
    exact lt_min (by linarith [hx.1]) (by linarith [hx.2])
  have heventually : ∀ᶠ n : Nat in Filter.atTop,
      suzukiBoundaryLayerWidth a n < d :=
    (tendsto_suzukiBoundaryLayerWidth_atTop a).eventually
      (eventually_lt_nhds hd)
  filter_upwards [heventually] with n hn
  apply deriv_suzukiBoundaryLayerCutoff_eq_zero_of_mem_Ioo
    (suzukiBoundaryLayerWidth_pos ha n)
  constructor <;> dsimp only [d] at hn <;>
    have hmin := min_le_left (x + a) (a - x) <;>
    have hmin' := min_le_right (x + a) (a - x) <;>
    linarith

/-- Every member of the canonical quantitative sequence lies in the exact
smooth source core. -/
def suzukiQuantitativeIntervalCutoffSmoothCore
    {a : Real} (ha : 0 < a) (n : Nat) : SuzukiSmoothCore a :=
  suzukiBoundaryLayerCutoffSmoothCore
    (suzukiBoundaryLayerWidth_pos ha n)

@[simp]
theorem suzukiQuantitativeIntervalCutoffSmoothCore_apply
    {a : Real} (ha : 0 < a) (n : Nat) (x : Real) :
    (suzukiQuantitativeIntervalCutoffSmoothCore ha n).1 x =
      (suzukiQuantitativeIntervalCutoff a n x : Complex) := by
  rfl

/-- The endpoint-zero primitive of an interval Fourier mode, localized by the
canonical shrinking cutoff and promoted to the exact smooth source core. -/
def suzukiQuantitativeModePrimitiveSmoothCore
    {a : Real} (ha : 0 < a) (m : Int) (n : Nat) : SuzukiSmoothCore a := by
  let f : Real → Complex := fun x =>
    (suzukiQuantitativeIntervalCutoff a n x : Complex) *
      suzukiIntervalExponentialPrimitive a m x
  have hsupport : Function.support f ⊆ Ioo (-a) a := by
    intro x hx
    apply support_suzukiQuantitativeIntervalCutoff_subset ha n
    change suzukiQuantitativeIntervalCutoff a n x ≠ 0
    intro hzero
    apply hx
    simp [f, hzero]
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hopen := hsupport hne
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  have hcutoff : ContDiff Real (⊤ : ℕ∞)
      (fun x : Real =>
        (suzukiQuantitativeIntervalCutoff a n x : Complex)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_suzukiBoundaryLayerCutoff a
        (suzukiBoundaryLayerWidth a n))
  refine ⟨hfCompact.toSchwartzMap
      (hcutoff.mul (contDiff_suzukiIntervalExponentialPrimitive a m)), ?_⟩
  exact hsupport

@[simp]
theorem suzukiQuantitativeModePrimitiveSmoothCore_apply
    {a : Real} (ha : 0 < a) (m : Int) (n : Nat) (x : Real) :
    (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x =
      (suzukiQuantitativeIntervalCutoff a n x : Complex) *
        suzukiIntervalExponentialPrimitive a m x := by
  rfl

theorem hasDerivAt_suzukiQuantitativeModePrimitive
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0)
    (n : Nat) (x : Real) :
    HasDerivAt
      (fun y : Real =>
        (suzukiQuantitativeIntervalCutoff a n y : Complex) *
          suzukiIntervalExponentialPrimitive a m y)
      (((deriv (suzukiQuantitativeIntervalCutoff a n) x : Real) : Complex) *
          suzukiIntervalExponentialPrimitive a m x +
        (suzukiQuantitativeIntervalCutoff a n x : Complex) *
          suzukiIntervalExponentialCore a m x)
      x := by
  have hcutoff : HasDerivAt
      (fun y : Real =>
        (suzukiQuantitativeIntervalCutoff a n y : Complex))
      ((deriv (suzukiQuantitativeIntervalCutoff a n) x : Real) : Complex) x := by
    have hδ := suzukiBoundaryLayerWidth_pos ha n
    simpa only [suzukiQuantitativeIntervalCutoff,
      deriv_suzukiBoundaryLayerCutoff hδ.ne'] using
        (hasDerivAt_suzukiBoundaryLayerCutoff
          (a := a) (δ := suzukiBoundaryLayerWidth a n) (x := x)
          hδ.ne').ofReal_comp
  exact hcutoff.mul
    (hasDerivAt_suzukiIntervalExponentialPrimitive ha hm x)

theorem suzukiQuantitativeModePrimitiveSmoothCore_deriv_apply
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0)
    (n : Nat) (x : Real) :
    SchwartzMap.derivCLM Complex Complex
        (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x =
      ((deriv (suzukiQuantitativeIntervalCutoff a n) x : Real) : Complex) *
          suzukiIntervalExponentialPrimitive a m x +
        (suzukiQuantitativeIntervalCutoff a n x : Complex) *
          suzukiIntervalExponentialCore a m x := by
  rw [SchwartzMap.derivCLM_apply]
  exact (hasDerivAt_suzukiQuantitativeModePrimitive ha hm n x).deriv

/-- Exact product-rule formula for the differential of the localized mode
primitive.  Its first summand is precisely the derivative layer controlled
by the preceding dominated-convergence theorem. -/
theorem suzukiDifferential_quantitativeModePrimitiveSmoothCore_apply
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0)
    (n : Nat) (x : Real) :
    suzukiDifferential
        (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x =
      Complex.I *
        (((deriv (suzukiQuantitativeIntervalCutoff a n) x : Real) : Complex) *
            suzukiIntervalExponentialPrimitive a m x +
          (suzukiQuantitativeIntervalCutoff a n x : Complex) *
            suzukiIntervalExponentialCore a m x) := by
  rw [suzukiDifferential_apply,
    suzukiQuantitativeModePrimitiveSmoothCore_deriv_apply ha hm]

/-- The derivative-layer error for a concrete primitive, on the actual
finite-interval subtype. -/
def suzukiQuantitativeDerivativeLayer
    (a : Real) (n : Nat) (F : Real → Complex)
    (x : SuzukiFiniteInterval a) : Complex :=
  ((deriv (suzukiQuantitativeIntervalCutoff a n) x.1 : Real) : Complex) * F x.1

theorem aestronglyMeasurable_suzukiQuantitativeDerivativeLayer
    (a : Real) (n : Nat) {K : NNReal} {F : Real → Complex}
    (hF : LipschitzWith K F) :
    AEStronglyMeasurable
      (suzukiQuantitativeDerivativeLayer a n F) volume := by
  have hderivContinuous :
      Continuous (deriv (suzukiQuantitativeIntervalCutoff a n)) := by
    unfold suzukiQuantitativeIntervalCutoff
    exact (contDiff_suzukiBoundaryLayerCutoff a
      (suzukiBoundaryLayerWidth a n)).continuous_deriv (by norm_num)
  exact (Complex.continuous_ofReal.comp
    (hderivContinuous.comp continuous_subtype_val)).aestronglyMeasurable.mul
      (hF.continuous.comp continuous_subtype_val).aestronglyMeasurable

/-- The inverse-width derivative loss and endpoint vanishing cancel strongly
in `L²`: the derivative-layer error tends to zero for every endpoint-zero
Lipschitz primitive. -/
theorem tendsto_integral_norm_sq_suzukiQuantitativeDerivativeLayer
    {a : Real} (ha : 0 < a) {K : NNReal} {F : Real → Complex}
    (hF : LipschitzWith K F)
    (hleftEndpoint : F (-a) = 0) (hrightEndpoint : F a = 0) :
    Filter.Tendsto
      (fun n : Nat => ∫ x : SuzukiFiniteInterval a,
        ‖suzukiQuantitativeDerivativeLayer a n F x‖ ^ 2)
      Filter.atTop (𝓝 0) := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  let B : Real := 2 * suzukiSmoothTransitionDerivativeBound * (K : Real)
  let G : Nat → SuzukiFiniteInterval a → Real := fun n x =>
    ‖suzukiQuantitativeDerivativeLayer a n F x‖ ^ 2
  let bound : SuzukiFiniteInterval a → Real := fun _ => B ^ 2
  have hBNonneg : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        suzukiSmoothTransitionDerivativeBound_nonneg) K.2
  have hGMeasurable : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    exact (aestronglyMeasurable_suzukiQuantitativeDerivativeLayer
      a n hF).norm.pow 2
  have hBoundIntegrable : Integrable bound volume := by
    exact integrable_const (B ^ 2)
  have hBound : ∀ n, ∀ᵐ x : SuzukiFiniteInterval a,
      ‖G n x‖ ≤ bound x := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      have hpoint := norm_deriv_boundaryLayerCutoff_mul_le
        (suzukiBoundaryLayerWidth_pos ha n) hF
        hleftEndpoint hrightEndpoint x.2
      dsimp only [G, bound, B, suzukiQuantitativeDerivativeLayer,
        suzukiQuantitativeIntervalCutoff]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hpoint 2
  have hLimit : ∀ᵐ x : SuzukiFiniteInterval a,
      Filter.Tendsto (fun n => G n x) Filter.atTop (𝓝 0) := by
    have haeInterior : ∀ᵐ x : SuzukiFiniteInterval a,
        x.1 ∈ Ioo (-a) a := by
      apply (ae_restrict_iff_subtype measurableSet_Icc).mp
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun _ hx => hx
    filter_upwards [haeInterior] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards
      [eventually_deriv_suzukiQuantitativeIntervalCutoff_eq_zero ha hx]
      with n hn
    dsimp only [G, suzukiQuantitativeDerivativeLayer]
    rw [hn]
    norm_num
  have hDCT := tendsto_integral_of_dominated_convergence
    bound hGMeasurable hBoundIntegrable hBound hLimit
  simpa only [G, integral_zero] using hDCT

/-- The shrinking-cutoff derivative layer tends to zero for every normalized
nonzero interval Fourier mode. -/
theorem tendsto_integral_norm_sq_suzukiIntervalExponentialPrimitive_derivativeLayer
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    Filter.Tendsto
      (fun n : Nat => ∫ x : SuzukiFiniteInterval a,
        ‖suzukiQuantitativeDerivativeLayer a n
          (suzukiIntervalExponentialPrimitive a m) x‖ ^ 2)
      Filter.atTop (𝓝 0) :=
  tendsto_integral_norm_sq_suzukiQuantitativeDerivativeLayer ha
    (lipschitzWith_suzukiIntervalExponentialPrimitive ha hm)
    (suzukiIntervalExponentialPrimitive_left_endpoint a m)
    (suzukiIntervalExponentialPrimitive_right_endpoint ha m)

/-- The ordinary cutoff-multiplier error also vanishes in `L²` for each
normalized interval Fourier mode. -/
theorem tendsto_integral_norm_sq_suzukiQuantitativeModeCutoff_error
    {a : Real} (ha : 0 < a) (m : Int) :
    Filter.Tendsto
      (fun n : Nat => ∫ x : SuzukiFiniteInterval a,
        ‖(((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1) *
            suzukiIntervalExponentialCore a m x.1‖ ^ 2)
      Filter.atTop (𝓝 0) := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  let A : Real := suzukiIntervalModeAmplitude a
  let G : Nat → SuzukiFiniteInterval a → Real := fun n x =>
    ‖(((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1) *
        suzukiIntervalExponentialCore a m x.1‖ ^ 2
  let bound : SuzukiFiniteInterval a → Real := fun _ => A ^ 2
  have hANonneg : 0 ≤ A := (suzukiIntervalModeAmplitude a).2
  have hGMeasurable : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    have hcutoffContinuous : Continuous
        (suzukiQuantitativeIntervalCutoff a n) :=
      (contDiff_suzukiBoundaryLayerCutoff a
        (suzukiBoundaryLayerWidth a n)).continuous
    exact (((Complex.continuous_ofReal.comp
        (hcutoffContinuous.comp continuous_subtype_val)).sub
          continuous_const).aestronglyMeasurable.mul
        ((contDiff_suzukiIntervalExponentialCore a m).continuous.comp
          continuous_subtype_val).aestronglyMeasurable).norm.pow 2
  have hBoundIntegrable : Integrable bound volume := integrable_const (A ^ 2)
  have hBound : ∀ n, ∀ᵐ x : SuzukiFiniteInterval a,
      ‖G n x‖ ≤ bound x := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      have hcutoffNonneg :
          0 ≤ suzukiQuantitativeIntervalCutoff a n x.1 :=
        suzukiBoundaryLayerCutoff_nonneg a
          (suzukiBoundaryLayerWidth a n) x.1
      have hcutoffLeOne :
          suzukiQuantitativeIntervalCutoff a n x.1 ≤ 1 :=
        suzukiBoundaryLayerCutoff_le_one a
          (suzukiBoundaryLayerWidth a n) x.1
      have hfactor :
          ‖((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1‖ ≤
            1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonpos]
        · linarith
        · exact sub_nonpos.mpr hcutoffLeOne
      have hproduct :
          ‖(((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1) *
              suzukiIntervalExponentialCore a m x.1‖ ≤ A := by
        rw [norm_mul, norm_suzukiIntervalExponentialCore]
        exact mul_le_of_le_one_left hANonneg hfactor
      dsimp only [G, bound]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hproduct 2
  have hLimit : ∀ᵐ x : SuzukiFiniteInterval a,
      Filter.Tendsto (fun n => G n x) Filter.atTop (𝓝 0) := by
    have haeInterior : ∀ᵐ x : SuzukiFiniteInterval a,
        x.1 ∈ Ioo (-a) a := by
      apply (ae_restrict_iff_subtype measurableSet_Icc).mp
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun _ hx => hx
    filter_upwards [haeInterior] with x hx
    have hcutoff := tendsto_suzukiQuantitativeIntervalCutoff_atTop ha hx
    have herror : Filter.Tendsto
        (fun n : Nat =>
          (((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1) *
            suzukiIntervalExponentialCore a m x.1)
        Filter.atTop (𝓝 0) := by
      have hcutoffComplex : Filter.Tendsto
          (fun n : Nat =>
            ((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex))
          Filter.atTop (𝓝 1) := by
        change Filter.Tendsto
          (Complex.ofReal ∘ fun n : Nat =>
            suzukiQuantitativeIntervalCutoff a n x.1)
          Filter.atTop (𝓝 (Complex.ofReal 1))
        exact (Complex.continuous_ofReal.tendsto 1).comp hcutoff
      have hsub : Filter.Tendsto
          (fun n : Nat =>
            ((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1)
          Filter.atTop (𝓝 0) := by
        simpa using hcutoffComplex.sub
          (tendsto_const_nhds : Filter.Tendsto
            (fun _ : Nat => (1 : Complex)) Filter.atTop (𝓝 1))
      have hcore : Filter.Tendsto
          (fun _ : Nat => suzukiIntervalExponentialCore a m x.1)
          Filter.atTop (𝓝 (suzukiIntervalExponentialCore a m x.1)) :=
        tendsto_const_nhds
      simpa using hsub.mul hcore
    simpa only [G, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)] using
      herror.norm.pow 2
  have hDCT := tendsto_integral_of_dominated_convergence
    bound hGMeasurable hBoundIntegrable hBound hLimit
  simpa only [G, integral_zero] using hDCT

/-- The complete Suzuki differential of the localized primitive converges in
squared `L²` to `i` times the normalized nonzero interval Fourier mode. -/
theorem tendsto_integral_norm_sq_suzukiDifferential_quantitativeModePrimitive_error
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    Filter.Tendsto
      (fun n : Nat => ∫ x : SuzukiFiniteInterval a,
        ‖suzukiDifferential
              (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
            Complex.I * suzukiIntervalExponentialCore a m x.1‖ ^ 2)
      Filter.atTop (𝓝 0) := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  let A : Real := suzukiIntervalModeAmplitude a
  let B : Real := 2 * suzukiSmoothTransitionDerivativeBound * A
  let G : Nat → SuzukiFiniteInterval a → Real := fun n x =>
    ‖suzukiDifferential
          (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
        Complex.I * suzukiIntervalExponentialCore a m x.1‖ ^ 2
  let bound : SuzukiFiniteInterval a → Real := fun _ => (B + A) ^ 2
  have hANonneg : 0 ≤ A := (suzukiIntervalModeAmplitude a).2
  have hBNonneg : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        suzukiSmoothTransitionDerivativeBound_nonneg) hANonneg
  have hGMeasurable : ∀ n, AEStronglyMeasurable (G n) volume := by
    intro n
    exact (((suzukiDifferential
        (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1).continuous.comp
          continuous_subtype_val).sub
        (continuous_const.mul
          ((contDiff_suzukiIntervalExponentialCore a m).continuous.comp
            continuous_subtype_val))).aestronglyMeasurable.norm.pow 2
  have hBoundIntegrable : Integrable bound volume :=
    integrable_const ((B + A) ^ 2)
  have hBound : ∀ n, ∀ᵐ x : SuzukiFiniteInterval a,
      ‖G n x‖ ≤ bound x := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      let d : Complex :=
        ((deriv (suzukiQuantitativeIntervalCutoff a n) x.1 : Real) : Complex) *
          suzukiIntervalExponentialPrimitive a m x.1
      let c : Complex :=
        (((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1) *
          suzukiIntervalExponentialCore a m x.1
      have hd : ‖d‖ ≤ B := by
        have hpoint := norm_deriv_boundaryLayerCutoff_mul_le
          (suzukiBoundaryLayerWidth_pos ha n)
          (lipschitzWith_suzukiIntervalExponentialPrimitive ha hm)
          (suzukiIntervalExponentialPrimitive_left_endpoint a m)
          (suzukiIntervalExponentialPrimitive_right_endpoint ha m) x.2
        simpa only [d, B, A, suzukiQuantitativeIntervalCutoff] using hpoint
      have hcutoffLeOne :
          suzukiQuantitativeIntervalCutoff a n x.1 ≤ 1 :=
        suzukiBoundaryLayerCutoff_le_one a
          (suzukiBoundaryLayerWidth a n) x.1
      have hfactor :
          ‖((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1‖ ≤
            1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonpos]
        · have hcutoffNonneg :
              0 ≤ suzukiQuantitativeIntervalCutoff a n x.1 :=
            suzukiBoundaryLayerCutoff_nonneg a
              (suzukiBoundaryLayerWidth a n) x.1
          linarith
        · exact sub_nonpos.mpr hcutoffLeOne
      have hc : ‖c‖ ≤ A := by
        dsimp only [c, A]
        rw [norm_mul, norm_suzukiIntervalExponentialCore]
        exact mul_le_of_le_one_left hANonneg hfactor
      have hrearrange :
          suzukiDifferential
                (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
              Complex.I * suzukiIntervalExponentialCore a m x.1 =
            Complex.I * (d + c) := by
        rw [suzukiDifferential_quantitativeModePrimitiveSmoothCore_apply
          ha hm]
        dsimp only [d, c]
        ring
      have htotal :
          ‖suzukiDifferential
                (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
              Complex.I * suzukiIntervalExponentialCore a m x.1‖ ≤ B + A := by
        rw [hrearrange, norm_mul, Complex.norm_I, one_mul]
        exact (norm_add_le d c).trans (add_le_add hd hc)
      dsimp only [G, bound]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) htotal 2
  have hLimit : ∀ᵐ x : SuzukiFiniteInterval a,
      Filter.Tendsto (fun n => G n x) Filter.atTop (𝓝 0) := by
    have haeInterior : ∀ᵐ x : SuzukiFiniteInterval a,
        x.1 ∈ Ioo (-a) a := by
      apply (ae_restrict_iff_subtype measurableSet_Icc).mp
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun _ hx => hx
    filter_upwards [haeInterior] with x hx
    let d : Nat → Complex := fun n =>
      ((deriv (suzukiQuantitativeIntervalCutoff a n) x.1 : Real) : Complex) *
        suzukiIntervalExponentialPrimitive a m x.1
    let c : Nat → Complex := fun n =>
      (((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1) *
        suzukiIntervalExponentialCore a m x.1
    have hd : Filter.Tendsto d Filter.atTop (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards
        [eventually_deriv_suzukiQuantitativeIntervalCutoff_eq_zero ha hx]
        with n hn
      simp [d, hn]
    have hc : Filter.Tendsto c Filter.atTop (𝓝 0) := by
      have hcutoff := tendsto_suzukiQuantitativeIntervalCutoff_atTop ha hx
      have hcutoffComplex : Filter.Tendsto
          (Complex.ofReal ∘ fun n : Nat =>
            suzukiQuantitativeIntervalCutoff a n x.1)
          Filter.atTop (𝓝 (Complex.ofReal 1)) :=
        (Complex.continuous_ofReal.tendsto 1).comp hcutoff
      have hsub : Filter.Tendsto
          (fun n : Nat =>
            ((suzukiQuantitativeIntervalCutoff a n x.1 : Real) : Complex) - 1)
          Filter.atTop (𝓝 0) := by
        simpa using hcutoffComplex.sub
          (tendsto_const_nhds : Filter.Tendsto
            (fun _ : Nat => (1 : Complex)) Filter.atTop (𝓝 1))
      have hcore : Filter.Tendsto
          (fun _ : Nat => suzukiIntervalExponentialCore a m x.1)
          Filter.atTop (𝓝 (suzukiIntervalExponentialCore a m x.1)) :=
        tendsto_const_nhds
      simpa only [c, zero_mul] using hsub.mul hcore
    have htotal : Filter.Tendsto
        (fun n : Nat =>
          suzukiDifferential
                (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
              Complex.I * suzukiIntervalExponentialCore a m x.1)
        Filter.atTop (𝓝 0) := by
      have hbase : Filter.Tendsto
          (fun n : Nat => Complex.I * (d n + c n))
          Filter.atTop (𝓝 0) := by
        simpa using (hd.add hc).const_mul Complex.I
      apply hbase.congr'
      exact Filter.Eventually.of_forall fun n => by
        symm
        change
          suzukiDifferential
                (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
              Complex.I * suzukiIntervalExponentialCore a m x.1 =
            Complex.I * (d n + c n)
        rw [suzukiDifferential_quantitativeModePrimitiveSmoothCore_apply
          ha hm]
        dsimp only [d, c]
        ring
    simpa only [G, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)] using
      htotal.norm.pow 2
  have hDCT := tendsto_integral_of_dominated_convergence
    bound hGMeasurable hBoundIntegrable hBound hLimit
  simpa only [G, integral_zero] using hDCT

/-- A canonical smooth real bump with support exactly `(-a,a)`. -/
def suzukiIntervalBump (a : Real) : Real → Real :=
  Classical.choose
    (isOpen_Ioo.exists_contDiff_support_eq
      (n := (⊤ : ℕ∞)) (s := Ioo (-a) a))

theorem support_suzukiIntervalBump (a : Real) :
    Function.support (suzukiIntervalBump a) = Ioo (-a) a :=
  (Classical.choose_spec
    (isOpen_Ioo.exists_contDiff_support_eq
      (n := (⊤ : ℕ∞)) (s := Ioo (-a) a))).1

theorem contDiff_suzukiIntervalBump (a : Real) :
    ContDiff Real (⊤ : ℕ∞) (suzukiIntervalBump a) :=
  (Classical.choose_spec
    (isOpen_Ioo.exists_contDiff_support_eq
      (n := (⊤ : ℕ∞)) (s := Ioo (-a) a))).2.1

theorem range_suzukiIntervalBump_subset (a : Real) :
    Set.range (suzukiIntervalBump a) ⊆ Icc 0 1 :=
  (Classical.choose_spec
    (isOpen_Ioo.exists_contDiff_support_eq
      (n := (⊤ : ℕ∞)) (s := Ioo (-a) a))).2.2

theorem suzukiIntervalBump_nonneg (a x : Real) :
    0 ≤ suzukiIntervalBump a x :=
  (range_suzukiIntervalBump_subset a (Set.mem_range_self x)).1

theorem suzukiIntervalBump_le_one (a x : Real) :
    suzukiIntervalBump a x ≤ 1 :=
  (range_suzukiIntervalBump_subset a (Set.mem_range_self x)).2

theorem suzukiIntervalBump_ne_zero_iff (a x : Real) :
    suzukiIntervalBump a x ≠ 0 ↔ x ∈ Ioo (-a) a := by
  exact Set.ext_iff.mp (support_suzukiIntervalBump a) x

theorem suzukiIntervalBump_pos_of_mem
    {a x : Real} (hx : x ∈ Ioo (-a) a) :
    0 < suzukiIntervalBump a x :=
  lt_of_le_of_ne (suzukiIntervalBump_nonneg a x)
    (Ne.symm ((suzukiIntervalBump_ne_zero_iff a x).2 hx))

theorem hasCompactSupport_suzukiIntervalBump
    {a : Real} (ha : 0 < a) :
    HasCompactSupport (suzukiIntervalBump a) := by
  unfold HasCompactSupport
  rw [tsupport, support_suzukiIntervalBump,
    closure_Ioo (by linarith : -a ≠ a)]
  exact isCompact_Icc

/-- The scalar interval bump, regarded as a complex-valued Schwartz map. -/
def suzukiIntervalBumpSchwartz {a : Real} (ha : 0 < a) :
    SchwartzLineTestFunction :=
  let f : Real → Complex := fun x ↦ (suzukiIntervalBump a x : Complex)
  have hfCompact : HasCompactSupport f := by
    unfold HasCompactSupport
    have hsupport : Function.support f = Ioo (-a) a := by
      ext x
      simp only [f, Function.mem_support, ne_eq, Complex.ofReal_eq_zero,
        suzukiIntervalBump_ne_zero_iff]
    rw [tsupport, hsupport, closure_Ioo (by linarith : -a ≠ a)]
    exact isCompact_Icc
  hfCompact.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_suzukiIntervalBump a))

@[simp]
theorem suzukiIntervalBumpSchwartz_apply
    {a : Real} (ha : 0 < a) (x : Real) :
    suzukiIntervalBumpSchwartz ha x =
      (suzukiIntervalBump a x : Complex) := by
  rfl

theorem support_suzukiIntervalBumpSchwartz
    {a : Real} (ha : 0 < a) :
    Function.support (suzukiIntervalBumpSchwartz ha) = Ioo (-a) a := by
  ext x
  rw [Function.mem_support, suzukiIntervalBumpSchwartz_apply,
    Complex.ofReal_ne_zero, suzukiIntervalBump_ne_zero_iff]

/-- The canonical bump as an element of the exact DF6F smooth source core. -/
def suzukiIntervalBumpSmoothCore {a : Real} (ha : 0 < a) :
    SuzukiSmoothCore a :=
  ⟨suzukiIntervalBumpSchwartz ha, by
    rw [support_suzukiIntervalBumpSchwartz ha]⟩

/-- Smooth cutoffs approaching one in the open interval while retaining
literal support in that interval. -/
def suzukiIntervalCutoff (a : Real) (n : Nat) (x : Real) : Real :=
  1 - Real.exp (-(((n + 1 : Nat) : Real) * suzukiIntervalBump a x))

theorem contDiff_suzukiIntervalCutoff (a : Real) (n : Nat) :
    ContDiff Real (⊤ : ℕ∞) (suzukiIntervalCutoff a n) := by
  unfold suzukiIntervalCutoff
  exact contDiff_const.sub
    ((contDiff_const.mul (contDiff_suzukiIntervalBump a)).neg.exp)

theorem support_suzukiIntervalCutoff
    (a : Real) (n : Nat) :
    Function.support (suzukiIntervalCutoff a n) = Ioo (-a) a := by
  ext x
  rw [Function.mem_support]
  constructor
  · intro hx
    by_contra hxInterval
    have hbump : suzukiIntervalBump a x = 0 := by
      apply not_ne_iff.mp
      intro hbumpNe
      exact hxInterval ((suzukiIntervalBump_ne_zero_iff a x).1 hbumpNe)
    simp [suzukiIntervalCutoff, hbump] at hx
  · intro hxInterval
    have hbump : 0 < suzukiIntervalBump a x :=
      suzukiIntervalBump_pos_of_mem hxInterval
    have hcoefficient : (0 : Real) < ((n + 1 : Nat) : Real) := by
      positivity
    have hexp :
        Real.exp (-(((n + 1 : Nat) : Real) * suzukiIntervalBump a x)) < 1 := by
      rw [Real.exp_lt_one_iff]
      exact neg_neg_of_pos (mul_pos hcoefficient hbump)
    exact sub_ne_zero.mpr (ne_of_gt hexp)

theorem hasCompactSupport_suzukiIntervalCutoff
    {a : Real} (ha : 0 < a) (n : Nat) :
    HasCompactSupport (suzukiIntervalCutoff a n) := by
  unfold HasCompactSupport
  rw [tsupport, support_suzukiIntervalCutoff,
    closure_Ioo (by linarith : -a ≠ a)]
  exact isCompact_Icc

theorem suzukiIntervalCutoff_nonneg
    (a : Real) (n : Nat) (x : Real) :
    0 ≤ suzukiIntervalCutoff a n x := by
  unfold suzukiIntervalCutoff
  rw [sub_nonneg, Real.exp_le_one_iff]
  exact neg_nonpos.mpr
    (mul_nonneg (by positivity) (suzukiIntervalBump_nonneg a x))

theorem suzukiIntervalCutoff_le_one
    (a : Real) (n : Nat) (x : Real) :
    suzukiIntervalCutoff a n x ≤ 1 := by
  unfold suzukiIntervalCutoff
  linarith [Real.exp_pos
    (-(((n + 1 : Nat) : Real) * suzukiIntervalBump a x))]

/-- Every interior point eventually sees the cutoff tend to one. -/
theorem tendsto_suzukiIntervalCutoff_atTop
    {a x : Real} (hx : x ∈ Ioo (-a) a) :
    Filter.Tendsto (fun n : Nat => suzukiIntervalCutoff a n x)
      Filter.atTop (𝓝 1) := by
  have hbump : 0 < suzukiIntervalBump a x :=
    suzukiIntervalBump_pos_of_mem hx
  have hscale :
      Filter.Tendsto
        (fun n : Nat => (((n : Real) + 1) * suzukiIntervalBump a x))
        Filter.atTop Filter.atTop :=
    (Filter.tendsto_atTop_add_const_right Filter.atTop 1
      tendsto_natCast_atTop_atTop).atTop_mul_const hbump
  have hexp :
      Filter.Tendsto
        (fun n : Nat => Real.exp
          (-(((n : Real) + 1) * suzukiIntervalBump a x)))
        Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have hone :
      Filter.Tendsto (fun _ : Nat => (1 : Real))
        Filter.atTop (𝓝 1) := tendsto_const_nhds
  simpa only [suzukiIntervalCutoff, Nat.cast_add, Nat.cast_one,
    sub_zero] using hone.sub hexp

/-- Endpoint discrepancies are null, so the cutoff family tends to one
almost everywhere on the closed interval used by the source operators. -/
theorem ae_tendsto_suzukiIntervalCutoff_atTop
    (a : Real) :
    ∀ᵐ x ∂(volume : Measure Real).restrict (Icc (-a) a),
      Filter.Tendsto (fun n : Nat => suzukiIntervalCutoff a n x)
        Filter.atTop (𝓝 1) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun x hx ↦
    tendsto_suzukiIntervalCutoff_atTop hx

/-- Almost every point of the finite-interval subtype lies in the open
interval; only its two endpoints are omitted. -/
theorem ae_suzukiFiniteInterval_val_mem_Ioo
    {a : Real} (_ha : 0 < a) :
    ∀ᵐ x : SuzukiFiniteInterval a, x.1 ∈ Ioo (-a) a := by
  apply (ae_restrict_iff_subtype measurableSet_Icc).mp
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  rw [ae_restrict_iff' measurableSet_Ioo]
  exact Filter.Eventually.of_forall fun _ hx ↦ hx

/-- The cutoff error against an arbitrary finite-interval `L²` vector tends
to zero at the level of its norm-square integral. -/
theorem tendsto_integral_norm_sq_suzukiIntervalCutoff_error
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalL2 a) :
    Filter.Tendsto
      (fun n : Nat => ∫ x : SuzukiFiniteInterval a,
        ‖(((suzukiIntervalCutoff a n x.1 : Real) : Complex) - 1) * u x‖ ^ 2)
      Filter.atTop (𝓝 0) := by
  let F : Nat → SuzukiFiniteInterval a → Real := fun n x =>
    ‖(((suzukiIntervalCutoff a n x.1 : Real) : Complex) - 1) * u x‖ ^ 2
  let bound : SuzukiFiniteInterval a → Real := fun x => ‖u x‖ ^ 2
  have hFMeasurable : ∀ n, AEStronglyMeasurable (F n) volume := by
    intro n
    exact (((Complex.continuous_ofReal.comp
      ((contDiff_suzukiIntervalCutoff a n).continuous.comp
        continuous_subtype_val)).aestronglyMeasurable.sub
          aestronglyMeasurable_const).mul (Lp.memLp u).1).norm.pow 2
  have hBoundIntegrable : Integrable bound volume := by
    exact (Lp.memLp u).integrable_norm_pow (by norm_num)
  have hBound : ∀ n, ∀ᵐ x : SuzukiFiniteInterval a,
      ‖F n x‖ ≤ bound x := by
    intro n
    exact Filter.Eventually.of_forall fun x => by
      have hnonneg := suzukiIntervalCutoff_nonneg a n x.1
      have hle := suzukiIntervalCutoff_le_one a n x.1
      have habs : |suzukiIntervalCutoff a n x.1 - 1| ≤ 1 := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hnormCoefficient :
          ‖((suzukiIntervalCutoff a n x.1 : Real) : Complex) - 1‖ ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
        exact habs
      dsimp only [F, bound]
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul]
      have hproduct := mul_le_mul_of_nonneg_right hnormCoefficient
        (norm_nonneg (u x))
      have hproductNonneg : 0 ≤
          ‖((suzukiIntervalCutoff a n x.1 : Real) : Complex) - 1‖ *
            ‖u x‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      simpa only [pow_two, one_mul] using
        (mul_self_le_mul_self hproductNonneg hproduct)
  have hLimit : ∀ᵐ x : SuzukiFiniteInterval a,
      Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 0) := by
    filter_upwards [ae_suzukiFiniteInterval_val_mem_Ioo ha] with x hx
    have hcutoff := tendsto_suzukiIntervalCutoff_atTop hx
    have hcutoffComplex :
        Filter.Tendsto
          (fun n : Nat => ((suzukiIntervalCutoff a n x.1 : Real) : Complex))
          Filter.atTop (𝓝 (1 : Complex)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hcutoff
    have herror :=
      (((hcutoffComplex.sub_const 1).mul_const (u x)).norm.pow 2)
    simpa only [F, sub_self, zero_mul, norm_zero, pow_two] using herror
  have hDCT := tendsto_integral_of_dominated_convergence
    bound hFMeasurable hBoundIntegrable hBound hLimit
  simpa only [F, integral_zero] using hDCT

/-- Pointwise multiplication of an interval `L²` representative by the
canonical cutoff. -/
def suzukiIntervalCutoffMulFunction
    (a : Real) (n : Nat) (u : SuzukiFiniteIntervalL2 a)
    (x : SuzukiFiniteInterval a) : Complex :=
  (suzukiIntervalCutoff a n x.1 : Complex) * u x

theorem aestronglyMeasurable_suzukiIntervalCutoffMulFunction
    (a : Real) (n : Nat) (u : SuzukiFiniteIntervalL2 a) :
    AEStronglyMeasurable
      (suzukiIntervalCutoffMulFunction a n u) volume := by
  exact (Complex.continuous_ofReal.comp
    ((contDiff_suzukiIntervalCutoff a n).continuous.comp
      continuous_subtype_val)).aestronglyMeasurable.mul (Lp.memLp u).1

theorem memLp_suzukiIntervalCutoffMulFunction
    (a : Real) (n : Nat) (u : SuzukiFiniteIntervalL2 a) :
    MemLp (suzukiIntervalCutoffMulFunction a n u)
      (2 : ENNReal) volume := by
  refine (Lp.memLp u).of_le_mul (c := 1)
    (aestronglyMeasurable_suzukiIntervalCutoffMulFunction a n u) ?_
  exact Filter.Eventually.of_forall fun x => by
    unfold suzukiIntervalCutoffMulFunction
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (suzukiIntervalCutoff_nonneg a n x.1)]
    exact mul_le_mul_of_nonneg_right
      (suzukiIntervalCutoff_le_one a n x.1) (norm_nonneg (u x))

/-- The cutoff product as an element of the actual finite-interval `L²`
space. -/
def suzukiIntervalCutoffMulL2
    (a : Real) (n : Nat) (u : SuzukiFiniteIntervalL2 a) :
    SuzukiFiniteIntervalL2 a :=
  (memLp_suzukiIntervalCutoffMulFunction a n u).toLp
    (suzukiIntervalCutoffMulFunction a n u)

theorem suzukiIntervalCutoffMulL2_coeFn
    (a : Real) (n : Nat) (u : SuzukiFiniteIntervalL2 a) :
    (suzukiIntervalCutoffMulL2 a n u : SuzukiFiniteInterval a → Complex)
      =ᵐ[volume] suzukiIntervalCutoffMulFunction a n u :=
  (memLp_suzukiIntervalCutoffMulFunction a n u).coeFn_toLp

/-- Squared interval `L²` norm of a concrete representative. -/
theorem norm_sq_toLp_finiteInterval_eq_integral_norm_sq
    {a : Real} (f : SuzukiFiniteInterval a → Complex)
    (hf : MemLp f (2 : ENNReal) volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x : SuzukiFiniteInterval a, ‖f x‖ ^ 2 := by
  let F : SuzukiFiniteIntervalL2 a := hf.toLp f
  have hself : (inner Complex F F).re = ‖F‖ ^ 2 :=
    inner_self_eq_norm_sq (𝕜 := Complex) F
  have hintegrable :
      Integrable (fun x : SuzukiFiniteInterval a => inner Complex (F x) (F x)) :=
    L2.integrable_inner F F
  calc
    ‖hf.toLp f‖ ^ 2 = (inner Complex F F).re := hself.symm
    _ = (∫ x : SuzukiFiniteInterval a, inner Complex (F x) (F x)).re := by
      rw [L2.inner_def]
    _ = ∫ x : SuzukiFiniteInterval a, (inner Complex (F x) (F x)).re :=
      (integral_re hintegrable).symm
    _ = ∫ x : SuzukiFiniteInterval a, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]
      simpa using (inner_self_eq_norm_sq (𝕜 := Complex) (f x))

theorem norm_sq_suzukiIntervalCutoffMulL2_sub
    (a : Real) (n : Nat) (u : SuzukiFiniteIntervalL2 a) :
    ‖suzukiIntervalCutoffMulL2 a n u - u‖ ^ 2 =
      ∫ x : SuzukiFiniteInterval a,
        ‖(((suzukiIntervalCutoff a n x.1 : Real) : Complex) - 1) * u x‖ ^ 2 := by
  let W : SuzukiFiniteIntervalL2 a := suzukiIntervalCutoffMulL2 a n u - u
  have hnorm := norm_sq_toLp_finiteInterval_eq_integral_norm_sq
    (fun x : SuzukiFiniteInterval a => W x) (Lp.memLp W)
  rw [Lp.toLp_coeFn] at hnorm
  rw [hnorm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (suzukiIntervalCutoffMulL2 a n u) u,
    suzukiIntervalCutoffMulL2_coeFn a n u] with x hsub hcutoff
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hcutoff]
  unfold suzukiIntervalCutoffMulFunction
  congr 2
  ring

/-- Multiplication by the canonical support-safe cutoffs converges strongly
to the identity on the actual finite-interval `L²` space. -/
theorem tendsto_suzukiIntervalCutoffMulL2
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalL2 a) :
    Filter.Tendsto (fun n : Nat => suzukiIntervalCutoffMulL2 a n u)
      Filter.atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsq : Filter.Tendsto
      (fun n : Nat => ‖suzukiIntervalCutoffMulL2 a n u - u‖ ^ 2)
      Filter.atTop (𝓝 0) := by
    simpa only [norm_sq_suzukiIntervalCutoffMulL2_sub] using
      tendsto_integral_norm_sq_suzukiIntervalCutoff_error ha u
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- A cutoff from the canonical family, promoted to the exact smooth source
core. -/
def suzukiIntervalCutoffSmoothCore
    {a : Real} (ha : 0 < a) (n : Nat) : SuzukiSmoothCore a := by
  let f : Real → Complex := fun x ↦ (suzukiIntervalCutoff a n x : Complex)
  have hsupport : Function.support f = Ioo (-a) a := by
    ext x
    change (suzukiIntervalCutoff a n x : Complex) ≠ 0 ↔
      x ∈ Ioo (-a) a
    rw [Complex.ofReal_ne_zero]
    exact Set.ext_iff.mp (support_suzukiIntervalCutoff a n) x
  have hfCompact : HasCompactSupport f := by
    unfold HasCompactSupport
    rw [tsupport, hsupport, closure_Ioo (by linarith : -a ≠ a)]
    exact isCompact_Icc
  refine ⟨hfCompact.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp
        (contDiff_suzukiIntervalCutoff a n)), ?_⟩
  change Function.support f ⊆ Ioo (-a) a
  rw [hsupport]

/-- The limiting differential mode, bundled as a continuous function on the
finite interval. -/
def suzukiIntervalDifferentialModeContinuous
    (a : Real) (m : Int) : C(SuzukiFiniteInterval a, Complex) :=
  ⟨fun x => Complex.I * suzukiIntervalExponentialCore a m x.1,
    continuous_const.mul
      ((contDiff_suzukiIntervalExponentialCore a m).continuous.comp
        continuous_subtype_val)⟩

@[simp]
theorem suzukiIntervalDifferentialModeContinuous_apply
    (a : Real) (m : Int) (x : SuzukiFiniteInterval a) :
    suzukiIntervalDifferentialModeContinuous a m x =
      Complex.I * suzukiIntervalExponentialCore a m x.1 := by
  rfl

/-- The normalized interval exponential before multiplication by Suzuki's
factor `i`. -/
def suzukiIntervalExponentialContinuous
    (a : Real) (m : Int) : C(SuzukiFiniteInterval a, Complex) :=
  ⟨fun x => suzukiIntervalExponentialCore a m x.1,
    (contDiff_suzukiIntervalExponentialCore a m).continuous.comp
      continuous_subtype_val⟩

/-- The normalized interval exponential in finite-interval `L²`. -/
def suzukiIntervalExponentialL2
    (a : Real) (m : Int) : SuzukiFiniteIntervalL2 a :=
  suzukiFiniteIntervalContinuousToL2 a
    (suzukiIntervalExponentialContinuous a m)

@[simp]
theorem suzukiIntervalExponentialContinuous_apply
    (a : Real) (m : Int) (x : SuzukiFiniteInterval a) :
    suzukiIntervalExponentialContinuous a m x =
      suzukiIntervalExponentialCore a m x.1 := by
  rfl

/-- Extend an interval `L²` representative by zero outside the interval. -/
def suzukiFiniteIntervalL2ZeroExtensionFunction
    (a : Real) (u : SuzukiFiniteIntervalL2 a) : Real → Complex :=
  Function.extend ((↑) : SuzukiFiniteInterval a → Real)
    (fun x => u x) 0

theorem suzukiFiniteIntervalL2ZeroExtensionFunction_apply
    (a : Real) (u : SuzukiFiniteIntervalL2 a)
    (x : SuzukiFiniteInterval a) :
    suzukiFiniteIntervalL2ZeroExtensionFunction a u x.1 = u x := by
  exact Subtype.coe_injective.extend_apply (fun x => u x) 0 x

theorem stronglyMeasurable_suzukiFiniteIntervalL2ZeroExtensionFunction
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    StronglyMeasurable (suzukiFiniteIntervalL2ZeroExtensionFunction a u) := by
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).stronglyMeasurable_extend
    (Lp.stronglyMeasurable u) stronglyMeasurable_const

theorem memLp_suzukiFiniteIntervalL2ZeroExtensionFunction
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    MemLp (suzukiFiniteIntervalL2ZeroExtensionFunction a u)
      (2 : ENNReal) (volume : Measure Real) := by
  let F : Real → Complex := suzukiFiniteIntervalL2ZeroExtensionFunction a u
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hrestricted : MemLp F (2 : ENNReal)
      ((volume : Measure Real).restrict (Icc (-a) a)) := by
    rw [← hmap, he.memLp_map_measure_iff]
    have hcomp : F ∘ e = fun x : SuzukiFiniteInterval a => u x := by
      funext x
      exact suzukiFiniteIntervalL2ZeroExtensionFunction_apply a u x
    rw [hcomp]
    exact Lp.memLp u
  have hindicator : (Icc (-a) a).indicator F = F := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · simp [hx]
    · simp only [Set.indicator, hx, ↓reduceIte]
      unfold F suzukiFiniteIntervalL2ZeroExtensionFunction
      rw [Function.extend_apply']
      simp only [Pi.zero_apply]
      rintro ⟨y, hy⟩
      exact hx (hy ▸ y.2)
  change MemLp F (2 : ENNReal) (volume : Measure Real)
  rw [← hindicator, memLp_indicator_iff_restrict measurableSet_Icc]
  exact hrestricted

/-- The literal zero extension of finite-interval `L²` into the global real
line model. -/
def suzukiFiniteIntervalL2ZeroExtension
    (a : Real) (u : SuzukiFiniteIntervalL2 a) : SuzukiL2 :=
  (memLp_suzukiFiniteIntervalL2ZeroExtensionFunction a u).toLp
    (suzukiFiniteIntervalL2ZeroExtensionFunction a u)

theorem suzukiFiniteIntervalL2ZeroExtension_coeFn
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    (suzukiFiniteIntervalL2ZeroExtension a u : Real → Complex) =ᵐ[volume]
      suzukiFiniteIntervalL2ZeroExtensionFunction a u :=
  (memLp_suzukiFiniteIntervalL2ZeroExtensionFunction a u).coeFn_toLp

theorem suzukiIntervalExponentialL2_coeFn
    (a : Real) (m : Int) :
    (suzukiIntervalExponentialL2 a m : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      fun x => suzukiIntervalExponentialCore a m x.1 := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  exact ContinuousMap.coeFn_toLp
    (𝕜 := Complex) (p := (2 : ENNReal))
    (volume : Measure (SuzukiFiniteInterval a))
    (suzukiIntervalExponentialContinuous a m)

/-- The literal interval zero extension is supported in its defining closed
interval. -/
theorem suzukiFiniteIntervalL2ZeroExtension_supportedAt
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    suzukiL2SupportedAt a (suzukiFiniteIntervalL2ZeroExtension a u) := by
  apply suzukiL2SupportedAt_toLp_of_functionSupport
    (memLp_suzukiFiniteIntervalL2ZeroExtensionFunction a u)
  intro x hx
  by_contra hxout
  apply hx
  unfold suzukiFiniteIntervalL2ZeroExtensionFunction
  rw [Function.extend_apply']
  simp only [Pi.zero_apply]
  rintro ⟨y, hy⟩
  exact hxout (hy ▸ y.2)

/-- Global truncated Fourier pairings agree with the corresponding
finite-interval pairings after literal zero extension. -/
theorem inner_suzukiYoshidaExponentialL2_zeroExtension_eq_interval
    {a : Real} (ha : 0 < a) (m : Int)
    (u : SuzukiFiniteIntervalL2 a) :
    inner Complex (suzukiYoshidaExponentialL2 a ha m)
        (suzukiFiniteIntervalL2ZeroExtension a u) =
      inner Complex (suzukiIntervalExponentialL2 a m) u := by
  let F : Real → Complex := suzukiFiniteIntervalL2ZeroExtensionFunction a u
  have hleft :
      inner Complex (suzukiYoshidaExponentialL2 a ha m)
          (suzukiFiniteIntervalL2ZeroExtension a u) =
        ∫ x : SuzukiFiniteInterval a,
          inner Complex (suzukiIntervalExponentialCore a m x.1) (u x) := by
    rw [MeasureTheory.L2.inner_def]
    have hmode := suzukiYoshidaExponentialL2_coeFn ha m
    have hzero := suzukiFiniteIntervalL2ZeroExtension_coeFn a u
    have hintegrand :
        (fun x : Real =>
          inner Complex
            ((suzukiYoshidaExponentialL2 a ha m : SuzukiL2) x)
            ((suzukiFiniteIntervalL2ZeroExtension a u : SuzukiL2) x)) =ᵐ[volume]
          fun x => inner Complex
            (suzukiYoshidaExponentialFunction a m x)
            (suzukiFiniteIntervalL2ZeroExtensionFunction a u x) := by
      filter_upwards [hmode, hzero] with x hxmode hxzero
      rw [hxmode, hxzero]
    rw [integral_congr_ae hintegrand]
    change (∫ x : Real,
        inner Complex (suzukiYoshidaExponentialFunction a m x) (F x)) = _
    have hpoint :
        (fun x : Real =>
          inner Complex (suzukiYoshidaExponentialFunction a m x) (F x)) =
        (Icc (-a) a).indicator
          (fun x => inner Complex (suzukiIntervalExponentialCore a m x) (F x)) := by
      funext x
      by_cases hx : x ∈ Icc (-a) a
      · simp [hx, suzukiYoshidaExponentialFunction,
          suzukiIntervalExponentialCore]
      · simp [hx, suzukiYoshidaExponentialFunction]
    rw [hpoint, MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← MeasureTheory.integral_subtype measurableSet_Icc
      (fun x : Real =>
        inner Complex (suzukiIntervalExponentialCore a m x) (F x))]
    apply integral_congr_ae
    filter_upwards with x
    rw [show F x.1 = u x by
      exact suzukiFiniteIntervalL2ZeroExtensionFunction_apply a u x]
  have hright :
      inner Complex (suzukiIntervalExponentialL2 a m) u =
        ∫ x : SuzukiFiniteInterval a,
          inner Complex (suzukiIntervalExponentialCore a m x.1) (u x) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [suzukiIntervalExponentialL2_coeFn a m] with x hx
    rw [hx]
  exact hleft.trans hright.symm

/-- Every nonzero limiting differential mode has zero interval mean. -/
theorem integral_suzukiIntervalDifferentialModeContinuous_eq_zero
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    (∫ x : SuzukiFiniteInterval a,
      suzukiIntervalDifferentialModeContinuous a m x ∂volume) = 0 := by
  have hfundamental :
      (∫ x in (-a)..a, suzukiIntervalExponentialCore a m x) =
        suzukiIntervalExponentialPrimitive a m a -
          suzukiIntervalExponentialPrimitive a m (-a) := by
    apply intervalIntegral.integral_deriv_eq_sub'
      (f := suzukiIntervalExponentialPrimitive a m)
    · funext x
      exact (hasDerivAt_suzukiIntervalExponentialPrimitive ha hm x).deriv
    · exact fun x _ =>
        (hasDerivAt_suzukiIntervalExponentialPrimitive ha hm x).differentiableAt
    · exact (contDiff_suzukiIntervalExponentialCore a m).continuous.continuousOn
  rw [show (∫ x : SuzukiFiniteInterval a,
      suzukiIntervalDifferentialModeContinuous a m x ∂volume) =
        ∫ x in Icc (-a) a,
          Complex.I * suzukiIntervalExponentialCore a m x by
    exact MeasureTheory.integral_subtype measurableSet_Icc
      (fun x : Real => Complex.I * suzukiIntervalExponentialCore a m x)]
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a), hfundamental]
  simp [suzukiIntervalExponentialPrimitive_right_endpoint ha m]

/-- The nonzero differential mode as an element of Suzuki's closed zero-mean
finite-interval source space. -/
def suzukiIntervalDifferentialModeZeroMeanL2
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalContinuousZeroMeanToL2 a
    (suzukiIntervalDifferentialModeContinuous a m)
    (integral_suzukiIntervalDifferentialModeContinuous_eq_zero ha hm)

@[simp]
theorem suzukiIntervalDifferentialModeZeroMeanL2_coe
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    (suzukiIntervalDifferentialModeZeroMeanL2 ha hm :
        SuzukiFiniteIntervalL2 a) =
      suzukiFiniteIntervalContinuousToL2 a
        (suzukiIntervalDifferentialModeContinuous a m) := by
  rfl

theorem suzukiIntervalDifferentialModeZeroMeanL2_coe_eq_smul_exponential
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    (suzukiIntervalDifferentialModeZeroMeanL2 ha hm :
        SuzukiFiniteIntervalL2 a) =
      Complex.I • suzukiIntervalExponentialL2 a m := by
  change suzukiFiniteIntervalContinuousToL2 a
      (suzukiIntervalDifferentialModeContinuous a m) =
    Complex.I • suzukiFiniteIntervalContinuousToL2 a
      (suzukiIntervalExponentialContinuous a m)
  rw [← map_smul]
  congr 1

theorem suzukiIntervalExponentialL2_zero
    (a : Real) :
    suzukiIntervalExponentialL2 a 0 =
      (((Real.sqrt (2 * a))⁻¹ : Real) : Complex) •
        suzukiFiniteIntervalOneComplexL2 a := by
  unfold suzukiIntervalExponentialL2 suzukiFiniteIntervalOneComplexL2
  rw [← map_smul]
  congr 1
  ext x
  simp [suzukiIntervalExponentialContinuous,
    suzukiIntervalExponentialCore]

theorem norm_sq_suzukiQuantitativeModeDifferentialZeroMeanL2_sub
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) (n : Nat) :
    ‖suzukiSmoothCoreDifferentialZeroMeanL2 ha
          (suzukiQuantitativeModePrimitiveSmoothCore ha m n) -
        suzukiIntervalDifferentialModeZeroMeanL2 ha hm‖ ^ 2 =
      ∫ x : SuzukiFiniteInterval a,
        ‖suzukiDifferential
              (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 -
            Complex.I * suzukiIntervalExponentialCore a m x.1‖ ^ 2 := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  let U : SuzukiFiniteIntervalL2 a :=
    (suzukiSmoothCoreDifferentialZeroMeanL2 ha
      (suzukiQuantitativeModePrimitiveSmoothCore ha m n) :
        SuzukiFiniteIntervalL2 a)
  let V : SuzukiFiniteIntervalL2 a :=
    (suzukiIntervalDifferentialModeZeroMeanL2 ha hm :
      SuzukiFiniteIntervalL2 a)
  let W : SuzukiFiniteIntervalL2 a := U - V
  have hnorm := norm_sq_toLp_finiteInterval_eq_integral_norm_sq
    (fun x : SuzukiFiniteInterval a => W x) (Lp.memLp W)
  rw [Lp.toLp_coeFn] at hnorm
  change ‖W‖ ^ 2 = _
  rw [hnorm]
  apply integral_congr_ae
  have hU : (U : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      fun x => suzukiDifferential
        (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1 := by
    change
      ((suzukiFiniteIntervalContinuousToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
            (suzukiQuantitativeModePrimitiveSmoothCore ha m n)) :
          SuzukiFiniteIntervalL2 a) : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
        fun x => suzukiDifferential
          (suzukiQuantitativeModePrimitiveSmoothCore ha m n).1 x.1
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
        (suzukiQuantitativeModePrimitiveSmoothCore ha m n))
  have hV : (V : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
      fun x => Complex.I * suzukiIntervalExponentialCore a m x.1 := by
    change
      ((suzukiFiniteIntervalContinuousToL2 a
          (suzukiIntervalDifferentialModeContinuous a m) :
          SuzukiFiniteIntervalL2 a) : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
        fun x => Complex.I * suzukiIntervalExponentialCore a m x.1
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiIntervalDifferentialModeContinuous a m)
  filter_upwards [Lp.coeFn_sub U V, hU, hV] with x hsub hUx hVx
  dsimp only [W]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hUx, hVx]

/-- The explicit localized primitives converge through the exact receiving
map to every nonzero Fourier mode in the closed zero-mean source space. -/
theorem tendsto_suzukiQuantitativeModeDifferentialZeroMeanL2
    {a : Real} (ha : 0 < a) {m : Int} (hm : m ≠ 0) :
    Filter.Tendsto
      (fun n : Nat => suzukiSmoothCoreDifferentialZeroMeanL2 ha
        (suzukiQuantitativeModePrimitiveSmoothCore ha m n))
      Filter.atTop (𝓝 (suzukiIntervalDifferentialModeZeroMeanL2 ha hm)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsq : Filter.Tendsto
      (fun n : Nat =>
        ‖suzukiSmoothCoreDifferentialZeroMeanL2 ha
              (suzukiQuantitativeModePrimitiveSmoothCore ha m n) -
            suzukiIntervalDifferentialModeZeroMeanL2 ha hm‖ ^ 2)
      Filter.atTop (𝓝 0) := by
    simpa only [norm_sq_suzukiQuantitativeModeDifferentialZeroMeanL2_sub]
      using
        tendsto_integral_norm_sq_suzukiDifferential_quantitativeModePrimitive_error
          ha hm
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Fourier uniqueness on the zero-mean interval source space: the nonzero
differential modes are total. -/
theorem eq_zero_of_forall_inner_suzukiIntervalDifferentialMode_eq_zero
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalZeroMeanL2 a)
    (horth : ∀ (m : Int) (hm : m ≠ 0),
      inner Complex (suzukiIntervalDifferentialModeZeroMeanL2 ha hm) u = 0) :
    u = 0 := by
  let U : SuzukiFiniteIntervalL2 a :=
    (u : SuzukiFiniteIntervalL2 a)
  let V : SuzukiL2 := suzukiFiniteIntervalL2ZeroExtension a U
  have hglobal : ∀ m : Int,
      inner Complex (suzukiYoshidaExponentialL2 a ha m) V = 0 := by
    intro m
    rw [show inner Complex (suzukiYoshidaExponentialL2 a ha m) V =
        inner Complex (suzukiIntervalExponentialL2 a m) U by
      exact inner_suzukiYoshidaExponentialL2_zeroExtension_eq_interval
        ha m U]
    by_cases hm : m = 0
    · subst m
      rw [suzukiIntervalExponentialL2_zero a, inner_smul_left]
      have hmean :
          inner Complex (suzukiFiniteIntervalOneComplexL2 a) U = 0 := by
        exact u.2
      rw [hmean, mul_zero]
    · have hd := horth m hm
      change inner Complex
          (suzukiIntervalDifferentialModeZeroMeanL2 ha hm :
            SuzukiFiniteIntervalL2 a) U = 0 at hd
      rw [show (suzukiIntervalDifferentialModeZeroMeanL2 ha hm :
          SuzukiFiniteIntervalL2 a) =
          Complex.I • suzukiIntervalExponentialL2 a m by
        exact
          suzukiIntervalDifferentialModeZeroMeanL2_coe_eq_smul_exponential
            ha hm] at hd
      simp only [inner_smul_left] at hd
      exact (mul_eq_zero.mp hd).resolve_left
        (star_ne_zero.mpr Complex.I_ne_zero)
  have hVzero : V = 0 :=
    eq_zero_of_supportedAt_of_forall_inner_exponential_eq_zero
      ha V (suzukiFiniteIntervalL2ZeroExtension_supportedAt a U) hglobal
  change suzukiFiniteIntervalL2ZeroExtension a U = 0 at hVzero
  have hFzero :
      suzukiFiniteIntervalL2ZeroExtensionFunction a U =ᵐ[volume]
        (0 : Real → Complex) := by
    filter_upwards [suzukiFiniteIntervalL2ZeroExtension_coeFn a U,
      Lp.coeFn_zero Complex (2 : ENNReal) (volume : Measure Real)] with x hx hz
    rw [hVzero] at hx
    exact hx.symm.trans hz
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hFrestrict : ∀ᵐ x ∂(volume : Measure Real).restrict (Icc (-a) a),
      suzukiFiniteIntervalL2ZeroExtensionFunction a U x = 0 :=
    ae_mono Measure.restrict_le_self hFzero
  rw [← hmap, he.ae_map_iff] at hFrestrict
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hFrestrict,
    Lp.coeFn_zero Complex (2 : ENNReal)
      (volume : Measure (SuzukiFiniteInterval a))] with x hx hz
  rw [show U x = suzukiFiniteIntervalL2ZeroExtensionFunction a U x.1 by
    exact (suzukiFiniteIntervalL2ZeroExtensionFunction_apply a U x).symm]
  exact hx.trans hz.symm

/-- The smooth-core differential receiving map with its linear source
structure exposed. -/
def suzukiSmoothCoreDifferentialZeroMeanLinearMap
    {a : Real} (ha : 0 < a) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiFiniteIntervalZeroMeanL2 a where
  toFun v := suzukiSmoothCoreDifferentialZeroMeanL2 ha
    (suzukiSmoothCoreLinearSubmoduleAsCore v)
  map_add' u v := by
    apply Subtype.ext
    change suzukiFiniteIntervalContinuousToL2 a
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
          (suzukiSmoothCoreLinearSubmoduleAsCore (u + v))) =
      suzukiFiniteIntervalContinuousToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
            (suzukiSmoothCoreLinearSubmoduleAsCore u)) +
        suzukiFiniteIntervalContinuousToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
            (suzukiSmoothCoreLinearSubmoduleAsCore v))
    rw [← map_add]
    congr 1
    ext x
    change Complex.I *
        SchwartzMap.derivCLM Complex Complex (u.1 + v.1) x.1 =
      Complex.I * SchwartzMap.derivCLM Complex Complex u.1 x.1 +
        Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x.1
    rw [map_add]
    change Complex.I *
        (SchwartzMap.derivCLM Complex Complex u.1 x.1 +
          SchwartzMap.derivCLM Complex Complex v.1 x.1) = _
    ring
  map_smul' c v := by
    apply Subtype.ext
    change suzukiFiniteIntervalContinuousToL2 a
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
          (suzukiSmoothCoreLinearSubmoduleAsCore (c • v))) =
      c • suzukiFiniteIntervalContinuousToL2 a
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
          (suzukiSmoothCoreLinearSubmoduleAsCore v))
    rw [← map_smul]
    congr 1
    ext x
    change Complex.I *
        SchwartzMap.derivCLM Complex Complex (c • v.1) x.1 =
      c * (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x.1)
    rw [map_smul]
    change Complex.I *
        (c * SchwartzMap.derivCLM Complex Complex v.1 x.1) = _
    ring

/-- The nonzero differential modes have dense complex span in the zero-mean
interval source space. -/
theorem topologicalClosure_span_suzukiIntervalDifferentialMode_eq_top
    {a : Real} (ha : 0 < a) :
    (Submodule.span Complex
      (Set.range fun m : {m : Int // m ≠ 0} =>
        suzukiIntervalDifferentialModeZeroMeanL2 ha m.2)).topologicalClosure =
      ⊤ := by
  letI : CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
    change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
    infer_instance
  let S : Submodule Complex (SuzukiFiniteIntervalZeroMeanL2 a) :=
    Submodule.span Complex
      (Set.range fun m : {m : Int // m ≠ 0} =>
        suzukiIntervalDifferentialModeZeroMeanL2 ha m.2)
  apply le_antisymm le_top
  intro u _hu
  let w : SuzukiFiniteIntervalZeroMeanL2 a :=
    u - S.topologicalClosure.starProjection u
  have hwOrth : w ∈ S.topologicalClosureᗮ :=
    S.topologicalClosure.sub_starProjection_mem_orthogonal u
  have hwInner : ∀ (m : Int) (hm : m ≠ 0),
      inner Complex (suzukiIntervalDifferentialModeZeroMeanL2 ha hm) w = 0 := by
    intro m hm
    let j : {m : Int // m ≠ 0} := ⟨m, hm⟩
    exact Submodule.inner_right_of_mem_orthogonal
      (S.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self j))) hwOrth
  have hwZero : w = 0 :=
    eq_zero_of_forall_inner_suzukiIntervalDifferentialMode_eq_zero
      ha w hwInner
  have huProjection : u = S.topologicalClosure.starProjection u := by
    exact sub_eq_zero.mp hwZero
  rw [huProjection]
  exact S.topologicalClosure.starProjection_apply_mem u

/-- The linear smooth-differential range is dense because its closure
contains every nonzero differential mode. -/
theorem topologicalClosure_range_suzukiSmoothCoreDifferential_eq_top
    {a : Real} (ha : 0 < a) :
    (LinearMap.range
      (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha)).topologicalClosure =
      ⊤ := by
  let R : Submodule Complex (SuzukiFiniteIntervalZeroMeanL2 a) :=
    LinearMap.range (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha)
  let S : Submodule Complex (SuzukiFiniteIntervalZeroMeanL2 a) :=
    Submodule.span Complex
      (Set.range fun m : {m : Int // m ≠ 0} =>
        suzukiIntervalDifferentialModeZeroMeanL2 ha m.2)
  have hmode : ∀ m : {m : Int // m ≠ 0},
      suzukiIntervalDifferentialModeZeroMeanL2 ha m.2 ∈
        R.topologicalClosure := by
    intro m
    apply mem_closure_of_tendsto
      (tendsto_suzukiQuantitativeModeDifferentialZeroMeanL2 ha m.2)
    filter_upwards with n
    let v : SuzukiSmoothCoreLinearSubmodule a :=
      ⟨(suzukiQuantitativeModePrimitiveSmoothCore ha m.1 n).1,
        (suzukiQuantitativeModePrimitiveSmoothCore ha m.1 n).2⟩
    exact ⟨v, rfl⟩
  have hspan : S ≤ R.topologicalClosure := by
    dsimp only [S]
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hmode m
  have hspanClosure : S.topologicalClosure ≤ R.topologicalClosure :=
    S.topologicalClosure_minimal hspan R.isClosed_topologicalClosure
  have htotal : S.topologicalClosure = ⊤ := by
    exact topologicalClosure_span_suzukiIntervalDifferentialMode_eq_top ha
  apply top_unique
  rw [← htotal]
  exact hspanClosure

/-- The constructive DF6F density gate: compactly supported smooth
primitives have dense differential image in the closed zero-mean interval
source space. -/
theorem suzukiSmoothDifferentialCoreDenseAt
    (a : Real) (ha : 0 < a) :
    SuzukiSmoothDifferentialCoreDenseAt a ha := by
  have hlinear : DenseRange
      (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha) := by
    rw [DenseRange, dense_iff_closure_eq]
    change closure
        ((LinearMap.range
          (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha) :
            Submodule Complex (SuzukiFiniteIntervalZeroMeanL2 a)) :
          Set (SuzukiFiniteIntervalZeroMeanL2 a)) = Set.univ
    rw [← Submodule.topologicalClosure_coe,
      topologicalClosure_range_suzukiSmoothCoreDifferential_eq_top ha]
    rfl
  unfold SuzukiSmoothDifferentialCoreDenseAt
  rw [DenseRange]
  have hrange :
      Set.range (fun v : SuzukiSmoothCore a =>
        suzukiSmoothCoreDifferentialZeroMeanL2 ha v) =
      Set.range (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha) := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v.1, v.2⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨suzukiSmoothCoreLinearSubmoduleAsCore v, rfl⟩
  rw [hrange]
  exact hlinear

/-- The full zero-mean source coercivity theorem with the density premise
discharged constructively.  The two independent endpoint source premises
remain explicit. -/
theorem suzukiDF6F_interval_source_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    (1 / 400000 : Real) *
        (inner Complex (suzukiSourceKOperator a u) u).re ≤
      (inner Complex (suzukiSourceGOperator a u) u).re := by
  exact suzukiDF6F_interval_source_coercive_of_dense
    hsource hequation25 ha
      (suzukiSmoothDifferentialCoreDenseAt a
        (suzukiDF6E_radius_pos ha)) u

/-- The shifted full-space source estimate with the constructive density
premise discharged. -/
theorem suzukiDF6F_interval_shifted_source_coercive
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    ((1 / 400000 : Real) - lambda) *
        (inner Complex (suzukiSourceKOperator a u) u).re ≤
      (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re := by
  exact suzukiDF6F_interval_shifted_source_coercive_of_dense
    hsource hequation25 ha
      (suzukiSmoothDifferentialCoreDenseAt a
        (suzukiDF6E_radius_pos ha)) lambda u

end

end RiemannHypothesisProject.Experiments.M100
