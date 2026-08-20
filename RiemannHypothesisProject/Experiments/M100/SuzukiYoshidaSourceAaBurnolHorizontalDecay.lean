import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaBurnolFiniteContour
import RiemannHypothesisProject.GuinandWeilConcrete.XiHorizontalDecay

/-!
# M100-DF6F horizontal decay for the Burnol xi contour

This module proves rapid horizontal decay of the actual compact-support Burnol
weight. Repeated integration by parts gives five inverse powers of the real
spectral coordinate, which dominates the fourth-degree good-height envelope
for the logarithmic derivative of xi.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory Filter Topology
open SchwartzLineTestFunction
open ComplexCompactExhaustion

/-- Iterated Schwartz differentiation used in the compact-support decay
estimate. -/
def suzukiSchwartzIteratedDeriv : Nat →
    SchwartzLineTestFunction → SchwartzLineTestFunction
  | 0, w => w
  | n + 1, w =>
      SchwartzMap.derivCLM Complex Complex (suzukiSchwartzIteratedDeriv n w)

/-- Differentiation does not enlarge a closed support interval. -/
private theorem support_derivCLM_subset_Icc
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a) :
    Function.support
        ((SchwartzMap.derivCLM Complex Complex w :
          SchwartzLineTestFunction) : Real → Complex) ⊆
      Icc (-a) a := by
  intro x hx
  have hderiv :
      deriv (w : Real → Complex) =
        ((SchwartzMap.derivCLM Complex Complex w :
          SchwartzLineTestFunction) : Real → Complex) := by
    funext y
    exact (SchwartzMap.derivCLM_apply Complex w y).symm
  have hxderiv : x ∈ Function.support (deriv (w : Real → Complex)) := by
    rw [hderiv]
    exact hx
  have hxtsupport : x ∈ tsupport (w : Real → Complex) :=
    support_deriv_subset hxderiv
  exact (closure_minimal hsupport isClosed_Icc) hxtsupport

/-- Every iterated derivative stays in the same closed support interval. -/
theorem support_suzukiSchwartzIteratedDeriv_subset_Icc
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a) (n : Nat) :
    Function.support (suzukiSchwartzIteratedDeriv n w) ⊆ Icc (-a) a := by
  induction n with
  | zero => simpa [suzukiSchwartzIteratedDeriv] using hsupport
  | succ n ih =>
      simpa [suzukiSchwartzIteratedDeriv] using
        (support_derivCLM_subset_Icc ih)

private theorem integrable_suzukiFourierIntegrand_of_support_subset_Icc''
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a) (z : Complex) :
    Integrable (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * w x) := by
  have hsub : Function.support
      (fun x : Real =>
        Complex.exp ((x : Complex) * Complex.I * z) * w x) ⊆
        Icc (-a) a := by
    intro x hx
    exact hsupport (fun hw => hx (by simp [hw]))
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * w x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

private theorem norm_suzukiFourierIntegrand_le_exp_radius_mul'
    {a : Real} (ha : 0 ≤ a) {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a)
    {z : Complex} (hz : |z.im| ≤ 1) (x : Real) :
    ‖Complex.exp ((x : Complex) * Complex.I * z) * w x‖ ≤
      Real.exp a * ‖w x‖ := by
  by_cases hw : w x = 0
  · simp [hw]
  have hx := hsupport hw
  have hxabs : |x| ≤ a := (abs_le).2 hx
  have hprod : |x * z.im| ≤ a := by
    rw [abs_mul]
    calc
      |x| * |z.im| ≤ a * 1 :=
        mul_le_mul hxabs hz (abs_nonneg _) ha
      _ = a := mul_one a
  have hre : (((x : Complex) * Complex.I * z).re) = -x * z.im := by
    simp
  rw [norm_mul, Complex.norm_exp, hre]
  gcongr
  simpa only [neg_mul] using (neg_le_abs (x * z.im)).trans hprod

/-- Direct compact-support transform bound for an arbitrary Schwartz test. -/
theorem norm_suzukiFourierSource_le_of_support_subset_Icc
    {a : Real} (ha : 0 ≤ a) {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a)
    {z : Complex} (hz : |z.im| ≤ 1) :
    ‖suzukiFourierSource w z‖ ≤
      Real.exp a * ∫ x : Real, ‖w x‖ := by
  have hintegrable :=
    integrable_suzukiFourierIntegrand_of_support_subset_Icc'' hsupport z
  rw [suzukiFourierSource]
  calc
    ‖∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * z) * w x‖ ≤
        ∫ x : Real,
          ‖Complex.exp ((x : Complex) * Complex.I * z) * w x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Real, Real.exp a * ‖w x‖ := by
      apply integral_mono hintegrable.norm
        (w.integrable.norm.const_mul (Real.exp a))
      intro x
      exact norm_suzukiFourierIntegrand_le_exp_radius_mul'
        ha hsupport hz x
    _ = Real.exp a * ∫ x : Real, ‖w x‖ := by
      rw [integral_const_mul]

/-- One exact integration-by-parts step for an arbitrary compactly supported
Schwartz test. -/
theorem suzukiFourierSource_deriv_identity
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a) (z : Complex) :
    (Complex.I * z) * suzukiFourierSource w z =
      -suzukiFourierSource
        (SchwartzMap.derivCLM Complex Complex w) z := by
  let dw : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex w
  let u : Real → Complex := fun x =>
    Complex.exp ((x : Complex) * Complex.I * z)
  let u' : Real → Complex := fun x => u x * (Complex.I * z)
  have hdwSupport : Function.support dw ⊆ Icc (-a) a :=
    support_derivCLM_subset_Icc hsupport
  have huw : Integrable (fun x : Real => u x * w x) := by
    simpa only [u] using
      integrable_suzukiFourierIntegrand_of_support_subset_Icc'' hsupport z
  have hudw : Integrable (fun x : Real => u x * dw x) := by
    simpa only [u] using
      integrable_suzukiFourierIntegrand_of_support_subset_Icc'' hdwSupport z
  have hu'w : Integrable (fun x : Real => u' x * w x) := by
    have hscaled := huw.const_mul (Complex.I * z)
    exact hscaled.congr (ae_of_all _ fun x => by
      dsimp only [u']
      ring)
  have huDeriv (x : Real) : HasDerivAt u (u' x) x := by
    have hlinear : HasDerivAt
        (fun y : Real => (y : Complex) * Complex.I * z)
        (Complex.I * z) x := by
      have hbase : HasDerivAt
          (fun y : Real => (Complex.I * z) * (y : Complex))
          (Complex.I * z) x := by
        simpa using ((((hasDerivAt_id (x : Complex)).const_mul
          (Complex.I * z)).comp_ofReal))
      convert hbase using 1 <;> funext y <;> ring
    simpa only [u, u'] using hlinear.cexp
  have hwDeriv (x : Real) :
      HasDerivAt (fun y : Real => w y) (dw x) x := by
    simpa only [dw, SchwartzMap.derivCLM_apply] using w.hasDerivAt x
  have hudwPi : Integrable (u * fun x : Real => dw x) := by
    change Integrable (fun x : Real => u x * dw x)
    exact hudw
  have hu'wPi : Integrable (u' * fun x : Real => w x) := by
    change Integrable (fun x : Real => u' x * w x)
    exact hu'w
  have huwPi : Integrable (u * fun x : Real => w x) := by
    change Integrable (fun x : Real => u x * w x)
    exact huw
  have hparts :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := u) (v := fun x : Real => w x)
      (u' := u') (v' := fun x : Real => dw x)
      (fun x _ => huDeriv x) (fun x _ => hwDeriv x)
      hudwPi hu'wPi huwPi
  have hfactor :
      (∫ x : Real, u' x * w x) =
        (Complex.I * z) * suzukiFourierSource w z := by
    rw [suzukiFourierSource, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [u', u]
    ring
  have hidentity :
      suzukiFourierSource dw z =
        -((Complex.I * z) * suzukiFourierSource w z) := by
    simpa only [suzukiFourierSource, u, Pi.mul_apply, hfactor] using hparts
  rw [hidentity]
  ring

/-- Norm form of one exact integration-by-parts step. -/
theorem norm_mul_norm_suzukiFourierSource_eq_deriv
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a) (z : Complex) :
    ‖z‖ * ‖suzukiFourierSource w z‖ =
      ‖suzukiFourierSource
        (SchwartzMap.derivCLM Complex Complex w) z‖ := by
  have h := congrArg norm (suzukiFourierSource_deriv_identity hsupport z)
  simpa [norm_mul] using h

/-- Repeated integration by parts gives arbitrary integral powers of decay. -/
theorem norm_pow_mul_norm_suzukiFourierSource_eq_iteratedDeriv
    {a : Real} {w : SchwartzLineTestFunction}
    (hsupport : Function.support w ⊆ Icc (-a) a)
    (n : Nat) (z : Complex) :
    ‖z‖ ^ n * ‖suzukiFourierSource w z‖ =
      ‖suzukiFourierSource (suzukiSchwartzIteratedDeriv n w) z‖ := by
  induction n with
  | zero => simp [suzukiSchwartzIteratedDeriv]
  | succ n ih =>
      calc
        ‖z‖ ^ (n + 1) * ‖suzukiFourierSource w z‖ =
            ‖z‖ * (‖z‖ ^ n * ‖suzukiFourierSource w z‖) := by ring
        _ = ‖z‖ *
            ‖suzukiFourierSource (suzukiSchwartzIteratedDeriv n w) z‖ := by
          rw [ih]
        _ = ‖suzukiFourierSource
              (SchwartzMap.derivCLM Complex Complex
                (suzukiSchwartzIteratedDeriv n w)) z‖ :=
          norm_mul_norm_suzukiFourierSource_eq_deriv
            (support_suzukiSchwartzIteratedDeriv_subset_Icc hsupport n) z
        _ = ‖suzukiFourierSource
              (suzukiSchwartzIteratedDeriv (n + 1) w) z‖ := by
          rfl

/-- Five integrations by parts dominate the fourth-degree xi good-height
envelope uniformly across the fixed horizontal contour strip. -/
theorem exists_pos_const_abs_pow_five_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    ∃ C : Real, 0 < C ∧ ∀ sigma T : Real,
      guinandWeilXiContourLeft ≤ sigma →
      sigma ≤ guinandWeilXiContourRight →
      |T| ^ 5 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ C := by
  let w : SchwartzLineTestFunction := autocorrelation v.1
  let a : Real := 2 * suzukiProjectAStar
  let d5 : SchwartzLineTestFunction := suzukiSchwartzIteratedDeriv 5 w
  let C : Real := Real.exp a * (∫ x : Real, ‖d5 x‖) + 1
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by norm_num) suzukiProjectAStar_pos.le
  have hsupport : Function.support w ⊆ Icc (-a) a := by
    dsimp [w, a]
    exact support_autocorrelation_subset_Icc_two_mul
      suzukiProjectAStar_pos.le
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)
  have hC : 0 < C := by
    dsimp [C]
    have hint : 0 ≤ ∫ x : Real, ‖d5 x‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  refine ⟨C, hC, ?_⟩
  intro sigma T hsigmaLower hsigmaUpper
  let z : Complex :=
    ((((sigma : Complex) + (T : Complex) * Complex.I) -
      (1 / 2 : Complex)) / Complex.I)
  have hzIm : |z.im| ≤ 1 := by
    have hcoordinate := guinandWeilXiContourCoordinate_horizontal sigma T
    dsimp only [z]
    rw [hcoordinate]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      zero_add]
    rw [abs_le]
    constructor
    · norm_num [guinandWeilXiContourRight] at hsigmaUpper ⊢
      linarith
    · norm_num [guinandWeilXiContourLeft] at hsigmaLower ⊢
      linarith
  have hTnorm : |T| ≤ ‖z‖ := by
    have hcoordinate := guinandWeilXiContourCoordinate_horizontal sigma T
    calc
      |T| = |z.re| := by
        dsimp only [z]
        rw [hcoordinate]
        simp
      _ ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hdecay :=
    norm_pow_mul_norm_suzukiFourierSource_eq_iteratedDeriv hsupport 5 z
  have hd5Support :=
    support_suzukiSchwartzIteratedDeriv_subset_Icc hsupport 5
  have hd5Bound := norm_suzukiFourierSource_le_of_support_subset_Icc
    ha hd5Support hzIm
  rw [show suzukiSmoothCoreBurnolXiContourWeight v
      ((sigma : Complex) + (T : Complex) * Complex.I) =
        suzukiFourierSource w z by
    rw [suzukiSmoothCoreBurnolXiContourWeight]
    exact burnolFourierLaplaceSource_suzukiProjectBase v.1 _]
  calc
    |T| ^ 5 * ‖suzukiFourierSource w z‖ ≤
        ‖z‖ ^ 5 * ‖suzukiFourierSource w z‖ := by
      gcongr
    _ = ‖suzukiFourierSource d5 z‖ := by
      simpa only [d5] using hdecay
    _ ≤ Real.exp a * ∫ x : Real, ‖d5 x‖ := by
      simpa only [d5] using hd5Bound
    _ ≤ C := by
      dsimp only [C]
      linarith

/-- A fifth-order pointwise Burnol-weight bound and a uniform xi
logarithmic-derivative bound control the complete horizontal edge. -/
theorem norm_suzukiSmoothCoreBurnolXi_horizontalIntegral_le
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (T C E : Real) (hT : T ≠ 0) (hC : 0 ≤ C)
    (hweight : ∀ sigma : Real,
      guinandWeilXiContourLeft ≤ sigma →
      sigma ≤ guinandWeilXiContourRight →
      |T| ^ 5 *
          ‖suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤ C)
    (hlogDeriv : ∀ sigma,
      sigma ∈ Icc guinandWeilXiContourLeft guinandWeilXiContourRight →
      ‖logDeriv riemannXi
        ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
        E) :
    ‖guinandWeilHorizontalIntegral
        (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
          logDeriv riemannXi s)
        guinandWeilXiContourLeft guinandWeilXiContourRight T‖ ≤
      (C / |T| ^ 5) * E * (3 / 2 : Real) := by
  let W : Real := C / |T| ^ 5
  have hTabs : 0 < |T| := abs_pos.mpr hT
  have hden : 0 < |T| ^ 5 := pow_pos hTabs 5
  have hW : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hE : 0 ≤ E := by
    have hleft : guinandWeilXiContourLeft ∈
        Icc guinandWeilXiContourLeft guinandWeilXiContourRight := by
      constructor
      · exact le_rfl
      · norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]
    exact (norm_nonneg _).trans (hlogDeriv _ hleft)
  unfold guinandWeilHorizontalIntegral
  calc
    ‖∫ sigma in guinandWeilXiContourLeft..guinandWeilXiContourRight,
        suzukiSmoothCoreBurnolXiContourWeight v
            ((sigma : Complex) + (T : Complex) * Complex.I) *
          logDeriv riemannXi
            ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
        (W * E) *
          |guinandWeilXiContourRight - guinandWeilXiContourLeft| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
      intro sigma hsigma
      have hsigma' := uIoc_subset_uIcc hsigma
      rw [uIcc_of_le (by
        norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight])] at hsigma'
      rw [norm_mul]
      calc
        ‖suzukiSmoothCoreBurnolXiContourWeight v
              ((sigma : Complex) + (T : Complex) * Complex.I)‖ *
            ‖logDeriv riemannXi
              ((sigma : Complex) + (T : Complex) * Complex.I)‖ ≤
            W *
              ‖logDeriv riemannXi
                ((sigma : Complex) + (T : Complex) * Complex.I)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          dsimp only [W]
          exact (le_div_iff₀ hden).2 (by
            rw [mul_comm]
            exact hweight sigma hsigma'.1 hsigma'.2)
        _ ≤ W * E := mul_le_mul_of_nonneg_left
          (hlogDeriv sigma hsigma') hW
    _ = (C / |T| ^ 5) * E * (3 / 2 : Real) := by
      dsimp only [W]
      norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]

/-- In each sufficiently high unit interval, one canonical good height
controls both Burnol horizontal edges by the same inverse-fifth-power times
degree-four envelope. -/
theorem exists_fixed_canonicalXi_goodHeight_both_burnolHorizontalIntegral_bound
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    ∃ K k A C : Real,
      0 < K ∧ 0 < k ∧ 0 < A ∧ 0 < C ∧
      ∀ N : Nat, 5 ≤ N → ∃ T : Real,
        (N : Real) ≤ T ∧ T ≤ N + 1 ∧
        (∀ sigma,
          sigma ∈ Icc guinandWeilXiContourLeft guinandWeilXiContourRight →
          riemannXi
            ((sigma : Complex) + (T : Complex) * Complex.I) ≠ 0) ∧
        let bound := (C / |T| ^ 5) *
          xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real)
        ‖guinandWeilHorizontalIntegral
            (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
              logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight T‖ ≤ bound ∧
          ‖guinandWeilHorizontalIntegral
            (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
              logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (-T)‖ ≤
              (C / |T| ^ 5) *
                xiGoodHeightLogDerivEnvelope K k A N T * (3 / 2 : Real) := by
  obtain ⟨K, k, A, hK, hk, hA, hgood⟩ :=
    exists_fixed_canonicalXi_goodHeight_global_logDeriv_bound
  obtain ⟨C, hC, hweight⟩ :=
    exists_pos_const_abs_pow_five_mul_norm_suzukiSmoothCoreBurnolXiContourWeight_le v
  refine ⟨K, k, A, C, hK, hk, hA, hC, ?_⟩
  intro N hN
  obtain ⟨T, hTN, hTN1, hgoodT⟩ := hgood N hN
  have hTpos : 0 < T := by
    have : (0 : Real) < N := by exact_mod_cast (show 0 < N by omega)
    exact this.trans_le hTN
  have hupper := norm_suzukiSmoothCoreBurnolXi_horizontalIntegral_le
    v T C (xiGoodHeightLogDerivEnvelope K k A N T) hTpos.ne' hC.le
      (fun sigma hsigmaLower hsigmaUpper =>
        hweight sigma T hsigmaLower hsigmaUpper)
      (fun sigma hsigma => (hgoodT sigma hsigma).2)
  have hlowerLog : ∀ sigma,
      sigma ∈ Icc guinandWeilXiContourLeft guinandWeilXiContourRight →
      ‖logDeriv riemannXi
        ((sigma : Complex) + (-T : Complex) * Complex.I)‖ ≤
        xiGoodHeightLogDerivEnvelope K k A N T := by
    intro sigma hsigma
    have hreflectedSigma : 1 - sigma ∈
        Icc guinandWeilXiContourLeft guinandWeilXiContourRight := by
      constructor <;>
        norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight] at * <;>
        linarith
    let s : Complex :=
      (((1 - sigma : Real) : Complex) + (T : Complex) * Complex.I)
    have hreflection := congrArg norm (logDeriv_riemannXi_one_sub_all s)
    have honeSub : 1 - s =
        (sigma : Complex) + (-T : Complex) * Complex.I := by
      dsimp only [s]
      push_cast
      ring
    rw [honeSub, norm_neg] at hreflection
    rw [hreflection]
    exact (hgoodT (1 - sigma) hreflectedSigma).2
  have hlower := norm_suzukiSmoothCoreBurnolXi_horizontalIntegral_le
    v (-T) C (xiGoodHeightLogDerivEnvelope K k A N T)
      (neg_ne_zero.mpr hTpos.ne') hC.le
      (fun sigma hsigmaLower hsigmaUpper =>
        hweight sigma (-T) hsigmaLower hsigmaUpper)
      (by
        intro sigma hsigma
        simpa only [Complex.ofReal_neg] using hlowerLog sigma hsigma)
  refine ⟨T, hTN, hTN1,
    (fun sigma hsigma => (hgoodT sigma hsigma).1), hupper, ?_⟩
  simpa only [abs_neg] using hlower

/-- The canonical good heights make both actual Burnol horizontal contour
integrals tend to zero.  This closes the horizontal-edge component of the
Burnol finite-contour limit. -/
theorem exists_canonicalXi_goodHeight_both_burnolHorizontalIntegrals_tendsto_zero
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    ∃ height : Nat → Real,
      (∀ᶠ N : Nat in atTop,
        (N : Real) ≤ height N ∧ height N ≤ N + 1) ∧
      (∀ᶠ N : Nat in atTop,
        ∀ sigma,
          sigma ∈ Icc guinandWeilXiContourLeft guinandWeilXiContourRight →
          riemannXi
            ((sigma : Complex) + (height N : Complex) * Complex.I) ≠ 0) ∧
      Tendsto
        (fun N : Nat =>
          guinandWeilHorizontalIntegral
            (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
              logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (height N))
        atTop (nhds 0) ∧
      Tendsto
        (fun N : Nat =>
          guinandWeilHorizontalIntegral
            (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
              logDeriv riemannXi s)
            guinandWeilXiContourLeft guinandWeilXiContourRight (-(height N)))
        atTop (nhds 0) := by
  obtain ⟨K, k, A, C, hK, hk, hA, hC, hbound⟩ :=
    exists_fixed_canonicalXi_goodHeight_both_burnolHorizontalIntegral_bound v
  obtain ⟨B, hB, henvelope⟩ :=
    exists_pos_const_xiGoodHeightLogDerivEnvelope_le_pow_four hK hk hA
  let height : Nat → Real := fun N =>
    if hN : 5 ≤ N then Classical.choose (hbound N hN) else (N : Real)
  have hheight (N : Nat) (hN : 5 ≤ N) :
      (N : Real) ≤ height N ∧ height N ≤ N + 1 ∧
      (∀ sigma,
        sigma ∈ Icc guinandWeilXiContourLeft guinandWeilXiContourRight →
        riemannXi
          ((sigma : Complex) + (height N : Complex) * Complex.I) ≠ 0) ∧
      let bound := (C / |height N| ^ 5) *
        xiGoodHeightLogDerivEnvelope K k A N (height N) * (3 / 2 : Real)
      ‖guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            logDeriv riemannXi s)
          guinandWeilXiContourLeft guinandWeilXiContourRight (height N)‖ ≤ bound ∧
        ‖guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            logDeriv riemannXi s)
          guinandWeilXiContourLeft guinandWeilXiContourRight (-(height N))‖ ≤
            (C / |height N| ^ 5) *
              xiGoodHeightLogDerivEnvelope K k A N (height N) *
                (3 / 2 : Real) := by
    dsimp only [height]
    rw [dif_pos hN]
    exact Classical.choose_spec (hbound N hN)
  let M : Nat → Real := fun N =>
    (C * B * 12 ^ 4 * (3 / 2 : Real)) / (N : Real)
  have hM : Tendsto M atTop (nhds 0) := by
    simpa only [M] using
      (tendsto_const_div_atTop_nhds_zero_nat
        (C * B * 12 ^ 4 * (3 / 2 : Real)))
  have hmajor (N : Nat) (hN : 5 ≤ N) :
      ‖guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            logDeriv riemannXi s)
          guinandWeilXiContourLeft guinandWeilXiContourRight (height N)‖ ≤ M N ∧
        ‖guinandWeilHorizontalIntegral
          (fun s => suzukiSmoothCoreBurnolXiContourWeight v s *
            logDeriv riemannXi s)
          guinandWeilXiContourLeft guinandWeilXiContourRight (-(height N))‖ ≤
            M N := by
    obtain ⟨hTN, hTN1, _hnz, hupper, hlower⟩ := hheight N hN
    have hNpos : (0 : Real) < N := by
      exact_mod_cast (show 0 < N by omega)
    have hTpos : 0 < height N := hNpos.trans_le hTN
    have hN11 : (N : Real) + 11 ≤ 12 * N := by
      nlinarith [show (1 : Real) ≤ N by exact_mod_cast (show 1 ≤ N by omega)]
    have hpowN : ((N : Real) + 11) ^ 4 ≤ (12 * N) ^ 4 := by
      exact pow_le_pow_left₀ (by positivity) hN11 4
    have henv := henvelope N (height N) hN hTN hTN1
    have henv0 : 0 ≤
        xiGoodHeightLogDerivEnvelope K k A N (height N) := by
      have hlog0 : 0 ≤
          Real.log (xiLocalDiskGrowthFactor K k A (height N) 4) :=
        Real.log_nonneg
          (one_lt_xiLocalDiskGrowthFactor hK hk hA (by norm_num)).le
      have hcount0 :=
        canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg ((N : Real) + 5)
      unfold xiGoodHeightLogDerivEnvelope
      positivity
    have hTpow : (N : Real) ^ 5 ≤ |height N| ^ 5 := by
      rw [abs_of_pos hTpos]
      exact pow_le_pow_left₀ hNpos.le hTN 5
    have hscalar :
        (C / |height N| ^ 5) *
              xiGoodHeightLogDerivEnvelope K k A N (height N) *
            (3 / 2 : Real) ≤ M N := by
      have hdenN : 0 < (N : Real) ^ 5 := pow_pos hNpos 5
      have hdenT : 0 < |height N| ^ 5 := pow_pos (abs_pos.mpr hTpos.ne') 5
      have hinv : 1 / |height N| ^ 5 ≤ 1 / (N : Real) ^ 5 := by
        exact one_div_le_one_div_of_le hdenN hTpow
      have hCdiv : C / |height N| ^ 5 ≤ C / (N : Real) ^ 5 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by
          simpa only [one_div] using hinv) hC.le
      calc
        (C / |height N| ^ 5) *
              xiGoodHeightLogDerivEnvelope K k A N (height N) *
            (3 / 2 : Real) ≤
            (C / (N : Real) ^ 5) *
              xiGoodHeightLogDerivEnvelope K k A N (height N) *
                (3 / 2 : Real) := by
          gcongr
        _ ≤
            (C / (N : Real) ^ 5) *
              (B * ((N : Real) + 11) ^ 4) * (3 / 2 : Real) := by
          gcongr
        _ ≤ (C / (N : Real) ^ 5) *
              (B * (12 * N) ^ 4) * (3 / 2 : Real) := by
          gcongr
        _ = M N := by
          dsimp only [M]
          field_simp
    exact ⟨hupper.trans hscalar, hlower.trans hscalar⟩
  refine ⟨height, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
    exact ⟨(hheight N hN).1, (hheight N hN).2.1⟩
  · filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
    exact (hheight N hN).2.2.1
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      (by
        filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
        exact (hmajor N hN).1)
      hM
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Eventually.of_forall fun _ => norm_nonneg _)
      (by
        filter_upwards [eventually_atTop.2 ⟨5, fun _ hN => hN⟩] with N hN
        exact (hmajor N hN).2)
      hM

end

end RiemannHypothesisProject.Experiments.M100
