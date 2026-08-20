import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaBurnolRightVerticalEvaluation
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaFourierPolarization
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFormulaIdentity

/-!
# M100-DF6F smooth-core Burnol formula

This module completes the infinite-rectangle passage for the actual
smooth-core Burnol source.  It combines the finite multiplicity-aware xi
divisor identity, the good-height horizontal decay, both vertical limits, and
the independently evaluated right vertical.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Complex Filter MeasureTheory Set Topology
open SchwartzLineTestFunction
open ComplexCompactExhaustion
open scoped ComplexConjugate FourierTransform

private theorem burnolFourierLaplaceSource_suzukiProjectBase_conj
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (z : Complex) :
    burnolFourierLaplaceSource (suzukiProjectBase v.1) (conj z) =
      conj (burnolFourierLaplaceSource (suzukiProjectBase v.1) z) := by
  rw [burnolFourierLaplaceSource_suzukiProjectBase,
    burnolFourierLaplaceSource_suzukiProjectBase]
  rw [suzukiFourierSource_autocorrelation_eq_mul_conj
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩),
    suzukiFourierSource_autocorrelation_eq_mul_conj
      (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)]
  simp only [map_mul, conj_conj]
  ring

private theorem suzukiSmoothCoreBurnolXiContourWeight_one_sub_conj
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) (s : Complex) :
    suzukiSmoothCoreBurnolXiContourWeight v (1 - conj s) =
      conj (suzukiSmoothCoreBurnolXiContourWeight v s) := by
  unfold suzukiSmoothCoreBurnolXiContourWeight
  rw [show ((1 - conj s) - (1 / 2 : Complex)) / Complex.I =
      conj ((s - (1 / 2 : Complex)) / Complex.I) by
    apply Complex.ext <;> simp <;> ring]
  exact burnolFourierLaplaceSource_suzukiProjectBase_conj v _

private theorem riemannXi_conj_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    riemannXi (conj s) = conj (riemannXi s) := by
  have hsc : 1 < (conj s).re := by simpa using hs
  rw [riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta hsc,
    riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta hs,
    riemannZeta_conj_of_one_lt_re hs]
  unfold Complex.Gammaℝ
  rw [show conj s / 2 = conj (s / 2) by
      apply Complex.ext <;> norm_num [div_eq_mul_inv],
    Complex.Gamma_conj]
  have hpiArg : Complex.arg (Real.pi : Complex) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  rw [show -(conj s) / 2 = conj (-s / 2) by
      apply Complex.ext <;> norm_num [div_eq_mul_inv],
    Complex.cpow_conj _ _ hpiArg]
  simp [map_ofNat]

private theorem logDeriv_riemannXi_conj_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    logDeriv riemannXi (conj s) = conj (logDeriv riemannXi s) := by
  let reflected : Complex → Complex := conj ∘ riemannXi ∘ conj
  have hreflected : reflected =ᶠ[nhds (conj s)] riemannXi := by
    have hright : ∀ᶠ z : Complex in nhds (conj s), 1 < z.re :=
      (Complex.continuous_re.tendsto (conj s)).eventually
        (lt_mem_nhds (by simpa using hs))
    filter_upwards [hright] with z hz
    dsimp only [reflected, Function.comp_apply]
    simpa using (riemannXi_conj_of_one_lt_re (s := conj z) (by simpa using hz)).symm
  have hderiv : deriv reflected (conj s) = deriv riemannXi (conj s) :=
    hreflected.deriv_eq
  have hstar : deriv reflected (conj s) = conj (deriv riemannXi s) := by
    dsimp only [reflected]
    simpa using congrFun (deriv_star_conj (f := riemannXi)) (conj s)
  have hderivConj : deriv riemannXi (conj s) = conj (deriv riemannXi s) := by
    exact hderiv.symm.trans hstar
  rw [logDeriv_apply, logDeriv_apply, hderivConj,
    riemannXi_conj_of_one_lt_re hs]
  simp

private theorem re_suzukiSmoothCoreBurnolXi_weightedZeroSum_eq_nontrivial_sum
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (z w : Complex) :
    (riemannXiRectangleWeightedZeroSum
        (suzukiSmoothCoreBurnolXiContourWeight v) z w).re =
      (riemannXiRectangleNontrivialZetaZeroFinset z w).sum
        (burnolNontrivialZeroWeight (suzukiProjectBase v.1)) := by
  rw [riemannXiRectangleWeightedZeroSum_eq_zetaZeroMultiplicity]
  rw [← Complex.reCLM_apply, map_sum]
  unfold riemannXiRectangleNontrivialZetaZeroFinset
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _hs
  simp [burnolNontrivialZeroWeight, zetaZeroMultiplicityReal,
    suzukiSmoothCoreBurnolXiContourWeight, riemannWeilZeroArgument,
    Complex.mul_re]
  rfl

private theorem tendsto_re_suzukiSmoothCoreBurnolXi_weightedZeroSum
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (height : Nat → Real) (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun N : Nat =>
        (riemannXiRectangleWeightedZeroSum
          (suzukiSmoothCoreBurnolXiContourWeight v)
          ((guinandWeilXiContourLeft : Complex) -
            (height N : Complex) * Complex.I)
          ((guinandWeilXiContourRight : Complex) +
            (height N : Complex) * Complex.I)).re)
      atTop
      (nhds (guinandWeilBurnolLiteratureZeroSide
        (suzukiProjectBase v.1))) := by
  let z : Nat → Complex := fun N =>
    (guinandWeilXiContourLeft : Complex) -
      (height N : Complex) * Complex.I
  let w : Nat → Complex := fun N =>
    (guinandWeilXiContourRight : Complex) +
      (height N : Complex) * Complex.I
  have hmem (rho : NontrivialZetaZeroSubtype) :
      ∀ᶠ N : Nat in atTop,
        rho ∈ riemannXiRectangleNontrivialZetaZeroFinset (z N) (w N) := by
    have hreLower : guinandWeilXiContourLeft ≤ (rho : Complex).re := by
      have hre := zetaZeroSubtype_re_pos_of_not_trivial rho.1 rho.property
      norm_num [guinandWeilXiContourLeft]
      linarith
    have hreUpper : (rho : Complex).re ≤ guinandWeilXiContourRight := by
      have hreLt : (rho : Complex).re < 1 := by
        by_contra hnot
        have hone : 1 ≤ (rho : Complex).re := le_of_not_gt hnot
        exact (riemannZeta_ne_zero_of_one_le_re hone) rho.1.property
      norm_num [guinandWeilXiContourRight]
      linarith
    filter_upwards
      [hheight.eventually (eventually_ge_atTop (abs (rho : Complex).im))]
      with N hN
    rw [mem_riemannXiRectangleNontrivialZetaZeroFinset_iff,
      Complex.Rectangle, Complex.mem_reProdIm]
    constructor
    · rw [Set.uIcc_of_le]
      · simpa [z, w] using And.intro hreLower hreUpper
      · norm_num [z, w, guinandWeilXiContourLeft,
          guinandWeilXiContourRight]
    · rw [Set.uIcc_of_le]
      · simpa [z, w] using (abs_le.mp hN)
      · simp only [z, w, Complex.sub_im, Complex.ofReal_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im,
          Complex.I_re, mul_one, zero_mul, Complex.add_im]
        linarith [abs_nonneg (rho : Complex).im, hN]
  have hfinsets :
      Tendsto
        (fun N : Nat =>
          riemannXiRectangleNontrivialZetaZeroFinset (z N) (w N))
        atTop (atTop : Filter (Finset NontrivialZetaZeroSubtype)) := by
    rw [Filter.atTop_finset_eq_iInf, tendsto_iInf]
    intro rho
    rw [tendsto_principal]
    filter_upwards [hmem rho] with N hN
    change {rho} ⊆ riemannXiRectangleNontrivialZetaZeroFinset (z N) (w N)
    simpa only [Finset.singleton_subset_iff] using hN
  have hsum :=
    (summable_burnolNontrivialZeroWeight
      (summable_norm_guinandWeilBurnolLiteratureZeroWeight_suzukiProjectBase v)).hasSum.comp
      hfinsets
  rw [← guinandWeilBurnolLiteratureZeroSide_eq_nontrivial] at hsum
  simpa only [z, w, Function.comp_def,
    re_suzukiSmoothCoreBurnolXi_weightedZeroSum_eq_nontrivial_sum] using hsum

private theorem integral_suzukiSmoothCoreBurnolXi_reflectedRight_eq_conj
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    (∫ t : Real,
        suzukiSmoothCoreBurnolXiContourWeight v
            (1 - ((guinandWeilXiContourRight : Complex) +
              (t : Complex) * Complex.I)) *
          logDeriv riemannXi
            ((guinandWeilXiContourRight : Complex) +
              (t : Complex) * Complex.I)) =
      conj (∫ t : Real,
        suzukiSmoothCoreBurnolXiContourWeight v
            ((guinandWeilXiContourRight : Complex) +
              (t : Complex) * Complex.I) *
          logDeriv riemannXi
            ((guinandWeilXiContourRight : Complex) +
              (t : Complex) * Complex.I)) := by
  let rightLine : Real → Complex := fun t =>
    suzukiSmoothCoreBurnolXiContourWeight v
        ((guinandWeilXiContourRight : Complex) +
          (t : Complex) * Complex.I) *
      logDeriv riemannXi
        ((guinandWeilXiContourRight : Complex) +
          (t : Complex) * Complex.I)
  have hpoint (t : Real) :
      suzukiSmoothCoreBurnolXiContourWeight v
          (1 - ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I)) *
        logDeriv riemannXi
          ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) =
        conj (rightLine (-t)) := by
    have hconj :
        conj ((guinandWeilXiContourRight : Complex) +
            ((-t : Real) : Complex) * Complex.I) =
          (guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I := by
      apply Complex.ext <;>
        norm_num [guinandWeilXiContourRight, map_ofNat] <;> ring
    have hweight :=
      suzukiSmoothCoreBurnolXiContourWeight_one_sub_conj v
        ((guinandWeilXiContourRight : Complex) +
          ((-t : Real) : Complex) * Complex.I)
    rw [hconj] at hweight
    have hlog := logDeriv_riemannXi_conj_of_one_lt_re
      (s := (guinandWeilXiContourRight : Complex) +
        ((-t : Real) : Complex) * Complex.I) (by
          norm_num [guinandWeilXiContourRight])
    rw [hconj] at hlog
    dsimp only [rightLine]
    rw [hweight, hlog, map_mul]
  calc
    (∫ t : Real,
        suzukiSmoothCoreBurnolXiContourWeight v
            (1 - ((guinandWeilXiContourRight : Complex) +
              (t : Complex) * Complex.I)) *
          logDeriv riemannXi
            ((guinandWeilXiContourRight : Complex) +
              (t : Complex) * Complex.I)) =
        ∫ t : Real, conj (rightLine (-t)) := by
          apply integral_congr_ae
          filter_upwards with t
          exact hpoint t
    _ = conj (∫ t : Real, rightLine (-t)) := integral_conj
    _ = conj (∫ t : Real, rightLine t) := by rw [integral_neg_eq_self]
    _ = _ := rfl

/-- The actual smooth-core Burnol source satisfies the multiplicity-aware
Guinand--Weil formula in the project's normalization. -/
theorem suzukiSmoothCoreBurnolGuinandWeilFormula
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    guinandWeilBurnolLiteratureZeroSide (suzukiProjectBase v.1) =
      guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v.1) := by
  let F : Complex → Complex := fun s =>
    suzukiSmoothCoreBurnolXiContourWeight v s * logDeriv riemannXi s
  let rightLine : Real → Complex := fun t =>
    F ((guinandWeilXiContourRight : Complex) +
      (t : Complex) * Complex.I)
  let completeRight : Complex := ∫ t : Real, rightLine t
  obtain ⟨height, hheightWindow, hupperNonzero, htop, hbottom⟩ :=
    exists_canonicalXi_goodHeight_both_burnolHorizontalIntegrals_tendsto_zero v
  have hheight : Tendsto height atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (hheightWindow.mono fun N hN => hN.1)
    exact tendsto_natCast_atTop_atTop
  let bottom : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F guinandWeilXiContourLeft
      guinandWeilXiContourRight (-(height N))
  let top : Nat → Complex := fun N =>
    guinandWeilHorizontalIntegral F guinandWeilXiContourLeft
      guinandWeilXiContourRight (height N)
  let right : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F guinandWeilXiContourRight
      (-(height N)) (height N)
  let left : Nat → Complex := fun N =>
    guinandWeilVerticalIntegral F guinandWeilXiContourLeft
      (-(height N)) (height N)
  have hbottom' : Tendsto bottom atTop (nhds 0) := by
    simpa only [bottom, F] using hbottom
  have htop' : Tendsto top atTop (nhds 0) := by
    simpa only [top, F] using htop
  have hright : Tendsto right atTop
      (nhds (Complex.I * completeRight)) := by
    simpa only [right, F, completeRight, rightLine] using
      tendsto_suzukiSmoothCoreBurnolXi_rightVerticalIntegral v height hheight
  have hleft : Tendsto left atTop
      (nhds (-(Complex.I * conj completeRight))) := by
    have hleftRaw :=
      tendsto_suzukiSmoothCoreBurnolXi_leftVerticalIntegral v height hheight
    rw [integral_suzukiSmoothCoreBurnolXi_reflectedRight_eq_conj v] at hleftRaw
    simpa only [left, F, completeRight, rightLine] using hleftRaw
  have hcomplex :
      Tendsto
        (fun N =>
          (1 / (2 * Real.pi * Complex.I)) *
            (bottom N - top N + right N - left N))
        atTop
        (nhds
          ((1 / (2 * Real.pi * Complex.I)) *
            ((0 : Complex) - 0 + Complex.I * completeRight -
              (-(Complex.I * conj completeRight))))) :=
    (((hbottom'.sub htop').add hright).sub hleft).const_mul
      (1 / (2 * Real.pi * Complex.I))
  have hlimitComplex :
      (1 / (2 * Real.pi * Complex.I)) *
          ((0 : Complex) - 0 + Complex.I * completeRight -
            (-(Complex.I * conj completeRight))) =
        (((1 / Real.pi) * completeRight.re : Real) : Complex) := by
    simp only [sub_self, zero_add, sub_neg_eq_add, ← mul_add,
      Complex.add_conj]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hcontour :
      Tendsto
        (fun N =>
          ((1 / (2 * Real.pi * Complex.I)) *
            (bottom N - top N + right N - left N)).re)
        atTop
        (nhds ((1 / Real.pi) * completeRight.re)) := by
    have hre :=
      (Complex.continuous_re.tendsto
        ((1 / (2 * Real.pi * Complex.I)) *
          ((0 : Complex) - 0 + Complex.I * completeRight -
            (-(Complex.I * conj completeRight))))).comp hcomplex
    rw [hlimitComplex] at hre
    have hre' :
        Tendsto
          (fun N =>
            ((1 / (2 * Real.pi * Complex.I)) *
              (bottom N - top N + right N - left N)).re)
          atTop
          (nhds ((((1 / Real.pi) * completeRight.re : Real) : Complex).re)) := by
      apply hre.congr'
      exact Eventually.of_forall fun _N => rfl
    simpa only [Complex.ofReal_re] using hre'
  have hzero :=
    tendsto_re_suzukiSmoothCoreBurnolXi_weightedZeroSum v height hheight
  have heq :
      (∀ᶠ N : Nat in atTop,
        (riemannXiRectangleWeightedZeroSum
          (suzukiSmoothCoreBurnolXiContourWeight v)
          ((guinandWeilXiContourLeft : Complex) -
            (height N : Complex) * Complex.I)
          ((guinandWeilXiContourRight : Complex) +
            (height N : Complex) * Complex.I)).re =
          ((1 / (2 * Real.pi * Complex.I)) *
            (bottom N - top N + right N - left N)).re) := by
    filter_upwards [hheightWindow, hupperNonzero] with N hwindow hnonzero
    have hT0 : 0 ≤ height N := by
      exact (Nat.cast_nonneg N).trans hwindow.1
    have hboundary :=
      riemannXi_ne_zero_on_symmetric_goodHeight_rectangleBorder
        (height N) hnonzero
    have hfinite :=
      suzukiSmoothCoreBurnolXi_normalizedRectangleIntegral_eq_weightedZeroSum
        v
        (z := (guinandWeilXiContourLeft : Complex) -
          (height N : Complex) * Complex.I)
        (w := (guinandWeilXiContourRight : Complex) +
          (height N : Complex) * Complex.I)
        (by
          norm_num [guinandWeilXiContourLeft,
            guinandWeilXiContourRight])
        (by
          simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one,
            zero_mul, Complex.add_im]
          linarith)
        hboundary
    have hre := congrArg Complex.re hfinite.symm
    simpa only [bottom, top, right, left, F,
      guinandWeilNormalizedRectangleIntegral,
      guinandWeilRectangleIntegral,
      Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, sub_zero, mul_one, Complex.add_re,
      Complex.sub_im, Complex.mul_im, Complex.add_im,
      add_zero, zero_add, zero_sub, neg_zero] using hre
  have hzeroAsContour :=
    hcontour.congr' (heq.mono fun _N hN => hN.symm)
  have hformula :
      guinandWeilBurnolLiteratureZeroSide (suzukiProjectBase v.1) =
        (1 / Real.pi) * completeRight.re :=
    tendsto_nhds_unique hzero hzeroAsContour
  have hrightEvaluation :=
    one_div_pi_mul_re_integral_suzukiSmoothCoreBurnol_logDeriv_riemannXi_right_eq_residual
      v
  change (1 / Real.pi) * completeRight.re =
      guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v.1)
    at hrightEvaluation
  exact hformula.trans hrightEvaluation

/-- The proved source record for one smooth-core vector. -/
theorem burnolGuinandWeilSourceAssumptions_suzukiProjectBase_proved
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    BurnolGuinandWeilSourceAssumptions (suzukiProjectBase v.1) where
  source_entire :=
    differentiable_burnolFourierLaplaceSource_suzukiProjectBase
      suzukiProjectAStar_pos.le v
  zeroSide_summable :=
    summable_norm_guinandWeilBurnolLiteratureZeroWeight_suzukiProjectBase v
  formula := suzukiSmoothCoreBurnolGuinandWeilFormula v

/-- The previously borrowed smooth-core Burnol premise is now discharged by
the analytic contour argument for every smooth-core vector. -/
theorem suzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions_proved :
    SuzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions := by
  intro v
  exact burnolGuinandWeilSourceAssumptions_suzukiProjectBase_proved v

end

end RiemannHypothesisProject.Experiments.M100
