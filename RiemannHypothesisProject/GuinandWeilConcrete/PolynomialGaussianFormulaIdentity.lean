import RiemannHypothesisProject.GuinandWeilConcrete.XiHorizontalDecay
import RiemannHypothesisProject.GuinandWeilConcrete.XiRectangleIdentity
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVerticalEvaluation
import RiemannHypothesisProject.GuinandWeilConcrete.MultiplicityPolynomialGaussianFormulaHandoff

/-!
# Unconditional real-even polynomial-Gaussian formula identity

This module completes the infinite-rectangle passage for the real-even
polynomial-Gaussian Guinand-Weil source family. It identifies the finite xi
divisor sums with cofinal nontrivial-zeta-zero sums, proves the reflected
vertical relation and complete-line convergence, and combines those results
with the vanishing good-height horizontal edges.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology

theorem riemannXi_eq_zero_of_nontrivialZetaZero
    (rho : NontrivialZetaZeroSubtype) :
    riemannXi (rho : Complex) = 0 := by
  have horder : analyticOrderAt riemannXi (rho : Complex) =
      zetaZeroMultiplicity rho.1 :=
    analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
      rho.1 rho.property
  apply apply_eq_zero_of_analyticOrderAt_ne_zero
  rw [horder]
  exact_mod_cast zetaZeroMultiplicity_ne_zero rho.1

private noncomputable def riemannXiRectangleNontrivialZetaZeroEmbedding
    (z w : Complex) :
    {s // s ∈ riemannXiRectangleDivisorSupport z w} ↪
      NontrivialZetaZeroSubtype where
  toFun s :=
    ⟨riemannXiRectangleZetaZero z w s s.property,
      not_isTrivialZetaZero_riemannXiRectangleZetaZero z w s s.property⟩
  inj' := by
    intro s t hst
    apply Subtype.ext
    exact congrArg (fun rho : NontrivialZetaZeroSubtype => (rho : Complex)) hst

noncomputable def riemannXiRectangleNontrivialZetaZeroFinset
    (z w : Complex) : Finset NontrivialZetaZeroSubtype :=
  (riemannXiRectangleDivisorSupport z w).attach.map
    (riemannXiRectangleNontrivialZetaZeroEmbedding z w)

theorem mem_riemannXiRectangleNontrivialZetaZeroFinset_iff
    {z w : Complex} {rho : NontrivialZetaZeroSubtype} :
    rho ∈ riemannXiRectangleNontrivialZetaZeroFinset z w ↔
      (rho : Complex) ∈ Rectangle z w := by
  constructor
  · intro hrho
    rw [riemannXiRectangleNontrivialZetaZeroFinset, Finset.mem_map] at hrho
    obtain ⟨s, _hs, rfl⟩ := hrho
    exact (mem_riemannXiRectangleDivisorSupport_iff.mp s.property).1
  · intro hrho
    have hs : (rho : Complex) ∈ riemannXiRectangleDivisorSupport z w :=
      mem_riemannXiRectangleDivisorSupport_iff.mpr
        ⟨hrho, riemannXi_eq_zero_of_nontrivialZetaZero rho⟩
    rw [riemannXiRectangleNontrivialZetaZeroFinset, Finset.mem_map]
    refine ⟨⟨(rho : Complex), hs⟩, by simp, ?_⟩
    apply Subtype.ext
    rfl

theorem re_riemannXiRectangleWeightedZeroSum_eq_nontrivial_sum
    (p : Polynomial Real) (z w : Complex) :
    (riemannXiRectangleWeightedZeroSum
        (guinandWeilXiContourWeight p) z w).re =
      (riemannXiRectangleNontrivialZetaZeroFinset z w).sum
        (multiplicityPolynomialGaussianNontrivialZetaZeroWeight
          (guinandWeilPiEvenPolynomial p)) := by
  rw [riemannXiRectangleWeightedZeroSum_eq_zetaZeroMultiplicity]
  rw [← Complex.reCLM_apply, map_sum]
  unfold riemannXiRectangleNontrivialZetaZeroFinset
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _hs
  simp [multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
    zetaZeroMultiplicityReal, guinandWeilXiContourWeight,
    riemannWeilZeroArgument, Complex.mul_re]
  rfl

theorem summable_multiplicityPolynomialGaussianNontrivialZetaZeroWeight_unconditional
    (p : Polynomial Complex) :
    Summable (multiplicityPolynomialGaussianNontrivialZetaZeroWeight p) := by
  have hs :=
    (summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional
      p).subtype nontrivialZetaZeroSet
  refine hs.congr ?_
  intro rho
  have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := rho.property
  simp [multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
    guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight, hnotTrivial]

theorem tendsto_re_riemannXiRectangleWeightedZeroSum
    (p : Polynomial Real) (height : Nat → Real)
    (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun N : Nat =>
        (riemannXiRectangleWeightedZeroSum
          (guinandWeilXiContourWeight p)
          ((guinandWeilXiContourLeft : Complex) -
            (height N : Complex) * Complex.I)
          ((guinandWeilXiContourRight : Complex) +
            (height N : Complex) * Complex.I)).re)
      atTop
      (nhds
        (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
          (guinandWeilPiEvenPolynomial p))) := by
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
    (summable_multiplicityPolynomialGaussianNontrivialZetaZeroWeight_unconditional
      (guinandWeilPiEvenPolynomial p)).hasSum.comp hfinsets
  rw [← tsum_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial]
    at hsum
  simpa only [z, w, Function.comp_def,
    re_riemannXiRectangleWeightedZeroSum_eq_nontrivial_sum,
    guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide,
    guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight] using hsum

theorem guinandWeilXi_verticalIntegral_left_eq_neg_right
    (p : Polynomial Real) (T : Real) :
    guinandWeilVerticalIntegral
        (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
        guinandWeilXiContourLeft (-T) T =
      -guinandWeilVerticalIntegral
        (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
        guinandWeilXiContourRight (-T) T := by
  let F : Complex → Complex := fun s =>
    guinandWeilXiContourWeight p s * logDeriv riemannXi s
  have hpoint (t : Real) :
      F ((guinandWeilXiContourLeft : Complex) +
          (t : Complex) * Complex.I) =
        -F ((guinandWeilXiContourRight : Complex) +
          (-t : Complex) * Complex.I) := by
    have hreflect :=
      guinandWeilXiContourWeight_mul_logDeriv_one_sub_all p
        ((guinandWeilXiContourRight : Complex) +
          (-t : Complex) * Complex.I)
    change F (1 - ((guinandWeilXiContourRight : Complex) +
        (-t : Complex) * Complex.I)) = _ at hreflect
    convert hreflect using 1
    (norm_num [guinandWeilXiContourLeft, guinandWeilXiContourRight]; ring_nf)
  unfold guinandWeilVerticalIntegral
  change Complex.I *
      (∫ t in -T..T,
        F ((guinandWeilXiContourLeft : Complex) +
          (t : Complex) * Complex.I)) = _
  rw [intervalIntegral.integral_congr
      (fun t _ht => hpoint t), intervalIntegral.integral_neg]
  have hneg := intervalIntegral.integral_comp_neg
    (f := fun t : Real =>
      F ((guinandWeilXiContourRight : Complex) +
        (t : Complex) * Complex.I))
    (a := -T) (b := T)
  have hneg' :
      (∫ t in -T..T,
        F ((guinandWeilXiContourRight : Complex) +
          (-t : Complex) * Complex.I)) =
        ∫ t in -T..T,
          F ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) := by
    simpa using hneg
  rw [hneg']
  ring

theorem integrable_xiContourWeight_logDeriv_riemannXi_right
    (p : Polynomial Real) :
    Integrable (fun t : Real =>
      guinandWeilXiContourWeight p
          ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I) *
        logDeriv riemannXi
          ((guinandWeilXiContourRight : Complex) +
            (t : Complex) * Complex.I)) := by
  let R : Real → Complex := fun t =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (1 / ((5 / 4 : Real) + (t : Complex) * Complex.I) +
        1 / ((1 / 4 : Real) + (t : Complex) * Complex.I))
  let A : Real → Complex := fun t =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      (-(Real.log Real.pi : Complex) / 2 +
        Complex.digamma
          ((5 / 8 : Complex) + (t / 2 : Real) * Complex.I) / 2)
  let P : Real → Complex := fun t =>
    guinandWeilXiContourWeight p
        ((5 / 4 : Real) + (t : Complex) * Complex.I) *
      LSeries (fun n : Nat =>
          (ArithmeticFunction.vonMangoldt n : Complex))
        ((5 / 4 : Real) + (t : Complex) * Complex.I)
  have hR : Integrable R := integrable_xiContourWeight_rational_right p
  have hA : Integrable A := integrable_xiContourWeight_archimedean_right p
  have hP : Integrable P :=
    integrable_xiContourWeight_vonMangoldtLSeries_right p
  have hpointwise :
      (fun t : Real =>
        guinandWeilXiContourWeight p
            ((5 / 4 : Real) + (t : Complex) * Complex.I) *
          logDeriv riemannXi
            ((5 / 4 : Real) + (t : Complex) * Complex.I)) =
        fun t => R t + A t - P t := by
    funext t
    rw [logDeriv_riemannXi_eq_rightHalfPlaneLiteratureTerms (by norm_num)]
    dsimp only [R, A, P]
    apply Complex.ext <;> simp <;> ring
  have hsource : Integrable (fun t => R t + A t - P t) :=
    (hR.add hA).sub hP
  rw [← hpointwise] at hsource
  simpa only [guinandWeilXiContourRight] using hsource

theorem tendsto_guinandWeilXi_rightVerticalIntegral
    (p : Polynomial Real) (height : Nat → Real)
    (hheight : Tendsto height atTop atTop) :
    Tendsto
      (fun N : Nat =>
        guinandWeilVerticalIntegral
          (fun s => guinandWeilXiContourWeight p s * logDeriv riemannXi s)
          guinandWeilXiContourRight (-(height N)) (height N))
      atTop
      (nhds
        (Complex.I * ∫ t : Real,
          guinandWeilXiContourWeight p
              ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I) *
            logDeriv riemannXi
              ((guinandWeilXiContourRight : Complex) +
                (t : Complex) * Complex.I))) := by
  unfold guinandWeilVerticalIntegral
  exact
    (MeasureTheory.intervalIntegral_tendsto_integral
      (integrable_xiContourWeight_logDeriv_riemannXi_right p)
      (tendsto_neg_atTop_atBot.comp hheight) hheight).const_mul Complex.I

theorem guinandWeilPiEvenPolynomialGaussianLiteratureFormula
    (p : Polynomial Real) :
    GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula
      (guinandWeilPiEvenPolynomial p) := by
  let F : Complex → Complex := fun s =>
    guinandWeilXiContourWeight p s * logDeriv riemannXi s
  let rightLine : Real → Complex := fun t =>
    F ((guinandWeilXiContourRight : Complex) +
      (t : Complex) * Complex.I)
  let completeRight : Complex := ∫ t : Real, rightLine t
  obtain ⟨height, hheightWindow, hupperNonzero, htop, hbottom⟩ :=
    exists_canonicalXi_goodHeight_both_horizontalIntegrals_tendsto_zero p
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
      tendsto_guinandWeilXi_rightVerticalIntegral p height hheight
  have hleft : Tendsto left atTop
      (nhds (-(Complex.I * completeRight))) := by
    have hneg := hright.neg
    apply hneg.congr'
    exact Eventually.of_forall fun N => by
      simpa only [left, right, F] using
        (guinandWeilXi_verticalIntegral_left_eq_neg_right p (height N)).symm
  have hcomplex :
      Tendsto
        (fun N =>
          (1 / (2 * Real.pi * Complex.I)) *
            (bottom N - top N + right N - left N))
        atTop
        (nhds
          ((1 / (2 * Real.pi * Complex.I)) *
            ((0 : Complex) - 0 + Complex.I * completeRight -
              (-(Complex.I * completeRight))))) :=
    (((hbottom'.sub htop').add hright).sub hleft).const_mul
      (1 / (2 * Real.pi * Complex.I))
  have hlimitComplex :
      (1 / (2 * Real.pi * Complex.I)) *
          ((0 : Complex) - 0 + Complex.I * completeRight -
            (-(Complex.I * completeRight))) =
        ((1 / Real.pi : Real) : Complex) * completeRight := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
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
            (-(Complex.I * completeRight))))).comp hcomplex
    rw [hlimitComplex] at hre
    have hre' :
        Tendsto
          (fun N =>
            ((1 / (2 * Real.pi * Complex.I)) *
              (bottom N - top N + right N - left N)).re)
          atTop
          (nhds
            ((((1 / Real.pi : Real) : Complex) * completeRight).re)) := by
      apply hre.congr'
      exact Eventually.of_forall fun _N => rfl
    simpa only [Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hre'
  have hzero :=
    tendsto_re_riemannXiRectangleWeightedZeroSum p height hheight
  have heq :
      (∀ᶠ N : Nat in atTop,
        (riemannXiRectangleWeightedZeroSum
          (guinandWeilXiContourWeight p)
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
      guinandWeilXi_rectangleBoundary_decomposition_eq_weightedZeroSum
        p
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
      Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
      mul_zero, sub_zero, mul_one, Complex.add_re,
      Complex.sub_im, Complex.mul_im, Complex.add_im,
      add_zero, zero_add, zero_sub, neg_zero] using hre
  have hzeroAsContour :=
    hcontour.congr' (heq.mono fun _N hN => hN.symm)
  have hformula :
      guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
          (guinandWeilPiEvenPolynomial p) =
        (1 / Real.pi) * completeRight.re :=
    tendsto_nhds_unique hzero hzeroAsContour
  have hrightEvaluation :=
    one_div_pi_mul_re_integral_xiContourWeight_logDeriv_riemannXi_right_eq_literatureResidual
      p
  change (1 / Real.pi) * completeRight.re =
      guinandWeilPiPolynomialGaussianLiteratureResidualSide
        (guinandWeilPiEvenPolynomial p) at hrightEvaluation
  unfold GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula
  exact hformula.trans hrightEvaluation

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
