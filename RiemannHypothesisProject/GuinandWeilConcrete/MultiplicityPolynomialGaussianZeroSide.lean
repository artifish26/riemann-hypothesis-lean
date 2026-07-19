import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianZeroSide
import RiemannHypothesisProject.LiCriterion.MultiplicityHeightDecay
import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicityConjugation
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityCount
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityGrowth
import RiemannHypothesisProject.RiemannVonMangoldt.BellottiWongCanonicalSource
import RiemannHypothesisProject.RiemannVonMangoldt.ResidualAxisCompactBound

/-!
# Multiplicity-aware polynomial-Gaussian zero-side decay

Bellotti-Wong's argument-principle count counts zeros with analytic
multiplicity.  This module uses that faithful canonical count to prove
absolute summability of the actual polynomial-Gaussian weight on the positive
zero half, with every term weighted by its analytic multiplicity.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Bellotti-Wong's canonical multiplicity estimate gives the dyadic
`T log T` bound needed by the multiplicity-aware shell theorem, without any
small-height zero-free hypothesis. -/
theorem canonicalMultiplicityCount_dyadic_le
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (m : Nat) :
    canonicalPositiveOrdinateZetaZeroMultiplicityCount
        ((2 : Real) ^ (m + 1)) <=
      (20 + canonicalPositiveOrdinateZetaZeroMultiplicityCount 2) *
        (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
  have hcount_two_nonneg :=
    canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg 2
  by_cases hm : m = 0
  · subst m
    norm_num
    linarith
  · have hm_one : 1 <= m := Nat.one_le_iff_ne_zero.mpr hm
    have hvalid :
        bellottiWongValidFrom <= (2 : Real) ^ (m + 1) := by
      calc
        bellottiWongValidFrom <= 3 := by
          simpa [bellottiWongValidFrom] using Real.exp_one_lt_three.le
        _ <= 4 := by norm_num
        _ = (2 : Real) ^ 2 := by norm_num
        _ <= (2 : Real) ^ (m + 1) :=
          pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hm_one)
    have habs := hpublished ((2 : Real) ^ (m + 1)) hvalid
    have hcount_le :
        canonicalPositiveOrdinateZetaZeroMultiplicityCount
            ((2 : Real) ^ (m + 1)) <=
          riemannVonMangoldtMainTerm ((2 : Real) ^ (m + 1)) +
            bellottiWongErrorTerm ((2 : Real) ^ (m + 1)) := by
      have hupper := (abs_le.mp habs).2
      linarith
    have hmain := riemannVonMangoldtMainTerm_dyadic_le m
    have herror := bellottiWongErrorTerm_dyadic_le m
    have hT_one : 1 <= (2 : Real) ^ (m + 1) := by
      calc
        (1 : Real) = 2 ^ 0 := by norm_num
        _ <= 2 ^ (m + 1) :=
          pow_le_pow_right₀ (by norm_num) (Nat.zero_le (m + 1))
    have hm_two_nonneg : 0 <= (m : Real) + 2 := by positivity
    have herror_scaled :
        10 * ((m : Real) + 2) <=
          10 * ((m : Real) + 2) * ((2 : Real) ^ (m + 1)) := by
      have hfactor_nonneg : 0 <= (10 : Real) * ((m : Real) + 2) :=
        mul_nonneg (by norm_num) hm_two_nonneg
      simpa using mul_le_mul_of_nonneg_left hT_one hfactor_nonneg
    have htwenty :
        canonicalPositiveOrdinateZetaZeroMultiplicityCount
            ((2 : Real) ^ (m + 1)) <=
          20 * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
      calc
        canonicalPositiveOrdinateZetaZeroMultiplicityCount
              ((2 : Real) ^ (m + 1)) <=
            riemannVonMangoldtMainTerm ((2 : Real) ^ (m + 1)) +
              bellottiWongErrorTerm ((2 : Real) ^ (m + 1)) := hcount_le
        _ <= 2 * (((m : Real) + 1) * ((2 : Real) ^ (m + 1))) +
            10 * ((m : Real) + 2) := add_le_add hmain herror
        _ <= 2 * (((m : Real) + 1) * ((2 : Real) ^ (m + 1))) +
            10 * ((m : Real) + 2) * ((2 : Real) ^ (m + 1)) :=
          add_le_add le_rfl herror_scaled
        _ <= 20 * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))) := by
          have hpow_nonneg : 0 <= (2 : Real) ^ (m + 1) := by positivity
          nlinarith
    have hfactor_nonneg :
        0 <= ((m : Real) + 2) * ((2 : Real) ^ (m + 1)) := by positivity
    exact htwenty.trans (by nlinarith)

/-- The faithful canonical Bellotti-Wong theorem gives multiplicity-weighted
inverse-square summability on the positive zero half. -/
theorem positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_bellottiWong
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  apply positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_exactCount
    canonicalExactPositiveOrdinateZetaZeroWindow
    (20 + canonicalPositiveOrdinateZetaZeroMultiplicityCount 2)
  · nlinarith [canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg 2]
  · exact canonicalMultiplicityCount_dyadic_le hpublished

/-- The second-order shifted-radius factor is bounded by the standard
positive-ordinate inverse-square height factor. -/
theorem shiftedRadiusFactor_two_le_positiveOrdinateHeightDecay
    (rho : PositiveOrdinateZetaZeroSubtype) :
    (1 /
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (2 : Real)) <=
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  let y : Real := Complex.im (rho : Complex)
  let r : Real := norm (riemannWeilZeroArgument (rho : Complex))
  have hy_pos : 0 < y := rho.property
  have hr_nonneg : 0 <= r := norm_nonneg _
  have hy_le_r : y <= r := by
    have hre := Complex.abs_re_le_norm (riemannWeilZeroArgument (rho : Complex))
    rw [riemannWeilZeroArgument_re, abs_of_pos hy_pos] at hre
    exact hre
  have hden_pos : 0 < y ^ 2 + (1 / 2 : Real) ^ 2 := by positivity
  have hden_le :
      y ^ 2 + (1 / 2 : Real) ^ 2 <= (r + 2) ^ 2 := by
    nlinarith [sq_nonneg (r - y)]
  have hinv := one_div_le_one_div_of_le hden_pos hden_le
  simpa [y, r, Real.rpow_two] using hinv

/-- The faithful canonical Bellotti-Wong theorem implies absolute convergence
of the actual positive-ordinate polynomial-Gaussian zero weight with analytic
multiplicity. -/
theorem summable_norm_positiveOrdinateMultiplicityPolynomialGaussianZeroWeight
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho.1 *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1)) := by
  rcases
      norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius
        p 2 with
    ⟨C, hC, hshifted⟩
  have hheight :=
    positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_bellottiWong
      hpublished
  have hmajorant :
      Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        C * (zetaZeroMultiplicityReal rho.1 *
          (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)) :=
    hheight.mul_left C
  apply Summable.of_nonneg_of_le (fun _rho => norm_nonneg _) ?_ hmajorant
  intro rho
  have hsource := hshifted rho.1
  have hfactor := shiftedRadiusFactor_two_le_positiveOrdinateHeightDecay rho
  have hsourceHeight :
      norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1) <=
        C * (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ :=
    hsource.trans (mul_le_mul_of_nonneg_left hfactor hC)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (zetaZeroMultiplicityReal_pos rho.1)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hsourceHeight
      (zetaZeroMultiplicityReal_pos rho.1).le)

/-- Conjugation transports the faithful multiplicity-weighted inverse-square
sum to the negative zero half. -/
theorem negativeOrdinateZetaZero_multiplicityHeightDecay_summable_of_bellottiWong
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem) :
    Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  let e := positiveNegativeOrdinateZetaZeroConjEquiv
  apply e.summable_iff.mp
  refine
    (positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_bellottiWong
      hpublished).congr ?_
  intro rho
  have hmult :
      zetaZeroMultiplicityReal
          (positiveNegativeOrdinateZetaZeroConjEquiv rho).1 =
        zetaZeroMultiplicityReal rho.1 := by
    unfold zetaZeroMultiplicityReal
    exact_mod_cast zetaZeroMultiplicity_positiveNegativeConjEquiv rho
  change
    zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ =
      zetaZeroMultiplicityReal
          (positiveNegativeOrdinateZetaZeroConjEquiv rho).1 *
        (Complex.im
            (positiveNegativeOrdinateZetaZeroConjEquiv rho : Complex) ^ 2 +
          (1 / 2 : Real) ^ 2)⁻¹
  rw [hmult]
  simp [positiveNegativeOrdinateZetaZeroConjEquiv, pow_two]

/-- The second-order shifted-radius factor is bounded by inverse-square height
decay on the negative zero half as well. -/
theorem shiftedRadiusFactor_two_le_negativeOrdinateHeightDecay
    (rho : NegativeOrdinateZetaZeroSubtype) :
    (1 /
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (2 : Real)) <=
      (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ := by
  let y : Real := -Complex.im (rho : Complex)
  let r : Real := norm (riemannWeilZeroArgument (rho : Complex))
  have hy_pos : 0 < y := by simpa [y] using neg_pos.mpr rho.property
  have hr_nonneg : 0 <= r := norm_nonneg _
  have hy_le_r : y <= r := by
    have hre := Complex.abs_re_le_norm (riemannWeilZeroArgument (rho : Complex))
    rw [riemannWeilZeroArgument_re, abs_of_neg rho.property] at hre
    simpa [y] using hre
  have hden_pos : 0 < y ^ 2 + (1 / 2 : Real) ^ 2 := by positivity
  have hden_le :
      y ^ 2 + (1 / 2 : Real) ^ 2 <= (r + 2) ^ 2 := by
    nlinarith [sq_nonneg (r - y)]
  have hinv := one_div_le_one_div_of_le hden_pos hden_le
  simpa [y, r, Real.rpow_two, pow_two] using hinv

/-- Absolute convergence of the actual negative-ordinate
polynomial-Gaussian zero weight with analytic multiplicity. -/
theorem summable_norm_negativeOrdinateMultiplicityPolynomialGaussianZeroWeight
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex) :
    Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho.1 *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1)) := by
  rcases
      norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius
        p 2 with
    ⟨C, hC, hshifted⟩
  have hheight :=
    negativeOrdinateZetaZero_multiplicityHeightDecay_summable_of_bellottiWong
      hpublished
  have hmajorant :
      Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
        C * (zetaZeroMultiplicityReal rho.1 *
          (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)) :=
    hheight.mul_left C
  apply Summable.of_nonneg_of_le (fun _rho => norm_nonneg _) ?_ hmajorant
  intro rho
  have hsource := hshifted rho.1
  have hfactor := shiftedRadiusFactor_two_le_negativeOrdinateHeightDecay rho
  have hsourceHeight :
      norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1) <=
        C * (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹ :=
    hsource.trans (mul_le_mul_of_nonneg_left hfactor hC)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (zetaZeroMultiplicityReal_pos rho.1)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hsourceHeight
      (zetaZeroMultiplicityReal_pos rho.1).le)

/-- Absolute convergence of the actual completed-zeta polynomial-Gaussian
zero weight over all zeta zeros, with faithful analytic multiplicity. -/
theorem summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  let f : ZetaZeroSubtype -> Real := fun rho =>
    norm
      (zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)
  let positiveSet : Set ZetaZeroSubtype :=
    {rho | 0 < Complex.im (rho : Complex)}
  let negativeSet : Set ZetaZeroSubtype :=
    {rho | Complex.im (rho : Complex) < 0}
  let axisSet : Set ZetaZeroSubtype :=
    {rho | Complex.im (rho : Complex) = 0}
  have hpositiveSubtype :
      Summable (fun rho : positiveSet => f rho.1) := by
    simpa [positiveSet, f] using
      summable_norm_positiveOrdinateMultiplicityPolynomialGaussianZeroWeight
        hpublished p
  have hnegativeSubtype :
      Summable (fun rho : negativeSet => f rho.1) := by
    simpa [negativeSet, f] using
      summable_norm_negativeOrdinateMultiplicityPolynomialGaussianZeroWeight
        hpublished p
  have hpositiveIndicator : Summable (positiveSet.indicator f) :=
    (summable_subtype_iff_indicator (s := positiveSet)).mp hpositiveSubtype
  have hnegativeIndicator : Summable (negativeSet.indicator f) :=
    (summable_subtype_iff_indicator (s := negativeSet)).mp hnegativeSubtype
  have haxisSupport : Function.HasFiniteSupport (axisSet.indicator f) := by
    refine (closedBallZeroResidualRealAxisFinset 1).finite_toSet.subset ?_
    intro rho hrho
    have hvalue_ne : axisSet.indicator f rho ≠ 0 := hrho
    have haxis : rho ∈ axisSet := by
      by_contra hnot
      simp [Set.indicator, hnot] at hvalue_ne
    have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := by
      intro htrivial
      apply hvalue_ne
      rw [Set.indicator_of_mem haxis]
      simp [f, guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
        htrivial]
    have hmem :=
      mem_closedBallZeroResidualRealAxisFinset_one_of_axis_not_trivial
        rho haxis hnotTrivial
    simpa using hmem
  have haxisIndicator : Summable (axisSet.indicator f) :=
    summable_of_hasFiniteSupport haxisSupport
  have hsum := (hpositiveIndicator.add hnegativeIndicator).add haxisIndicator
  refine hsum.congr ?_
  intro rho
  rcases lt_trichotomy (Complex.im (rho : Complex)) 0 with
      hnegative | haxis | hpositive
  · simp [positiveSet, negativeSet, axisSet, f, hnegative,
      ne_of_lt hnegative, not_lt_of_ge hnegative.le]
  · simp [positiveSet, negativeSet, axisSet, f, haxis]
  · simp [positiveSet, negativeSet, axisSet, f, hpositive,
      ne_of_gt hpositive, not_lt_of_ge hpositive.le]

/-- Signed convergence of the faithful multiplicity-weighted actual
polynomial-Gaussian completed-zeta zero side. -/
theorem summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) :=
  (summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
    hpublished p).of_norm

/-- The raw polynomial-Gaussian value on the nontrivial-zero subtype, weighted
by the actual analytic multiplicity. -/
noncomputable def multiplicityPolynomialGaussianNontrivialZetaZeroWeight
    (p : Polynomial Complex)
    (rho : NontrivialZetaZeroSubtype) : Real :=
  zetaZeroMultiplicityReal rho.1 *
    (guinandWeilPiPolynomialGaussianSource p
      (riemannWeilZeroArgument (rho : Complex))).re

/-- The faithful multiplicity-weighted completed-zeta weight is exactly the
indicator of the corresponding raw weight on nontrivial zeros. -/
theorem multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_indicator
    (p : Polynomial Complex) :
    (fun rho : ZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) =
      nontrivialZetaZeroSet.indicator (fun rho : ZetaZeroSubtype =>
        zetaZeroMultiplicityReal rho *
          (guinandWeilPiPolynomialGaussianSource p
            (riemannWeilZeroArgument (rho : Complex))).re) := by
  classical
  funext rho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
      nontrivialZetaZeroSet, htrivial]
  · simp [guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
      nontrivialZetaZeroSet, htrivial]

/-- Finite completed-zeta multiplicity-weighted sums reduce exactly to the
nontrivial subwindow with the raw polynomial-Gaussian value. -/
theorem sum_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial
    (p : Polynomial Complex)
    (zeroes : Finset ZetaZeroSubtype) :
    zeroes.sum (fun rho : ZetaZeroSubtype =>
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) =
      (nontrivialZetaZeroFinset zeroes).sum (fun rho : ZetaZeroSubtype =>
        zetaZeroMultiplicityReal rho *
          (guinandWeilPiPolynomialGaussianSource p
            (riemannWeilZeroArgument (rho : Complex))).re) := by
  classical
  unfold nontrivialZetaZeroFinset
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _hrho
  simpa [Set.indicator] using congrFun
    (multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_indicator p) rho

/-- Absolute finite completed-zeta sums reduce to the absolute raw sum over
the nontrivial subwindow. -/
theorem sum_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial
    (p : Polynomial Complex)
    (zeroes : Finset ZetaZeroSubtype) :
    zeroes.sum (fun rho : ZetaZeroSubtype =>
        norm
          (zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) =
      (nontrivialZetaZeroFinset zeroes).sum (fun rho : ZetaZeroSubtype =>
        norm
          (zetaZeroMultiplicityReal rho *
            (guinandWeilPiPolynomialGaussianSource p
              (riemannWeilZeroArgument (rho : Complex))).re)) := by
  classical
  unfold nontrivialZetaZeroFinset
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · simp [guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
      nontrivialZetaZeroSet, htrivial]
  · simp [guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
      nontrivialZetaZeroSet, htrivial]

/-- The raw multiplicity-weighted polynomial-Gaussian weight is summable on
the actual nontrivial-zero subtype. -/
theorem summable_multiplicityPolynomialGaussianNontrivialZetaZeroWeight
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex) :
    Summable (multiplicityPolynomialGaussianNontrivialZetaZeroWeight p) := by
  have hs :=
    (summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight
      hpublished p).subtype nontrivialZetaZeroSet
  refine hs.congr ?_
  intro rho
  have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := by
    have hprop := rho.property
    change ¬ IsTrivialZetaZero (rho : Complex) at hprop
    exact hprop
  simp [multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
    guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
    hnotTrivial]

/-- Absolute summability of the faithful raw weight on the nontrivial-zero
subtype. -/
theorem summable_norm_multiplicityPolynomialGaussianNontrivialZetaZeroWeight
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex) :
    Summable (fun rho : NontrivialZetaZeroSubtype =>
      norm (multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho)) := by
  have hs :=
    (summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
      hpublished p).subtype nontrivialZetaZeroSet
  refine hs.congr ?_
  intro rho
  have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := by
    have hprop := rho.property
    change ¬ IsTrivialZetaZero (rho : Complex) at hprop
    exact hprop
  simp [multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
    guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
    hnotTrivial]

/-- The faithful global completed-zeta zero sum is the raw multiplicity sum
over nontrivial zeros. -/
theorem tsum_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial
    (p : Polynomial Complex) :
    (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) =
      ∑' rho : NontrivialZetaZeroSubtype,
        multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho := by
  classical
  calc
    (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) =
        ∑' rho : ZetaZeroSubtype,
          nontrivialZetaZeroSet.indicator (fun zetaZero : ZetaZeroSubtype =>
            zetaZeroMultiplicityReal zetaZero *
              (guinandWeilPiPolynomialGaussianSource p
                (riemannWeilZeroArgument (zetaZero : Complex))).re) rho := by
      apply tsum_congr
      intro rho
      exact congrFun
        (multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_indicator p) rho
    _ = ∑' rho : NontrivialZetaZeroSubtype,
          multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho := by
      simpa [multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
        Function.comp_def] using
        (tsum_subtype nontrivialZetaZeroSet
          (fun rho : ZetaZeroSubtype =>
            zetaZeroMultiplicityReal rho *
              (guinandWeilPiPolynomialGaussianSource p
                (riemannWeilZeroArgument (rho : Complex))).re)).symm

/-- The global absolute completed-zeta sum equals the absolute raw sum over
the nontrivial-zero subtype. -/
theorem tsum_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial
    (p : Polynomial Complex) :
    (∑' rho : ZetaZeroSubtype,
        norm
          (zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) =
      ∑' rho : NontrivialZetaZeroSubtype,
        norm (multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho) := by
  classical
  let raw : ZetaZeroSubtype -> Real := fun rho =>
    zetaZeroMultiplicityReal rho *
      (guinandWeilPiPolynomialGaussianSource p
        (riemannWeilZeroArgument (rho : Complex))).re
  have hpointwise :
      (fun rho : ZetaZeroSubtype =>
        norm
          (zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) =
        nontrivialZetaZeroSet.indicator (fun rho => norm (raw rho)) := by
    funext rho
    by_cases htrivial : IsTrivialZetaZero (rho : Complex)
    · simp [raw, guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
        nontrivialZetaZeroSet, htrivial]
    · simp [raw, guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight,
        nontrivialZetaZeroSet, htrivial]
  calc
    (∑' rho : ZetaZeroSubtype,
        norm
          (zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) =
        ∑' rho : ZetaZeroSubtype,
          nontrivialZetaZeroSet.indicator (fun zetaZero => norm (raw zetaZero)) rho := by
      apply tsum_congr
      intro rho
      exact congrFun hpointwise rho
    _ = ∑' rho : NontrivialZetaZeroSubtype,
          norm (multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho) := by
      simpa [raw, multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
        Function.comp_def] using
        (tsum_subtype nontrivialZetaZeroSet (fun rho => norm (raw rho))).symm

/-- Along any compact exhaustion, faithful multiplicity-weighted
polynomial-Gaussian zero-window sums converge to the global `tsum`. -/
theorem tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
          zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))
      Filter.atTop
      (nhds (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) :=
  exhaustion.tendsto_zetaZeroWindowSum
    (summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight
      hpublished p)

/-- The raw multiplicity-weighted sums over the nontrivial part of each
compact zero window converge to the raw nontrivial-zero `tsum`. -/
theorem tendsto_multiplicityPolynomialGaussianNontrivialZetaZeroWindowSum
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        (nontrivialZetaZeroFinset
          (exhaustion.zetaZeroSubtypeFinset n)).sum
            (fun rho : ZetaZeroSubtype =>
              zetaZeroMultiplicityReal rho *
                (guinandWeilPiPolynomialGaussianSource p
                  (riemannWeilZeroArgument (rho : Complex))).re))
      Filter.atTop
      (nhds (∑' rho : NontrivialZetaZeroSubtype,
        multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho)) := by
  have hcompleted :=
    tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum
      hpublished p exhaustion
  rw [tsum_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial]
    at hcompleted
  simpa only [ComplexCompactExhaustion.zetaZeroWindowSum,
    sum_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial]
    using hcompleted

/-- The compact-window sums of absolute multiplicity-weighted contributions
also converge to the finite global absolute sum. -/
theorem tendsto_norm_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
          norm
            (zetaZeroMultiplicityReal rho *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)))
      Filter.atTop
      (nhds (∑' rho : ZetaZeroSubtype,
        norm
          (zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))) :=
  exhaustion.tendsto_zetaZeroWindowSum
    (summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
      hpublished p)

/-- Absolute raw sums over the nontrivial part of compact zero windows
converge to the absolute nontrivial-zero `tsum`. -/
theorem tendsto_norm_multiplicityPolynomialGaussianNontrivialZetaZeroWindowSum
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        (nontrivialZetaZeroFinset
          (exhaustion.zetaZeroSubtypeFinset n)).sum
            (fun rho : ZetaZeroSubtype =>
              norm
                (zetaZeroMultiplicityReal rho *
                  (guinandWeilPiPolynomialGaussianSource p
                    (riemannWeilZeroArgument (rho : Complex))).re)))
      Filter.atTop
      (nhds (∑' rho : NontrivialZetaZeroSubtype,
        norm (multiplicityPolynomialGaussianNontrivialZetaZeroWeight p rho))) := by
  have hcompleted :=
    tendsto_norm_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum
      hpublished p exhaustion
  rw [tsum_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial]
    at hcompleted
  simpa only [ComplexCompactExhaustion.zetaZeroWindowSum,
    sum_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial]
    using hcompleted

/-- The absolute multiplicity-weighted contribution outside each compact
zero window tends to zero.  This is the direct tail statement used for
cutoff-error control. -/
theorem tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        ∑' rho :
          {rho : ZetaZeroSubtype //
            rho ∉ exhaustion.zetaZeroSubtypeFinset n},
          norm
            (zetaZeroMultiplicityReal rho.1 *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1))
      Filter.atTop (nhds 0) := by
  let u : ZetaZeroSubtype -> Real := fun rho =>
    norm
      (zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)
  have hu : Summable u := by
    simpa [u] using
      summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
        hpublished p
  have hwindow := exhaustion.tendsto_zetaZeroWindowSum hu
  have hdiff :
      Filter.Tendsto
        (fun n : Nat =>
          (∑' rho : ZetaZeroSubtype, u rho) -
            exhaustion.zetaZeroWindowSum n u)
        Filter.atTop (nhds 0) := by
    convert tendsto_const_nhds.sub hwindow using 1
    all_goals simp
  refine hdiff.congr' (Filter.Eventually.of_forall ?_)
  intro n
  rw [← hu.sum_add_tsum_subtype_compl
    (exhaustion.zetaZeroSubtypeFinset n)]
  simp [ComplexCompactExhaustion.zetaZeroWindowSum, u]

/-- At every cutoff, the signed truncation error is bounded by the absolute
multiplicity-weighted contribution outside the compact zero window. -/
theorem norm_tsum_sub_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_le
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    (n : Nat) :
    norm
        ((∑' rho : ZetaZeroSubtype,
            zetaZeroMultiplicityReal rho *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) -
          exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
            zetaZeroMultiplicityReal rho *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) <=
      ∑' rho :
        {rho : ZetaZeroSubtype //
          rho ∉ exhaustion.zetaZeroSubtypeFinset n},
        norm
          (zetaZeroMultiplicityReal rho.1 *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1) := by
  let weight : ZetaZeroSubtype -> Real := fun rho =>
    zetaZeroMultiplicityReal rho *
      guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho
  have hnorm : Summable (fun rho : ZetaZeroSubtype => norm (weight rho)) := by
    simpa [weight] using
      summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
        hpublished p
  have hsummable : Summable weight := hnorm.of_norm
  unfold ComplexCompactExhaustion.zetaZeroWindowSum
  change
    norm
        ((∑' rho : ZetaZeroSubtype, weight rho) -
          ∑ rho ∈ exhaustion.zetaZeroSubtypeFinset n, weight rho) <=
      ∑' rho :
        {rho : ZetaZeroSubtype //
          rho ∉ exhaustion.zetaZeroSubtypeFinset n},
        norm (weight rho.1)
  rw [← hsummable.sum_add_tsum_subtype_compl
    (exhaustion.zetaZeroSubtypeFinset n), add_sub_cancel_left]
  exact norm_tsum_le_tsum_norm (hnorm.subtype _)

/-- The absolute complementary tail is eventually below every positive error
tolerance. -/
theorem eventually_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_lt
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n : Nat in Filter.atTop,
      (∑' rho :
          {rho : ZetaZeroSubtype //
            rho ∉ exhaustion.zetaZeroSubtypeFinset n},
          norm
            (zetaZeroMultiplicityReal rho.1 *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1)) < ε := by
  have ht :=
    tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl
      hpublished p exhaustion
  exact (tendsto_order.1 ht).2 ε hε

/-- Consequently, the signed compact-window truncation error is eventually
below every positive tolerance. -/
theorem eventually_norm_tsum_sub_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_lt
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n : Nat in Filter.atTop,
      norm
          ((∑' rho : ZetaZeroSubtype,
              zetaZeroMultiplicityReal rho *
                guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) -
            exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
              zetaZeroMultiplicityReal rho *
                guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) < ε := by
  filter_upwards
    [eventually_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_lt
      hpublished p exhaustion hε] with n hn
  exact
    (norm_tsum_sub_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_le
      hpublished p exhaustion n).trans_lt hn

/-- The published Bellotti-Wong source package, with its stated `T >= e`
domain and first-row constants, instantiates the faithful absolute
multiplicity-weighted polynomial-Gaussian zero-side summability theorem. -/
theorem summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_bellottiWongSource
    (source : BellottiWongCanonicalSourceInputs)
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  exact summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight
    source.toCanonicalMultiplicityNTTheorem p

/-- The same canonical Bellotti-Wong source package instantiates convergence
of faithful signed compact-window zero sums. -/
theorem tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_of_bellottiWongSource
    (source : BellottiWongCanonicalSourceInputs)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
          zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))
      Filter.atTop
      (nhds (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  exact tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum
    source.toCanonicalMultiplicityNTTheorem p exhaustion

/-- For every positive tolerance, the Bellotti-Wong canonical source package
instantiates the quantitative faithful compact-window truncation bound. -/
theorem eventually_norm_tsum_sub_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_lt_of_bellottiWongSource
    (source : BellottiWongCanonicalSourceInputs)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion)
    {ε : Real} (hε : 0 < ε) :
    ∀ᶠ n : Nat in Filter.atTop,
      norm
          ((∑' rho : ZetaZeroSubtype,
              zetaZeroMultiplicityReal rho *
                guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) -
            exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
              zetaZeroMultiplicityReal rho *
                guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) < ε := by
  exact eventually_norm_tsum_sub_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_lt
    source.toCanonicalMultiplicityNTTheorem p exhaustion hε

/-! ## Eventual polynomial-count source lane -/

/-- Every natural shifted-radius decay factor is bounded by the corresponding
clamped absolute-ordinate factor. -/
theorem shiftedRadiusFactor_nat_le_clampedAbsOrdinatePow
    (rho : ZetaZeroSubtype) (k : Nat) :
    (1 /
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real)) <=
      1 / (max 1 |Complex.im (rho : Complex)|) ^ k := by
  have him_le :
      |Complex.im (rho : Complex)| <=
        norm (riemannWeilZeroArgument (rho : Complex)) := by
    simpa [riemannWeilZeroArgument_re] using
      Complex.abs_re_le_norm (riemannWeilZeroArgument (rho : Complex))
  have hmax :
      max 1 |Complex.im (rho : Complex)| <=
        norm (riemannWeilZeroArgument (rho : Complex)) + 2 := by
    apply max_le
    · nlinarith [norm_nonneg (riemannWeilZeroArgument (rho : Complex))]
    · exact him_le.trans (by
        nlinarith [norm_nonneg (riemannWeilZeroArgument (rho : Complex))])
  have hclamped_pos : 0 < max 1 |Complex.im (rho : Complex)| :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpow :
      (max 1 |Complex.im (rho : Complex)|) ^ k <=
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ k :=
    pow_le_pow_left₀ hclamped_pos.le hmax _
  have hinv := one_div_le_one_div_of_le (pow_pos hclamped_pos k) hpow
  simpa [Real.rpow_natCast] using hinv

/-- An eventual canonical polynomial count gives absolute convergence on the
positive zero half using the freely available decay order `degree + 1`. -/
theorem summable_norm_positiveOrdinateMultiplicityPolynomialGaussianZeroWeight_of_growth
    (growth : CanonicalMultiplicityPolynomialGrowth)
    (p : Polynomial Complex) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho.1 *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1)) := by
  let k : Nat := growth.degree + 1
  have hdegree : growth.degree < k := by simp [k]
  rcases
      norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius
        p k with
    ⟨C, hC, hshifted⟩
  have hheight := growth.positiveOrdinate_abs_summable hdegree
  have hmajorant :
      Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        C * (zetaZeroMultiplicityReal rho.1 /
          (max 1 |Complex.im (rho : Complex)|) ^ k)) :=
    hheight.mul_left C
  apply Summable.of_nonneg_of_le (fun _rho => norm_nonneg _) ?_ hmajorant
  intro rho
  have hsource := hshifted rho.1
  have hfactor := shiftedRadiusFactor_nat_le_clampedAbsOrdinatePow rho.1 k
  have hsourceHeight :
      norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1) <=
        C * (1 / (max 1 |Complex.im (rho : Complex)|) ^ k) :=
    hsource.trans (mul_le_mul_of_nonneg_left hfactor hC)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (zetaZeroMultiplicityReal_pos rho.1)]
  have hmul := mul_le_mul_of_nonneg_left hsourceHeight
    (zetaZeroMultiplicityReal_pos rho.1).le
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Conjugation transports the clamped absolute-ordinate majorant to the
negative zero half. -/
theorem CanonicalMultiplicityPolynomialGrowth.negativeOrdinate_abs_summable
    (growth : CanonicalMultiplicityPolynomialGrowth)
    {decayOrder : Nat} (hdegree : growth.degree < decayOrder) :
    Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        (max 1 |Complex.im (rho : Complex)|) ^ decayOrder) := by
  let e := positiveNegativeOrdinateZetaZeroConjEquiv
  apply e.summable_iff.mp
  refine (growth.positiveOrdinate_abs_summable hdegree).congr ?_
  intro rho
  have hmult :
      zetaZeroMultiplicityReal
          (positiveNegativeOrdinateZetaZeroConjEquiv rho).1 =
        zetaZeroMultiplicityReal rho.1 := by
    unfold zetaZeroMultiplicityReal
    exact_mod_cast zetaZeroMultiplicity_positiveNegativeConjEquiv rho
  change
    zetaZeroMultiplicityReal rho.1 /
        (max 1 |Complex.im (rho : Complex)|) ^ decayOrder =
      zetaZeroMultiplicityReal
          (positiveNegativeOrdinateZetaZeroConjEquiv rho).1 /
        (max 1 |Complex.im
          (positiveNegativeOrdinateZetaZeroConjEquiv rho : Complex)|) ^ decayOrder
  rw [hmult]
  simp [positiveNegativeOrdinateZetaZeroConjEquiv]

/-- The same eventual count gives absolute convergence on the negative half. -/
theorem summable_norm_negativeOrdinateMultiplicityPolynomialGaussianZeroWeight_of_growth
    (growth : CanonicalMultiplicityPolynomialGrowth)
    (p : Polynomial Complex) :
    Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho.1 *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1)) := by
  let k : Nat := growth.degree + 1
  have hdegree : growth.degree < k := by simp [k]
  rcases
      norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius
        p k with
    ⟨C, hC, hshifted⟩
  have hheight := growth.negativeOrdinate_abs_summable hdegree
  have hmajorant :
      Summable (fun rho : NegativeOrdinateZetaZeroSubtype =>
        C * (zetaZeroMultiplicityReal rho.1 /
          (max 1 |Complex.im (rho : Complex)|) ^ k)) :=
    hheight.mul_left C
  apply Summable.of_nonneg_of_le (fun _rho => norm_nonneg _) ?_ hmajorant
  intro rho
  have hsource := hshifted rho.1
  have hfactor := shiftedRadiusFactor_nat_le_clampedAbsOrdinatePow rho.1 k
  have hsourceHeight :
      norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1) <=
        C * (1 / (max 1 |Complex.im (rho : Complex)|) ^ k) :=
    hsource.trans (mul_le_mul_of_nonneg_left hfactor hC)
  rw [norm_mul, Real.norm_eq_abs,
    abs_of_pos (zetaZeroMultiplicityReal_pos rho.1)]
  have hmul := mul_le_mul_of_nonneg_left hsourceHeight
    (zetaZeroMultiplicityReal_pos rho.1).le
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- P0 synthetic endpoint: an eventual canonical polynomial count reaches the
actual all-zero completed-zeta absolute series with analytic multiplicity. -/
theorem summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
    (growth : CanonicalMultiplicityPolynomialGrowth)
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      norm
        (zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  let f : ZetaZeroSubtype -> Real := fun rho =>
    norm
      (zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)
  let positiveSet : Set ZetaZeroSubtype := {rho | 0 < Complex.im (rho : Complex)}
  let negativeSet : Set ZetaZeroSubtype := {rho | Complex.im (rho : Complex) < 0}
  let axisSet : Set ZetaZeroSubtype := {rho | Complex.im (rho : Complex) = 0}
  have hpositiveSubtype : Summable (fun rho : positiveSet => f rho.1) := by
    simpa [positiveSet, f] using
      summable_norm_positiveOrdinateMultiplicityPolynomialGaussianZeroWeight_of_growth
        growth p
  have hnegativeSubtype : Summable (fun rho : negativeSet => f rho.1) := by
    simpa [negativeSet, f] using
      summable_norm_negativeOrdinateMultiplicityPolynomialGaussianZeroWeight_of_growth
        growth p
  have hpositiveIndicator : Summable (positiveSet.indicator f) :=
    (summable_subtype_iff_indicator (s := positiveSet)).mp hpositiveSubtype
  have hnegativeIndicator : Summable (negativeSet.indicator f) :=
    (summable_subtype_iff_indicator (s := negativeSet)).mp hnegativeSubtype
  have haxisSupport : Function.HasFiniteSupport (axisSet.indicator f) := by
    refine (closedBallZeroResidualRealAxisFinset 1).finite_toSet.subset ?_
    intro rho hrho
    have hvalue_ne : axisSet.indicator f rho ≠ 0 := hrho
    have haxis : rho ∈ axisSet := by
      by_contra hnot
      simp [Set.indicator, hnot] at hvalue_ne
    have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := by
      intro htrivial
      apply hvalue_ne
      rw [Set.indicator_of_mem haxis]
      simp [f, guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight, htrivial]
    simpa using
      mem_closedBallZeroResidualRealAxisFinset_one_of_axis_not_trivial
        rho haxis hnotTrivial
  have haxisIndicator : Summable (axisSet.indicator f) :=
    summable_of_hasFiniteSupport haxisSupport
  have hsum := (hpositiveIndicator.add hnegativeIndicator).add haxisIndicator
  refine hsum.congr ?_
  intro rho
  rcases lt_trichotomy (Complex.im (rho : Complex)) 0 with
      hnegative | haxis | hpositive
  · simp [positiveSet, negativeSet, axisSet, f, hnegative,
      ne_of_lt hnegative, not_lt_of_ge hnegative.le]
  · simp [positiveSet, negativeSet, axisSet, f, haxis]
  · simp [positiveSet, negativeSet, axisSet, f, hpositive,
      ne_of_gt hpositive, not_lt_of_ge hpositive.le]

/-- Signed all-zero convergence from the eventual canonical count. -/
theorem summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
    (growth : CanonicalMultiplicityPolynomialGrowth)
    (p : Polynomial Complex) :
    Summable (fun rho : ZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) :=
  (summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
    growth p).of_norm

/-- P0 synthetic window endpoint from the eventual count. -/
theorem tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_of_growth
    (growth : CanonicalMultiplicityPolynomialGrowth)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        exhaustion.zetaZeroWindowSum n (fun rho : ZetaZeroSubtype =>
          zetaZeroMultiplicityReal rho *
            guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho))
      Filter.atTop
      (nhds (∑' rho : ZetaZeroSubtype,
        zetaZeroMultiplicityReal rho *
          guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) :=
  exhaustion.tendsto_zetaZeroWindowSum
    (summable_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
      growth p)

/-- P0 synthetic complementary-tail endpoint from the eventual count. -/
theorem tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_of_growth
    (growth : CanonicalMultiplicityPolynomialGrowth)
    (p : Polynomial Complex)
    (exhaustion : ComplexCompactExhaustion) :
    Filter.Tendsto
      (fun n : Nat =>
        ∑' rho :
          {rho : ZetaZeroSubtype // rho ∉ exhaustion.zetaZeroSubtypeFinset n},
          norm
            (zetaZeroMultiplicityReal rho.1 *
              guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho.1))
      Filter.atTop (nhds 0) := by
  let u : ZetaZeroSubtype -> Real := fun rho =>
    norm
      (zetaZeroMultiplicityReal rho *
        guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)
  have hu : Summable u := by
    simpa [u] using
      summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth
        growth p
  have hwindow := exhaustion.tendsto_zetaZeroWindowSum hu
  have hdiff :
      Filter.Tendsto
        (fun n : Nat => (∑' rho : ZetaZeroSubtype, u rho) -
          exhaustion.zetaZeroWindowSum n u)
        Filter.atTop (nhds 0) := by
    convert tendsto_const_nhds.sub hwindow using 1 <;> simp
  refine hdiff.congr' (Filter.Eventually.of_forall ?_)
  intro n
  rw [← hu.sum_add_tsum_subtype_compl (exhaustion.zetaZeroSubtypeFinset n)]
  simp [ComplexCompactExhaustion.zetaZeroWindowSum, u]

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
