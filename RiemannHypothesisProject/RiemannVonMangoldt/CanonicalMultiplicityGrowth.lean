import RiemannHypothesisProject.LiCriterion.MultiplicityHeightDecay
import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalMultiplicityCount

/-!
# Eventual growth of the canonical multiplicity count

The p-series argument only needs an eventual polynomial bound for the
canonical positive-ordinate zeta-zero count with analytic multiplicity.  This
module records that weak source statement explicitly, absorbs the finitely
many dyadic shells below its threshold, and proves the arbitrary-order dyadic
summability lemma used by polynomial-Gaussian decay.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- An eventual polynomial bound for the actual analytic-multiplicity count. -/
structure CanonicalMultiplicityPolynomialGrowth where
  countConstant : Real
  threshold : Real
  degree : Nat
  countConstant_nonneg : 0 <= countConstant
  count_le : forall T : Real,
    threshold <= T ->
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T <=
        countConstant * (T + 1) ^ degree

/-- Every eventual canonical polynomial count admits one global dyadic bound.
The new constant contains the finite prefix below the source threshold. -/
theorem CanonicalMultiplicityPolynomialGrowth.exists_global_dyadic_bound
    (growth : CanonicalMultiplicityPolynomialGrowth) :
    exists A : Real, 0 <= A /\
      forall m : Nat,
        canonicalPositiveOrdinateZetaZeroMultiplicityCount
            ((2 : Real) ^ (m + 1)) <=
          A * (((2 : Real) ^ (m + 1) + 1) ^ growth.degree) := by
  have heventual : ∀ᶠ n : Nat in Filter.atTop,
      growth.threshold <= (2 : Real) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 2)).eventually_ge_atTop
      growth.threshold
  rcases heventual.exists with ⟨M, hM⟩
  let prefixMass : Real :=
    ∑ m ∈ Finset.range M,
      canonicalPositiveOrdinateZetaZeroMultiplicityCount ((2 : Real) ^ (m + 1))
  let A : Real := growth.countConstant + prefixMass
  have hprefix_nonneg : 0 <= prefixMass := by
    dsimp [prefixMass]
    exact Finset.sum_nonneg fun m _ =>
      canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg _
  have hA_nonneg : 0 <= A := by
    dsimp [A]
    exact add_nonneg growth.countConstant_nonneg hprefix_nonneg
  refine ⟨A, hA_nonneg, ?_⟩
  intro m
  have hfactor_one :
      1 <= (((2 : Real) ^ (m + 1) + 1) ^ growth.degree) := by
    apply one_le_pow₀
    have hpow_nonneg : 0 <= (2 : Real) ^ (m + 1) := by positivity
    linarith
  by_cases hm : m < M
  · have hm_mem : m ∈ Finset.range M := Finset.mem_range.mpr hm
    have hterm_nonneg : ∀ i ∈ Finset.range M,
        0 <= canonicalPositiveOrdinateZetaZeroMultiplicityCount
          ((2 : Real) ^ (i + 1)) := by
      intro i _hi
      exact canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg _
    have hcount_prefix :
        canonicalPositiveOrdinateZetaZeroMultiplicityCount
            ((2 : Real) ^ (m + 1)) <= prefixMass := by
      dsimp [prefixMass]
      exact Finset.single_le_sum hterm_nonneg hm_mem
    calc
      canonicalPositiveOrdinateZetaZeroMultiplicityCount
          ((2 : Real) ^ (m + 1)) <= prefixMass := hcount_prefix
      _ <= A := by dsimp [A]; linarith [growth.countConstant_nonneg]
      _ <= A * (((2 : Real) ^ (m + 1) + 1) ^ growth.degree) := by
        nlinarith
  · have hMm : M <= m := Nat.le_of_not_gt hm
    have hpowM : (2 : Real) ^ M <= (2 : Real) ^ (m + 1) :=
      pow_le_pow_right₀ (by norm_num) (hMm.trans (Nat.le_add_right m 1))
    have hsource := growth.count_le ((2 : Real) ^ (m + 1)) (hM.trans hpowM)
    have hC_le_A : growth.countConstant <= A := by
      dsimp [A]
      linarith
    exact hsource.trans
      (mul_le_mul_of_nonneg_right hC_le_A (by positivity))

/-- A global dyadic polynomial count and a strictly larger decay order give
multiplicity-weighted summability on the positive zero half. -/
theorem positiveOrdinateZetaZero_multiplicityClampedHeightDecay_summable_of_exactCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (C : Real) (degree decayOrder : Nat)
    (hC_nonneg : 0 <= C) (hdegree : degree < decayOrder)
    (hcount : forall m : Nat,
      multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
          ((2 : Real) ^ (m + 1)) <=
        C * (((2 : Real) ^ (m + 1) + 1) ^ degree)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        positiveOrdinateZetaZeroClampedHeight rho ^ decayOrder) := by
  let fiber : Nat -> Type := fun m =>
    PositiveOrdinateZetaZeroClampedDyadicShell m
  let fiberFintype : forall m : Nat, Fintype (fiber m) := fun m =>
    positiveOrdinateZetaZeroClampedDyadicShellFintype exactWindow m
  let shellMass : Nat -> Real := fun m =>
    ∑' rho : fiber m, zetaZeroMultiplicityReal rho.1.1
  let ratio : Real := (2 : Real) ^ degree / (2 : Real) ^ decayOrder
  have hratio_nonneg : 0 <= ratio := by
    dsimp [ratio]
    positivity
  have hratio_lt_one : ratio < 1 := by
    rw [div_lt_one (by positivity : (0 : Real) < 2 ^ decayOrder)]
    exact pow_lt_pow_right₀ (by norm_num : (1 : Real) < 2) hdegree
  have hmajorant : Summable (fun m : Nat =>
      (C * (2 : Real) ^ (2 * degree)) * ratio ^ m) :=
    (summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).mul_left
      (C * (2 : Real) ^ (2 * degree))
  have hshell_summable : Summable (fun m : Nat =>
      ∑' rho : fiber m,
        zetaZeroMultiplicityReal rho.1.1 /
          positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
    · intro m
      exact tsum_nonneg fun rho => div_nonneg
        (zetaZeroMultiplicityReal_pos rho.1.1).le
        (pow_nonneg (by
          unfold positiveOrdinateZetaZeroClampedHeight
          exact (zero_le_one.trans (le_max_left (1 : Real) _))) _)
    · intro m
      letI : Fintype (fiber m) := fiberFintype m
      have hshell_le :=
        positiveOrdinateZetaZeroClampedShellMultiplicity_le_weightedWindow
          exactWindow m
      have hcumulative := hcount m
      have hlower (rho : fiber m) :
          (2 : Real) ^ m <= positiveOrdinateZetaZeroClampedHeight rho.1 := by
        simpa [rho.2] using
          positiveOrdinateZetaZeroClampedDyadicShellIndex_lower rho.1
      have hpow_lower (rho : fiber m) :
          ((2 : Real) ^ m) ^ decayOrder <=
            positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder :=
        pow_le_pow_left₀ (by positivity) (hlower rho) _
      have hpoint (rho : fiber m) :
          zetaZeroMultiplicityReal rho.1.1 /
              positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder <=
            zetaZeroMultiplicityReal rho.1.1 / ((2 : Real) ^ m) ^ decayOrder := by
        exact div_le_div_of_nonneg_left
          (zetaZeroMultiplicityReal_pos rho.1.1).le (by positivity) (hpow_lower rho)
      have hsum_le :
          (∑' rho : fiber m,
              zetaZeroMultiplicityReal rho.1.1 /
                positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) <=
            shellMass m / ((2 : Real) ^ m) ^ decayOrder := by
        rw [tsum_fintype]
        calc
          (∑ rho : fiber m,
              zetaZeroMultiplicityReal rho.1.1 /
                positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) <=
              ∑ rho : fiber m,
                zetaZeroMultiplicityReal rho.1.1 / ((2 : Real) ^ m) ^ decayOrder :=
            Finset.sum_le_sum fun rho _ => hpoint rho
          _ = shellMass m / ((2 : Real) ^ m) ^ decayOrder := by
            simp [shellMass, tsum_fintype, Finset.sum_div]
      calc
        (∑' rho : fiber m,
            zetaZeroMultiplicityReal rho.1.1 /
              positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) <=
            shellMass m / ((2 : Real) ^ m) ^ decayOrder := hsum_le
        _ <= (C * (((2 : Real) ^ (m + 1) + 1) ^ degree)) /
              ((2 : Real) ^ m) ^ decayOrder := by
          exact div_le_div_of_nonneg_right (hshell_le.trans hcumulative) (by positivity)
        _ <= (C * ((2 : Real) ^ (m + 2)) ^ degree) /
              ((2 : Real) ^ m) ^ decayOrder := by
          have hpow_one : (1 : Real) <= (2 : Real) ^ (m + 1) := by
            exact one_le_pow₀ (by norm_num)
          have hadd : (2 : Real) ^ (m + 1) + 1 <= (2 : Real) ^ (m + 2) := by
            calc
              (2 : Real) ^ (m + 1) + 1 <=
                  (2 : Real) ^ (m + 1) + (2 : Real) ^ (m + 1) :=
                by nlinarith
              _ = (2 : Real) ^ (m + 2) := by
                rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
                ring
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hadd _)
              hC_nonneg) (by positivity)
        _ = (C * (2 : Real) ^ (2 * degree)) * ratio ^ m := by
          have hden_ne : (((2 : Real) ^ m) ^ decayOrder) ≠ 0 := by positivity
          have hratio_den_ne : (((2 : Real) ^ decayOrder) ^ m) ≠ 0 := by positivity
          have hfour : (4 : Real) ^ degree = ((2 : Real) ^ degree) ^ 2 := by
            calc
              (4 : Real) ^ degree = (((2 : Real) ^ 2) ^ degree) := by norm_num
              _ = (2 : Real) ^ (2 * degree) := by rw [pow_mul]
              _ = (2 : Real) ^ (degree * 2) := by rw [Nat.mul_comm]
              _ = ((2 : Real) ^ degree) ^ 2 := by rw [pow_mul]
          have hdegree_two :
              (2 : Real) ^ (degree * 2) = ((2 : Real) ^ degree) ^ 2 := by
            rw [pow_mul]
          dsimp [ratio]
          rw [div_pow]
          field_simp [hden_ne, hratio_den_ne]
          ring_nf
          rw [hfour, hdegree_two]
  let shellEquiv : Sigma fiber ≃ PositiveOrdinateZetaZeroSubtype :=
    Equiv.sigmaFiberEquiv positiveOrdinateZetaZeroClampedDyadicShellIndex
  have hsigma : Summable (fun p : Sigma fiber =>
      zetaZeroMultiplicityReal p.2.1.1 /
        positiveOrdinateZetaZeroClampedHeight p.2.1 ^ decayOrder) := by
    have hnonneg : forall p : Sigma fiber,
        0 <= zetaZeroMultiplicityReal p.2.1.1 /
          positiveOrdinateZetaZeroClampedHeight p.2.1 ^ decayOrder := by
      intro p
      exact div_nonneg (zetaZeroMultiplicityReal_pos p.2.1.1).le
        (pow_nonneg (by
          unfold positiveOrdinateZetaZeroClampedHeight
          exact (zero_le_one.trans (le_max_left (1 : Real) _))) _)
    refine (summable_sigma_of_nonneg hnonneg).2 ⟨?_, hshell_summable⟩
    intro m
    letI : Fintype (fiber m) := fiberFintype m
    exact (hasSum_fintype _).summable
  apply shellEquiv.summable_iff.mp
  refine hsigma.congr ?_
  rintro ⟨m, rho⟩
  simp [shellEquiv, fiber, Function.comp_apply]

/-- A global dyadic count with a nonnegative real exponent strictly below the
integer decay order gives multiplicity-weighted summability.  Unlike the
natural-degree variant, this theorem preserves a subquadratic exponent such
as `3 / 2` all the way through the shell ratio. -/
theorem positiveOrdinateZetaZero_multiplicityClampedHeightDecay_summable_of_exactCount_rpow
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (C degree : Real) (decayOrder : Nat)
    (hC_nonneg : 0 <= C) (hdegree_nonneg : 0 <= degree)
    (hdegree : degree < decayOrder)
    (hcount : forall m : Nat,
      multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
          ((2 : Real) ^ (m + 1)) <=
        C * (((2 : Real) ^ (m + 1) + 1) ^ degree)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        positiveOrdinateZetaZeroClampedHeight rho ^ decayOrder) := by
  let fiber : Nat -> Type := fun m =>
    PositiveOrdinateZetaZeroClampedDyadicShell m
  let fiberFintype : forall m : Nat, Fintype (fiber m) := fun m =>
    positiveOrdinateZetaZeroClampedDyadicShellFintype exactWindow m
  let shellMass : Nat -> Real := fun m =>
    ∑' rho : fiber m, zetaZeroMultiplicityReal rho.1.1
  let ratio : Real := (2 : Real) ^ degree / (2 : Real) ^ decayOrder
  have hratio_nonneg : 0 <= ratio := by
    dsimp [ratio]
    positivity
  have hratio_lt_one : ratio < 1 := by
    dsimp [ratio]
    rw [div_lt_one (by positivity : (0 : Real) < 2 ^ decayOrder)]
    rw [← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hdegree
  have hmajorant : Summable (fun m : Nat =>
      (C * (2 : Real) ^ (2 * degree)) * ratio ^ m) :=
    (summable_geometric_of_lt_one hratio_nonneg hratio_lt_one).mul_left
      (C * (2 : Real) ^ (2 * degree))
  have hshell_summable : Summable (fun m : Nat =>
      ∑' rho : fiber m,
        zetaZeroMultiplicityReal rho.1.1 /
          positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hmajorant
    · intro m
      exact tsum_nonneg fun rho => div_nonneg
        (zetaZeroMultiplicityReal_pos rho.1.1).le
        (pow_nonneg (by
          unfold positiveOrdinateZetaZeroClampedHeight
          exact (zero_le_one.trans (le_max_left (1 : Real) _))) _)
    · intro m
      letI : Fintype (fiber m) := fiberFintype m
      have hshell_le :=
        positiveOrdinateZetaZeroClampedShellMultiplicity_le_weightedWindow
          exactWindow m
      have hcumulative := hcount m
      have hlower (rho : fiber m) :
          (2 : Real) ^ m <= positiveOrdinateZetaZeroClampedHeight rho.1 := by
        simpa [rho.2] using
          positiveOrdinateZetaZeroClampedDyadicShellIndex_lower rho.1
      have hpow_lower (rho : fiber m) :
          ((2 : Real) ^ m) ^ decayOrder <=
            positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder :=
        pow_le_pow_left₀ (by positivity) (hlower rho) _
      have hpoint (rho : fiber m) :
          zetaZeroMultiplicityReal rho.1.1 /
              positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder <=
            zetaZeroMultiplicityReal rho.1.1 / ((2 : Real) ^ m) ^ decayOrder := by
        exact div_le_div_of_nonneg_left
          (zetaZeroMultiplicityReal_pos rho.1.1).le (by positivity) (hpow_lower rho)
      have hsum_le :
          (∑' rho : fiber m,
              zetaZeroMultiplicityReal rho.1.1 /
                positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) <=
            shellMass m / ((2 : Real) ^ m) ^ decayOrder := by
        rw [tsum_fintype]
        calc
          (∑ rho : fiber m,
              zetaZeroMultiplicityReal rho.1.1 /
                positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) <=
              ∑ rho : fiber m,
                zetaZeroMultiplicityReal rho.1.1 / ((2 : Real) ^ m) ^ decayOrder :=
            Finset.sum_le_sum fun rho _ => hpoint rho
          _ = shellMass m / ((2 : Real) ^ m) ^ decayOrder := by
            simp [shellMass, tsum_fintype, Finset.sum_div]
      have hpow_one : (1 : Real) <= (2 : Real) ^ (m + 1) := by
        exact one_le_pow₀ (by norm_num)
      have hadd : (2 : Real) ^ (m + 1) + 1 <= (2 : Real) ^ (m + 2) := by
        calc
          (2 : Real) ^ (m + 1) + 1 <=
              (2 : Real) ^ (m + 1) + (2 : Real) ^ (m + 1) := by
            nlinarith
          _ = (2 : Real) ^ (m + 2) := by
            rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
            ring
      have hrpow_add :
          ((2 : Real) ^ (m + 1) + 1) ^ degree <=
            ((2 : Real) ^ (m + 2)) ^ degree :=
        Real.rpow_le_rpow (by positivity) hadd hdegree_nonneg
      have hnum : ((2 : Real) ^ (m + 2)) ^ degree =
          (2 : Real) ^ (2 * degree) * (((2 : Real) ^ degree) ^ m) := by
        have hpow : (((2 : Real) ^ degree) ^ m) =
            (2 : Real) ^ (degree * (m : Real)) := by
          rw [← Real.rpow_natCast]
          rw [Real.rpow_mul (by positivity)]
        rw [hpow]
        rw [← Real.rpow_add (by positivity)]
        calc
          ((2 : Real) ^ (m + 2)) ^ degree =
              ((2 : Real) ^ ((m + 2 : Nat) : Real)) ^ degree := by
            rw [Real.rpow_natCast]
          _ = (2 : Real) ^ (((m + 2 : Nat) : Real) * degree) := by
            rw [Real.rpow_mul (by positivity)]
          _ = (2 : Real) ^ (2 * degree + degree * (m : Real)) := by
            congr 1
            push_cast
            ring
      have hden : ((2 : Real) ^ m) ^ decayOrder =
          (((2 : Real) ^ decayOrder) ^ m) := by
        calc
          ((2 : Real) ^ m) ^ decayOrder = (2 : Real) ^ (m * decayOrder) := by
            rw [pow_mul]
          _ = (2 : Real) ^ (decayOrder * m) := by rw [Nat.mul_comm]
          _ = ((2 : Real) ^ decayOrder) ^ m := by rw [pow_mul]
      calc
        (∑' rho : fiber m,
            zetaZeroMultiplicityReal rho.1.1 /
              positiveOrdinateZetaZeroClampedHeight rho.1 ^ decayOrder) <=
            shellMass m / ((2 : Real) ^ m) ^ decayOrder := hsum_le
        _ <= (C * (((2 : Real) ^ (m + 1) + 1) ^ degree)) /
              ((2 : Real) ^ m) ^ decayOrder := by
          exact div_le_div_of_nonneg_right (hshell_le.trans hcumulative) (by positivity)
        _ <= (C * ((2 : Real) ^ (m + 2)) ^ degree) /
              ((2 : Real) ^ m) ^ decayOrder := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrpow_add hC_nonneg) (by positivity)
        _ = (C * (2 : Real) ^ (2 * degree)) * ratio ^ m := by
          dsimp [ratio]
          rw [hnum, div_pow, hden]
          field_simp
  let shellEquiv : Sigma fiber ≃ PositiveOrdinateZetaZeroSubtype :=
    Equiv.sigmaFiberEquiv positiveOrdinateZetaZeroClampedDyadicShellIndex
  have hsigma : Summable (fun p : Sigma fiber =>
      zetaZeroMultiplicityReal p.2.1.1 /
        positiveOrdinateZetaZeroClampedHeight p.2.1 ^ decayOrder) := by
    have hnonneg : forall p : Sigma fiber,
        0 <= zetaZeroMultiplicityReal p.2.1.1 /
          positiveOrdinateZetaZeroClampedHeight p.2.1 ^ decayOrder := by
      intro p
      exact div_nonneg (zetaZeroMultiplicityReal_pos p.2.1.1).le
        (pow_nonneg (by
          unfold positiveOrdinateZetaZeroClampedHeight
          exact (zero_le_one.trans (le_max_left (1 : Real) _))) _)
    refine (summable_sigma_of_nonneg hnonneg).2 ⟨?_, hshell_summable⟩
    intro m
    letI : Fintype (fiber m) := fiberFintype m
    exact (hasSum_fintype _).summable
  apply shellEquiv.summable_iff.mp
  refine hsigma.congr ?_
  rintro ⟨m, rho⟩
  simp [shellEquiv, fiber, Function.comp_apply]

/-- The eventual source proposition supplies the global dyadic hypothesis for
the arbitrary-order multiplicity shell theorem. -/
theorem CanonicalMultiplicityPolynomialGrowth.positiveOrdinate_summable
    (growth : CanonicalMultiplicityPolynomialGrowth)
    {decayOrder : Nat} (hdegree : growth.degree < decayOrder) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        positiveOrdinateZetaZeroClampedHeight rho ^ decayOrder) := by
  rcases growth.exists_global_dyadic_bound with ⟨A, hA, hdyadic⟩
  exact
    positiveOrdinateZetaZero_multiplicityClampedHeightDecay_summable_of_exactCount
      canonicalExactPositiveOrdinateZetaZeroWindow A growth.degree decayOrder
      hA hdegree hdyadic

/-- On the positive zero half the clamped height is the clamped absolute
ordinate.  This symmetric form transports directly to negative ordinates. -/
theorem CanonicalMultiplicityPolynomialGrowth.positiveOrdinate_abs_summable
    (growth : CanonicalMultiplicityPolynomialGrowth)
    {decayOrder : Nat} (hdegree : growth.degree < decayOrder) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 /
        (max 1 |Complex.im (rho : Complex)|) ^ decayOrder) := by
  refine (growth.positiveOrdinate_summable hdegree).congr ?_
  intro rho
  rw [abs_of_pos rho.property]
  rfl

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
