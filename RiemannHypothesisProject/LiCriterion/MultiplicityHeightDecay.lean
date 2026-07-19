import RiemannHypothesisProject.LiCriterion.CanonicalZetaZeroHeightDecay
import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicity

/-!
# Multiplicity-aware zeta-zero height decay

This module runs the clamped dyadic shell argument with the actual analytic
multiplicity of each Riemann-zeta zero.  The cumulative hypothesis is explicitly
multiplicity-weighted, matching the classical meaning of `N(T)`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- A clamped shell's total analytic multiplicity is bounded by the enclosing window's. -/
theorem positiveOrdinateZetaZeroClampedShellMultiplicity_le_weightedWindow
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (m : Nat) :
    (∑' rho : PositiveOrdinateZetaZeroClampedDyadicShell m,
        zetaZeroMultiplicityReal rho.1.1) <=
      multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
        ((2 : Real) ^ (m + 1)) := by
  letI : Fintype (PositiveOrdinateZetaZeroClampedDyadicShell m) :=
    positiveOrdinateZetaZeroClampedDyadicShellFintype exactWindow m
  let windowSubtype :=
    {rho : ZetaZeroSubtype //
      rho ∈ exactWindow.window ((2 : Real) ^ (m + 1))}
  let e : PositiveOrdinateZetaZeroClampedDyadicShell m ↪ windowSubtype :=
    positiveOrdinateZetaZeroClampedDyadicShellEmbedding exactWindow m
  let shellImage : Finset windowSubtype := Finset.univ.map e
  have hsubset : shellImage ⊆ Finset.univ := Finset.subset_univ _
  calc
    (∑' rho : PositiveOrdinateZetaZeroClampedDyadicShell m,
        zetaZeroMultiplicityReal rho.1.1) =
        ∑ rho : PositiveOrdinateZetaZeroClampedDyadicShell m,
          zetaZeroMultiplicityReal rho.1.1 := by rw [tsum_fintype]
    _ = ∑ rho ∈ shellImage, zetaZeroMultiplicityReal rho.1 := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro rho _hrho
      rfl
    _ <= ∑ rho : windowSubtype, zetaZeroMultiplicityReal rho.1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun rho _hmem _hnot => (zetaZeroMultiplicityReal_pos rho.1).le)
    _ = multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
          ((2 : Real) ^ (m + 1)) := by
      rfl

/--
A multiplicity-weighted cumulative dyadic count gives multiplicity-aware
inverse-square summability over all actual positive-ordinate zeta zeroes.
-/
theorem positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_exactCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
            ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1)))) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
  let fiber : Nat -> Type := fun m =>
    PositiveOrdinateZetaZeroClampedDyadicShell m
  let fiberFintype : forall m : Nat, Fintype (fiber m) := fun m =>
    positiveOrdinateZetaZeroClampedDyadicShellFintype exactWindow m
  let height : Sigma fiber -> Real := fun p =>
    positiveOrdinateZetaZeroClampedHeight p.2.1
  let multiplicity : Sigma fiber -> Real := fun p =>
    zetaZeroMultiplicityReal p.2.1.1
  let shellMass : Nat -> Real := fun m =>
    ∑' rho : fiber m, zetaZeroMultiplicityReal rho.1.1
  let cumulativeMass : Nat -> Real := fun m =>
    multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
      ((2 : Real) ^ (m + 1))
  have hsigma :
      Summable (fun p : Sigma fiber =>
        multiplicity p *
          (height p ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) := by
    apply criticalLineShellHeightDecay_summable_of_cumulativeDyadicTlogTBound
      height multiplicity fiberFintype shellMass cumulativeMass C
    · intro p
      exact (zetaZeroMultiplicityReal_pos p.2.1.1).le
    · intro p
      have hpos : 0 < height p := by
        simp [height, positiveOrdinateZetaZeroClampedHeight]
      simpa [height, fiber, abs_of_pos hpos, p.2.2] using
        positiveOrdinateZetaZeroClampedDyadicShellIndex_lower p.2.1
    · intro m
      rfl
    · exact hC_nonneg
    · intro m
      exact positiveOrdinateZetaZeroClampedShellMultiplicity_le_weightedWindow
        exactWindow m
    · exact hcount
  let shellEquiv : Sigma fiber ≃ PositiveOrdinateZetaZeroSubtype :=
    Equiv.sigmaFiberEquiv positiveOrdinateZetaZeroClampedDyadicShellIndex
  have hclamped :
      Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        zetaZeroMultiplicityReal rho.1 *
          (positiveOrdinateZetaZeroClampedHeight rho ^ 2 +
            (1 / 2 : Real) ^ 2)⁻¹) := by
    apply shellEquiv.summable_iff.mp
    refine hsigma.congr ?_
    rintro ⟨m, rho⟩
    simp [multiplicity, height, shellEquiv, fiber, Function.comp_apply]
  have hfive := Summable.mul_left (5 : Real) hclamped
  refine Summable.of_nonneg_of_le ?_ ?_ hfive
  · intro rho
    exact mul_nonneg (zetaZeroMultiplicityReal_pos rho.1).le (by positivity)
  · intro rho
    have hbound := positiveOrdinateZetaZero_heightDecay_le_five_mul_clamped rho
    have hmul := mul_le_mul_of_nonneg_left hbound
      (zetaZeroMultiplicityReal_pos rho.1).le
    nlinarith

/-- The multiplicity-aware positive-zero Li coefficient. -/
def positiveOrdinateZetaZeroMultiplicityLiCoefficient (n : Nat) : Real :=
  ∑' rho : PositiveOrdinateZetaZeroSubtype,
    zetaZeroMultiplicityReal rho.1 * zetaZeroLiSummand rho.1 n

/--
Multiplicity-weighted counting and critical-line geometry give a summable,
nonnegative actual positive-zero Li coefficient.
-/
theorem positiveOrdinateZetaZeroMultiplicityLiCoefficient_summable_and_nonneg
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (C : Real) (hC_nonneg : 0 <= C)
    (hcount :
      forall m : Nat,
        multiplicityWeightedPositiveOrdinateHeightCountReal exactWindow
            ((2 : Real) ^ (m + 1)) <=
          C * (((m : Real) + 2) * ((2 : Real) ^ (m + 1))))
    (n : Nat)
    (hcritical :
      forall rho : PositiveOrdinateZetaZeroSubtype,
        IsCriticalLine (rho : Complex)) :
    Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
        zetaZeroMultiplicityReal rho.1 * zetaZeroLiSummand rho.1 n) ∧
      0 <= positiveOrdinateZetaZeroMultiplicityLiCoefficient n := by
  have hdecay :=
    positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_exactCount
      exactWindow C hC_nonneg hcount
  let majorant : PositiveOrdinateZetaZeroSubtype -> Real := fun rho =>
    ((n : Real) ^ 2 / 2) *
      (zetaZeroMultiplicityReal rho.1 *
        (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹)
  have hmajorant : Summable majorant := by
    simpa [majorant] using Summable.mul_left ((n : Real) ^ 2 / 2) hdecay
  constructor
  · exact
      @Summable.of_nonneg_of_le PositiveOrdinateZetaZeroSubtype majorant
        (fun rho =>
          zetaZeroMultiplicityReal rho.1 * zetaZeroLiSummand rho.1 n)
        (fun rho => by
          exact mul_nonneg (zetaZeroMultiplicityReal_pos rho.1).le (by
            rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
            exact criticalLineLiSummand_nonneg (Complex.im (rho : Complex)) n))
        (fun rho => by
          rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
          have hbound := criticalLineLiSummand_le_quadratic_height_decay
            (Complex.im (rho : Complex)) n
          have hmul := mul_le_mul_of_nonneg_left hbound
            (zetaZeroMultiplicityReal_pos rho.1).le
          calc
            zetaZeroMultiplicityReal rho.1 *
                criticalLineLiSummand (Complex.im (rho : Complex)) n <=
              zetaZeroMultiplicityReal rho.1 *
                (((n : Real) ^ 2 / 2) *
                  (Complex.im (rho : Complex) ^ 2 + (1 / 2 : Real) ^ 2)⁻¹) :=
              hmul
            _ = majorant rho := by simp [majorant]; ring)
        hmajorant
  · unfold positiveOrdinateZetaZeroMultiplicityLiCoefficient
    exact tsum_nonneg (fun rho =>
      mul_nonneg (zetaZeroMultiplicityReal_pos rho.1).le (by
        rw [zetaZeroLiSummand_eq_criticalLineLiSummand rho.1 n (hcritical rho)]
        exact criticalLineLiSummand_nonneg (Complex.im (rho : Complex)) n))

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
