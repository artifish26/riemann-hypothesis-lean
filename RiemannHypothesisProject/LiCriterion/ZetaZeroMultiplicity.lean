import Mathlib.Analysis.Analytic.Order
import RiemannHypothesisProject.LiCriterion.ZetaZeroHeightDecay
import RiemannHypothesisProject.ZetaConjugation

/-!
# Analytic multiplicity of actual Riemann-zeta zeroes

This module defines the multiplicity of an actual zeta zero as the analytic
order of `riemannZeta`.  It proves that this order is finite and strictly
positive, then records the finite-window distinction between counting distinct
zero locations and counting zeroes with multiplicity.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Riemann zeta is analytic at every actual zero. -/
theorem analyticAt_riemannZeta_of_zetaZeroSubtype
    (rho : ZetaZeroSubtype) :
    AnalyticAt Complex riemannZeta (rho : Complex) := by
  have hz : IsZetaZero (rho : Complex) := by
    exact mem_riemannZetaZeros.mp rho.property
  have hrho_ne_one : (rho : Complex) ≠ 1 := by
    intro hrho
    have hre := hz.re_lt_one
    rw [hrho] at hre
    norm_num at hre
  exact analyticOn_riemannZeta (rho : Complex) (by simpa using hrho_ne_one)

/-- The analytic order of zeta is finite at every actual zero. -/
theorem analyticOrderAt_riemannZeta_ne_top_of_zetaZeroSubtype
    (rho : ZetaZeroSubtype) :
    analyticOrderAt riemannZeta (rho : Complex) ≠ ⊤ := by
  let U : Set Complex := ({(1 : Complex)} : Set Complex)ᶜ
  have hU : IsPreconnected U := by
    have hrank : 1 < Module.rank Real Complex := by
      rw [Complex.rank_real_complex]
      norm_num
    exact (isConnected_compl_singleton_of_one_lt_rank
      (E := Complex) hrank (1 : Complex)).isPreconnected
  have htwo_mem : (2 : Complex) ∈ U := by
    simp [U]
  have hrho_mem : (rho : Complex) ∈ U := by
    have hz : IsZetaZero (rho : Complex) := by
      exact mem_riemannZetaZeros.mp rho.property
    have hrho_ne_one : (rho : Complex) ≠ 1 := by
      intro hrho
      have hre := hz.re_lt_one
      rw [hrho] at hre
      norm_num at hre
    simpa [U] using hrho_ne_one
  have htwo_order : analyticOrderAt riemannZeta (2 : Complex) ≠ ⊤ := by
    have htwo_analytic : AnalyticAt Complex riemannZeta (2 : Complex) :=
      analyticOn_riemannZeta (2 : Complex) (by norm_num)
    have htwo_nonzero : riemannZeta (2 : Complex) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by norm_num)
    have horder_zero : analyticOrderAt riemannZeta (2 : Complex) = 0 :=
      htwo_analytic.analyticOrderAt_eq_zero.mpr htwo_nonzero
    rw [horder_zero]
    exact ENat.coe_ne_top 0
  exact analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (f := riemannZeta) (U := U) hU
    htwo_mem hrho_mem htwo_order

/-- The actual analytic multiplicity of a Riemann-zeta zero. -/
def zetaZeroMultiplicity (rho : ZetaZeroSubtype) : Nat :=
  analyticOrderNatAt riemannZeta (rho : Complex)

/-- The analytic order is the natural-number multiplicity at an actual zero. -/
theorem analyticOrderAt_riemannZeta_eq_zetaZeroMultiplicity
    (rho : ZetaZeroSubtype) :
    analyticOrderAt riemannZeta (rho : Complex) = zetaZeroMultiplicity rho := by
  symm
  exact Nat.cast_analyticOrderNatAt
    (analyticOrderAt_riemannZeta_ne_top_of_zetaZeroSubtype rho)

/-- Every actual zeta zero has nonzero analytic multiplicity. -/
theorem zetaZeroMultiplicity_ne_zero (rho : ZetaZeroSubtype) :
    zetaZeroMultiplicity rho ≠ 0 := by
  intro hzero
  have horder_zero : analyticOrderAt riemannZeta (rho : Complex) = 0 := by
    rw [analyticOrderAt_riemannZeta_eq_zetaZeroMultiplicity, hzero]
    rfl
  have hz : riemannZeta (rho : Complex) = 0 := rho.property
  have horder_ne_zero : analyticOrderAt riemannZeta (rho : Complex) ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨analyticAt_riemannZeta_of_zetaZeroSubtype rho, hz⟩
  exact horder_ne_zero horder_zero

/-- Every actual zeta zero has analytic multiplicity at least one. -/
theorem one_le_zetaZeroMultiplicity (rho : ZetaZeroSubtype) :
    1 <= zetaZeroMultiplicity rho :=
  Nat.one_le_iff_ne_zero.mpr (zetaZeroMultiplicity_ne_zero rho)

/-- Real-valued multiplicity used in Li and shell sums. -/
def zetaZeroMultiplicityReal (rho : ZetaZeroSubtype) : Real :=
  zetaZeroMultiplicity rho

theorem one_le_zetaZeroMultiplicityReal (rho : ZetaZeroSubtype) :
    1 <= zetaZeroMultiplicityReal rho := by
  unfold zetaZeroMultiplicityReal
  exact_mod_cast one_le_zetaZeroMultiplicity rho

theorem zetaZeroMultiplicityReal_pos (rho : ZetaZeroSubtype) :
    0 < zetaZeroMultiplicityReal rho :=
  zero_lt_one.trans_le (one_le_zetaZeroMultiplicityReal rho)

/-- Multiplicity-weighted cardinality of an exact positive-ordinate window. -/
def multiplicityWeightedPositiveOrdinateHeightCount
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) : Nat :=
  ∑ rho ∈ exactWindow.window T, zetaZeroMultiplicity rho

/-- Real-valued weighted count, expressed directly over the finite window subtype. -/
def multiplicityWeightedPositiveOrdinateHeightCountReal
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) : Real :=
  ∑ rho : {rho : ZetaZeroSubtype // rho ∈ exactWindow.window T},
    zetaZeroMultiplicityReal rho.1

/-- Distinct-zero cardinality is bounded by multiplicity-weighted cardinality. -/
theorem card_exactPositiveOrdinateHeightWindow_le_multiplicityWeighted
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) :
    (exactWindow.window T).card <=
      multiplicityWeightedPositiveOrdinateHeightCount exactWindow T := by
  rw [Finset.card_eq_sum_ones]
  unfold multiplicityWeightedPositiveOrdinateHeightCount
  exact Finset.sum_le_sum (fun rho _hrho => one_le_zetaZeroMultiplicity rho)

/--
The real exact count is bounded by the real multiplicity-weighted count.  The
reverse inequality does not follow from finite-window semantics and must not be
used when importing a classical multiplicity-counted `N(T)` theorem.
-/
theorem exactPositiveOrdinateHeightCount_le_multiplicityWeighted
    {heightCount : Real -> Real}
    (exactWindow : ExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) :
    heightCount T <=
      (multiplicityWeightedPositiveOrdinateHeightCount exactWindow T : Real) := by
  rw [exactWindow.heightCount_eq_card]
  exact_mod_cast
    card_exactPositiveOrdinateHeightWindow_le_multiplicityWeighted exactWindow T

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
