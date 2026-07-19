import RiemannHypothesisProject.RiemannVonMangoldt.CanonicalPositiveOrdinateCount
import RiemannHypothesisProject.LiCriterion.ZetaZeroMultiplicity

/-!
# Canonical multiplicity-aware positive-ordinate zero count

Bellotti-Wong's `N(T)` is obtained by the argument principle and therefore
counts zeroes with analytic multiplicity.  The canonical finite window in
`CanonicalPositiveOrdinateCount` records distinct zero locations.  This module
puts the analytic multiplicity on that exact window and records the correct
source theorem target without assuming that every zeta zero is simple.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The canonical distinct-zero window, transported to `ZetaZeroSubtype`. -/
noncomputable def canonicalExactPositiveOrdinateZetaZeroWindow :
    ExactPositiveOrdinateHeightCountWindow
      canonicalPositiveOrdinateZetaZeroCount :=
  canonicalSourceExactPositiveOrdinateHeightCountWindow
    |>.toExactPositiveOrdinateHeightCountWindow

/-- Bellotti-Wong's canonical `N(T)`: the sum of analytic multiplicities over
the actual zeta zeroes with `0 < Im rho <= T`. -/
noncomputable def canonicalPositiveOrdinateZetaZeroMultiplicityCount
    (T : Real) : Real :=
  multiplicityWeightedPositiveOrdinateHeightCountReal
    canonicalExactPositiveOrdinateZetaZeroWindow T

/-- The canonical multiplicity count is a finite sum of nonnegative terms. -/
theorem canonicalPositiveOrdinateZetaZeroMultiplicityCount_nonneg
    (T : Real) :
    0 <= canonicalPositiveOrdinateZetaZeroMultiplicityCount T := by
  unfold canonicalPositiveOrdinateZetaZeroMultiplicityCount
  exact Finset.sum_nonneg (fun _ _ => (zetaZeroMultiplicityReal_pos _).le)

/-- The distinct-location count is bounded by the argument-principle count.
Equality would require simplicity and is deliberately not asserted. -/
theorem canonicalPositiveOrdinateZetaZeroCount_le_multiplicityCount
    (T : Real) :
    canonicalPositiveOrdinateZetaZeroCount T <=
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T := by
  rw [canonicalExactPositiveOrdinateZetaZeroWindow.heightCount_eq_card T]
  unfold canonicalPositiveOrdinateZetaZeroMultiplicityCount
  unfold multiplicityWeightedPositiveOrdinateHeightCountReal
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  calc
    (∑ rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window T,
        ((1 : Nat) : Real)) <=
        ∑ rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window T,
          zetaZeroMultiplicityReal rho := by
      exact Finset.sum_le_sum
        (fun rho _hrho => by
          simpa using one_le_zetaZeroMultiplicityReal rho)
    _ = ∑ rho :
          {rho : ZetaZeroSubtype //
            rho ∈ canonicalExactPositiveOrdinateZetaZeroWindow.window T},
          zetaZeroMultiplicityReal rho.1 := by
      rw [← Finset.sum_attach]
      simp only [Finset.attach_eq_univ]

/-- Every finite positive-ordinate zeta-zero window is bounded by the
canonical multiplicity-counted `N(T)`. -/
theorem positiveFiniteWindow_card_le_canonicalMultiplicityCount
    (s : Finset ZetaZeroSubtype) (T : Real)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    ((s.card : Nat) : Real) <=
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T := by
  have hsubset :
      s ⊆ canonicalExactPositiveOrdinateZetaZeroWindow.window T := by
    intro rho hrho
    exact
      (canonicalExactPositiveOrdinateZetaZeroWindow.mem_window_iff T rho).mpr
        (hs rho hrho)
  have hcard :
      ((s.card : Nat) : Real) <= canonicalPositiveOrdinateZetaZeroCount T := by
    rw [canonicalExactPositiveOrdinateZetaZeroWindow.heightCount_eq_card T]
    exact_mod_cast Finset.card_le_card hsubset
  exact hcard.trans
    (canonicalPositiveOrdinateZetaZeroCount_le_multiplicityCount T)

/-- The exact Bellotti-Wong source theorem in the project's canonical,
multiplicity-aware normalization. -/
def BellottiWongCanonicalMultiplicityNTTheorem : Prop :=
  forall T : Real,
    bellottiWongValidFrom <= T ->
      |canonicalPositiveOrdinateZetaZeroMultiplicityCount T -
          riemannVonMangoldtMainTerm T| <=
        bellottiWongErrorTerm T

/-- The published multiplicity estimate gives the upper bound needed for the
distinct canonical zero window, without any simplicity hypothesis. -/
theorem canonicalPositiveOrdinateZetaZeroCount_le_main_add_error
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    {T : Real} (hT : bellottiWongValidFrom <= T) :
    canonicalPositiveOrdinateZetaZeroCount T <=
      riemannVonMangoldtMainTerm T + bellottiWongErrorTerm T := by
  have hmult := hpublished T hT
  have hupper :
      canonicalPositiveOrdinateZetaZeroMultiplicityCount T <=
        riemannVonMangoldtMainTerm T + bellottiWongErrorTerm T := by
    have := (le_abs_self
      (canonicalPositiveOrdinateZetaZeroMultiplicityCount T -
        riemannVonMangoldtMainTerm T)).trans hmult
    linarith
  exact
    (canonicalPositiveOrdinateZetaZeroCount_le_multiplicityCount T).trans hupper

/-- Bellotti-Wong's multiplicity-counted theorem bounds every finite
positive-ordinate zeta-zero window by the published main term and error. -/
theorem positiveFiniteWindow_card_le_main_add_error
    (hpublished : BellottiWongCanonicalMultiplicityNTTheorem)
    (s : Finset ZetaZeroSubtype) {T : Real}
    (hT : bellottiWongValidFrom <= T)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    ((s.card : Nat) : Real) <=
      riemannVonMangoldtMainTerm T + bellottiWongErrorTerm T := by
  exact
    (positiveFiniteWindow_card_le_canonicalMultiplicityCount s T hs).trans
      (by
        have hmult := hpublished T hT
        have := (le_abs_self
          (canonicalPositiveOrdinateZetaZeroMultiplicityCount T -
            riemannVonMangoldtMainTerm T)).trans hmult
        linarith)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
