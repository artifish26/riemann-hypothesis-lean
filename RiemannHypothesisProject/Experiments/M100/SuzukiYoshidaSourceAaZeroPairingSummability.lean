import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaLocalizedWeilForm

/-!
# M100-DF6F diagonal reduction for the source zero pairing

The literal localized Weil form currently exposes absolute summability of
every polarized zero-pairing family.  This module reduces that two-input
condition to the literature-shaped diagonal square summability of each
transported entire transform.

The reduction is unconditional.  It uses the functional-reflection
equivalence of positive-ordinate zeta zeros and preservation of analytic
multiplicity; it does not assume RH or identify the source form with the
project form.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open ComplexConjugate

/-- Functional reflection rewrites the diagonal square family as the two
reflected values which occur in the second slot of the Weil pairing. -/
theorem zetaWeilNormSqSummand_functionalReflection
    (F : Complex → Complex)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaWeilNormSqSummand F
        (positiveOrdinateZetaZeroFunctionalReflection rho) =
      zetaZeroMultiplicityReal rho.1 *
        (norm (F (1 - conj (rho : Complex))) ^ 2 +
          norm (F (1 - (rho : Complex))) ^ 2) := by
  unfold zetaWeilNormSqSummand zetaZeroMultiplicityReal
  rw [zetaZeroMultiplicity_positiveOrdinateFunctionalReflection]
  simp [positiveOrdinateZetaZeroFunctionalReflection_value]

/-- A pairing summand is dominated by the two diagonal square summands, one
of them reindexed by functional reflection. -/
theorem norm_zetaWeilPairingSummand_le_normSq_add_reflection
    (F G : Complex → Complex)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    norm (zetaWeilPairingSummand F G rho) ≤
      zetaWeilNormSqSummand F rho +
        zetaWeilNormSqSummand G
          (positiveOrdinateZetaZeroFunctionalReflection rho) := by
  let m : Real := zetaZeroMultiplicityReal rho.1
  let a := norm (F (rho : Complex))
  let b := norm (G (1 - conj (rho : Complex)))
  let c := norm (F (conj (rho : Complex)))
  let d := norm (G (1 - (rho : Complex)))
  have hm : 0 ≤ m := (zetaZeroMultiplicityReal_pos rho.1).le
  have hab : a * b ≤ a ^ 2 + b ^ 2 := by
    dsimp [a, b]
    nlinarith [sq_nonneg
      (norm (F (rho : Complex)) -
        norm (G (1 - conj (rho : Complex))))]
  have hcd : c * d ≤ c ^ 2 + d ^ 2 := by
    dsimp [c, d]
    nlinarith [sq_nonneg
      (norm (F (conj (rho : Complex))) -
        norm (G (1 - (rho : Complex))))]
  calc
    norm (zetaWeilPairingSummand F G rho) ≤
        m * (a * b + c * d) := by
      rw [zetaWeilPairingSummand]
      rw [norm_mul]
      rw [norm_natCast]
      change
        m *
            norm
              (F (rho : Complex) * conj (G (1 - conj (rho : Complex))) +
                F (conj (rho : Complex)) *
                  conj (G (1 - (rho : Complex)))) ≤
          m * (a * b + c * d)
      gcongr
      exact (norm_add_le _ _).trans_eq (by
        simp [a, b, c, d])
    _ ≤ m * ((a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hab hcd) hm
    _ = zetaWeilNormSqSummand F rho +
        zetaWeilNormSqSummand G
          (positiveOrdinateZetaZeroFunctionalReflection rho) := by
      rw [zetaWeilNormSqSummand,
        zetaWeilNormSqSummand_functionalReflection]
      dsimp [m, a, b, c, d]
      ring

/-- Diagonal square summability for two transforms implies absolute
summability of their polarized zeta Weil pairing. -/
theorem summable_zetaWeilPairingSummand_of_normSq
    (F G : Complex → Complex)
    (hF : Summable (zetaWeilNormSqSummand F))
    (hG : Summable (zetaWeilNormSqSummand G)) :
    Summable (zetaWeilPairingSummand F G) := by
  have hGReflection : Summable
      (fun rho : PositiveOrdinateZetaZeroSubtype ↦
        zetaWeilNormSqSummand G
          (positiveOrdinateZetaZeroFunctionalReflection rho)) := by
    exact positiveOrdinateZetaZeroFunctionalReflectionEquiv.summable_iff.mpr hG
  apply Summable.of_norm
  exact (hF.add hGReflection).of_nonneg_of_le
    (fun rho ↦ norm_nonneg (zetaWeilPairingSummand F G rho))
    (norm_zetaWeilPairingSummand_le_normSq_add_reflection F G)

end

end ComplexCompactExhaustion

namespace Experiments.M100

noncomputable section

/-- Literature-shaped diagonal source-domain condition: every transported
vector has a multiplicity-weighted square-summable zero transform. -/
def SuzukiSourceAaLocalizedWeilNormSqSummable : Prop :=
  ∀ u : SuzukiYoshidaCorrectedCommonFormDomain,
    Summable (ComplexCompactExhaustion.zetaWeilNormSqSummand
      (suzukiSourceWeilTransform suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)))

/-- The diagonal source-domain condition supplies all polarized pairing
summability required by the literal localized Weil form. -/
theorem suzukiSourceAaLocalizedWeilPairingSummable_of_normSq
    (hdiag : SuzukiSourceAaLocalizedWeilNormSqSummable) :
    SuzukiSourceAaLocalizedWeilPairingSummable := by
  intro u v
  exact ComplexCompactExhaustion.summable_zetaWeilPairingSummand_of_normSq
    _ _ (hdiag u) (hdiag v)

end


end Experiments.M100

end RiemannHypothesisProject
