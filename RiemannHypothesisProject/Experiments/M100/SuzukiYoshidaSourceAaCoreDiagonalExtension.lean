import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaDiagonalFormBound

/-!
# M100-DF6F smooth-core extension of the diagonal zero estimate

The natural source sampling theorem is stated on Suzuki's compactly supported
smooth core, whereas the literal localized Weil form lives on the completed
logarithmic graph domain.  This module proves that a uniform smooth-core
diagonal estimate extends to that completion.

The extension uses only continuity of each finite family of Fourier
evaluations, density of the smooth core, and bounded finite sums of
nonnegative terms.  The multiplicity-weighted Paley--Wiener sampling estimate
on the smooth core remains an explicit analytic source input.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open ComplexConjugate
open scoped InnerProductSpace

/-- Evaluation of the transported entire transform at one complex point is a
continuous complex-linear functional on the completed source-form domain. -/
def suzukiSourceAaWeilEvaluationCLM (rho : Complex) :
    SuzukiYoshidaCorrectedCommonFormDomain →L[Complex] Complex :=
  (innerSL Complex
      (suzukiFiniteIntervalComplexExponential suzukiProjectAStar
        (suzukiSourceGammaArgument rho))).comp
    suzukiLogRadiusLinearCompletionToFiniteIntervalL2

@[simp]
theorem suzukiSourceAaWeilEvaluationCLM_apply
    (rho : Complex) (u : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaWeilEvaluationCLM rho u =
      suzukiSourceAaLocalizedWeilTransform u rho :=
  rfl

/-- Every individual multiplicity-weighted diagonal summand varies
continuously on the completed form domain. -/
theorem continuous_zetaWeilNormSqSummand_suzukiSourceAa
    (rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    Continuous (fun u : SuzukiYoshidaCorrectedCommonFormDomain ↦
      ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform u) rho) := by
  change Continuous (fun u : SuzukiYoshidaCorrectedCommonFormDomain ↦
    ComplexCompactExhaustion.zetaZeroMultiplicityReal rho.1 *
      (norm (suzukiSourceAaWeilEvaluationCLM (rho : Complex) u) ^ 2 +
        norm (suzukiSourceAaWeilEvaluationCLM
          (conj (rho : Complex)) u) ^ 2))
  fun_prop

/-- A finite diagonal zero energy.  These are the continuous approximants
used to pass the source estimate through the smooth-core closure. -/
def suzukiSourceAaDiagonalPartialEnergy
    (s : Finset
      ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype)
    (u : SuzukiYoshidaCorrectedCommonFormDomain) : Real :=
  ∑ rho ∈ s,
    ComplexCompactExhaustion.zetaWeilNormSqSummand
      (suzukiSourceAaLocalizedWeilTransform u) rho

theorem continuous_suzukiSourceAaDiagonalPartialEnergy
    (s : Finset
      ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype) :
    Continuous (suzukiSourceAaDiagonalPartialEnergy s) := by
  unfold suzukiSourceAaDiagonalPartialEnergy
  apply continuous_finset_sum
  intro rho hrho
  exact continuous_zetaWeilNormSqSummand_suzukiSourceAa rho

/-- Literature-shaped remaining source theorem: a single constant controls
the multiplicity-weighted Paley--Wiener samples of every compactly supported
smooth-core vector in the completed logarithmic graph norm.  Summability is
kept explicit because `tsum` is totalized. -/
def SuzukiSourceAaSmoothCoreWeilDiagonalBound : Prop :=
  ∃ C : Real, 0 < C ∧
    ∀ u : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
      Summable (ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceWeilTransform suzukiProjectAStar
          (suzukiSmoothCoreFiniteIntervalL2LinearMap
            suzukiProjectAStar u))) ∧
      (∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceWeilTransform suzukiProjectAStar
          (suzukiSmoothCoreFiniteIntervalL2LinearMap
            suzukiProjectAStar u)) rho) ≤
        C * ‖suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar u‖ ^ 2

/-- Uniform control on the dense smooth core extends to genuine summability
and the same diagonal bound on the whole completed form domain. -/
theorem suzukiSourceAaLocalizedWeilDiagonalBound_of_smoothCore
    (hcore : SuzukiSourceAaSmoothCoreWeilDiagonalBound) :
    SuzukiSourceAaLocalizedWeilDiagonalBound := by
  obtain ⟨C, hC, hcore⟩ := hcore
  refine ⟨C, hC, ?_⟩
  intro u
  have htermNonneg : ∀
      rho : ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype,
      0 ≤ ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform u) rho := by
    intro rho
    unfold ComplexCompactExhaustion.zetaWeilNormSqSummand
    exact mul_nonneg
      (ComplexCompactExhaustion.zetaZeroMultiplicityReal_pos rho.1).le
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hfinite : ∀ s : Finset
      ComplexCompactExhaustion.PositiveOrdinateZetaZeroSubtype,
      suzukiSourceAaDiagonalPartialEnergy s u ≤ C * ‖u‖ ^ 2 := by
    intro s
    let controlledSet : Set SuzukiYoshidaCorrectedCommonFormDomain :=
      {v | suzukiSourceAaDiagonalPartialEnergy s v ≤ C * ‖v‖ ^ 2}
    have hcontrolledClosed : IsClosed controlledSet := by
      exact isClosed_le
        (continuous_suzukiSourceAaDiagonalPartialEnergy s)
        (continuous_const.mul (continuous_norm.pow 2))
    have hcoreControlled : Set.range
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar) ⊆ controlledSet := by
      rintro _ ⟨v, rfl⟩
      have hv := hcore v
      have hsum : suzukiSourceAaDiagonalPartialEnergy s
          (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
            suzukiProjectAStar v) ≤
          ∑' rho, ComplexCompactExhaustion.zetaWeilNormSqSummand
            (suzukiSourceWeilTransform suzukiProjectAStar
              (suzukiSmoothCoreFiniteIntervalL2LinearMap
                suzukiProjectAStar v)) rho := by
        unfold suzukiSourceAaDiagonalPartialEnergy
        change (∑ rho ∈ s,
            ComplexCompactExhaustion.zetaWeilNormSqSummand
              (suzukiSourceWeilTransform suzukiProjectAStar
                (suzukiLogRadiusLinearCompletionToFiniteIntervalL2
                  (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
                    suzukiProjectAStar v))) rho) ≤ _
        rw [suzukiLogRadiusLinearCompletionToFiniteIntervalL2_core_apply]
        apply hv.1.sum_le_tsum s
        intro rho hrho
        unfold ComplexCompactExhaustion.zetaWeilNormSqSummand
        exact mul_nonneg
          (ComplexCompactExhaustion.zetaZeroMultiplicityReal_pos rho.1).le
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      exact hsum.trans hv.2
    have hclosure : closure (Set.range
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar)) ⊆ controlledSet :=
      closure_minimal hcoreControlled hcontrolledClosed
    have huClosure : u ∈ closure (Set.range
        (suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap
          suzukiProjectAStar)) := by
      rw [(suzukiSmoothCoreToLogRadiusLinearCompletionLinearMap_denseRange
        suzukiProjectAStar).closure_eq]
      exact Set.mem_univ u
    exact hclosure huClosure
  have hsummable : Summable
      (ComplexCompactExhaustion.zetaWeilNormSqSummand
        (suzukiSourceAaLocalizedWeilTransform u)) := by
    apply summable_of_sum_le htermNonneg
    intro s
    exact hfinite s
  refine ⟨hsummable, ?_⟩
  apply Real.tsum_le_of_sum_le htermNonneg
  intro s
  exact hfinite s

/-- The smooth-core sampling theorem therefore supplies the complete literal
localized-Weil-form boundedness premise. -/
theorem suzukiSourceAaLocalizedWeilFormBounded_of_smoothCoreDiagonalBound
    (hcore : SuzukiSourceAaSmoothCoreWeilDiagonalBound) :
    SuzukiSourceAaLocalizedWeilFormBounded :=
  suzukiSourceAaLocalizedWeilFormBounded_of_diagonalBound
    (suzukiSourceAaLocalizedWeilDiagonalBound_of_smoothCore hcore)

/-- With the other two independent source identifications, the smooth-core
sampling estimate reaches the checked corrected-form operator directly. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_smoothCoreDiagonalBound
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hcoreDiagonal : SuzukiSourceAaSmoothCoreWeilDiagonalBound)
    (hcoreG : SuzukiSourceAaLocalizedWeilFormCoreGRepresentation) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_localizedWeilForm
    A hsourceGraph
    (suzukiSourceAaLocalizedWeilFormBounded_of_smoothCoreDiagonalBound
      hcoreDiagonal)
    hcoreG

/-- The same reduced source surface also gives source self-adjointness. -/
theorem sourceAa_isSelfAdjoint_of_smoothCoreDiagonalBound
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hcoreDiagonal : SuzukiSourceAaSmoothCoreWeilDiagonalBound)
    (hcoreG : SuzukiSourceAaLocalizedWeilFormCoreGRepresentation) :
    IsSelfAdjoint A :=
  sourceAa_isSelfAdjoint_of_localizedWeilForm A hsourceGraph
    (suzukiSourceAaLocalizedWeilFormBounded_of_smoothCoreDiagonalBound
      hcoreDiagonal)
    hcoreG

end

end RiemannHypothesisProject.Experiments.M100
