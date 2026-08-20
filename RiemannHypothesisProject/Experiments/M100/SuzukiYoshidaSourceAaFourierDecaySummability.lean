import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaFourierPolarization
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiJensen

/-!
# M100-DF6F smooth-core Fourier decay implies pairing summability

This module reduces the full two-input zero-pairing summability premise to a
one-input linear decay estimate at the two conjugate zero coordinates.  The
product of two such bounds has inverse-square height decay, which is consumed
by the project's unconditional multiplicity-aware xi/Jensen theorem.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open ComplexCompactExhaustion
open scoped ComplexConjugate

/-- Literature-shaped one-input decay target on Suzuki's smooth core.  One
constant controls the two conjugate source coordinates by inverse clamped
ordinate height. -/
def SuzukiSourceAaSmoothCoreFourierLinearZeroDecay : Prop :=
  ∀ v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
    ∃ C : Real, 0 ≤ C ∧
      ∀ rho : PositiveOrdinateZetaZeroSubtype,
        ‖suzukiFourierSource v.1
            (suzukiSourceGammaArgument (rho : Complex))‖ ≤
              C / positiveOrdinateZetaZeroClampedHeight rho ∧
        ‖suzukiFourierSource v.1
            (suzukiSourceGammaArgument (conj (rho : Complex)))‖ ≤
              C / positiveOrdinateZetaZeroClampedHeight rho

private theorem positiveOrdinateZetaZeroClampedHeight_functionalReflection
    (rho : PositiveOrdinateZetaZeroSubtype) :
    positiveOrdinateZetaZeroClampedHeight
        (positiveOrdinateZetaZeroFunctionalReflection rho) =
      positiveOrdinateZetaZeroClampedHeight rho := by
  simp [positiveOrdinateZetaZeroClampedHeight,
    positiveOrdinateZetaZeroFunctionalReflection_value]

/-- Two one-input linear-decay bounds give the inverse-square majorant for one
cross-pairing summand. -/
theorem norm_zetaWeilPairingSummand_smoothCore_le_of_linearZeroDecay
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (Cu Cv : Real) (_hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (hu : ∀ rho : PositiveOrdinateZetaZeroSubtype,
      ‖suzukiFourierSource u.1
          (suzukiSourceGammaArgument (rho : Complex))‖ ≤
            Cu / positiveOrdinateZetaZeroClampedHeight rho ∧
      ‖suzukiFourierSource u.1
          (suzukiSourceGammaArgument (conj (rho : Complex)))‖ ≤
            Cu / positiveOrdinateZetaZeroClampedHeight rho)
    (hv : ∀ rho : PositiveOrdinateZetaZeroSubtype,
      ‖suzukiFourierSource v.1
          (suzukiSourceGammaArgument (rho : Complex))‖ ≤
            Cv / positiveOrdinateZetaZeroClampedHeight rho ∧
      ‖suzukiFourierSource v.1
          (suzukiSourceGammaArgument (conj (rho : Complex)))‖ ≤
            Cv / positiveOrdinateZetaZeroClampedHeight rho)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    ‖zetaWeilPairingSummand
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource u.1 (suzukiSourceGammaArgument s)) rho‖ ≤
      (2 * Cv * Cu) *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by
  let H := positiveOrdinateZetaZeroClampedHeight rho
  have hH : 0 < H := by
    dsimp [H, positiveOrdinateZetaZeroClampedHeight]
    exact zero_lt_one.trans_le (le_max_left 1 _)
  have hv₁ := (hv rho).1
  have hv₂ := (hv rho).2
  have huRef := hu (positiveOrdinateZetaZeroFunctionalReflection rho)
  rw [positiveOrdinateZetaZeroClampedHeight_functionalReflection] at huRef
  rw [positiveOrdinateZetaZeroFunctionalReflection_value] at huRef
  have hu₁ :
      ‖suzukiFourierSource u.1
          (suzukiSourceGammaArgument (1 - conj (rho : Complex)))‖ ≤ Cu / H := by
    simpa [H] using huRef.1
  have hu₂ :
      ‖suzukiFourierSource u.1
          (suzukiSourceGammaArgument (1 - (rho : Complex)))‖ ≤ Cu / H := by
    simpa [H, map_sub, map_one] using huRef.2
  have hm : 0 ≤ zetaZeroMultiplicityReal rho.1 :=
    (zetaZeroMultiplicityReal_pos rho.1).le
  calc
    ‖zetaWeilPairingSummand
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource u.1 (suzukiSourceGammaArgument s)) rho‖ ≤
        zetaZeroMultiplicityReal rho.1 *
          (‖suzukiFourierSource v.1
              (suzukiSourceGammaArgument (rho : Complex))‖ *
              ‖suzukiFourierSource u.1
                (suzukiSourceGammaArgument (1 - conj (rho : Complex)))‖ +
            ‖suzukiFourierSource v.1
              (suzukiSourceGammaArgument (conj (rho : Complex)))‖ *
              ‖suzukiFourierSource u.1
                (suzukiSourceGammaArgument (1 - (rho : Complex)))‖) := by
          rw [zetaWeilPairingSummand, norm_mul, norm_natCast]
          rw [zetaZeroMultiplicityReal]
          gcongr
          exact (norm_add_le _ _).trans_eq (by simp)
    _ ≤ zetaZeroMultiplicityReal rho.1 *
        ((Cv / H) * (Cu / H) + (Cv / H) * (Cu / H)) := by
      gcongr
    _ = (2 * Cv * Cu) *
        (zetaZeroMultiplicityReal rho.1 / H ^ 2) := by
      field_simp
      ring
    _ = (2 * Cv * Cu) *
        (zetaZeroMultiplicityReal rho.1 /
          positiveOrdinateZetaZeroClampedHeight rho ^ 2) := by rfl

/-- The one-input smooth-core decay estimate and unconditional xi/Jensen zero
counting imply the exact all-pairs summability premise. -/
theorem suzukiSourceAaSmoothCoreFourierPairingSummable_of_linearZeroDecay
    (hdecay : SuzukiSourceAaSmoothCoreFourierLinearZeroDecay) :
    SuzukiSourceAaSmoothCoreFourierPairingSummable := by
  intro u v
  obtain ⟨Cu, hCu, hu⟩ := hdecay u
  obtain ⟨Cv, hCv, hv⟩ := hdecay v
  have hbase :=
    unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable
  have hmajor := hbase.mul_left (2 * Cv * Cu)
  apply Summable.of_norm
  exact hmajor.of_nonneg_of_le
    (fun rho => norm_nonneg (zetaWeilPairingSummand
      (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
      (fun s => suzukiFourierSource u.1 (suzukiSourceGammaArgument s)) rho))
    (norm_zetaWeilPairingSummand_smoothCore_le_of_linearZeroDecay
      u v Cu Cv hCu hCv hu hv)

/-- Decay plus the pointwise Burnol source theorem supplies the exact
smooth-core Fourier Guinand--Weil formula. -/
theorem suzukiSourceAaSmoothCoreFourierGuinandWeilFormula_of_decay_burnol
    (hdecay : SuzukiSourceAaSmoothCoreFourierLinearZeroDecay)
    (hsource : SuzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions) :
    SuzukiSourceAaSmoothCoreFourierGuinandWeilFormula :=
  suzukiSourceAaSmoothCoreFourierGuinandWeilFormula_of_burnol
    (suzukiSourceAaSmoothCoreFourierPairingSummable_of_linearZeroDecay hdecay)
    hsource

/-- Final source-associated-operator receiver with summability reduced to the
one-input smooth-core linear-decay estimate. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_decay_burnol
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hbounded : SuzukiSourceAaLocalizedWeilFormBounded)
    (hdecay : SuzukiSourceAaSmoothCoreFourierLinearZeroDecay)
    (hsource : SuzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_burnol
    A hsourceGraph hbounded
      (suzukiSourceAaSmoothCoreFourierPairingSummable_of_linearZeroDecay hdecay)
      hsource

end

end RiemannHypothesisProject.Experiments.M100
