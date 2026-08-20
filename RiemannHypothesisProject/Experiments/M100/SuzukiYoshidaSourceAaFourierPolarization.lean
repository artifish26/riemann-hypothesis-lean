import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaCompletedZeroRegrouping

/-!
# M100-DF6F off-diagonal Fourier polarization assembly

This module reconstructs the full smooth-core Suzuki pairing from the four
diagonal pairings.  It keeps convergence visible, proves the supported global
Fourier--Laplace transform is linear on the smooth core, and turns pointwise
Burnol source assumptions into the exact off-diagonal Guinand--Weil premise
used by the source-operator receiver.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open SchwartzLineTestFunction
open ComplexCompactExhaustion
open scoped ComplexConjugate

/-- The complex Fourier--Laplace integrand of a supported smooth-core vector
is integrable at every complex frequency. -/
private theorem integrable_suzukiSmoothCoreFourierIntegrand
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a) (z : Complex) :
    Integrable (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * v.1 x) := by
  have hsub : Function.support
      (fun x : Real =>
        Complex.exp ((x : Complex) * Complex.I * z) * v.1 x) ⊆
        Icc (-a) a := by
    intro x hx
    have hv : v.1 x ≠ 0 := by
      intro hzero
      exact hx (by simp [hzero])
    exact ⟨(v.2 hv).1.le, (v.2 hv).2.le⟩
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous (fun x : Real =>
      Complex.exp ((x : Complex) * Complex.I * z) * v.1 x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- The supported global Fourier--Laplace transform is additive on the smooth
core. -/
theorem suzukiFourierSource_smoothCore_add
    {a : Real} (u v : SuzukiSmoothCoreLinearSubmodule a) (z : Complex) :
    suzukiFourierSource (u + v).1 z =
      suzukiFourierSource u.1 z + suzukiFourierSource v.1 z := by
  unfold suzukiFourierSource
  rw [← integral_add
    (integrable_suzukiSmoothCoreFourierIntegrand u z)
    (integrable_suzukiSmoothCoreFourierIntegrand v z)]
  apply integral_congr_ae
  filter_upwards with x
  simp
  ring

/-- The supported global Fourier--Laplace transform is complex-linear on the
smooth core. -/
theorem suzukiFourierSource_smoothCore_smul
    {a : Real} (c : Complex) (v : SuzukiSmoothCoreLinearSubmodule a)
    (z : Complex) :
    suzukiFourierSource (c • v).1 z =
      c * suzukiFourierSource v.1 z := by
  unfold suzukiFourierSource
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp
  ring

/-- The exact summability input needed to polarize the smooth-core Fourier
pairing without conditionally rearranging zero sums. -/
def SuzukiSourceAaSmoothCoreFourierPairingSummable : Prop :=
  ∀ u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
    Summable (zetaWeilPairingSummand
      (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
      (fun s => suzukiFourierSource u.1 (suzukiSourceGammaArgument s)))

/-- The borrowed Burnol source theorem, retained pointwise on every vector of
Suzuki's smooth core. -/
def SuzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions : Prop :=
  ∀ v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar,
    BurnolGuinandWeilSourceAssumptions (suzukiProjectBase v.1)

/-- Additivity in the second zero-pairing argument, with convergence explicit. -/
private theorem zetaWeilPairing_add_right_of_summable
    (F G H : Complex → Complex)
    (hG : Summable (zetaWeilPairingSummand F G))
    (hH : Summable (zetaWeilPairingSummand F H)) :
    zetaWeilPairing F (fun s => G s + H s) =
      zetaWeilPairing F G + zetaWeilPairing F H := by
  rw [zetaWeilPairing, zetaWeilPairing, zetaWeilPairing]
  rw [← hG.tsum_add hH]
  apply tsum_congr
  intro rho
  simp [zetaWeilPairingSummand]
  ring

theorem suzukiSourceSmoothCoreFourierWeilPairing_add_left
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (u₁ u₂ v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing (u₁ + u₂) v =
      suzukiSourceSmoothCoreFourierWeilPairing u₁ v +
        suzukiSourceSmoothCoreFourierWeilPairing u₂ v := by
  unfold suzukiSourceSmoothCoreFourierWeilPairing
  have hadd :
      (fun s => suzukiFourierSource (u₁ + u₂).1
        (suzukiSourceGammaArgument s)) =
        fun s =>
          suzukiFourierSource u₁.1 (suzukiSourceGammaArgument s) +
            suzukiFourierSource u₂.1 (suzukiSourceGammaArgument s) := by
    funext s
    exact suzukiFourierSource_smoothCore_add u₁ u₂ _
  rw [hadd]
  exact zetaWeilPairing_add_right_of_summable _ _ _
    (hsum u₁ v) (hsum u₂ v)

theorem suzukiSourceSmoothCoreFourierWeilPairing_add_right
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (u v₁ v₂ : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing u (v₁ + v₂) =
      suzukiSourceSmoothCoreFourierWeilPairing u v₁ +
        suzukiSourceSmoothCoreFourierWeilPairing u v₂ := by
  unfold suzukiSourceSmoothCoreFourierWeilPairing
  have hadd :
      (fun s => suzukiFourierSource (v₁ + v₂).1
        (suzukiSourceGammaArgument s)) =
        fun s =>
          suzukiFourierSource v₁.1 (suzukiSourceGammaArgument s) +
            suzukiFourierSource v₂.1 (suzukiSourceGammaArgument s) := by
    funext s
    exact suzukiFourierSource_smoothCore_add v₁ v₂ _
  rw [hadd]
  exact zetaWeilPairing_add_left _ _ _ (hsum u v₁) (hsum u v₂)

theorem suzukiSourceSmoothCoreFourierWeilPairing_smul_left
    (c : Complex)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing (c • u) v =
      conj c * suzukiSourceSmoothCoreFourierWeilPairing u v := by
  unfold suzukiSourceSmoothCoreFourierWeilPairing
  have hsmul :
      (fun s => suzukiFourierSource (c • u).1
        (suzukiSourceGammaArgument s)) =
        fun s => c * suzukiFourierSource u.1 (suzukiSourceGammaArgument s) := by
    funext s
    exact suzukiFourierSource_smoothCore_smul c u _
  rw [hsmul]
  exact zetaWeilPairing_mul_right _ _ _

theorem suzukiSourceSmoothCoreFourierWeilPairing_smul_right
    (c : Complex)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing u (c • v) =
      c * suzukiSourceSmoothCoreFourierWeilPairing u v := by
  unfold suzukiSourceSmoothCoreFourierWeilPairing
  have hsmul :
      (fun s => suzukiFourierSource (c • v).1
        (suzukiSourceGammaArgument s)) =
        fun s => c * suzukiFourierSource v.1 (suzukiSourceGammaArgument s) := by
    funext s
    exact suzukiFourierSource_smoothCore_smul c v _
  rw [hsmul]
  exact zetaWeilPairing_mul_left _ _ _

theorem suzukiSourceSmoothCoreFourierWeilPairing_sub_left
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (u₁ u₂ v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing (u₁ - u₂) v =
      suzukiSourceSmoothCoreFourierWeilPairing u₁ v -
        suzukiSourceSmoothCoreFourierWeilPairing u₂ v := by
  rw [sub_eq_add_neg,
    suzukiSourceSmoothCoreFourierWeilPairing_add_left hsum,
    show -u₂ = (-1 : Complex) • u₂ by simp,
    suzukiSourceSmoothCoreFourierWeilPairing_smul_left]
  simpa [sub_eq_add_neg]

theorem suzukiSourceSmoothCoreFourierWeilPairing_sub_right
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (u v₁ v₂ : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing u (v₁ - v₂) =
      suzukiSourceSmoothCoreFourierWeilPairing u v₁ -
        suzukiSourceSmoothCoreFourierWeilPairing u v₂ := by
  rw [sub_eq_add_neg,
    suzukiSourceSmoothCoreFourierWeilPairing_add_right hsum,
    show -v₂ = (-1 : Complex) • v₂ by simp,
    suzukiSourceSmoothCoreFourierWeilPairing_smul_right]
  simpa [sub_eq_add_neg]

/-- The full off-diagonal Fourier pairing is the standard four-diagonal
complex polarization. -/
theorem suzukiSourceSmoothCoreFourierWeilPairing_eq_diagonalPolarization
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (u v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar) :
    suzukiSourceSmoothCoreFourierWeilPairing u v =
      (4 : Complex)⁻¹ *
        (suzukiSourceSmoothCoreFourierWeilPairing (u + v) (u + v) -
          suzukiSourceSmoothCoreFourierWeilPairing (u - v) (u - v) -
          Complex.I *
            suzukiSourceSmoothCoreFourierWeilPairing
              (u + Complex.I • v) (u + Complex.I • v) +
          Complex.I *
            suzukiSourceSmoothCoreFourierWeilPairing
              (u - Complex.I • v) (u - Complex.I • v)) := by
  have hplus :
      suzukiSourceSmoothCoreFourierWeilPairing (u + v) (u + v) =
        suzukiSourceSmoothCoreFourierWeilPairing u u +
          suzukiSourceSmoothCoreFourierWeilPairing u v +
          (suzukiSourceSmoothCoreFourierWeilPairing v u +
            suzukiSourceSmoothCoreFourierWeilPairing v v) := by
    rw [suzukiSourceSmoothCoreFourierWeilPairing_add_left hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_add_right hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_add_right hsum]
  have hminus :
      suzukiSourceSmoothCoreFourierWeilPairing (u - v) (u - v) =
        (suzukiSourceSmoothCoreFourierWeilPairing u u -
          suzukiSourceSmoothCoreFourierWeilPairing u v) -
          (suzukiSourceSmoothCoreFourierWeilPairing v u -
            suzukiSourceSmoothCoreFourierWeilPairing v v) := by
    rw [suzukiSourceSmoothCoreFourierWeilPairing_sub_left hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_sub_right hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_sub_right hsum]
  have hiPlus :
      suzukiSourceSmoothCoreFourierWeilPairing
          (u + Complex.I • v) (u + Complex.I • v) =
        suzukiSourceSmoothCoreFourierWeilPairing u u +
          Complex.I * suzukiSourceSmoothCoreFourierWeilPairing u v +
          (conj Complex.I *
              suzukiSourceSmoothCoreFourierWeilPairing v u +
            conj Complex.I * Complex.I *
              suzukiSourceSmoothCoreFourierWeilPairing v v) := by
    rw [suzukiSourceSmoothCoreFourierWeilPairing_add_left hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_add_right hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_add_right hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_right,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_left,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_left,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_right]
    ring
  have hiMinus :
      suzukiSourceSmoothCoreFourierWeilPairing
          (u - Complex.I • v) (u - Complex.I • v) =
        (suzukiSourceSmoothCoreFourierWeilPairing u u -
          Complex.I * suzukiSourceSmoothCoreFourierWeilPairing u v) -
          (conj Complex.I *
              suzukiSourceSmoothCoreFourierWeilPairing v u -
            conj Complex.I * Complex.I *
              suzukiSourceSmoothCoreFourierWeilPairing v v) := by
    rw [suzukiSourceSmoothCoreFourierWeilPairing_sub_left hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_sub_right hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_sub_right hsum,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_right,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_left,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_left,
      suzukiSourceSmoothCoreFourierWeilPairing_smul_right]
    ring
  rw [hplus, hminus, hiPlus, hiMinus]
  simp only [Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Named diagonal wrapper for the direct Fourier pairing. -/
theorem suzukiSourceSmoothCoreFourierWeilPairing_diagonal_eq_burnolResidual
    (v : SuzukiSmoothCoreLinearSubmodule suzukiProjectAStar)
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (hsource : BurnolGuinandWeilSourceAssumptions (suzukiProjectBase v.1)) :
    suzukiSourceSmoothCoreFourierWeilPairing v v =
      (guinandWeilBurnolLiteratureResidualSide
        (suzukiProjectBase v.1) : Complex) := by
  unfold suzukiSourceSmoothCoreFourierWeilPairing
  exact suzukiSourceSmoothCoreFourierWeilPairing_self_eq_burnolResidual
    v (hsum v v) hsource

/-- Pointwise Burnol source assumptions plus honest all-pairs summability
inhabit the exact smooth-core Fourier Guinand--Weil theorem. -/
theorem suzukiSourceAaSmoothCoreFourierGuinandWeilFormula_of_burnol
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (hsource : SuzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions) :
    SuzukiSourceAaSmoothCoreFourierGuinandWeilFormula := by
  intro u v
  rw [suzukiSourceSmoothCoreFourierWeilPairing_eq_diagonalPolarization hsum]
  unfold suzukiSourceSmoothCoreResidualPolarization
  change (4 : Complex)⁻¹ *
    (suzukiSourceSmoothCoreFourierWeilPairing (u + v) (u + v) -
      suzukiSourceSmoothCoreFourierWeilPairing (u - v) (u - v) -
      Complex.I * suzukiSourceSmoothCoreFourierWeilPairing
        (u + Complex.I • v) (u + Complex.I • v) +
      Complex.I * suzukiSourceSmoothCoreFourierWeilPairing
        (u - Complex.I • v) (u - Complex.I • v)) =
    (4 : Complex)⁻¹ *
      ((guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase (u + v).1) : Complex) -
        (guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase (u - v).1) : Complex) -
        Complex.I * (guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase (u + Complex.I • v).1) : Complex) +
        Complex.I * (guinandWeilBurnolLiteratureResidualSide
          (suzukiProjectBase (u - Complex.I • v).1) : Complex))
  rw [suzukiSourceSmoothCoreFourierWeilPairing_diagonal_eq_burnolResidual
      (u + v) hsum (hsource (u + v)),
    suzukiSourceSmoothCoreFourierWeilPairing_diagonal_eq_burnolResidual
      (u - v) hsum (hsource (u - v)),
    suzukiSourceSmoothCoreFourierWeilPairing_diagonal_eq_burnolResidual
      (u + Complex.I • v) hsum (hsource (u + Complex.I • v)),
    suzukiSourceSmoothCoreFourierWeilPairing_diagonal_eq_burnolResidual
      (u - Complex.I • v) hsum (hsource (u - Complex.I • v))]

/-- Operator endpoint with the off-diagonal formula assembled locally from
diagonal Burnol source assumptions. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_burnol
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hbounded : SuzukiSourceAaLocalizedWeilFormBounded)
    (hsum : SuzukiSourceAaSmoothCoreFourierPairingSummable)
    (hsource : SuzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_fourierGuinandWeil
    A hsourceGraph hbounded
      (suzukiSourceAaSmoothCoreFourierGuinandWeilFormula_of_burnol hsum hsource)

end

end RiemannHypothesisProject.Experiments.M100
