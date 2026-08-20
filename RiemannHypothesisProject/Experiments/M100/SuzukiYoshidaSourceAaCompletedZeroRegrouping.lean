import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaSmoothCoreTransform
import RiemannHypothesisProject.WeilPositivity.ZetaPolynomialGaussianFormulaBridge

/-!
# M100-DF6F completed-zero regrouping for the Suzuki smooth core

This module separates the unconditional completed-zero bookkeeping from the
borrowed compact-support Guinand--Weil identity.  Burnol's all-zero side is
restricted to nontrivial zeros, split through the canonical
positive/conjugate-ordinate equivalence, and then identified with the real
part of Suzuki's functionally reflected diagonal pairing.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open SchwartzLineTestFunction
open ComplexCompactExhaustion
open scoped ComplexConjugate

/-- Burnol's zero weight after restricting to the nontrivial-zero subtype. -/
def burnolNontrivialZeroWeight
    (g : SchwartzLineTestFunction)
    (rho : NontrivialZetaZeroSubtype) : Real :=
  zetaZeroMultiplicityReal rho.1 *
    (burnolFourierLaplaceSource g
      (riemannWeilZeroArgument (rho : Complex))).re

/-- The completed Burnol zero side has no residual contribution from the
project-known trivial zeros. -/
theorem guinandWeilBurnolLiteratureZeroSide_eq_nontrivial
    (g : SchwartzLineTestFunction) :
    guinandWeilBurnolLiteratureZeroSide g =
      ∑' rho : NontrivialZetaZeroSubtype,
        burnolNontrivialZeroWeight g rho := by
  classical
  let raw : ZetaZeroSubtype → Real := fun rho =>
    zetaZeroMultiplicityReal rho *
      (burnolFourierLaplaceSource g
        (riemannWeilZeroArgument (rho : Complex))).re
  unfold guinandWeilBurnolLiteratureZeroSide
  calc
    (∑' rho : ZetaZeroSubtype,
        guinandWeilBurnolLiteratureZeroWeight g rho) =
        ∑' rho : ZetaZeroSubtype,
          nontrivialZetaZeroSet.indicator raw rho := by
      apply tsum_congr
      intro rho
      by_cases htrivial : IsTrivialZetaZero (rho : Complex)
      · simp [guinandWeilBurnolLiteratureZeroWeight,
          nontrivialZetaZeroSet, raw, htrivial]
      · simp [guinandWeilBurnolLiteratureZeroWeight,
          nontrivialZetaZeroSet, raw, htrivial]
    _ = ∑' rho : NontrivialZetaZeroSubtype,
          burnolNontrivialZeroWeight g rho := by
      simpa [burnolNontrivialZeroWeight, raw, Function.comp_def] using
        (tsum_subtype nontrivialZetaZeroSet raw).symm

/-- Absolute convergence in Burnol's source assumptions descends to the raw
nontrivial-zero family. -/
theorem summable_burnolNontrivialZeroWeight
    {g : SchwartzLineTestFunction}
    (hzero : Summable (fun rho : ZetaZeroSubtype =>
      norm (guinandWeilBurnolLiteratureZeroWeight g rho))) :
    Summable (burnolNontrivialZeroWeight g) := by
  have hall : Summable (guinandWeilBurnolLiteratureZeroWeight g) :=
    hzero.of_norm
  have hrestricted := hall.subtype nontrivialZetaZeroSet
  exact hrestricted.congr (fun rho => by
    have hnotTrivial : ¬ IsTrivialZetaZero (rho : Complex) := by
      exact rho.property
    simp [burnolNontrivialZeroWeight,
      guinandWeilBurnolLiteratureZeroWeight, hnotTrivial])

/-- A positive zero and its conjugate give the two real Burnol evaluations
with the same analytic multiplicity. -/
theorem burnolNontrivialZeroWeight_positive_add_conjugate
    (g : SchwartzLineTestFunction)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    burnolNontrivialZeroWeight g
        (positiveOrdinateToNontrivialZetaZero rho) +
      burnolNontrivialZeroWeight g
        (conjugatePositiveOrdinateToNontrivialZetaZero rho) =
      zetaZeroMultiplicityReal rho.1 *
        ((burnolFourierLaplaceSource g
            (riemannWeilZeroArgument (rho : Complex))).re +
          (burnolFourierLaplaceSource g
            (riemannWeilZeroArgument (conj (rho : Complex)))).re) := by
  unfold burnolNontrivialZeroWeight
  unfold positiveOrdinateToNontrivialZetaZero
  unfold conjugatePositiveOrdinateToNontrivialZetaZero
  rw [zetaZeroMultiplicityReal, zetaZeroMultiplicityReal,
    zetaZeroMultiplicity_conj]
  ring

/-- Burnol's absolutely convergent completed-zero side is the canonical
positive/conjugate pair sum for an arbitrary compact-support source. -/
theorem guinandWeilBurnolLiteratureZeroSide_eq_positivePairSum
    (g : SchwartzLineTestFunction)
    (hzero : Summable (fun rho : ZetaZeroSubtype =>
      norm (guinandWeilBurnolLiteratureZeroWeight g rho))) :
    guinandWeilBurnolLiteratureZeroSide g =
      ∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaZeroMultiplicityReal rho.1 *
          ((burnolFourierLaplaceSource g
              (riemannWeilZeroArgument (rho : Complex))).re +
            (burnolFourierLaplaceSource g
              (riemannWeilZeroArgument (conj (rho : Complex)))).re) := by
  let w := burnolNontrivialZeroWeight g
  have hw : Summable w := summable_burnolNontrivialZeroWeight hzero
  have hsum : Summable (w ∘ nontrivialZetaZeroOrdinateEquiv) :=
    hw.comp_injective nontrivialZetaZeroOrdinateEquiv.injective
  have hpositive := hsum.comp_injective Sum.inl_injective
  have hconjugate := hsum.comp_injective Sum.inr_injective
  have hpositive' : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      w (positiveOrdinateToNontrivialZetaZero rho)) := by
    simpa [Function.comp_def, nontrivialZetaZeroOrdinateEquiv] using hpositive
  have hconjugate' : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      w (conjugatePositiveOrdinateToNontrivialZetaZero rho)) := by
    simpa [Function.comp_def, nontrivialZetaZeroOrdinateEquiv] using hconjugate
  rw [guinandWeilBurnolLiteratureZeroSide_eq_nontrivial]
  change (∑' rho : NontrivialZetaZeroSubtype, w rho) = _
  calc
    (∑' rho : NontrivialZetaZeroSubtype, w rho) =
        ∑' i : PositiveOrdinateZetaZeroSubtype ⊕
            PositiveOrdinateZetaZeroSubtype,
          w (nontrivialZetaZeroOrdinateEquiv i) :=
      (nontrivialZetaZeroOrdinateEquiv.tsum_eq w).symm
    _ = (∑' rho : PositiveOrdinateZetaZeroSubtype,
          w (positiveOrdinateToNontrivialZetaZero rho)) +
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          w (conjugatePositiveOrdinateToNontrivialZetaZero rho) := by
      exact hpositive.tsum_sum hconjugate
    _ = ∑' rho : PositiveOrdinateZetaZeroSubtype,
        (w (positiveOrdinateToNontrivialZetaZero rho) +
          w (conjugatePositiveOrdinateToNontrivialZetaZero rho)) := by
      exact (hpositive'.tsum_add hconjugate').symm
    _ = _ := by
      apply tsum_congr
      intro rho
      exact burnolNontrivialZeroWeight_positive_add_conjugate g rho

/-- Suzuki's source coordinate at a functionally reflected positive zero is
the Riemann--Weil coordinate of the conjugate zero. -/
theorem suzukiSourceGammaArgument_functionalReflection
    (rho : PositiveOrdinateZetaZeroSubtype) :
    suzukiSourceGammaArgument
        (positiveOrdinateZetaZeroFunctionalReflection rho : Complex) =
      riemannWeilZeroArgument (conj (rho : Complex)) := by
  rw [positiveOrdinateZetaZeroFunctionalReflection_value]
  unfold suzukiSourceGammaArgument
  rw [riemannWeilZeroArgument_one_sub_conj,
    riemannWeilZeroArgument_conj]

/-- Conjugating the functionally reflected zero supplies the original
Riemann--Weil coordinate in Suzuki's sign convention. -/
theorem suzukiSourceGammaArgument_conj_functionalReflection
    (rho : PositiveOrdinateZetaZeroSubtype) :
    suzukiSourceGammaArgument
        (conj (positiveOrdinateZetaZeroFunctionalReflection rho : Complex)) =
      riemannWeilZeroArgument (rho : Complex) := by
  rw [positiveOrdinateZetaZeroFunctionalReflection_value]
  unfold suzukiSourceGammaArgument
  rw [map_sub, map_one, Complex.conj_conj,
    riemannWeilZeroArgument_one_sub]
  ring

/-- After functional-reflection reindexing, the real part of each Suzuki
diagonal summand is exactly the corresponding Burnol positive/conjugate pair. -/
theorem re_zetaWeilPairingSummand_smoothCore_functionalReflection
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    (zetaWeilPairingSummand
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (positiveOrdinateZetaZeroFunctionalReflection rho)).re =
      zetaZeroMultiplicityReal rho.1 *
        ((burnolFourierLaplaceSource (suzukiProjectBase v.1)
            (riemannWeilZeroArgument (rho : Complex))).re +
          (burnolFourierLaplaceSource (suzukiProjectBase v.1)
            (riemannWeilZeroArgument (conj (rho : Complex)))).re) := by
  rw [zetaWeilPairingSummand_smoothCore_self_eq_autocorrelation]
  rw [zetaZeroMultiplicity_positiveOrdinateFunctionalReflection]
  rw [suzukiSourceGammaArgument_functionalReflection,
    suzukiSourceGammaArgument_conj_functionalReflection]
  rw [burnolFourierLaplaceSource_suzukiProjectBase,
    burnolFourierLaplaceSource_suzukiProjectBase]
  simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re,
    Complex.natCast_im,
    zero_mul, sub_zero]
  rw [zetaZeroMultiplicityReal]
  ring

/-- The convergent diagonal Suzuki pairing is exactly the complex embedding
of Burnol's completed-zero side.  This is the completed-zero regrouping bridge;
the borrowed formula identity remains a separate source premise. -/
theorem suzukiSourceSmoothCoreFourierWeilPairing_self_eq_burnolZeroSide
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a)
    (hpair : Summable (zetaWeilPairingSummand
      (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
      (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))))
    (hzero : Summable (fun rho : ZetaZeroSubtype =>
      norm (guinandWeilBurnolLiteratureZeroWeight
        (suzukiProjectBase v.1) rho))) :
    zetaWeilPairing
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s)) =
      (guinandWeilBurnolLiteratureZeroSide
        (suzukiProjectBase v.1) : Complex) := by
  let F : Complex → Complex := fun s =>
    suzukiFourierSource v.1 (suzukiSourceGammaArgument s)
  have hre :
      (zetaWeilPairing F F).re =
        guinandWeilBurnolLiteratureZeroSide (suzukiProjectBase v.1) := by
    rw [zetaWeilPairing, Complex.re_tsum hpair,
      guinandWeilBurnolLiteratureZeroSide_eq_positivePairSum _ hzero]
    calc
      (∑' rho : PositiveOrdinateZetaZeroSubtype,
          (zetaWeilPairingSummand F F rho).re) =
          ∑' rho : PositiveOrdinateZetaZeroSubtype,
            (zetaWeilPairingSummand F F
              (positiveOrdinateZetaZeroFunctionalReflectionEquiv rho)).re :=
        (positiveOrdinateZetaZeroFunctionalReflectionEquiv.tsum_eq
          (fun rho => (zetaWeilPairingSummand F F rho).re)).symm
      _ = _ := by
        apply tsum_congr
        intro rho
        exact re_zetaWeilPairingSummand_smoothCore_functionalReflection v rho
  have hconj : conj (zetaWeilPairing F F) = zetaWeilPairing F F :=
    (zetaWeilPairing_conj_symm F F).symm
  calc
    zetaWeilPairing F F = ((zetaWeilPairing F F).re : Complex) :=
      (Complex.conj_eq_iff_re.mp hconj).symm
    _ = (guinandWeilBurnolLiteratureZeroSide
        (suzukiProjectBase v.1) : Complex) := by rw [hre]

/-- Once Burnol's source theorem is supplied, the completed-zero regrouping
turns the diagonal Suzuki pairing into the literature-normalized residual. -/
theorem suzukiSourceSmoothCoreFourierWeilPairing_self_eq_burnolResidual
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a)
    (hpair : Summable (zetaWeilPairingSummand
      (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
      (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))))
    (hsource : BurnolGuinandWeilSourceAssumptions
      (suzukiProjectBase v.1)) :
    zetaWeilPairing
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s)) =
      (guinandWeilBurnolLiteratureResidualSide
        (suzukiProjectBase v.1) : Complex) := by
  calc
    zetaWeilPairing
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s))
        (fun s => suzukiFourierSource v.1 (suzukiSourceGammaArgument s)) =
        (guinandWeilBurnolLiteratureZeroSide
          (suzukiProjectBase v.1) : Complex) :=
      suzukiSourceSmoothCoreFourierWeilPairing_self_eq_burnolZeroSide
        v hpair hsource.zeroSide_summable
    _ = (guinandWeilBurnolLiteratureResidualSide
        (suzukiProjectBase v.1) : Complex) := by rw [hsource.formula]

end

end RiemannHypothesisProject.Experiments.M100
