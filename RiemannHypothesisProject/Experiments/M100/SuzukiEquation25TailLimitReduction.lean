import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25FinitePairingCancellation

/-!
# Tail-limit reduction for Suzuki's equation (2.5)

The finite Gamma cancellation is now exact at the source-pairing level.  This
module isolates the sole remaining analytic limit and proves that it implies
the full scalar-free regular-kernel correction.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter Topology SchwartzLineTestFunction

/-- The non-scalar Abel-tail statement left after the shifted-harmonic
constant has been evaluated. -/
def SuzukiEquation25RenormalizedGammaTailLimitAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    Tendsto
      (fun N : Nat =>
        (Real.log N + Real.eulerMascheroniConstant + Real.log 2) *
            ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25GammaTailKernel N) a v.1).re)
      atTop
      (nhds (suzukiSourceLogFourierForm v.1))

/-- The combined tail limit, before separating the already evaluated scalar
asymptotic. -/
def SuzukiEquation25GammaTailPairingLimitAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    Tendsto
      (fun N : Nat =>
        suzukiEquation25ShiftedHarmonicPartial N *
            ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
          (suzukiFiniteKernelPairingComplex
            (suzukiEquation25GammaTailKernel N) a v.1).re)
      atTop
      (nhds (suzukiSourceLogFourierForm v.1 +
        suzukiEquation25GammaRestorationScalar *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2))

/-- The quarter-point shifted-harmonic asymptotic converts the normalized
Abel-tail statement into the combined finite-cancellation limit. -/
theorem suzukiEquation25GammaTailPairingLimitAt_of_renormalized
    {a : Real}
    (htail : SuzukiEquation25RenormalizedGammaTailLimitAt a) :
    SuzukiEquation25GammaTailPairingLimitAt a := by
  intro ha v
  let mass : Real := ‖suzukiSmoothCoreToL2 v‖ ^ 2
  have hscalar :=
    tendsto_suzukiEquation25ShiftedHarmonicPartial_sub_log_sub_scale
      |>.mul_const mass
  have htail_v := htail ha v
  have hadd := hscalar.add htail_v
  convert hadd using 1
  · funext N
    dsimp only [mass]
    ring
  · dsimp only [mass]
    ring

/-- The Lerch finite pairings converge to the full cancellation-safe Lerch
pairing by the already established inverse-square summability. -/
theorem tendsto_suzukiEquation25GammaLerchKernelPartial_pairing
    {a : Real} (v : SuzukiSmoothCore a) :
    Tendsto
      (fun N : Nat =>
        (suzukiFiniteKernelPairingComplex
          (suzukiEquation25GammaLerchKernelPartial N) a
          (SchwartzMap.derivCLM Complex Complex v.1)).re)
      atTop
      (nhds
        (suzukiFiniteKernelPairingComplex
          suzukiEquation25LerchPhysicalKernel a
          (SchwartzMap.derivCLM Complex Complex v.1)).re) := by
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v.1
  have hsum :=
    (hasSum_suzukiFiniteKernelPairingComplex_gammaLerch a u.continuous)
      |>.tendsto_sum_nat
  have hkernel :
      (fun x => ∑' n : Nat, suzukiGammaLerchKernelSummand n x) =
        suzukiEquation25LerchPhysicalKernel := by
    funext x
    rw [tsum_suzukiGammaLerchKernelSummand]
    rfl
  rw [hkernel] at hsum
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hsum
  convert hre using 1
  funext N
  have hpartial :=
    suzukiFiniteKernelPairingComplex_finsetSum
      (Finset.range N) suzukiGammaLerchKernelSummand a u
      (fun n _ => continuous_suzukiGammaLerchKernelSummand n)
      u.continuous
  change
    (suzukiFiniteKernelPairingComplex
      (suzukiEquation25GammaLerchKernelPartial N) a u).re = _
  exact congrArg Complex.re hpartial

/-- The renormalized Gamma-tail limit is the only missing analytic input for
the scalar-free regular-kernel identity. -/
theorem suzukiEquation25RegularKernelCorrectionAt_of_tailPairingLimit
    {a : Real}
    (htail : SuzukiEquation25GammaTailPairingLimitAt a) :
    SuzukiEquation25RegularKernelCorrectionAt a := by
  intro ha v
  have hleftLerch :=
    tendsto_suzukiEquation25GammaLerchKernelPartial_pairing v
  have hleft := hleftLerch.add_const
    (suzukiFiniteKernelPairingComplex suzukiR1SecondKernel a v.1).re
  have hright := htail ha v
  have heq : ∀ N : Nat,
      (suzukiFiniteKernelPairingComplex
          (suzukiEquation25GammaLerchKernelPartial N) a
          (SchwartzMap.derivCLM Complex Complex v.1)).re +
        (suzukiFiniteKernelPairingComplex
          suzukiR1SecondKernel a v.1).re =
      suzukiEquation25ShiftedHarmonicPartial N *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
        (suzukiFiniteKernelPairingComplex
          (suzukiEquation25GammaTailKernel N) a v.1).re :=
    fun N => suzukiEquation25FinitePairing_eq_shiftedHarmonic_add_tail
      ha v N
  have hright' := (tendsto_congr' (Filter.Eventually.of_forall heq)).1 hleft
  exact tendsto_nhds_unique hright' hright

/-- Consequently the normalized Abel-tail statement closes the full regular
Gamma correction. -/
theorem suzukiEquation25RegularKernelCorrectionAt_of_renormalizedTailLimit
    {a : Real}
    (htail : SuzukiEquation25RenormalizedGammaTailLimitAt a) :
    SuzukiEquation25RegularKernelCorrectionAt a :=
  suzukiEquation25RegularKernelCorrectionAt_of_tailPairingLimit
    (suzukiEquation25GammaTailPairingLimitAt_of_renormalized htail)

end

end M100
end Experiments
end RiemannHypothesisProject
