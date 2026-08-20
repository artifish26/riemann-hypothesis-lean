import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25FiniteGammaCancellation

/-!
# Shifted harmonic limit in Suzuki's equation (2.5)

This module evaluates the scalar divergence exposed by finite Gamma
cancellation.  The shifted cusp coefficient is a harmonic number minus
Gauss's quarter-point reciprocal partial sum, so its logarithmically
renormalized limit is fixed by the quarter-point digamma value.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Filter Topology
open scoped BigOperators
open ComplexCompactExhaustion

/-- The shifted cusp coefficient is a standard harmonic number minus Gauss's
quarter-point reciprocal partial sum. -/
theorem suzukiEquation25ShiftedHarmonicPartial_eq_harmonic_sub_gauss
    (N : Nat) :
    suzukiEquation25ShiftedHarmonicPartial N =
      (harmonic N : Real) -
        ∑ k ∈ Finset.range N,
          realGaussDigammaSeriesTerm (1 / 4) k := by
  unfold suzukiEquation25ShiftedHarmonicPartial
    realGaussDigammaSeriesTerm
  rw [Finset.sum_sub_distrib, sum_one_div_natCast_eq_harmonic]
  ring

/-- Before inserting the explicit quarter-point value, the renormalized
shifted harmonic coefficient tends to the negative real digamma value. -/
theorem tendsto_suzukiEquation25ShiftedHarmonicPartial_sub_log_digamma :
    Tendsto
      (fun N : Nat =>
        suzukiEquation25ShiftedHarmonicPartial N - Real.log N)
      atTop
      (nhds (-(Complex.digamma (1 / 4 : Complex)).re)) := by
  have hgauss := tendsto_realGaussDigammaSeriesPartialSum
    (x := (1 / 4 : Real)) (by norm_num)
  have hlimit := Real.tendsto_harmonic_sub_log.sub hgauss
  have hdigamma := congrArg Complex.re
    (digamma_ofReal_eq_deriv_logGamma
      (x := (1 / 4 : Real)) (by norm_num))
  have hdigamma' :
      (Complex.digamma (1 / 4 : Complex)).re =
        deriv (Real.log ∘ Real.Gamma) (1 / 4 : Real) := by
    convert hdigamma using 1 <;> norm_num
  convert hlimit using 1
  · funext N
    rw [suzukiEquation25ShiftedHarmonicPartial_eq_harmonic_sub_gauss]
    ring
  · rw [hdigamma']
    ring

/-- The exact scalar left by logarithmic renormalization of the shifted cusp
coefficient. -/
def suzukiEquation25ShiftedHarmonicLimitConstant : Real :=
  Real.eulerMascheroniConstant + Real.pi / 2 + 3 * Real.log 2

theorem tendsto_suzukiEquation25ShiftedHarmonicPartial_sub_log :
    Tendsto
      (fun N : Nat =>
        suzukiEquation25ShiftedHarmonicPartial N - Real.log N)
      atTop
      (nhds suzukiEquation25ShiftedHarmonicLimitConstant) := by
  have h := tendsto_suzukiEquation25ShiftedHarmonicPartial_sub_log_digamma
  have hquarter := congrArg Complex.re suzuki_digamma_one_fourth
  simp only [Complex.ofReal_re] at hquarter
  convert h using 1
  rw [hquarter]
  unfold suzukiEquation25ShiftedHarmonicLimitConstant
  ring

/-- Removing the Euler/scale constant leaves exactly the restoration scalar
already identified in the regular-kernel reduction. -/
theorem tendsto_suzukiEquation25ShiftedHarmonicPartial_sub_log_sub_scale :
    Tendsto
      (fun N : Nat =>
        suzukiEquation25ShiftedHarmonicPartial N - Real.log N -
          (Real.eulerMascheroniConstant + Real.log 2))
      atTop
      (nhds suzukiEquation25GammaRestorationScalar) := by
  have h :=
    tendsto_suzukiEquation25ShiftedHarmonicPartial_sub_log.sub_const
      (Real.eulerMascheroniConstant + Real.log 2)
  convert h using 1
  unfold suzukiEquation25ShiftedHarmonicLimitConstant
    suzukiEquation25GammaRestorationScalar
  ring

end

end M100
end Experiments
end RiemannHypothesisProject
