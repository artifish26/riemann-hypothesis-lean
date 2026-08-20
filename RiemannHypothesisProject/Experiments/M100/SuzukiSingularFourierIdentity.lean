import RiemannHypothesisProject.Experiments.M100.SuzukiSingularCutoffAssembly

/-!
# M100-DF6D2 singular/Fourier identity

This module takes the joint reciprocal-kernel cutoff limit in two ways.  The
physical decomposition converges to twice Suzuki's singular local form, while
finite Plancherel and the scalar cosine-integral asymptotic converge to twice
the logarithmic Fourier form.  Uniqueness of limits gives the exact source
identity on the Suzuki smooth core.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

/-- The exact finite-cutoff physical decomposition converges to twice the
singular local form along the joint lower/upper cutoff filter. -/
theorem tendsto_suzukiRenormalizedCutoffPhysicalPairing_to_local
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    Tendsto
      (fun p : Real × Real =>
        suzukiRenormalizedCutoffPhysicalPairing p.1 p.2 v.1)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (2 * suzukiSingularLocalForm a v.1)) := by
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεOneScalar : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ 1 := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < 1 :=
      mem_inf_of_left (Iio_mem_nhds zero_lt_one)
    exact hlt.mono fun ε hε => hε.le
  have hεOne : ∀ᶠ p in l, p.1 ≤ 1 :=
    tendsto_fst.eventually hεOneScalar
  have hR : ∀ᶠ p in l, 2 * a ≤ p.2 :=
    tendsto_snd.eventually (eventually_ge_atTop (2 * a))
  have hevent : ∀ᶠ p in l,
      suzukiRenormalizedCutoffPhysicalPairing p.1 p.2 v.1 =
        (1 / 2 : Real) *
            (∫ q in suzukiFiniteSquare a,
              suzukiCutoffSingularDifferenceIntegrand p.1 v.1 q) -
          ∫ x in Icc (-a) a,
            suzukiBoundaryCutoffIntegrand p.1 a v.1 x := by
    filter_upwards [hεpos, hεOne, hR] with p hp hεp hRp
    exact suzukiRenormalizedCutoffPhysicalPairing_eq_difference_sub_boundary
      hp hεp ha hRp v
  have hdifference :
      Tendsto
        (fun p : Real × Real =>
          ∫ q in suzukiFiniteSquare a,
            suzukiCutoffSingularDifferenceIntegrand p.1 v.1 q)
        l
        (𝓝 (∫ q in suzukiFiniteSquare a,
          ‖v.1 q.1 - v.1 q.2‖ ^ 2 / |q.1 - q.2|)) :=
    (tendsto_integral_suzukiCutoffSingularDifferenceIntegrand a v.1).comp
      tendsto_fst
  have hboundary :
      Tendsto
        (fun p : Real × Real =>
          ∫ x in Icc (-a) a,
            suzukiBoundaryCutoffIntegrand p.1 a v.1 x)
        l
        (𝓝 (∫ x in Icc (-a) a,
          Real.log (a ^ 2 - x ^ 2) * ‖v.1 x‖ ^ 2)) :=
    (tendsto_integral_suzukiBoundaryCutoffIntegrand ha v.1).comp tendsto_fst
  have hcombined :
      Tendsto
        (fun p : Real × Real =>
          (1 / 2 : Real) *
              (∫ q in suzukiFiniteSquare a,
                suzukiCutoffSingularDifferenceIntegrand p.1 v.1 q) -
            ∫ x in Icc (-a) a,
              suzukiBoundaryCutoffIntegrand p.1 a v.1 x)
        l
        (𝓝 ((1 / 2 : Real) *
            (∫ q in suzukiFiniteSquare a,
              ‖v.1 q.1 - v.1 q.2‖ ^ 2 / |q.1 - q.2|) -
          ∫ x in Icc (-a) a,
            Real.log (a ^ 2 - x ^ 2) * ‖v.1 x‖ ^ 2)) :=
    (tendsto_const_nhds.mul hdifference).sub hboundary
  have hlocal :
      Tendsto
        (fun p : Real × Real =>
          (1 / 2 : Real) *
              (∫ q in suzukiFiniteSquare a,
                suzukiCutoffSingularDifferenceIntegrand p.1 v.1 q) -
            ∫ x in Icc (-a) a,
              suzukiBoundaryCutoffIntegrand p.1 a v.1 x)
        l
        (𝓝 (2 * suzukiSingularLocalForm a v.1)) := by
    convert hcombined using 1
    unfold suzukiSingularLocalForm
    ring
  exact (tendsto_congr' hevent).2 hlocal

/-- Finite Plancherel and the scalar cutoff asymptotic give the second limit
of the same physical pairing. -/
theorem tendsto_suzukiRenormalizedCutoffPhysicalPairing_to_fourier
    (hasymptotic : SuzukiCosineIntegralAsymptotic)
    (v : SchwartzLineTestFunction) :
    Tendsto
      (fun p : Real × Real =>
        suzukiRenormalizedCutoffPhysicalPairing p.1 p.2 v)
      (𝓝[>] (0 : Real) ×ˢ atTop)
      (𝓝 (2 * suzukiSourceLogFourierForm v)) := by
  let l : Filter (Real × Real) := 𝓝[>] (0 : Real) ×ˢ atTop
  have hεpos : ∀ᶠ p in l, 0 < p.1 :=
    tendsto_fst.eventually self_mem_nhdsWithin
  have hεOneScalar : ∀ᶠ ε in 𝓝[>] (0 : Real), ε ≤ 1 := by
    have hlt : ∀ᶠ ε in 𝓝[>] (0 : Real), ε < 1 :=
      mem_inf_of_left (Iio_mem_nhds zero_lt_one)
    exact hlt.mono fun ε hε => hε.le
  have hεOne : ∀ᶠ p in l, p.1 ≤ 1 :=
    tendsto_fst.eventually hεOneScalar
  have hROne : ∀ᶠ p in l, 1 ≤ p.2 :=
    tendsto_snd.eventually (eventually_ge_atTop 1)
  have hevent : ∀ᶠ p in l,
      suzukiRenormalizedCutoffPhysicalPairing p.1 p.2 v =
        ∫ ξ : Real,
          suzukiRenormalizedCutoffFourierIntegrand p.1 p.2 v ξ := by
    filter_upwards [hεpos, hεOne, hROne] with p hp hεp hRp
    exact suzukiRenormalizedCutoffPhysicalPairing_eq_fourierIntegral
      hp hεp hRp v
  exact (tendsto_congr' hevent).2
    (tendsto_integral_suzukiRenormalizedCutoffFourierIntegrand
      hasymptotic v)

/-- The scalar cosine-integral asymptotic implies Suzuki's exact singular /
logarithmic-Fourier identity on every positive-radius smooth core. -/
theorem suzukiSingularFourierIdentityAt_of_asymptotic
    (hasymptotic : SuzukiCosineIntegralAsymptotic)
    {a : Real} (ha : 0 < a) :
    SuzukiSingularFourierIdentityAt a := by
  intro v
  have hlocal :=
    tendsto_suzukiRenormalizedCutoffPhysicalPairing_to_local ha v
  have hfourier :=
    tendsto_suzukiRenormalizedCutoffPhysicalPairing_to_fourier
      hasymptotic v.1
  have htwice :
      2 * suzukiSingularLocalForm a v.1 =
        2 * suzukiSourceLogFourierForm v.1 :=
    tendsto_nhds_unique hlocal hfourier
  linarith

/-- DF6D2's remaining classical scalar constant identity is sufficient for
the exact singular/Fourier identity. -/
theorem suzukiSingularFourierIdentityAt_of_constantIdentity
    (hconstant : SuzukiCosineIntegralConstantIdentity)
    {a : Real} (ha : 0 < a) :
    SuzukiSingularFourierIdentityAt a :=
  suzukiSingularFourierIdentityAt_of_asymptotic
    (suzukiCosineIntegralAsymptotic_of_constantIdentity hconstant) ha

end

end M100
end Experiments
end RiemannHypothesisProject
