import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.PSeries
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.GaussDigammaReal

/-!
# Holomorphy and continuation of Gauss's digamma series

The reciprocal terms have derivatives bounded by a shifted `p = 2` series on
every smaller right half-plane.  This gives a holomorphic sum and lets the
positive-real identity extend to the full half-plane.
-/

open Filter Set Topology

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Derivative term of Gauss's reciprocal series. -/
def gaussDigammaSeriesDerivativeTerm (z : Complex) (k : Nat) : Complex :=
  1 / (z + k) ^ 2

/-- Each reciprocal term is holomorphic away from its single negative-integer
pole. -/
theorem hasDerivAt_gaussDigammaSeriesTerm
    {z : Complex} {k : Nat} (hzk : z + k ≠ 0) :
    HasDerivAt (fun w : Complex => gaussDigammaSeriesTerm w k)
      (gaussDigammaSeriesDerivativeTerm z k) z := by
  have hlinear : HasDerivAt (fun w : Complex => w + k) 1 z :=
    (hasDerivAt_id z).add_const (k : Complex)
  have hinv := hlinear.inv hzk
  have hconst : HasDerivAt
      (fun _ : Complex => 1 / (k + 1 : Complex)) 0 z :=
    hasDerivAt_const z _
  have hfunction :
      (fun w : Complex => gaussDigammaSeriesTerm w k) =ᶠ[𝓝 z]
        ((fun _ : Complex => 1 / (k + 1 : Complex)) -
          (fun w : Complex => w + k)⁻¹) := by
    filter_upwards with w
    simp only [gaussDigammaSeriesTerm, Pi.sub_apply, Pi.inv_apply, one_div]
  have hderiv := (hconst.sub hinv).congr_of_eventuallyEq hfunction
  apply hderiv.congr_deriv
  simp only [gaussDigammaSeriesDerivativeTerm]
  ring

/-- The shifted inverse-square majorant is summable whenever its shift is
positive. -/
theorem summable_one_div_nat_add_sq {b : Real} (hb : 0 < b) :
    Summable (fun k : Nat => 1 / ((k : Real) + b) ^ 2) := by
  have h := (Real.summable_one_div_nat_add_rpow b 2).2 (by norm_num)
  apply h.congr
  intro k
  rw [abs_of_pos (by
    have hk : (0 : Real) ≤ k := Nat.cast_nonneg k
    linarith), Real.rpow_two]

/-- On `b < re z`, the derivative terms are dominated by a shifted inverse
square series. -/
theorem norm_gaussDigammaSeriesDerivativeTerm_le
    {b : Real} {z : Complex} (hb : 0 < b) (hz : b < z.re) (k : Nat) :
    ‖gaussDigammaSeriesDerivativeTerm z k‖ ≤
      1 / ((k : Real) + b) ^ 2 := by
  have hRe : (k : Real) + b ≤ ‖z + k‖ := by
    calc
      (k : Real) + b ≤ (z + k).re := by
        simp only [Complex.add_re, Complex.natCast_re]
        linarith
      _ ≤ ‖z + k‖ := Complex.re_le_norm _
  simp only [gaussDigammaSeriesDerivativeTerm, norm_div, norm_one, norm_pow]
  have hk : (0 : Real) ≤ k := Nat.cast_nonneg k
  gcongr <;> positivity

/-- Gauss's reciprocal series is summable at every point of the right
half-plane. -/
theorem summable_gaussDigammaSeriesTerm {z : Complex} (hz : 0 < z.re) :
    Summable (fun k : Nat => gaussDigammaSeriesTerm z k) := by
  let b : Real := min z.re 1 / 2
  let t : Set Complex := {w | b < w.re}
  let u : Nat → Real := fun k => 1 / ((k : Real) + b) ^ 2
  have hmin : 0 < min z.re 1 := lt_min hz zero_lt_one
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hbz : b < z.re := by
    have hle : min z.re 1 ≤ z.re := min_le_left _ _
    dsimp only [b]
    nlinarith
  have hb1 : b < 1 := by
    have hle : min z.re 1 ≤ 1 := min_le_right _ _
    dsimp only [b]
    nlinarith
  have hu : Summable u := summable_one_div_nat_add_sq hb
  have ht : IsOpen t := by
    exact isOpen_Ioi.preimage Complex.continuous_re
  have htc : IsPreconnected t :=
    (convex_halfSpace_re_gt b).isPreconnected
  have hder : ∀ k w, w ∈ t →
      HasDerivAt (fun v : Complex => gaussDigammaSeriesTerm v k)
        (gaussDigammaSeriesDerivativeTerm w k) w := by
    intro k w hw
    apply hasDerivAt_gaussDigammaSeriesTerm
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.natCast_re]
    have hk : (0 : Real) ≤ k := Nat.cast_nonneg k
    change b < w.re at hw
    linarith
  have hbound : ∀ k w, w ∈ t →
      ‖gaussDigammaSeriesDerivativeTerm w k‖ ≤ u k := by
    intro k w hw
    exact norm_gaussDigammaSeriesDerivativeTerm_le hb hw k
  have hbase : Summable
      (fun k : Nat => gaussDigammaSeriesTerm (1 : Complex) k) := by
    simpa [gaussDigammaSeriesTerm, add_comm] using
      (summable_zero : Summable (fun _ : Nat => (0 : Complex)))
  apply summable_of_summable_hasDerivAt_of_isPreconnected
    hu ht htc hder hbound (y₀ := (1 : Complex))
  · exact hb1
  · exact hbase
  · exact hbz

/-- The holomorphic sum of Gauss's reciprocal series. -/
def gaussDigammaSeriesSum (z : Complex) : Complex :=
  ∑' k : Nat, gaussDigammaSeriesTerm z k

/-- The reciprocal-series sum is complex differentiable throughout the right
half-plane. -/
theorem hasDerivAt_gaussDigammaSeriesSum {z : Complex} (hz : 0 < z.re) :
    HasDerivAt gaussDigammaSeriesSum
      (∑' k : Nat, gaussDigammaSeriesDerivativeTerm z k) z := by
  let b : Real := z.re / 2
  let t : Set Complex := {w | b < w.re}
  let u : Nat → Real := fun k => 1 / ((k : Real) + b) ^ 2
  have hb : 0 < b := by
    dsimp only [b]
    positivity
  have hbz : b < z.re := by
    dsimp only [b]
    linarith
  have hu : Summable u := summable_one_div_nat_add_sq hb
  have ht : IsOpen t := isOpen_Ioi.preimage Complex.continuous_re
  have htc : IsPreconnected t :=
    (convex_halfSpace_re_gt b).isPreconnected
  have hder : ∀ k w, w ∈ t →
      HasDerivAt (fun v : Complex => gaussDigammaSeriesTerm v k)
        (gaussDigammaSeriesDerivativeTerm w k) w := by
    intro k w hw
    apply hasDerivAt_gaussDigammaSeriesTerm
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.natCast_re]
    have hk : (0 : Real) ≤ k := Nat.cast_nonneg k
    change b < w.re at hw
    linarith
  have hbound : ∀ k w, w ∈ t →
      ‖gaussDigammaSeriesDerivativeTerm w k‖ ≤ u k := by
    intro k w hw
    exact norm_gaussDigammaSeriesDerivativeTerm_le hb hw k
  change HasDerivAt
    (fun w : Complex => ∑' k : Nat, gaussDigammaSeriesTerm w k)
    (∑' k : Nat, gaussDigammaSeriesDerivativeTerm z k) z
  apply hasDerivAt_tsum_of_isPreconnected
    hu ht htc hder hbound (y₀ := z)
  · exact hbz
  · exact summable_gaussDigammaSeriesTerm hz
  · exact hbz

/-- Pointwise differentiability form of
`hasDerivAt_gaussDigammaSeriesSum`. -/
theorem differentiableAt_gaussDigammaSeriesSum {z : Complex} (hz : 0 < z.re) :
    DifferentiableAt Complex gaussDigammaSeriesSum z :=
  (hasDerivAt_gaussDigammaSeriesSum hz).differentiableAt

/-- The series sum agrees with the already-constructed Gauss integral on the
right half-plane. -/
theorem gaussDigammaSeriesSum_eq_integral {z : Complex} (hz : 0 < z.re) :
    gaussDigammaSeriesSum z =
      ∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand z x := by
  have hsum := summable_gaussDigammaSeriesTerm hz
  exact ((Summable.hasSum_iff_tendsto_nat hsum).2
    (tendsto_gaussDigammaSeriesPartialSum hz)).tsum_eq

/-- On positive real arguments the series sum is `digamma x + γ`. -/
theorem gaussDigammaSeriesSum_ofReal {x : Real} (hx : 0 < x) :
    gaussDigammaSeriesSum (x : Complex) =
      Complex.digamma (x : Complex) + Real.eulerMascheroniConstant := by
  have hsum := summable_gaussDigammaSeriesTerm (z := (x : Complex)) (by simpa)
  exact ((Summable.hasSum_iff_tendsto_nat hsum).2
    (tendsto_gaussDigammaSeriesPartialSum_ofReal hx)).tsum_eq

/-- The reciprocal-series sum is analytic on the right half-plane. -/
theorem analyticOnNhd_gaussDigammaSeriesSum :
    AnalyticOnNhd Complex gaussDigammaSeriesSum
      {z : Complex | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (differentiableAt_gaussDigammaSeriesSum hz).differentiableWithinAt
  · exact isOpen_Ioi.preimage Complex.continuous_re

/-- The complex digamma function is analytic at every point of the right
half-plane. -/
theorem analyticAt_digamma_of_re_pos {z : Complex} (hz : 0 < z.re) :
    AnalyticAt Complex Complex.digamma z := by
  have hGammaDiff : DifferentiableAt Complex Complex.Gamma z :=
    Complex.differentiableAt_Gamma z (fun m => by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
  have hGammaAnalytic : AnalyticAt Complex Complex.Gamma z :=
    (Meromorphic.Gamma z).analyticAt hGammaDiff.continuousAt
  have hquotient := hGammaAnalytic.deriv.div hGammaAnalytic
    (Complex.Gamma_ne_zero_of_re_pos hz)
  simpa [Complex.digamma_def, logDeriv] using hquotient

/-- `digamma + γ` is analytic on the right half-plane. -/
theorem analyticOnNhd_digamma_add_eulerMascheroni :
    AnalyticOnNhd Complex
      (fun z : Complex =>
        Complex.digamma z + Real.eulerMascheroniConstant)
      {z : Complex | 0 < z.re} := by
  intro z hz
  exact (analyticAt_digamma_of_re_pos hz).add analyticAt_const

/-- The positive real identities accumulate at `1`, providing the seed set
for the complex identity theorem. -/
theorem one_mem_closure_gaussDigammaSeriesSum_eq_digamma :
    (1 : Complex) ∈ closure
      ({z : Complex |
          gaussDigammaSeriesSum z =
            Complex.digamma z + Real.eulerMascheroniConstant} \ {1}) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let x : Real := 1 + ε / 2
  refine ⟨(x : Complex), ⟨?_, ?_⟩, ?_⟩
  · exact gaussDigammaSeriesSum_ofReal (by
      dsimp only [x]
      linarith)
  · simp only [Set.mem_singleton_iff]
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hre
    dsimp only [x] at hre
    linarith
  · simpa [x, abs_of_pos hε] using (half_lt_self hε)

/-- Gauss's reciprocal series equals `digamma + γ` throughout the right
half-plane. -/
theorem gaussDigammaSeriesSum_eq_digamma_add_eulerMascheroni :
    Set.EqOn gaussDigammaSeriesSum
      (fun z : Complex =>
        Complex.digamma z + Real.eulerMascheroniConstant)
      {z : Complex | 0 < z.re} := by
  exact analyticOnNhd_gaussDigammaSeriesSum.eqOn_of_preconnected_of_mem_closure
    analyticOnNhd_digamma_add_eulerMascheroni
    (convex_halfSpace_re_gt 0).isPreconnected
    (by norm_num : (1 : Complex) ∈ {z : Complex | 0 < z.re})
    one_mem_closure_gaussDigammaSeriesSum_eq_digamma

/-- Unconditional proof of Gauss's right-half-plane integral formula in the
source normalization. -/
theorem gaussDigammaIntegralFormula : GaussDigammaIntegralFormula := by
  intro z hz
  calc
    Complex.digamma z + Real.eulerMascheroniConstant =
        gaussDigammaSeriesSum z :=
      (gaussDigammaSeriesSum_eq_digamma_add_eulerMascheroni hz).symm
    _ = ∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand z x :=
      gaussDigammaSeriesSum_eq_integral hz

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
