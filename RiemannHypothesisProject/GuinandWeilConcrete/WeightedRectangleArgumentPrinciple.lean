import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import RiemannHypothesisProject.GuinandWeilConcrete.RectangleBoundaryIntegral

/-
Portions of the local simple-residue and logarithmic-derivative arguments are
adapted from PrimeNumberTheoremAnd, `ResidueCalcOnRectangles.lean` and
`RectangleArgumentPrinciple.lean`, licensed under Apache 2.0:

https://github.com/AlexKontorovich/PrimeNumberTheoremAnd

This version is modified for the current Mathlib API, uses project-local names,
and isolates the weighted local theorem before the rectangle-integration port.
-/

/-!
# Weighted logarithmic-derivative residues

This module begins the generic source theorem needed by the direct xi
rectangle proof.  It defines the simple-residue limit used by the cited
rectangle development and proves that an analytic weight `H` changes the
residue of `f'/f` at `p` from the meromorphic order of `f` to that order times
`H p`.

The theorem applies to zeros of arbitrary finite multiplicity: the logarithmic
derivative has a simple pole, while its residue records the full order.
-/

namespace RiemannHypothesisProject

noncomputable section

open Asymptotics Filter Function Set Topology
open scoped Topology

/-- The simple-residue limit used by the rectangle argument principle.  It is
the ordinary residue at analytic points and simple poles, which are the only
singularities used for logarithmic derivatives in this project. -/
noncomputable def guinandWeilSimpleResidue
    (F : Complex → Complex) (p : Complex) : Complex :=
  limUnder (𝓝[≠] p) (fun z => (z - p) * F z)

/-- Identify the simple residue from a proved punctured-neighborhood limit. -/
theorem guinandWeilSimpleResidue_eq_of_tendsto
    {F : Complex → Complex} {p c : Complex}
    (h : Tendsto (fun z => (z - p) * F z) (𝓝[≠] p) (𝓝 c)) :
    guinandWeilSimpleResidue F p = c := by
  unfold guinandWeilSimpleResidue
  exact h.limUnder_eq

/-- An analytic function has zero simple residue. -/
theorem guinandWeilSimpleResidue_eq_zero_of_analyticAt
    {F : Complex → Complex} {p : Complex}
    (hF : AnalyticAt Complex F p) :
    guinandWeilSimpleResidue F p = 0 := by
  apply guinandWeilSimpleResidue_eq_of_tendsto
  have hsub :
      Tendsto (fun z : Complex => z - p) (𝓝[≠] p) (𝓝 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Tendsto (fun z : Complex => z - p) (𝓝[≠] p) (𝓝 (p - p)))
  have hFtendsto : Tendsto F (𝓝[≠] p) (𝓝 (F p)) :=
    hF.continuousAt.continuousWithinAt.tendsto
  simpa using hsub.mul hFtendsto

private theorem tendsto_self_sub_mul_of_sub_principal_isBigO_one
    {F : Complex → Complex} {p c : Complex}
    (h : (F - fun z : Complex => c / (z - p)) =O[𝓝[≠] p]
      (1 : Complex → Complex)) :
    Tendsto (fun z : Complex => (z - p) * F z) (𝓝[≠] p) (𝓝 c) := by
  have hp_tendsto :
      Tendsto (fun z : Complex => z - p) (𝓝[≠] p) (𝓝 0) := by
    simpa using
      ((continuous_id.sub continuous_const).continuousAt.continuousWithinAt.tendsto :
        Tendsto (fun z : Complex => z - p) (𝓝[≠] p) (𝓝 (p - p)))
  have hp_small :
      (fun z : Complex => z - p) =o[𝓝[≠] p] (1 : Complex → Complex) :=
    (isLittleO_one_iff Complex).2 hp_tendsto
  have hrem_tendsto :
      Tendsto
        (fun z : Complex =>
          (z - p) * ((F - fun w : Complex => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 0) := by
    simpa using hp_small.mul_isBigO h
  have hprincipal :
      (fun z : Complex => (z - p) * (c / (z - p))) =ᶠ[𝓝[≠] p]
        fun _ : Complex => c := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    field_simp [sub_ne_zero.mpr hz]
  have hprincipal_tendsto :
      Tendsto (fun z : Complex => (z - p) * (c / (z - p)))
        (𝓝[≠] p) (𝓝 c) :=
    tendsto_const_nhds.congr' hprincipal.symm
  have hsum_tendsto :
      Tendsto
        (fun z : Complex =>
          (z - p) * (c / (z - p)) +
            (z - p) * ((F - fun w : Complex => c / (w - p)) z))
        (𝓝[≠] p) (𝓝 (c + 0)) :=
    hprincipal_tendsto.add hrem_tendsto
  have hsum :
      (fun z : Complex => (z - p) * F z) =ᶠ[𝓝[≠] p]
        fun z : Complex =>
          (z - p) * (c / (z - p)) +
            (z - p) * ((F - fun w : Complex => c / (w - p)) z) := by
    filter_upwards with z
    simp only [Pi.sub_apply]
    ring
  simpa using hsum_tendsto.congr' hsum.symm

/-- After removing its order principal part, the logarithmic derivative of a
meromorphic function is locally bounded. -/
theorem logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt
    {f : Complex → Complex} {p : Complex} {n : Int}
    (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = (n : WithTop Int)) :
    (logDeriv f - fun s : Complex => (n : Complex) / (s - p)) =O[𝓝[≠] p]
      (1 : Complex → Complex) := by
  obtain ⟨g, hg_analytic, hg_ne, hfg⟩ :=
    (meromorphicOrderAt_eq_int_iff hf).1 horder
  let factored : Complex → Complex := fun s => (s - p) ^ n * g s
  have hfg_ne : f =ᶠ[𝓝[≠] p] factored := by
    filter_upwards [hfg] with s hs
    simpa [factored, smul_eq_mul] using hs
  have hderiv_ne : deriv f =ᶠ[𝓝[≠] p] deriv factored :=
    hfg_ne.nhdsNE_deriv
  have hg_nonzero_ne : ∀ᶠ s in 𝓝[≠] p, g s ≠ 0 := by
    exact (hg_analytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hg_ne
      |>.filter_mono nhdsWithin_le_nhds
  have hg_analytic_ne : ∀ᶠ s in 𝓝[≠] p, AnalyticAt Complex g s := by
    exact hg_analytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hlog_eq :
      (logDeriv f - fun s : Complex => (n : Complex) / (s - p)) =ᶠ[𝓝[≠] p]
        logDeriv g := by
    filter_upwards [hfg_ne, hderiv_ne, self_mem_nhdsWithin,
      hg_nonzero_ne, hg_analytic_ne]
      with s hfs hderiv hs_ne hgs_ne hgs_analytic
    have hpow_ne : (s - p) ^ n ≠ 0 :=
      zpow_ne_zero n (sub_ne_zero.mpr hs_ne)
    have hdiff_pow :
        DifferentiableAt Complex (fun z : Complex => (z - p) ^ n) s := by
      exact ((by fun_prop : DifferentiableAt Complex (fun z : Complex => z - p) s)).zpow
        (Or.inl (sub_ne_zero.mpr hs_ne))
    have hlog_factored :
        logDeriv factored s =
          logDeriv (fun z : Complex => (z - p) ^ n) s + logDeriv g s := by
      exact logDeriv_mul (f := fun z : Complex => (z - p) ^ n) (g := g) s
        hpow_ne hgs_ne hdiff_pow hgs_analytic.differentiableAt
    have hlog_pow :
        logDeriv (fun z : Complex => (z - p) ^ n) s =
          (n : Complex) / (s - p) := by
      rw [logDeriv_fun_zpow
        (f := fun z : Complex => z - p) (x := s) (by fun_prop) n]
      simp [logDeriv_apply, div_eq_mul_inv]
    simp only [Pi.sub_apply]
    calc
      logDeriv f s - (n : Complex) / (s - p) =
          logDeriv factored s - (n : Complex) / (s - p) := by
        simp [logDeriv_apply, hfs, hderiv]
      _ = logDeriv g s := by
        rw [hlog_factored, hlog_pow]
        ring
  have hderiv_bounded : deriv g =O[𝓝 p] (1 : Complex → Complex) :=
    hg_analytic.deriv.continuousAt.norm.isBoundedUnder_le.isBigO_one Complex
  have hinv_bounded : g⁻¹ =O[𝓝 p] (1 : Complex → Complex) :=
    (hg_analytic.continuousAt.inv₀ hg_ne).norm.isBoundedUnder_le.isBigO_one Complex
  have hlog_bounded : logDeriv g =O[𝓝 p] (1 : Complex → Complex) := by
    have hmul_bounded :
        (deriv g * g⁻¹) =O[𝓝 p]
          ((1 : Complex → Complex) * (1 : Complex → Complex)) :=
      IsBigO.mul hderiv_bounded hinv_bounded
    have hmul_bounded' :
        (fun x => deriv g x * (g x)⁻¹) =O[𝓝 p] (1 : Complex → Complex) := by
      refine hmul_bounded.congr ?_ ?_
      · intro x
        rfl
      · intro x
        simp
    change (fun x => deriv g x / g x) =O[𝓝 p] (1 : Complex → Complex)
    simpa only [div_eq_mul_inv] using hmul_bounded'
  exact hlog_eq.trans_isBigO (hlog_bounded.mono nhdsWithin_le_nhds)

/-- The punctured-neighborhood logarithmic residue tends to the full
meromorphic order, including multiplicity. -/
theorem tendsto_self_sub_mul_logDeriv_of_meromorphicOrderAt
    {f : Complex → Complex} {p : Complex} {n : Int}
    (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = (n : WithTop Int)) :
    Tendsto (fun z : Complex => (z - p) * logDeriv f z)
      (𝓝[≠] p) (𝓝 (n : Complex)) :=
  tendsto_self_sub_mul_of_sub_principal_isBigO_one
    (logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf horder)

/-- The simple residue of a logarithmic derivative is the meromorphic order. -/
theorem guinandWeilSimpleResidue_logDeriv_eq_meromorphicOrderAt
    {f : Complex → Complex} {p : Complex} {n : Int}
    (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = (n : WithTop Int)) :
    guinandWeilSimpleResidue (logDeriv f) p = (n : Complex) :=
  guinandWeilSimpleResidue_eq_of_tendsto
    (tendsto_self_sub_mul_logDeriv_of_meromorphicOrderAt hf horder)

/-- Multiplying a logarithmic derivative by an analytic weight evaluates that
weight at the pole and preserves the full order as the residue coefficient. -/
theorem guinandWeilSimpleResidue_weight_mul_logDeriv_eq
    {H f : Complex → Complex} {p : Complex} {n : Int}
    (hH : AnalyticAt Complex H p)
    (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = (n : WithTop Int)) :
    guinandWeilSimpleResidue (fun z => H z * logDeriv f z) p =
      H p * (n : Complex) := by
  apply guinandWeilSimpleResidue_eq_of_tendsto
  have hHtendsto : Tendsto H (𝓝[≠] p) (𝓝 (H p)) :=
    hH.continuousAt.continuousWithinAt.tendsto
  have hlogtendsto :=
    tendsto_self_sub_mul_logDeriv_of_meromorphicOrderAt hf horder
  have hproduct :
      Tendsto (fun z => H z * ((z - p) * logDeriv f z))
        (𝓝[≠] p) (𝓝 (H p * (n : Complex))) :=
    hHtendsto.mul hlogtendsto
  convert hproduct using 1
  funext z
  ring

/-- Removing the weighted order principal part leaves a locally bounded
function.  This is the removable-singularity input needed to construct the
analytic remainder in the finite rectangle theorem. -/
theorem weight_mul_logDeriv_sub_principal_isBigO_one
    {H f : Complex → Complex} {p : Complex} {n : Int}
    (hH : AnalyticAt Complex H p)
    (hf : MeromorphicAt f p)
    (horder : meromorphicOrderAt f p = (n : WithTop Int)) :
    ((fun z => H z * logDeriv f z) -
        fun z => (H p * (n : Complex)) / (z - p)) =O[𝓝[≠] p]
      (1 : Complex → Complex) := by
  have hlog :=
    logDeriv_sub_principal_isBigO_one_of_meromorphicOrderAt hf horder
  have hHbounded : H =O[𝓝[≠] p] (1 : Complex → Complex) := by
    exact (hH.continuousAt.norm.isBoundedUnder_le.isBigO_one Complex).mono
      nhdsWithin_le_nhds
  have hfirst :
      (fun z => H z *
        (logDeriv f z - (n : Complex) / (z - p))) =O[𝓝[≠] p]
        (fun _ : Complex => (1 : Complex)) := by
    have hmul := hHbounded.mul hlog
    simpa only [Pi.sub_apply, Pi.one_apply, one_mul] using hmul
  have hslope_continuous : ContinuousAt (dslope H p) p :=
    continuousAt_dslope_same.2 hH.differentiableAt
  have hslope_bigO : dslope H p =O[𝓝 p] (1 : Complex → Complex) :=
    hslope_continuous.norm.isBoundedUnder_le.isBigO_one Complex
  have hslope_ne :
      (fun z => (H z - H p) / (z - p)) =O[𝓝[≠] p]
        (1 : Complex → Complex) := by
    have hrestricted :
        dslope H p =O[nhdsWithin p {p}ᶜ] (1 : Complex → Complex) :=
      hslope_bigO.mono nhdsWithin_le_nhds
    refine hrestricted.congr' ?_ .rfl
    filter_upwards [dslope_eventuallyEq_slope_nhdsNE (f := H) (a := p)]
      with z hz
    simpa [slope, div_eq_mul_inv, mul_comm] using hz
  have hsecond :
      (fun z => (n : Complex) * ((H z - H p) / (z - p))) =O[𝓝[≠] p]
        (1 : Complex → Complex) := by
    simpa using hslope_ne.const_mul_left (n : Complex)
  have hsum := hfirst.add hsecond
  refine hsum.congr' ?_ .rfl
  filter_upwards with z
  simp only [Pi.sub_apply]
  ring

/-- A meromorphic function that is locally bounded on a punctured
neighborhood has nonnegative meromorphic order. -/
theorem meromorphicOrderAt_nonneg_of_isBigO_one
    {F : Complex → Complex} {p : Complex}
    (_hF : MeromorphicAt F p)
    (hO : F =O[𝓝[≠] p] (1 : Complex → Complex)) :
    0 ≤ meromorphicOrderAt F p := by
  by_contra hnonneg
  have hnegative : meromorphicOrderAt F p < 0 := lt_of_not_ge hnonneg
  have hnorm :
      Tendsto (fun z : Complex => ‖F z‖) (𝓝[≠] p) Filter.atTop := by
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hnegative
  exact (Filter.not_isBoundedUnder_of_tendsto_atTop hnorm)
    hO.isBoundedUnder_le

/-- The weighted logarithmic derivative is meromorphic wherever the weight is
analytic and the original function is meromorphic. -/
theorem meromorphicOn_weight_mul_logDeriv
    {H f : Complex → Complex} {U : Set Complex}
    (hH : AnalyticOnNhd Complex H U)
    (hf : MeromorphicOn f U) :
    MeromorphicOn (fun z => H z * logDeriv f z) U :=
  hH.meromorphicOn.mul hf.logDeriv

/-- Weighted argument principle on a rectangle for an analytic function with
an explicitly identified finite zero set.  The coefficient at each zero is
its complete analytic order, so zeros of arbitrary finite multiplicity are
counted correctly. -/
theorem guinandWeilNormalizedRectangleIntegral_weight_mul_logDeriv_eq_sum
    {H f : Complex → Complex} {z w : Complex} {S : Finset Complex}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hH : AnalyticOnNhd Complex H (Complex.Rectangle z w))
    (hf : AnalyticOnNhd Complex f (Complex.Rectangle z w))
    (hfinite : ∀ s ∈ Complex.Rectangle z w, analyticOrderAt f s ≠ ⊤)
    (hSsubset : (S : Set Complex) ⊆ Complex.Rectangle z w)
    (hzeros : ∀ s ∈ Complex.Rectangle z w, s ∈ S ↔ f s = 0)
    (hboundary : ∀ s ∈ guinandWeilRectangleBorder z w, f s ≠ 0) :
    guinandWeilNormalizedRectangleIntegral
        (fun s => H s * logDeriv f s) z w =
      ∑ s ∈ S, H s * (analyticOrderNatAt f s : Complex) := by
  classical
  let R : Set Complex := Complex.Rectangle z w
  let F : Complex → Complex := fun s => H s * logDeriv f s
  let P : Complex → Complex := fun s =>
    ∑ p ∈ S, (H p * (analyticOrderNatAt f p : Complex)) / (s - p)
  let Q : Complex → Complex := fun s => F s - P s
  let G : Complex → Complex := toMeromorphicNFOn Q R
  have hFmero : MeromorphicOn F R := by
    exact meromorphicOn_weight_mul_logDeriv hH hf.meromorphicOn
  have hPmero : MeromorphicOn P R := by
    dsimp only [P]
    apply MeromorphicOn.fun_sum
    intro p x _hx
    exact (MeromorphicAt.const
      (H p * (analyticOrderNatAt f p : Complex)) x).div
        ((MeromorphicAt.id x).sub (MeromorphicAt.const p x))
  have hQmero : MeromorphicOn Q R := by
    exact hFmero.sub hPmero
  have hQanalytic_of_not_mem :
      ∀ {x : Complex}, x ∈ R → x ∉ S → AnalyticAt Complex Q x := by
    intro x hxR hxS
    have hfx : f x ≠ 0 := by
      intro hzero
      exact hxS ((hzeros x hxR).mpr hzero)
    have hlog : AnalyticAt Complex (logDeriv f) x := by
      simpa [logDeriv] using (hf x hxR).deriv.div (hf x hxR) hfx
    have hFan : AnalyticAt Complex F x := by
      exact (hH x hxR).mul hlog
    have hPan : AnalyticAt Complex P x := by
      dsimp only [P]
      apply Finset.analyticAt_fun_sum
      intro p hpS
      have hxp : x ≠ p := by
        intro hxp
        apply hxS
        simpa [hxp] using hpS
      fun_prop (disch := exact sub_ne_zero.mpr hxp)
    exact hFan.sub hPan
  have hQorder : ∀ x ∈ R, 0 ≤ meromorphicOrderAt Q x := by
    intro x hxR
    by_cases hxS : x ∈ S
    · have horder :
          meromorphicOrderAt f x =
            (((analyticOrderNatAt f x : Nat) : Int) : WithTop Int) := by
        rw [(hf x hxR).meromorphicOrderAt_eq]
        rw [← ENat.coe_toNat (hfinite x hxR)]
        rfl
      have hlocal :=
        weight_mul_logDeriv_sub_principal_isBigO_one
          (hH x hxR) (hf x hxR).meromorphicAt horder
      have hrestAnalytic : AnalyticAt Complex
          (fun s => ∑ p ∈ S.erase x,
            (H p * (analyticOrderNatAt f p : Complex)) / (s - p)) x := by
        apply Finset.analyticAt_fun_sum
        intro p hp
        have hpx : p ≠ x := Finset.ne_of_mem_erase hp
        fun_prop (disch := exact sub_ne_zero.mpr hpx.symm)
      have hrestO :
          (fun s => ∑ p ∈ S.erase x,
            (H p * (analyticOrderNatAt f p : Complex)) / (s - p))
            =O[nhdsWithin x {x}ᶜ] (1 : Complex → Complex) := by
        exact (hrestAnalytic.continuousAt.norm.isBoundedUnder_le
          |>.isBigO_one Complex).mono nhdsWithin_le_nhds
      have hQO : Q =O[nhdsWithin x {x}ᶜ] (1 : Complex → Complex) := by
        have hsub := hlocal.sub hrestO
        simp only [Int.cast_natCast] at hsub
        refine hsub.congr' ?_ .rfl
        filter_upwards with s
        dsimp only [Q, F, P]
        rw [← Finset.add_sum_erase S
          (fun p => (H p * (analyticOrderNatAt f p : Complex)) / (s - p)) hxS]
        simp only [Pi.sub_apply]
        ring_nf
      exact meromorphicOrderAt_nonneg_of_isBigO_one (hQmero x hxR) hQO
    · exact (hQanalytic_of_not_mem hxR hxS).meromorphicOrderAt_nonneg
  have hGdiff : DifferentiableOn Complex G R := by
    intro x hxR
    have hGNF : MeromorphicNFAt G x :=
      meromorphicNFOn_toMeromorphicNFOn Q R hxR
    have hGanalytic : AnalyticAt Complex G x := by
      apply hGNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      change 0 ≤ meromorphicOrderAt (toMeromorphicNFOn Q R) x
      rw [meromorphicOrderAt_toMeromorphicNFOn hQmero hxR]
      exact hQorder x hxR
    exact hGanalytic.differentiableAt.differentiableWithinAt
  have hpInterior : ∀ p ∈ S, R ∈ nhds p := by
    intro p hpS
    have hpR : p ∈ R := hSsubset hpS
    have hpnot : p ∉ guinandWeilRectangleBorder z w := by
      intro hpBorder
      exact hboundary p hpBorder ((hzeros p hpR).mp hpS)
    exact guinandWeilRectangle_mem_nhds_of_mem_not_border
      hzre hzim hpR hpnot
  apply guinandWeilNormalizedRectangleIntegral_eq_sum_of_analyticRemainder
    hzre hzim hpInterior hGdiff
  intro s hsBorder
  have hsR : s ∈ R := guinandWeilRectangleBorder_subset_rectangle z w hsBorder
  have hsnot : s ∉ S := by
    intro hsS
    exact hboundary s hsBorder ((hzeros s hsR).mp hsS)
  have hQan := hQanalytic_of_not_mem hsR hsnot
  have hGvalue : G s = Q s := by
    change toMeromorphicNFOn Q R s = Q s
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hQmero hsR,
      toMeromorphicNFAt_eq_self.2 hQan.meromorphicNFAt]
  dsimp only [F, P, Q] at hGvalue ⊢
  rw [hGvalue]
  ring

end

end RiemannHypothesisProject
