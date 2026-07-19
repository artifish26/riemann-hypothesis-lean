import Mathlib.Analysis.Complex.AbelLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Order.Filter.AtTopBot.Basic
import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisCleanup
import RiemannHypothesisProject.ZetaConjugation
import RiemannHypothesisProject.ZetaSetup

/-!
# Dirichlet eta alternating-series tools

This module contains the base eta alternating-series terms, partial sums,
alternating-limit package, conditional-sum bridge, Abel power-series limit, and
positivity facts used by the Riemann-von-Mangoldt real-axis cleanup route.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section

/-- The `n`th term of the real Dirichlet eta alternating series. -/
def dirichletEtaSeriesTerm (x : Real) (n : Nat) : Real :=
  (-1 : Real) ^ n * (((n : Real) + 1) ^ (-x))

/-- The complex cast of the `n`th Dirichlet eta alternating-series term. -/
def dirichletEtaComplexSeriesTerm (x : Real) (n : Nat) : Complex :=
  (dirichletEtaSeriesTerm x n : Complex)

/--
The `n`th partial sum of the real Dirichlet eta alternating series
`1 - 2^(-x) + 3^(-x) - ...`.

For `0 < x <= 1` this series is conditionally convergent, so it is deliberately
recorded as a sequential partial-sum limit rather than as an unconditional
`tsum`.
-/
def dirichletEtaPartialSum (x : Real) (n : Nat) : Real :=
  (Finset.range n).sum fun i =>
    (-1 : Real) ^ i * (((i : Real) + 1) ^ (-x))

/-- The partial-sum definition is the finite sum of the named eta terms. -/
theorem dirichletEtaPartialSum_eq_sum_seriesTerm (x : Real) (n : Nat) :
    dirichletEtaPartialSum x n =
      (Finset.range n).sum (dirichletEtaSeriesTerm x) := by
  rfl

/--
A real number `eta` is the sequential alternating-series value of the
Dirichlet eta series at `x`.
-/
def DirichletEtaAlternatingLimit (x eta : Real) : Prop :=
  Tendsto (fun n : Nat => dirichletEtaPartialSum x n) atTop (nhds eta)

/-- The eta positive terms `(n + 1)^(-x)` decrease for `0 < x`. -/
theorem dirichletEtaTerm_antitone_of_pos {x : Real} (hx : 0 < x) :
    Antitone fun n : Nat => (((n : Real) + 1) ^ (-x)) := by
  intro m n hmn
  have hanti :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show -x <= 0 by linarith)
  have hm_pos : 0 < (m : Real) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hn_pos : 0 < (n : Real) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) zero_lt_one
  have hmn_real : (m : Real) <= (n : Real) := by
    exact_mod_cast hmn
  have hle : (m : Real) + 1 <= (n : Real) + 1 := by
    linarith
  exact hanti hm_pos hn_pos hle

/-- The eta positive terms `(n + 1)^(-x)` tend to zero for `0 < x`. -/
theorem dirichletEtaTerm_tendsto_zero_of_pos {x : Real} (hx : 0 < x) :
    Tendsto (fun n : Nat => (((n : Real) + 1) ^ (-x))) atTop (nhds 0) := by
  have hnat : Tendsto (fun n : Nat => (n : Real) + 1) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop 1
      tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using (tendsto_rpow_neg_atTop hx).comp hnat

/-- The real Dirichlet eta alternating series has a sequential limit for `0 < x`. -/
theorem exists_dirichletEtaAlternatingLimit_of_pos {x : Real} (hx : 0 < x) :
    Exists (DirichletEtaAlternatingLimit x) := by
  let h_exists :=
    (dirichletEtaTerm_antitone_of_pos hx).tendsto_alternating_series_of_tendsto_zero
      (dirichletEtaTerm_tendsto_zero_of_pos hx)
  let eta := Classical.choose h_exists
  have heta := Classical.choose_spec h_exists
  exact Exists.intro eta
    (by
      simpa [DirichletEtaAlternatingLimit, dirichletEtaPartialSum] using heta)

/--
The canonical sequential alternating-series value of Dirichlet eta at `x`.

For `x <= 0` this is the harmless junk value `0`; all project use below is
guarded by `0 < x`.
-/
noncomputable def dirichletEtaAlternatingValue (x : Real) : Real :=
  if hx : 0 < x then
    Classical.choose (exists_dirichletEtaAlternatingLimit_of_pos hx)
  else
    0

/-- The canonical eta value is realized by the alternating partial sums. -/
theorem dirichletEtaAlternatingValue_spec {x : Real} (hx : 0 < x) :
    DirichletEtaAlternatingLimit x (dirichletEtaAlternatingValue x) := by
  simp [dirichletEtaAlternatingValue, hx,
    Classical.choose_spec (exists_dirichletEtaAlternatingLimit_of_pos hx)]

/--
The sequential eta limit is exactly Lean's conditional summation over `Nat`.

This uses `SummationFilter.conditional Nat`, whose filter is the ordinary
partial-sum filter `Finset.range n` as `n -> infinity`.  The theorem is
deliberately not stated with the default unconditional `HasSum`, since the eta
series on `(0, 1)` is only conditionally convergent.
-/
theorem dirichletEtaAlternatingLimit_hasSum_conditional {x eta : Real}
    (hlim : DirichletEtaAlternatingLimit x eta) :
    HasSum (dirichletEtaSeriesTerm x) eta
      (SummationFilter.conditional Nat) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  simpa [Function.comp_def, DirichletEtaAlternatingLimit,
    dirichletEtaPartialSum, dirichletEtaSeriesTerm] using hlim

/-- Conditional eta summability recovers the sequential alternating limit. -/
theorem dirichletEtaAlternatingLimit_of_hasSum_conditional {x eta : Real}
    (hsum : HasSum (dirichletEtaSeriesTerm x) eta
      (SummationFilter.conditional Nat)) :
    DirichletEtaAlternatingLimit x eta := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff] at hsum
  have hlim :
      Tendsto (fun n : Nat =>
        (Finset.range n).sum (dirichletEtaSeriesTerm x))
        atTop (nhds eta) := by
    simpa [Function.comp_def] using hsum
  simpa [DirichletEtaAlternatingLimit, dirichletEtaPartialSum,
    dirichletEtaSeriesTerm] using hlim

/-- Sequential eta limits and conditional eta sums are equivalent. -/
theorem dirichletEtaAlternatingLimit_iff_hasSum_conditional
    {x eta : Real} :
    DirichletEtaAlternatingLimit x eta <->
      HasSum (dirichletEtaSeriesTerm x) eta
        (SummationFilter.conditional Nat) :=
  ⟨dirichletEtaAlternatingLimit_hasSum_conditional,
    dirichletEtaAlternatingLimit_of_hasSum_conditional⟩

/-- The canonical eta value is the conditional eta sum for `0 < x`. -/
theorem dirichletEtaAlternatingValue_hasSum_conditional
    {x : Real} (hx : 0 < x) :
    HasSum (dirichletEtaSeriesTerm x) (dirichletEtaAlternatingValue x)
      (SummationFilter.conditional Nat) :=
  dirichletEtaAlternatingLimit_hasSum_conditional
    (dirichletEtaAlternatingValue_spec hx)

/-- The complex eta terms conditionally sum to the complex-cast eta value. -/
theorem dirichletEtaAlternatingValue_hasSum_conditional_complex
    {x : Real} (hx : 0 < x) :
    HasSum (dirichletEtaComplexSeriesTerm x)
      (dirichletEtaAlternatingValue x : Complex)
      (SummationFilter.conditional Nat) := by
  change HasSum (fun n : Nat => (dirichletEtaSeriesTerm x n : Complex))
    (dirichletEtaAlternatingValue x : Complex)
    (SummationFilter.conditional Nat)
  exact
    (Complex.hasSum_ofReal (L := SummationFilter.conditional Nat)).2
      (dirichletEtaAlternatingValue_hasSum_conditional hx)

/-- The conditional eta `tsum` is the canonical alternating eta value. -/
theorem dirichletEtaConditional_tsum_eq_alternatingValue
    {x : Real} (hx : 0 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaSeriesTerm x n) =
      dirichletEtaAlternatingValue x :=
  (dirichletEtaAlternatingValue_hasSum_conditional hx).tsum_eq

/--
The conditional complex eta `tsum` is the complex-cast canonical alternating
eta value.
-/
theorem dirichletEtaComplexConditional_tsum_eq_alternatingValue
    {x : Real} (hx : 0 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaComplexSeriesTerm x n) =
      (dirichletEtaAlternatingValue x : Complex) :=
  (dirichletEtaAlternatingValue_hasSum_conditional_complex hx).tsum_eq

/--
The complex eta partial sums tend to the complex-cast canonical alternating
eta value.
-/
theorem dirichletEtaComplexPartialSums_tendsto_alternatingValue
    {x : Real} (hx : 0 < x) :
    Tendsto (fun n : Nat =>
      (Finset.range n).sum (dirichletEtaComplexSeriesTerm x))
      atTop (nhds (dirichletEtaAlternatingValue x : Complex)) := by
  have hsum := dirichletEtaAlternatingValue_hasSum_conditional_complex hx
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff] at hsum
  simpa [Function.comp_def] using hsum

/--
Inside the open unit disk, the Abel-damped eta power series is summable.
-/
theorem summable_dirichletEtaComplexSeriesTerm_mul_pow_of_norm_lt_one
    {x : Real} (hx : 0 < x) {z : Complex} (hz : ‖z‖ < 1) :
    Summable fun n : Nat =>
      dirichletEtaComplexSeriesTerm x n * z ^ n :=
  summable_powerSeries_of_norm_lt_one
    (dirichletEtaComplexPartialSums_tendsto_alternatingValue hx).cauchySeq
    hz

/--
Abel's theorem evaluates the boundary limit of the damped eta power series as
the canonical alternating eta value.
-/
theorem dirichletEtaAbelPowerSeries_tendsto_alternatingValue
    {x : Real} (hx : 0 < x) :
    Tendsto
      (fun z : Complex =>
        ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
      ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
      (nhds (dirichletEtaAlternatingValue x : Complex)) :=
  Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (dirichletEtaComplexPartialSums_tendsto_alternatingValue hx)

/-- The sequential eta alternating-series limit is unique. -/
theorem dirichletEtaAlternatingLimit_unique {x eta eta' : Real}
    (hlim : DirichletEtaAlternatingLimit x eta)
    (hlim' : DirichletEtaAlternatingLimit x eta') :
    eta = eta' :=
  tendsto_nhds_unique hlim hlim'

/-- Any eta alternating-series limit for `0 < x` equals the canonical value. -/
theorem dirichletEtaAlternatingLimit_eq_value {x eta : Real}
    (hx : 0 < x) (hlim : DirichletEtaAlternatingLimit x eta) :
    eta = dirichletEtaAlternatingValue x :=
  dirichletEtaAlternatingLimit_unique hlim
    (dirichletEtaAlternatingValue_spec hx)

/-- The real Dirichlet eta alternating-series value is positive for `0 < x`. -/
theorem dirichletEtaAlternatingLimit_pos_of_pos {x eta : Real}
    (hx : 0 < x) (hlim : DirichletEtaAlternatingLimit x eta) :
    0 < eta := by
  have hanti := dirichletEtaTerm_antitone_of_pos hx
  have hlim' : Tendsto
      (fun n => (Finset.range n).sum fun i : Nat =>
        (-1 : Real) ^ i * (((i : Real) + 1) ^ (-x)))
      atTop (nhds eta) := by
    simpa [DirichletEtaAlternatingLimit, dirichletEtaPartialSum] using hlim
  have hlower := hanti.alternating_series_le_tendsto hlim' 1
  have htwo_lt_one : (2 : Real) ^ (-x) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hsum_eq :
      (Finset.range (2 * 1)).sum (fun i : Nat =>
        (-1 : Real) ^ i * (((i : Real) + 1) ^ (-x))) =
          1 - (2 : Real) ^ (-x) := by
    simp [Finset.sum_range_succ, Real.one_rpow]
    rw [show (1 : Real) + 1 = 2 by norm_num]
    ring
  have hpartial_pos :
      0 < (Finset.range (2 * 1)).sum (fun i : Nat =>
        (-1 : Real) ^ i * (((i : Real) + 1) ^ (-x))) := by
    rw [hsum_eq]
    linarith
  exact hpartial_pos.trans_le hlower

/-- The canonical eta alternating-series value is positive for `0 < x`. -/
theorem dirichletEtaAlternatingValue_pos_of_pos {x : Real} (hx : 0 < x) :
    0 < dirichletEtaAlternatingValue x :=
  dirichletEtaAlternatingLimit_pos_of_pos hx
    (dirichletEtaAlternatingValue_spec hx)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
