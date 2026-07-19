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
import RiemannHypothesisProject.RiemannVonMangoldt.EtaAlternating
import RiemannHypothesisProject.ZetaConjugation
import RiemannHypothesisProject.ZetaSetup

/-!
# ZMod additive-character boundary values

This module contains the mod-2 eta parity character, general ZMod additive-character coefficients, Abel terms, bounded partial sums, and conditional boundary values.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/--
The mod-2 periodic coefficient underlying the eta series:
odd positive integers have coefficient `1`, even positive integers have
coefficient `-1`.

This is the coefficient system whose congruence L-function is the natural
analytic-continuation object for the eta/zeta bridge.
-/
noncomputable def dirichletEtaParity (j : ZMod 2) : Complex :=
  if j = 0 then -1 else 1

@[simp]
theorem dirichletEtaParity_zero : dirichletEtaParity 0 = -1 := by
  simp [dirichletEtaParity]

@[simp]
theorem dirichletEtaParity_one : dirichletEtaParity 1 = 1 := by
  simp [dirichletEtaParity]

/-- Adding one modulo two flips the eta parity coefficient. -/
theorem dirichletEtaParity_add_one (j : ZMod 2) :
    dirichletEtaParity (j + 1) = -dirichletEtaParity j := by
  by_cases hj0 : j = 0
  · subst j
    have h01 : ((0 : ZMod 2) + 1) = 1 := by decide
    rw [h01]
    simp [dirichletEtaParity]
  · have hj1 : j = 1 := by
      fin_cases j
      · exact False.elim (hj0 rfl)
      · rfl
    subst j
    have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
    rw [h11]
    simp [dirichletEtaParity]

/--
The eta parity coefficient on positive integers is the alternating sign used
by the sequential eta series.
-/
theorem dirichletEtaParity_natCast_succ (n : Nat) :
    dirichletEtaParity ((n + 1 : Nat) : ZMod 2) = (-1 : Complex) ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        dirichletEtaParity (((n + 1) + 1 : Nat) : ZMod 2)
            = dirichletEtaParity (((n + 1 : Nat) : ZMod 2) + 1) := by
              norm_num [Nat.cast_add]
        _ = -dirichletEtaParity ((n + 1 : Nat) : ZMod 2) :=
          dirichletEtaParity_add_one _
        _ = -((-1 : Complex) ^ n) := by
          rw [ih]
        _ = (-1 : Complex) ^ (n + 1) := by
          rw [pow_succ]
          ring

/-- The eta parity coefficient has average zero over `ZMod 2`. -/
theorem dirichletEtaParity_sum_eq_zero :
    (∑ j : ZMod 2, dirichletEtaParity j) = 0 := by
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by
    ext j
    fin_cases j
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl rfl
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr rfl]
  simp

/-- In modulus two, the eta parity coefficient is even. -/
theorem dirichletEtaParity_even : dirichletEtaParity.Even := by
  intro j
  fin_cases j <;> simp

/-- The nontrivial standard additive character on `ZMod 2` has value `-1` at `1`. -/
theorem zmodTwo_stdAddChar_one :
    ZMod.stdAddChar (1 : ZMod 2) = (-1 : Complex) := by
  rw [show (1 : ZMod 2) = ((1 : Int) : ZMod 2) by rfl]
  rw [ZMod.stdAddChar_coe]
  norm_num
  rw [show 2 * (Real.pi : Complex) * Complex.I / 2 =
    (Real.pi : Complex) * Complex.I by ring]
  exact Complex.exp_pi_mul_I

/-- The eta parity coefficient is the negative of the nontrivial `ZMod 2` additive character. -/
theorem dirichletEtaParity_eq_neg_stdAddChar :
    dirichletEtaParity = fun j : ZMod 2 => -ZMod.stdAddChar j := by
  funext j
  by_cases hj0 : j = 0
  · subst j
    simp [dirichletEtaParity]
  · have hj1 : j = 1 := by
      fin_cases j
      · exact False.elim (hj0 rfl)
      · rfl
    subst j
    simp [dirichletEtaParity, zmodTwo_stdAddChar_one]

/--
The analytic-continuation candidate for Dirichlet eta, expressed as the
congruence L-function attached to the mod-2 eta parity coefficient.
-/
noncomputable def dirichletEtaLFunction (s : Complex) : Complex :=
  ZMod.LFunction dirichletEtaParity s

/-- The explicit Hurwitz-zeta mod-2 value corresponding to eta. -/
noncomputable def dirichletEtaHurwitzModTwoValue (s : Complex) : Complex :=
  (2 : Complex) ^ (-s) *
    (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (1 : ZMod 2)) s -
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle (0 : ZMod 2)) s)

/--
The mod-2 eta L-function is the difference of the two Hurwitz-zeta branches
attached to the residue classes `1` and `0`.
-/
theorem dirichletEtaLFunction_eq_hurwitzZeta_modTwo (s : Complex) :
    dirichletEtaLFunction s = dirichletEtaHurwitzModTwoValue s := by
  rw [dirichletEtaLFunction, ZMod.LFunction]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by
    ext j
    fin_cases j
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl rfl
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr rfl]
  simp [dirichletEtaHurwitzModTwoValue, sub_eq_add_neg, add_comm]

/--
The mod-2 eta L-function is negative the exponential zeta branch at the
nontrivial point of `ZMod 2`.
-/
theorem dirichletEtaLFunction_eq_neg_expZeta_modTwo (s : Complex) :
    dirichletEtaLFunction s =
      -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
  have hone_ne : (1 : ZMod 2) ≠ 0 := by decide
  calc
    dirichletEtaLFunction s =
        ZMod.LFunction (fun j : ZMod 2 => -ZMod.stdAddChar j) s := by
          rw [dirichletEtaLFunction, dirichletEtaParity_eq_neg_stdAddChar]
    _ = -ZMod.LFunction (fun j : ZMod 2 => ZMod.stdAddChar j) s := by
          simp [ZMod.LFunction, Finset.sum_neg_distrib, neg_mul]
    _ = -ZMod.LFunction
          (fun j : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * j)) s := by
          simp
    _ = -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s := by
          rw [ZMod.LFunction_stdAddChar_eq_expZeta _ _ (Or.inl hone_ne)]

/--
The additive-character coefficient system indexed from denominator `n + 1`.
-/
noncomputable def zmodAdditiveCharacterCoeff {N : Nat} [NeZero N]
    (j : ZMod N) (n : Nat) : Complex :=
  ZMod.stdAddChar (j * ((n + 1 : Nat) : ZMod N))

/--
The real-line Abel-damped power-series term for the additive character
`k ↦ stdAddChar (j * k)`, indexed from denominator `n + 1`.
-/
noncomputable def zmodAdditiveCharacterAbelSeriesTerm {N : Nat} [NeZero N]
    (j : ZMod N) (x : Real) (n : Nat) : Complex :=
  zmodAdditiveCharacterCoeff j n *
    ((((n : Real) + 1) ^ (-x) : Real) : Complex)

/--
For `0 < x`, each Abel-damped additive-character term is norm-bounded by the
undamped character coefficient.  This is the local estimate needed to control
the interior power series before taking the Abel boundary limit.
-/
theorem zmodAdditiveCharacterAbelSeriesTerm_mul_pow_norm_le {N : Nat} [NeZero N]
    (j : ZMod N) {x : Real} (hx : 0 < x) (z : Complex) (n : Nat) :
    norm (zmodAdditiveCharacterAbelSeriesTerm j x n * z ^ n) <= norm (z ^ n) := by
  have hn : (0 : Real) <= (n : Real) := by
    exact_mod_cast Nat.zero_le n
  have hbase_nonneg : 0 <= (n : Real) + 1 := by
    linarith
  have hbase_one : (1 : Real) <= (n : Real) + 1 := by
    linarith
  have hweight_nonneg : 0 <= (((n : Real) + 1) ^ (-x) : Real) :=
    Real.rpow_nonneg hbase_nonneg _
  have hweight_le_one :
      norm (((((n : Real) + 1) ^ (-x) : Real) : Complex)) <= 1 := by
    have hle : (((n : Real) + 1) ^ (-x) : Real) <= 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hbase_one (by linarith)
    simpa [Complex.normSq, hweight_nonneg, abs_of_nonneg hweight_nonneg] using hle
  calc
    norm (zmodAdditiveCharacterAbelSeriesTerm j x n * z ^ n) =
        norm (zmodAdditiveCharacterCoeff j n) *
          norm (((((n : Real) + 1) ^ (-x) : Real) : Complex)) * norm (z ^ n) := by
          simp [zmodAdditiveCharacterAbelSeriesTerm, mul_assoc]
    _ = norm (((((n : Real) + 1) ^ (-x) : Real) : Complex)) * norm (z ^ n) := by
          simp [zmodAdditiveCharacterCoeff]
    _ <= 1 * norm (z ^ n) := by
          exact mul_le_mul_of_nonneg_right hweight_le_one (norm_nonneg _)
    _ = norm (z ^ n) := by
          ring

/--
Inside the open unit disk, every positive-real-parameter additive-character
Abel power series is summable.  The boundary theorem still needs cancellation,
but the interior disk control is now a checked input.
-/
theorem summable_zmodAdditiveCharacterAbelSeriesTerm_mul_pow_of_norm_lt_one
    {N : Nat} [NeZero N] (j : ZMod N) {x : Real} (hx : 0 < x)
    {z : Complex} (hz : norm z < 1) :
    Summable fun n : Nat => zmodAdditiveCharacterAbelSeriesTerm j x n * z ^ n := by
  refine Summable.of_norm_bounded (summable_norm_geometric_of_norm_lt_one hz) ?_
  intro n
  simpa using zmodAdditiveCharacterAbelSeriesTerm_mul_pow_norm_le j hx z n

/--
The unweighted nontrivial additive-character coefficients have zero total
sum over one full residue system.
-/
theorem zmodAdditiveCharacterCoeff_zmod_sum_eq_zero {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) :
    (∑ k : ZMod N, ZMod.stdAddChar (j * k)) = 0 := by
  have h :=
    AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := N)) j
      (ZMod.isPrimitive_stdAddChar N)
  simpa [hj, mul_comm] using h

/--
The shifted coefficient system used by the `n + 1` indexing also has zero
total sum over one full residue system.
-/
theorem zmodAdditiveCharacterCoeff_zmod_shift_sum_eq_zero {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) :
    (∑ k : ZMod N, ZMod.stdAddChar (j * (k + 1))) = 0 := by
  calc
    (∑ k : ZMod N, ZMod.stdAddChar (j * (k + 1))) =
        (∑ k : ZMod N, ZMod.stdAddChar (j * k) * ZMod.stdAddChar j) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [mul_add, mul_one, AddChar.map_add_eq_mul]
    _ = (∑ k : ZMod N, ZMod.stdAddChar (j * k)) * ZMod.stdAddChar j := by
          rw [Finset.sum_mul]
    _ = 0 := by
          rw [zmodAdditiveCharacterCoeff_zmod_sum_eq_zero hj, zero_mul]

/--
One full residue-system period of the shifted additive-character coefficient
sequence, read through canonical representatives, has sum zero.
-/
theorem zmodAdditiveCharacterCoeff_zmod_val_period_sum_eq_zero {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) :
    (∑ k : ZMod N, zmodAdditiveCharacterCoeff j k.val) = 0 := by
  calc
    (∑ k : ZMod N, zmodAdditiveCharacterCoeff j k.val) =
        ∑ k : ZMod N, ZMod.stdAddChar (j * (k + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [zmodAdditiveCharacterCoeff, Nat.cast_add, ZMod.natCast_zmod_val]
          norm_num
    _ = 0 := zmodAdditiveCharacterCoeff_zmod_shift_sum_eq_zero hj

/--
The shifted additive-character coefficient sequence is periodic with period
`N`.
-/
theorem zmodAdditiveCharacterCoeff_periodic {N : Nat} [NeZero N]
    (j : ZMod N) (n : Nat) :
    zmodAdditiveCharacterCoeff j (n + N) =
      zmodAdditiveCharacterCoeff j n := by
  have hcast :
      (((n + N) + 1 : Nat) : ZMod N) =
        ((n + 1 : Nat) : ZMod N) := by
    rw [show (n + N) + 1 = (n + 1) + N by omega]
    rw [Nat.cast_add, ZMod.natCast_self, add_zero]
  rw [zmodAdditiveCharacterCoeff, zmodAdditiveCharacterCoeff, hcast]

/--
The shifted finite additive-character coefficient is the corresponding power
of the character value at `j`.
-/
theorem zmodAdditiveCharacterCoeff_eq_stdAddChar_pow {N : Nat} [NeZero N]
    (j : ZMod N) (n : Nat) :
    zmodAdditiveCharacterCoeff j n = ZMod.stdAddChar j ^ (n + 1) := by
  have hsmul :
      j * ((n + 1 : Nat) : ZMod N) = (n + 1) • j := by
    rw [nsmul_eq_mul]
    exact mul_comm j ((n + 1 : Nat) : ZMod N)
  rw [zmodAdditiveCharacterCoeff, hsmul, AddChar.map_nsmul_eq_pow]

/-- A nonzero `ZMod` additive character value is not the trivial value `1`. -/
theorem zmod_stdAddChar_ne_one_of_ne_zero {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) :
    ZMod.stdAddChar j ≠ 1 := by
  intro h
  have hzero : ZMod.stdAddChar j = ZMod.stdAddChar (0 : ZMod N) := by
    simpa using h
  exact hj (ZMod.injective_stdAddChar hzero)

/--
Finite partial sums of a nontrivial shifted additive-character coefficient are
geometric sums with an explicit denominator.
-/
theorem zmodAdditiveCharacterCoeff_partial_sum_eq {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) (n : Nat) :
    (Finset.range n).sum (zmodAdditiveCharacterCoeff j) =
      ZMod.stdAddChar j *
        ((ZMod.stdAddChar j ^ n - 1) / (ZMod.stdAddChar j - 1)) := by
  let q : Complex := ZMod.stdAddChar j
  have hq : q ≠ 1 := by
    simpa [q] using zmod_stdAddChar_ne_one_of_ne_zero hj
  calc
    (Finset.range n).sum (zmodAdditiveCharacterCoeff j) =
        (Finset.range n).sum (fun k => q ^ (k + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          simpa [q] using zmodAdditiveCharacterCoeff_eq_stdAddChar_pow j k
    _ = (Finset.range n).sum (fun k => q * q ^ k) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [pow_succ']
    _ = q * ((Finset.range n).sum (fun k => q ^ k)) := by
          rw [Finset.mul_sum]
    _ = q * ((q ^ n - 1) / (q - 1)) := by
          rw [geom_sum_eq hq]

/--
The additive character value at `j` has period `N`.

This is the power identity that lets complete `ZMod N` blocks cancel inside
the project shifted coefficient sums.
-/
theorem zmod_stdAddChar_pow_modulus {N : Nat} [NeZero N] (j : ZMod N) :
    ZMod.stdAddChar j ^ N = 1 := by
  calc
    ZMod.stdAddChar j ^ N = ZMod.stdAddChar (N • j) := by
      rw [AddChar.map_nsmul_eq_pow]
    _ = 1 := by
      simp

/--
Adding complete `ZMod N` periods to the shifted coefficient partial sum does
not change it.

This is the finite residue-block cancellation behind the Abel-integral
comparison problem: the floor-indexed partial sums in the Abel formula are
controlled by the incomplete residue prefix rather than by the size of the
cutoff.
-/
theorem zmodAdditiveCharacterCoeff_partial_sum_add_period_mul_eq
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0) (m r : Nat) :
    (Finset.range (m * N + r)).sum (zmodAdditiveCharacterCoeff j) =
      (Finset.range r).sum (zmodAdditiveCharacterCoeff j) := by
  let q : Complex := ZMod.stdAddChar j
  have hperiod : q ^ N = 1 := by
    simpa [q] using zmod_stdAddChar_pow_modulus (N := N) j
  have hpow : q ^ (m * N + r) = q ^ r := by
    rw [pow_add]
    have hblock : q ^ (m * N) = 1 := by
      rw [Nat.mul_comm m N, pow_mul, hperiod, one_pow]
    rw [hblock, one_mul]
  rw [zmodAdditiveCharacterCoeff_partial_sum_eq hj (m * N + r),
    zmodAdditiveCharacterCoeff_partial_sum_eq hj r, hpow]

/--
Uniform norm bound for finite partial sums of a nontrivial shifted
additive-character coefficient.
-/
theorem zmodAdditiveCharacterCoeff_partialSums_norm_le {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) (n : Nat) :
    ‖(Finset.range n).sum (zmodAdditiveCharacterCoeff j)‖ ≤
      (2 : Real) / ‖ZMod.stdAddChar j - 1‖ := by
  let q : Complex := ZMod.stdAddChar j
  have hq : q ≠ 1 := by
    simpa [q] using zmod_stdAddChar_ne_one_of_ne_zero hj
  have hden_nonneg : 0 ≤ ‖q - 1‖ := norm_nonneg _
  have hq_norm : ‖q‖ = 1 := by
    simp [q]
  have hq_pow_norm : ‖q ^ n‖ = 1 := by
    rw [norm_pow, hq_norm, one_pow]
  have hnum :
      ‖q ^ n - 1‖ ≤ ‖q ^ n‖ + ‖(1 : Complex)‖ := by
    simpa [sub_eq_add_neg] using norm_add_le (q ^ n) (-(1 : Complex))
  have hnum_div :
      ‖q ^ n - 1‖ / ‖q - 1‖ ≤
        (‖q ^ n‖ + ‖(1 : Complex)‖) / ‖q - 1‖ :=
    div_le_div_of_nonneg_right hnum hden_nonneg
  calc
    ‖(Finset.range n).sum (zmodAdditiveCharacterCoeff j)‖ =
        ‖q * ((q ^ n - 1) / (q - 1))‖ := by
          rw [zmodAdditiveCharacterCoeff_partial_sum_eq hj n]
    _ = ‖q‖ * ‖(q ^ n - 1) / (q - 1)‖ := by
          rw [norm_mul]
    _ = ‖(q ^ n - 1) / (q - 1)‖ := by
          rw [hq_norm, one_mul]
    _ = ‖q ^ n - 1‖ / ‖q - 1‖ := by
          rw [norm_div]
    _ ≤ (‖q ^ n‖ + ‖(1 : Complex)‖) / ‖q - 1‖ := hnum_div
    _ = (2 : Real) / ‖q - 1‖ := by
          rw [hq_pow_norm, norm_one]
          norm_num

/--
Existential boundedness form of the additive-character partial-sum estimate,
for downstream Dirichlet-test style statements.
-/
theorem zmodAdditiveCharacterCoeff_partialSums_bounded {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) :
    ∃ B : Real,
      0 ≤ B ∧
        ∀ n : Nat,
          ‖(Finset.range n).sum (zmodAdditiveCharacterCoeff j)‖ ≤ B := by
  refine ⟨(2 : Real) / ‖ZMod.stdAddChar j - 1‖, ?_, ?_⟩
  · exact div_nonneg zero_le_two (norm_nonneg _)
  · intro n
    exact zmodAdditiveCharacterCoeff_partialSums_norm_le hj n

/--
The project shifted-coefficient partial sums are the same sums as Mathlib's
positive-indexed `LSeries` additive-character coefficients over `Icc 1 n`.

This removes a normalization hurdle for later Abel-summation or conditional
analytic-continuation arguments, whose standard partial sums are indexed by
`1 ≤ k ≤ n` rather than by `range n` with denominator `n + 1`.
-/
theorem zmodAdditiveCharacterCoeff_Icc_one_sum_eq_range {N : Nat} [NeZero N]
    (j : ZMod N) (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n,
      ZMod.stdAddChar (j * (k : ZMod N))) =
      (Finset.range n).sum (zmodAdditiveCharacterCoeff j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc 1 n]
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl ?_
  intro k _
  simp [zmodAdditiveCharacterCoeff, Nat.cast_add, add_comm]

/--
Uniform norm bound for the ordinary positive-indexed additive-character
coefficient partial sums.

This is the same Dirichlet cancellation estimate as
`zmodAdditiveCharacterCoeff_partialSums_norm_le`, restated in the exact
`LSeries.term` coefficient indexing used by Mathlib's summation-by-parts API.
-/
theorem zmodAdditiveCharacterCoeff_Icc_one_partialSums_norm_le {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) (n : Nat) :
    ‖(∑ k ∈ Finset.Icc 1 n,
      ZMod.stdAddChar (j * (k : ZMod N)))‖ ≤
      (2 : Real) / ‖ZMod.stdAddChar j - 1‖ := by
  rw [zmodAdditiveCharacterCoeff_Icc_one_sum_eq_range j n]
  exact zmodAdditiveCharacterCoeff_partialSums_norm_le hj n

/--
Existential boundedness form of the ordinary positive-indexed
additive-character partial-sum estimate.
-/
theorem zmodAdditiveCharacterCoeff_Icc_one_partialSums_bounded {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) :
    ∃ B : Real,
      0 ≤ B ∧
        ∀ n : Nat,
          ‖(∑ k ∈ Finset.Icc 1 n,
            ZMod.stdAddChar (j * (k : ZMod N)))‖ ≤ B := by
  refine ⟨(2 : Real) / ‖ZMod.stdAddChar j - 1‖, ?_, ?_⟩
  · exact div_nonneg zero_le_two (norm_nonneg _)
  · intro n
    exact zmodAdditiveCharacterCoeff_Icc_one_partialSums_norm_le hj n

/--
The zero-at-index-`0` coefficient convention used by Mathlib's `LSeries.term`
has the same partial sums as the positive-indexed additive-character
coefficients.
-/
theorem zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_Icc_one {N : Nat}
    [NeZero N] (j : ZMod N) (n : Nat) :
    (∑ k ∈ Finset.Icc 0 n,
      (if k = 0 then 0 else
        ZMod.stdAddChar (j * (k : ZMod N)))) =
      ∑ k ∈ Finset.Icc 1 n,
        ZMod.stdAddChar (j * (k : ZMod N)) := by
  rw [Finset.Icc_eq_cons_Ioc n.zero_le, Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  simp only [if_pos, zero_add, zero_add]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [if_neg (zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1).ne']

/--
Positive-indexed additive-character partial sums depend only on the upper
cutoff modulo `N`.

This converts the boundedness statement into an exact residue-prefix statement,
which is the finite combinatorial core of the Abel-integral-to-`ZMod.LFunction`
comparison.
-/
theorem zmodAdditiveCharacterCoeff_Icc_one_sum_eq_mod {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n,
      ZMod.stdAddChar (j * (k : ZMod N))) =
      ∑ k ∈ Finset.Icc 1 (n % N),
        ZMod.stdAddChar (j * (k : ZMod N)) := by
  rw [zmodAdditiveCharacterCoeff_Icc_one_sum_eq_range j n,
    zmodAdditiveCharacterCoeff_Icc_one_sum_eq_range j (n % N)]
  conv_lhs =>
    rw [← Nat.div_add_mod n N]
  simpa [Nat.mul_comm] using
    zmodAdditiveCharacterCoeff_partial_sum_add_period_mul_eq hj (n / N) (n % N)

/--
The zero-at-index-`0` partial sums used by Mathlib's `LSeries.term` convention
also depend only on the upper cutoff modulo `N`.
-/
theorem zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_mod {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) (n : Nat) :
    (∑ k ∈ Finset.Icc 0 n,
      (if k = 0 then 0 else
        ZMod.stdAddChar (j * (k : ZMod N)))) =
      ∑ k ∈ Finset.Icc 0 (n % N),
        (if k = 0 then 0 else
          ZMod.stdAddChar (j * (k : ZMod N))) := by
  rw [zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_Icc_one j n,
    zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_Icc_one j (n % N)]
  exact zmodAdditiveCharacterCoeff_Icc_one_sum_eq_mod hj n

/--
Floor-indexed coefficient sums in the Abel integral are exactly finite
residue-prefix sums.
-/
theorem zmodAdditiveCharacterCoeff_Icc_zero_floor_sum_eq_mod {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) (t : Real) :
    (∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
      (if k = 0 then 0 else
        ZMod.stdAddChar (j * (k : ZMod N)))) =
      ∑ k ∈ Finset.Icc 0 (⌊t⌋₊ % N),
        (if k = 0 then 0 else
          ZMod.stdAddChar (j * (k : ZMod N))) := by
  exact zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_mod hj ⌊t⌋₊

/--
Boundedness of the zero-at-index-`0` coefficient partial sums.  This is the
coefficient-side hypothesis needed by Abel summation in exactly Mathlib's
`LSeries.term` convention.
-/
theorem zmodAdditiveCharacterCoeff_Icc_zero_partialSums_bounded {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) :
    ∃ B : Real,
      0 ≤ B ∧
        ∀ n : Nat,
          ‖(∑ k ∈ Finset.Icc 0 n,
            (if k = 0 then 0 else
              ZMod.stdAddChar (j * (k : ZMod N))))‖ ≤ B := by
  rcases zmodAdditiveCharacterCoeff_Icc_one_partialSums_bounded hj with
    ⟨B, hB_nonneg, hB⟩
  refine ⟨B, hB_nonneg, ?_⟩
  intro n
  rw [zmodAdditiveCharacterCoeff_Icc_zero_sum_eq_Icc_one j n]
  exact hB n

/--
Floor-indexed coefficient sums are `O(1)`, in the exact form used by Abel's
limit theorem.
-/
theorem zmodAdditiveCharacterCoeff_Icc_zero_floor_partialSums_isBigO_one
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0) :
    (fun t : Real =>
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        (if k = 0 then 0 else
          ZMod.stdAddChar (j * (k : ZMod N)))) =O[atTop]
      fun _ : Real => (1 : Real) := by
  rcases zmodAdditiveCharacterCoeff_Icc_zero_partialSums_bounded hj with
    ⟨B, _hB_nonneg, hB⟩
  refine isBigO_of_le' (l := atTop) (c := B) ?_
  intro t
  simpa using hB ⌊t⌋₊

/--
Positive-indexed eta-parity prefixes collapse exactly to the upper cutoff
modulo two: the prefix is `0` at even cutoffs and `1` at odd cutoffs.
-/
theorem dirichletEtaParity_Icc_one_sum_eq_if (n : Nat) :
    (∑ k ∈ Finset.Icc 1 n,
      dirichletEtaParity ((k : Nat) : ZMod 2)) =
      if n % 2 = 0 then (0 : Complex) else 1 := by
  have hterm (k : Nat) :
      dirichletEtaParity ((k : Nat) : ZMod 2) =
        -ZMod.stdAddChar ((1 : ZMod 2) * (k : ZMod 2)) := by
    simpa using
      (congrFun dirichletEtaParity_eq_neg_stdAddChar
        ((k : Nat) : ZMod 2))
  calc
    (∑ k ∈ Finset.Icc 1 n,
      dirichletEtaParity ((k : Nat) : ZMod 2)) =
        ∑ k ∈ Finset.Icc 1 n,
          -ZMod.stdAddChar ((1 : ZMod 2) * (k : ZMod 2)) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          exact hterm k
    _ = -∑ k ∈ Finset.Icc 1 n,
          ZMod.stdAddChar ((1 : ZMod 2) * (k : ZMod 2)) := by
          rw [Finset.sum_neg_distrib]
    _ = -∑ k ∈ Finset.Icc 1 (n % 2),
          ZMod.stdAddChar ((1 : ZMod 2) * (k : ZMod 2)) := by
          rw [zmodAdditiveCharacterCoeff_Icc_one_sum_eq_mod
            (N := 2) (j := (1 : ZMod 2)) (by decide) n]
    _ = if n % 2 = 0 then (0 : Complex) else 1 := by
          have hcases : n % 2 = 0 ∨ n % 2 = 1 := by
            have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
            omega
          rcases hcases with hmod | hmod
          · simp [hmod]
          · simp [hmod, zmodTwo_stdAddChar_one]

/-- The eta-parity positive-indexed prefixes are uniformly bounded by `1`. -/
theorem dirichletEtaParity_Icc_one_partialSums_norm_le (n : Nat) :
    ‖(∑ k ∈ Finset.Icc 1 n,
      dirichletEtaParity ((k : Nat) : ZMod 2))‖ ≤ (1 : Real) := by
  rw [dirichletEtaParity_Icc_one_sum_eq_if]
  by_cases hmod : n % 2 = 0 <;> simp [hmod]

/--
The exact boundedness hypothesis needed by Mathlib's `LSeries_eq_mul_integral`
for the eta-parity coefficient system.
-/
theorem dirichletEtaParity_Icc_one_partialSums_isBigO_rpow_zero :
    (fun n : Nat =>
      ∑ k ∈ Finset.Icc 1 n,
        dirichletEtaParity ((k : Nat) : ZMod 2)) =O[atTop]
      fun n : Nat => (n : Real) ^ (0 : Real) := by
  refine isBigO_of_le' (l := atTop) (c := (1 : Real)) ?_
  intro n
  have hbound := dirichletEtaParity_Icc_one_partialSums_norm_le n
  simpa [Real.rpow_zero] using hbound

/-- Floor-indexed eta-parity prefixes in the explicit odd-floor form. -/
theorem dirichletEtaParity_Icc_one_floor_sum_eq_if (t : Real) :
    (∑ k ∈ Finset.Icc 1 ⌊t⌋₊,
      dirichletEtaParity ((k : Nat) : ZMod 2)) =
      if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else 1 :=
  dirichletEtaParity_Icc_one_sum_eq_if ⌊t⌋₊

/--
Dirichlet's test gives Cauchy convergence of the boundary additive-character
Dirichlet series for every positive real exponent.  This proves the convergence
side of the reusable Abel-boundary target; identifying the limit with the
`expZeta` continuation remains the explicit source theorem below.
-/
theorem zmodAdditiveCharacterAbelSeriesTerm_partialSums_cauchy {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) {x : Real} (hx : 0 < x) :
    CauchySeq fun n : Nat =>
      (Finset.range n).sum (zmodAdditiveCharacterAbelSeriesTerm j x) := by
  let H := zmodAdditiveCharacterCoeff_partialSums_bounded hj
  let B : Real := Classical.choose H
  have hBspec := Classical.choose_spec H
  have hB (n : Nat) :
      ‖(Finset.range n).sum (zmodAdditiveCharacterCoeff j)‖ ≤ B :=
    hBspec.2 n
  let f : Nat -> Real := fun n => (((n : Real) + 1) ^ (-x))
  let z : Nat -> Complex := zmodAdditiveCharacterCoeff j
  have hanti : Antitone f := by
    simpa [f] using dirichletEtaTerm_antitone_of_pos (x := x) hx
  have hf0 : Tendsto f atTop (nhds 0) := by
    simpa [f] using dirichletEtaTerm_tendsto_zero_of_pos (x := x) hx
  have hzb (n : Nat) : ‖(Finset.range n).sum z‖ ≤ B := by
    simpa [z] using hB n
  have hc := hanti.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hzb
  simpa [f, z, zmodAdditiveCharacterAbelSeriesTerm, mul_comm] using hc

/--
Existential boundary convergence form of the additive-character Dirichlet
series.  The missing analytic input is no longer convergence itself, but the
identification of this boundary value with `HurwitzZeta.expZeta`.
-/
theorem exists_zmodAdditiveCharacterAbelSeriesTerm_tendsto {N : Nat}
    [NeZero N] {j : ZMod N} (hj : j ≠ 0) {x : Real} (hx : 0 < x) :
    ∃ L : Complex,
      Tendsto
        (fun n : Nat =>
          (Finset.range n).sum (zmodAdditiveCharacterAbelSeriesTerm j x))
        atTop (nhds L) :=
  cauchySeq_tendsto_of_complete
    (zmodAdditiveCharacterAbelSeriesTerm_partialSums_cauchy hj hx)

/--
The canonical boundary value of the nontrivial additive-character Dirichlet
series at a positive real exponent, obtained from the checked Dirichlet-test
convergence theorem.
-/
noncomputable def zmodAdditiveCharacterBoundaryValue {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) {x : Real} (hx : 0 < x) : Complex :=
  Classical.choose (exists_zmodAdditiveCharacterAbelSeriesTerm_tendsto hj hx)

/-- The named additive-character boundary value is the partial-sum limit. -/
theorem zmodAdditiveCharacterBoundaryValue_spec {N : Nat} [NeZero N]
    {j : ZMod N} (hj : j ≠ 0) {x : Real} (hx : 0 < x) :
    Tendsto
      (fun n : Nat =>
        (Finset.range n).sum (zmodAdditiveCharacterAbelSeriesTerm j x))
      atTop (nhds (zmodAdditiveCharacterBoundaryValue hj hx)) :=
  Classical.choose_spec
    (exists_zmodAdditiveCharacterAbelSeriesTerm_tendsto hj hx)

/--
The positive-indexed Mathlib `LSeries.term` for the additive character is the
same shifted boundary term used by the source Dirichlet-test construction.

This is the exact normalization bridge between Mathlib's zero-at-index-`0`
Dirichlet-series convention and the source denominator `n + 1` convention.
-/
theorem zmodAdditiveCharacter_lseriesTerm_succ_eq_abelSeriesTerm {N : Nat}
    [NeZero N] (j : ZMod N) (x : Real) (n : Nat) :
    LSeries.term
        (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
        (x : Complex) (n + 1) =
      zmodAdditiveCharacterAbelSeriesTerm j x n := by
  have hn_ne : n + 1 ≠ 0 := by omega
  have hbase_nonneg : 0 <= (n : Real) + 1 := by positivity
  have hcast_base :
      ((n + 1 : Nat) : Complex) = (((n : Real) + 1 : Real) : Complex) := by
    norm_num
  have hpow :
      ((n + 1 : Nat) : Complex) ^ (-(x : Complex)) =
        (((n : Real) + 1) ^ (-x) : Real) := by
    rw [hcast_base]
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    exact (Complex.ofReal_cpow hbase_nonneg (-x)).symm
  rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, <- Complex.cpow_neg, hpow]
  simp [zmodAdditiveCharacterAbelSeriesTerm, zmodAdditiveCharacterCoeff,
    mul_comm]

/--
The checked source boundary value is the conditional sum of the matching
positive-indexed Mathlib L-series terms.

This does not identify the sum with `expZeta`; it proves that the remaining
analytic-continuation blocker can be stated directly as a conditional
L-series value theorem.
-/
theorem zmodAdditiveCharacterBoundaryValue_hasSum_conditional_shifted_lseriesTerm
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    HasSum
      (fun n : Nat =>
        LSeries.term
          (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
          (x : Complex) (n + 1))
      (zmodAdditiveCharacterBoundaryValue hj hx)
      (SummationFilter.conditional Nat) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  have hboundary := zmodAdditiveCharacterBoundaryValue_spec hj hx
  have hpartial :
      (fun n : Nat =>
        (Finset.range n).sum
          (fun k : Nat =>
            LSeries.term
              (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
              (x : Complex) (k + 1))) =
        fun n : Nat =>
          (Finset.range n).sum (zmodAdditiveCharacterAbelSeriesTerm j x) := by
    funext n
    refine Finset.sum_congr rfl ?_
    intro k _
    exact zmodAdditiveCharacter_lseriesTerm_succ_eq_abelSeriesTerm j x k
  change Tendsto
    (fun n : Nat =>
      (Finset.range n).sum
        (fun k : Nat =>
          LSeries.term
            (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
            (x : Complex) (k + 1)))
    atTop (nhds (zmodAdditiveCharacterBoundaryValue hj hx))
  rw [hpartial]
  exact hboundary

/--
The source boundary value equals the conditional `tsum` of the shifted Mathlib
L-series terms.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_conditional_shifted_lseriesTerm
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      LSeries.term
        (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
        (x : Complex) (n + 1)) =
      zmodAdditiveCharacterBoundaryValue hj hx :=
  (zmodAdditiveCharacterBoundaryValue_hasSum_conditional_shifted_lseriesTerm
    hj hx).tsum_eq

/--
The checked source boundary value is the conditional sum of the ordinary
Mathlib `LSeries.term` additive-character series.

Mathlib's `LSeries.term` is zero at index `0`, so the checked shifted
positive-indexed sum and the ordinary `n`-indexed sum have the same conditional
partial-sum limit.
-/
theorem zmodAdditiveCharacterBoundaryValue_hasSum_conditional_lseriesTerm
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    HasSum
      (fun n : Nat =>
        LSeries.term
          (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
          (x : Complex) n)
      (zmodAdditiveCharacterBoundaryValue hj hx)
      (SummationFilter.conditional Nat) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff]
  have hshift :=
    zmodAdditiveCharacterBoundaryValue_hasSum_conditional_shifted_lseriesTerm
      (N := N) (j := j) hj (x := x) hx
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff] at hshift
  change Tendsto
    (fun n : Nat =>
      (Finset.range n).sum
        (fun k : Nat =>
          LSeries.term
            (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
            (x : Complex) k))
    atTop (nhds (zmodAdditiveCharacterBoundaryValue hj hx))
  rw [← tendsto_add_atTop_iff_nat 1]
  have hpartial_succ :
      (fun n : Nat =>
        (Finset.range (n + 1)).sum
          (fun k : Nat =>
            LSeries.term
              (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
              (x : Complex) k)) =
        fun n : Nat =>
          (Finset.range n).sum
            (fun k : Nat =>
              LSeries.term
                (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
                (x : Complex) (k + 1)) := by
    funext n
    rw [Finset.sum_range_succ']
    simp [LSeries.term_zero]
  rw [hpartial_succ]
  exact hshift

/--
The source boundary value equals the conditional `tsum` of the ordinary Mathlib
L-series terms.
-/
theorem zmodAdditiveCharacterBoundaryValue_eq_conditional_lseriesTerm
    {N : Nat} [NeZero N] {j : ZMod N} (hj : j ≠ 0)
    {x : Real} (hx : 0 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      LSeries.term
        (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
        (x : Complex) n) =
      zmodAdditiveCharacterBoundaryValue hj hx :=
  (zmodAdditiveCharacterBoundaryValue_hasSum_conditional_lseriesTerm
    hj hx).tsum_eq
end

end ComplexCompactExhaustion

end RiemannHypothesisProject