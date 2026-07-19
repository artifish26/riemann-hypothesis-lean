import RiemannHypothesisProject.RiemannVonMangoldt.FloorParityKernel

/-!
# Eta partial-sum bracket estimates

This module contains even/odd eta partial-sum bracket estimates and the reversed zeta-bracket criteria used by the open-unit-interval zeta route.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/-- The even eta partial-sum residual is real. -/
theorem dirichletEtaAlternatingValue_sub_evenPartialSum_im_eq_zero
    (x : Real) (M : Nat) :
    (((dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)).im) = 0 := by
  simp [dirichletEtaComplexSeriesTerm]

/-- The real part of the even eta partial-sum residual is the real residual. -/
theorem dirichletEtaAlternatingValue_sub_evenPartialSum_re_eq
    (x : Real) (M : Nat) :
    (((dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)).re) =
      dirichletEtaAlternatingValue x -
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) := by
  simp [dirichletEtaComplexSeriesTerm]

/-- The even eta partial sums approach the eta value from below. -/
theorem dirichletEtaAlternatingValue_sub_evenPartialSum_re_pos
    {x : Real} (hx : 0 < x) (M : Nat) :
    0 < (((dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)).re) := by
  let E : Complex :=
    (dirichletEtaAlternatingValue x : Complex) -
      (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)
  have hscale_pos : 0 < (2 : Real) ^ x :=
    Real.rpow_pos_of_pos (by norm_num) x
  have htail_pos :=
    zmodTwoRegularizedHalfTail_tsum_sub_partialSum_re_pos hx M
  have hscaled := congrArg Complex.re
    (zmodTwoRegularizedHalfTail_tsum_sub_partialSum_eq_scaled_etaPartialSum_error
      hx M)
  have hE_im : E.im = 0 := by
    simpa [E] using
      dirichletEtaAlternatingValue_sub_evenPartialSum_im_eq_zero x M
  change 0 < E.re
  rw [hscaled] at htail_pos
  change 0 <
    ((((2 : Real) ^ x : Real) : Complex) * E).re at htail_pos
  simp [hE_im] at htail_pos
  exact pos_of_mul_pos_right htail_pos hscale_pos.le

/--
The norm of the even eta partial-sum residual is exactly its positive real
residual.
-/
theorem dirichletEtaAlternatingValue_sub_evenPartialSum_norm_eq_re
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)‖ =
      (((dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)).re) := by
  let E : Complex :=
    (dirichletEtaAlternatingValue x : Complex) -
      (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)
  have hE_im : E.im = 0 := by
    simpa [E] using
      dirichletEtaAlternatingValue_sub_evenPartialSum_im_eq_zero x M
  have hE_pos : 0 < E.re := by
    simpa [E] using
      dirichletEtaAlternatingValue_sub_evenPartialSum_re_pos hx M
  have hE : E = (E.re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using hE_im
  calc
    ‖(dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)‖ =
        ‖E‖ := by rfl
    _ = ‖(E.re : Complex)‖ := congrArg norm hE
    _ = E.re := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE_pos]

/--
The norm of the even eta partial-sum residual is the positive real residual.
-/
theorem dirichletEtaAlternatingValue_sub_evenPartialSum_norm_eq_real
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)‖ =
      dirichletEtaAlternatingValue x -
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) := by
  rw [dirichletEtaAlternatingValue_sub_evenPartialSum_norm_eq_re hx M]
  exact dirichletEtaAlternatingValue_sub_evenPartialSum_re_eq x M

/-- The odd eta partial-sum residual is real. -/
theorem dirichletEtaOddPartialSum_sub_alternatingValue_im_eq_zero
    (x : Real) (M : Nat) :
    (((Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)).im) = 0 := by
  simp [dirichletEtaComplexSeriesTerm]

/-- The real part of the odd eta partial-sum residual is the real residual. -/
theorem dirichletEtaOddPartialSum_sub_alternatingValue_re_eq
    (x : Real) (M : Nat) :
    (((Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)).re) =
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) -
        dirichletEtaAlternatingValue x := by
  simp [dirichletEtaComplexSeriesTerm]

/-- Odd eta partial sums lie above the canonical eta value. -/
theorem dirichletEtaOddPartialSum_sub_alternatingValue_re_nonneg
    {x : Real} (hx : 0 < x) (M : Nat) :
    0 ≤ (((Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)).re) := by
  have heven_pos :
      0 <
        dirichletEtaAlternatingValue x -
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) := by
    simpa [dirichletEtaAlternatingValue_sub_evenPartialSum_re_eq x M] using
      dirichletEtaAlternatingValue_sub_evenPartialSum_re_pos hx M
  have heven_bound :
      dirichletEtaAlternatingValue x -
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
        (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
    simpa [dirichletEtaAlternatingValue_sub_evenPartialSum_norm_eq_real hx M] using
      dirichletEtaAlternatingValue_sub_evenPartialSum_norm_le hx M
  have hpow_even : (-1 : Real) ^ (2 * M) = 1 := by
    rw [Even.neg_one_pow]
    exact even_two_mul M
  have hterm :
      dirichletEtaSeriesTerm x (2 * M) =
        (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
    simp [dirichletEtaSeriesTerm, hpow_even, Nat.cast_add, Nat.cast_mul]
  have hsum :
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) =
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) +
          dirichletEtaSeriesTerm x (2 * M) := by
    rw [show 2 * M + 1 = 2 * M + 1 by rfl]
    rw [Finset.sum_range_succ]
  rw [dirichletEtaOddPartialSum_sub_alternatingValue_re_eq x M]
  rw [hsum, hterm]
  linarith

/--
The norm of the odd eta partial-sum residual is exactly its nonnegative real
residual.
-/
theorem dirichletEtaOddPartialSum_sub_alternatingValue_norm_eq_re
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)‖ =
      (((Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)).re) := by
  let O : Complex :=
    (Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
      (dirichletEtaAlternatingValue x : Complex)
  have hO_im : O.im = 0 := by
    simpa [O] using
      dirichletEtaOddPartialSum_sub_alternatingValue_im_eq_zero x M
  have hO_nonneg : 0 ≤ O.re := by
    simpa [O] using
      dirichletEtaOddPartialSum_sub_alternatingValue_re_nonneg hx M
  have hO : O = (O.re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using hO_im
  calc
    ‖(Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)‖ =
        ‖O‖ := by rfl
    _ = ‖(O.re : Complex)‖ := congrArg norm hO
    _ = O.re := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hO_nonneg]

/-- The norm of the odd eta partial-sum residual is the real residual. -/
theorem dirichletEtaOddPartialSum_sub_alternatingValue_norm_eq_real
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(Finset.range (2 * M + 1)).sum (dirichletEtaComplexSeriesTerm x) -
        (dirichletEtaAlternatingValue x : Complex)‖ =
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) -
        dirichletEtaAlternatingValue x := by
  rw [dirichletEtaOddPartialSum_sub_alternatingValue_norm_eq_re hx M]
  exact dirichletEtaOddPartialSum_sub_alternatingValue_re_eq x M

/-- Even eta partial sums lie strictly below the canonical eta value. -/
theorem dirichletEta_evenPartialSum_lt_alternatingValue
    {x : Real} (hx : 0 < x) (M : Nat) :
    (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) <
      dirichletEtaAlternatingValue x := by
  have h :=
    dirichletEtaAlternatingValue_sub_evenPartialSum_re_pos hx M
  rw [dirichletEtaAlternatingValue_sub_evenPartialSum_re_eq x M] at h
  linarith

/-- Even eta partial sums are lower bounds for the canonical eta value. -/
theorem dirichletEta_evenPartialSum_le_alternatingValue
    {x : Real} (hx : 0 < x) (M : Nat) :
    (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
      dirichletEtaAlternatingValue x :=
  (dirichletEta_evenPartialSum_lt_alternatingValue hx M).le

/-- Odd eta partial sums are upper bounds for the canonical eta value. -/
theorem dirichletEta_alternatingValue_le_oddPartialSum
    {x : Real} (hx : 0 < x) (M : Nat) :
    dirichletEtaAlternatingValue x ≤
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) := by
  have h :=
    dirichletEtaOddPartialSum_sub_alternatingValue_re_nonneg hx M
  rw [dirichletEtaOddPartialSum_sub_alternatingValue_re_eq x M] at h
  linarith

/-- Even eta partial sums are nonnegative for positive exponents. -/
theorem dirichletEta_evenPartialSum_nonneg_of_pos
    {x : Real} (hx : 0 < x) (M : Nat) :
    0 ≤ (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) := by
  have htail_nonneg :
      0 ≤ ((Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun m _ =>
      (zmodTwoRegularizedHalfTailTerm_re_pos hx m).le
  have hscaled_re :
      ((Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)).re =
        (2 : Real) ^ x *
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) := by
    have h :=
      congrArg Complex.re
        (zmodTwoRegularizedHalfTail_partialSum_eq_scaled_etaPartialSum x M)
    simpa [dirichletEtaComplexSeriesTerm] using h
  have hscale_pos : 0 < (2 : Real) ^ x :=
    Real.rpow_pos_of_pos (by norm_num) x
  rw [hscaled_re] at htail_nonneg
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using htail_nonneg) hscale_pos

/-- Odd eta partial sums are strictly positive for positive exponents. -/
theorem dirichletEta_oddPartialSum_pos_of_pos
    {x : Real} (hx : 0 < x) (M : Nat) :
    0 < (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) :=
  (dirichletEtaAlternatingValue_pos_of_pos hx).trans_le
    (dirichletEta_alternatingValue_le_oddPartialSum hx M)

/-- Closed form for an even-indexed eta term. -/
theorem dirichletEtaSeriesTerm_even_eq (x : Real) (M : Nat) :
    dirichletEtaSeriesTerm x (2 * M) =
      (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
  have hpow_even : (-1 : Real) ^ (2 * M) = 1 := by
    rw [Even.neg_one_pow]
    exact even_two_mul M
  simp [dirichletEtaSeriesTerm, hpow_even, Nat.cast_add, Nat.cast_mul]

/-- Closed form for an odd-indexed eta term. -/
theorem dirichletEtaSeriesTerm_odd_eq (x : Real) (M : Nat) :
    dirichletEtaSeriesTerm x (2 * M + 1) =
      -((((2 * M + 2 : Nat) : Real)) ^ (-x)) := by
  have hpow_odd : (-1 : Real) ^ (2 * M + 1) = -1 := by
    rw [Odd.neg_one_pow]
    exact Nat.not_even_iff_odd.mp (Nat.not_even_two_mul_add_one M)
  rw [dirichletEtaSeriesTerm, hpow_odd]
  have hbase :
      ((2 * M + 1 : Nat) : Real) + 1 =
        ((2 * M + 2 : Nat) : Real) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  rw [hbase]
  ring

/-- Even eta partial sums strictly increase with the cutoff. -/
theorem dirichletEta_evenPartialSum_lt_succ
    {x : Real} (hx : 0 < x) (M : Nat) :
    (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) <
      (Finset.range (2 * (M + 1))).sum (dirichletEtaSeriesTerm x) := by
  have hsum :
      (Finset.range (2 * (M + 1))).sum (dirichletEtaSeriesTerm x) =
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) +
          dirichletEtaSeriesTerm x (2 * M) +
          dirichletEtaSeriesTerm x (2 * M + 1) := by
    rw [show 2 * (M + 1) = (2 * M + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [show 2 * M + 1 = 2 * M + 1 by rfl]
    rw [Finset.sum_range_succ]
  have hblock_pos :
      0 <
        dirichletEtaSeriesTerm x (2 * M) +
          dirichletEtaSeriesTerm x (2 * M + 1) := by
    rw [dirichletEtaSeriesTerm_even_eq, dirichletEtaSeriesTerm_odd_eq]
    have hleft_pos : 0 < (((2 * M + 1 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_pos (2 * M)
    have hlt :
        (((2 * M + 1 : Nat) : Real)) <
          (((2 * M + 2 : Nat) : Real)) := by
      exact_mod_cast Nat.lt_succ_self (2 * M + 1)
    have hpow_lt :
        (((2 * M + 2 : Nat) : Real)) ^ (-x) <
          (((2 * M + 1 : Nat) : Real)) ^ (-x) :=
      Real.rpow_lt_rpow_of_neg hleft_pos hlt (show -x < 0 by linarith)
    linarith
  rw [hsum]
  linarith

/-- Odd eta partial sums strictly decrease with the cutoff. -/
theorem dirichletEta_oddPartialSum_succ_lt
    {x : Real} (hx : 0 < x) (M : Nat) :
    (Finset.range (2 * (M + 1) + 1)).sum (dirichletEtaSeriesTerm x) <
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) := by
  have hsum :
      (Finset.range (2 * (M + 1) + 1)).sum (dirichletEtaSeriesTerm x) =
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) +
          dirichletEtaSeriesTerm x (2 * M + 1) +
          dirichletEtaSeriesTerm x (2 * M + 2) := by
    rw [show 2 * (M + 1) + 1 = (2 * M + 2) + 1 by omega]
    rw [Finset.sum_range_succ]
    rw [show 2 * M + 2 = (2 * M + 1) + 1 by omega]
    rw [Finset.sum_range_succ]
  have hblock_neg :
      dirichletEtaSeriesTerm x (2 * M + 1) +
          dirichletEtaSeriesTerm x (2 * M + 2) < 0 := by
    rw [dirichletEtaSeriesTerm_odd_eq]
    have heven_next :
        dirichletEtaSeriesTerm x (2 * M + 2) =
          (((2 * M + 3 : Nat) : Real)) ^ (-x) := by
      have hidx : 2 * M + 2 = 2 * (M + 1) := by omega
      rw [hidx]
      simpa [show 2 * (M + 1) + 1 = 2 * M + 3 by omega] using
        dirichletEtaSeriesTerm_even_eq x (M + 1)
    rw [heven_next]
    have hleft_pos : 0 < (((2 * M + 2 : Nat) : Real)) := by
      exact_mod_cast Nat.succ_pos (2 * M + 1)
    have hlt :
        (((2 * M + 2 : Nat) : Real)) <
          (((2 * M + 3 : Nat) : Real)) := by
      exact_mod_cast Nat.lt_succ_self (2 * M + 2)
    have hpow_lt :
        (((2 * M + 3 : Nat) : Real)) ^ (-x) <
          (((2 * M + 2 : Nat) : Real)) ^ (-x) :=
      Real.rpow_lt_rpow_of_neg hleft_pos hlt (show -x < 0 by linarith)
    linarith
  rw [hsum]
  linarith

/-- Even eta partial sums converge to the canonical eta value. -/
theorem dirichletEta_evenPartialSum_tendsto_alternatingValue
    {x : Real} (hx : 0 < x) :
    Tendsto (fun M : Nat =>
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x))
      atTop (nhds (dirichletEtaAlternatingValue x)) := by
  have hpartial :
      Tendsto (fun n : Nat =>
        (Finset.range n).sum (dirichletEtaSeriesTerm x))
        atTop (nhds (dirichletEtaAlternatingValue x)) := by
    have hspec := dirichletEtaAlternatingValue_spec hx
    simpa [DirichletEtaAlternatingLimit, dirichletEtaPartialSum,
      dirichletEtaSeriesTerm] using hspec
  have hsubseq : Tendsto (fun M : Nat => 2 * M) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  simpa [Function.comp_def] using hpartial.comp hsubseq

/-- Odd eta partial sums converge to the canonical eta value. -/
theorem dirichletEta_oddPartialSum_tendsto_alternatingValue
    {x : Real} (hx : 0 < x) :
    Tendsto (fun M : Nat =>
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x))
      atTop (nhds (dirichletEtaAlternatingValue x)) := by
  have hpartial :
      Tendsto (fun n : Nat =>
        (Finset.range n).sum (dirichletEtaSeriesTerm x))
        atTop (nhds (dirichletEtaAlternatingValue x)) := by
    have hspec := dirichletEtaAlternatingValue_spec hx
    simpa [DirichletEtaAlternatingLimit, dirichletEtaPartialSum,
      dirichletEtaSeriesTerm] using hspec
  have hsubseq : Tendsto (fun M : Nat => 2 * M + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  simpa [Function.comp_def] using hpartial.comp hsubseq

/-- The width of the even/odd eta bracket is exactly the next positive term. -/
theorem dirichletEta_oddPartialSum_sub_evenPartialSum_eq
    (x : Real) (M : Nat) :
    (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) -
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) =
      (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
  have hpow_even : (-1 : Real) ^ (2 * M) = 1 := by
    rw [Even.neg_one_pow]
    exact even_two_mul M
  have hterm :
      dirichletEtaSeriesTerm x (2 * M) =
        (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
    simp [dirichletEtaSeriesTerm, hpow_even, Nat.cast_add, Nat.cast_mul]
  have hsum :
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) =
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) +
          dirichletEtaSeriesTerm x (2 * M) := by
    rw [show 2 * M + 1 = 2 * M + 1 by rfl]
    rw [Finset.sum_range_succ]
  rw [hsum, hterm]
  ring

/--
Any real candidate lying in the finite even/odd eta bracket is within the
bracket width of the canonical eta value.
-/
theorem dirichletEta_abs_sub_alternatingValue_le_of_mem_evenOddBracket
    {x y : Real} (hx : 0 < x) (M : Nat)
    (hy_even :
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤ y)
    (hy_odd :
      y ≤ (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) :
    |dirichletEtaAlternatingValue x - y| ≤
      (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
  let evenSum := (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x)
  let oddSum := (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)
  have heta_even :
      evenSum ≤ dirichletEtaAlternatingValue x := by
    simpa [evenSum] using
      dirichletEta_evenPartialSum_le_alternatingValue hx M
  have heta_odd :
      dirichletEtaAlternatingValue x ≤ oddSum := by
    simpa [oddSum] using
      dirichletEta_alternatingValue_le_oddPartialSum hx M
  have hwidth :
      oddSum - evenSum =
        (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
    simpa [oddSum, evenSum] using
      dirichletEta_oddPartialSum_sub_evenPartialSum_eq x M
  rw [← hwidth]
  have hy_even' : evenSum ≤ y := by simpa [evenSum] using hy_even
  have hy_odd' : y ≤ oddSum := by simpa [oddSum] using hy_odd
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

/--
Finite-bracket estimate for the remaining scalar eta/zeta continuation gap on
the open unit interval.
-/
theorem openUnitInterval_etaZetaGap_abs_le_of_zetaTarget_mem_evenOddBracket
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1) (M : Nat)
    (hzeta_even :
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re)
    (hzeta_odd :
      (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) :
    |dirichletEtaAlternatingValue x -
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re| ≤
      (((2 * M + 1 : Nat) : Real)) ^ (-x) :=
  dirichletEta_abs_sub_alternatingValue_le_of_mem_evenOddBracket
    hx M hzeta_even hzeta_odd

/-- The eta/zeta multiplier is negative on the open unit interval. -/
theorem openUnitInterval_etaZetaMultiplier_neg
    {x : Real} (_hx : 0 < x) (hx_lt_one : x < 1) :
    1 - (2 : Real) ^ (1 - x) < 0 := by
  have hpow : 1 < (2 : Real) ^ (1 - x) :=
    Real.one_lt_rpow one_lt_two (by linarith)
  linarith

/--
Because the eta/zeta multiplier is negative on `(0, 1)`, placing the
zeta-continuation candidate in a finite eta bracket is equivalent to reversed
finite bounds on the real part of zeta.
-/
theorem openUnitInterval_zetaTarget_mem_evenOddBracket_iff_zetaRe_mem_reversed_etaBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    ((Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
          (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ∧
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) ↔
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x)) ≤
          (riemannZeta (x : Complex)).re ∧
        (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x)) := by
  have hcoef_neg := openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one
  constructor
  · intro hbracket
    constructor
    · rw [div_le_iff_of_neg hcoef_neg]
      simpa [mul_comm] using hbracket.2
    · rw [le_div_iff_of_neg hcoef_neg]
      simpa [mul_comm] using hbracket.1
  · intro hzeta
    constructor
    · have h := (le_div_iff_of_neg hcoef_neg).mp hzeta.2
      simpa [mul_comm] using h
    · have h := (div_le_iff_of_neg hcoef_neg).mp hzeta.1
      simpa [mul_comm] using h

/--
The width of the reversed real-zeta interval induced by the `M`th eta bracket is
the eta bracket width divided by the positive multiplier `2^(1 - x) - 1`.
-/
theorem openUnitInterval_zetaRe_reversedEtaBracket_width_eq
    {x : Real} (_hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) -
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) =
      (((2 * M + 1 : Nat) : Real)) ^ (-x) /
        ((2 : Real) ^ (1 - x) - 1) := by
  let evenSum := (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x)
  let oddSum := (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)
  let width := (((2 * M + 1 : Nat) : Real)) ^ (-x)
  let denom := (2 : Real) ^ (1 - x) - 1
  let coeff := 1 - (2 : Real) ^ (1 - x)
  have hdenom_pos : 0 < denom := by
    have hpow : 1 < (2 : Real) ^ (1 - x) :=
      Real.one_lt_rpow one_lt_two (by linarith)
    dsimp [denom]
    linarith
  have hdenom_ne : denom ≠ 0 := hdenom_pos.ne'
  have hcoeff_eq : coeff = -denom := by
    dsimp [coeff, denom]
    ring
  have hcoeff_ne : coeff ≠ 0 := by
    rw [hcoeff_eq]
    exact neg_ne_zero.mpr hdenom_ne
  have hodd_sub_even :
      oddSum - evenSum = width := by
    simpa [oddSum, evenSum, width] using
      dirichletEta_oddPartialSum_sub_evenPartialSum_eq x M
  have heven_sub_odd :
      evenSum - oddSum = -width := by
    linarith
  calc
    (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) / coeff -
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) / coeff =
        (evenSum - oddSum) / coeff := by
          dsimp [evenSum, oddSum]
          field_simp [hcoeff_ne]
    _ = (-width) / (-denom) := by
          rw [heven_sub_odd, hcoeff_eq]
    _ = width / denom := by
          field_simp [hdenom_ne]

/-- The lower endpoint of the reversed real-zeta bracket is strictly negative. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_lower_neg
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
        (1 - (2 : Real) ^ (1 - x)) < 0 :=
  div_neg_of_pos_of_neg
    (dirichletEta_oddPartialSum_pos_of_pos hx M)
    (openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one)

/-- The upper endpoint of the reversed real-zeta bracket is nonpositive. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_upper_nonpos
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
        (1 - (2 : Real) ^ (1 - x)) ≤ 0 :=
  div_nonpos_of_nonneg_of_nonpos
    (dirichletEta_evenPartialSum_nonneg_of_pos hx M)
    (openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one).le

/-- The reversed real-zeta bracket is an ordered interval. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_lower_le_upper
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) ≤
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) := by
  have hcoef_neg := openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one
  rw [div_le_div_right_of_neg hcoef_neg]
  have hwidth :=
    dirichletEta_oddPartialSum_sub_evenPartialSum_eq x M
  have hwidth_nonneg :
      0 ≤ (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
    positivity
  linarith

/-- The lower endpoints of the reversed real-zeta brackets increase with `M`. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_lower_mono
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) ≤
        (Finset.range (2 * (M + 1) + 1)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) := by
  have hcoef_neg := openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one
  rw [div_le_div_right_of_neg hcoef_neg]
  exact (dirichletEta_oddPartialSum_succ_lt hx M).le

/-- The upper endpoints of the reversed real-zeta brackets decrease with `M`. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_upper_antitone
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * (M + 1))).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) ≤
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) := by
  have hcoef_neg := openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one
  rw [div_le_div_right_of_neg hcoef_neg]
  exact (dirichletEta_evenPartialSum_lt_succ hx M).le

/-- Consecutive reversed real-zeta brackets are nested. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_nested_succ
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat) :
    (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) ≤
        (Finset.range (2 * (M + 1) + 1)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) ∧
      (Finset.range (2 * (M + 1))).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) ≤
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) :=
  ⟨openUnitInterval_zetaRe_reversedEtaBracket_lower_mono hx hx_lt_one M,
    openUnitInterval_zetaRe_reversedEtaBracket_upper_antitone hx hx_lt_one M⟩

/-- The lower endpoints of the reversed real-zeta brackets converge to the eta quotient. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_lower_tendsto
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1) :
    Tendsto (fun M : Nat =>
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
        (1 - (2 : Real) ^ (1 - x)))
      atTop
      (nhds (dirichletEtaAlternatingValue x /
        (1 - (2 : Real) ^ (1 - x)))) := by
  have hodd := dirichletEta_oddPartialSum_tendsto_alternatingValue hx
  have hconst :
      Tendsto (fun _ : Nat => ((1 - (2 : Real) ^ (1 - x))⁻¹))
        atTop (nhds ((1 - (2 : Real) ^ (1 - x))⁻¹)) :=
    tendsto_const_nhds
  simpa [div_eq_mul_inv] using hodd.mul hconst

/-- The upper endpoints of the reversed real-zeta brackets converge to the eta quotient. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_upper_tendsto
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1) :
    Tendsto (fun M : Nat =>
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
        (1 - (2 : Real) ^ (1 - x)))
      atTop
      (nhds (dirichletEtaAlternatingValue x /
        (1 - (2 : Real) ^ (1 - x)))) := by
  have heven := dirichletEta_evenPartialSum_tendsto_alternatingValue hx
  have hconst :
      Tendsto (fun _ : Nat => ((1 - (2 : Real) ^ (1 - x))⁻¹))
        atTop (nhds ((1 - (2 : Real) ^ (1 - x))⁻¹)) :=
    tendsto_const_nhds
  simpa [div_eq_mul_inv] using heven.mul hconst

/--
If the real part of zeta eventually lies in the reversed shrinking eta brackets,
then it is forced to equal the eta quotient.
-/
theorem openUnitInterval_zetaRe_eq_etaQuotient_of_eventually_mem_reversed_etaBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1)
    (hzeta : ∀ᶠ M : Nat in atTop,
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x)) ≤
          (riemannZeta (x : Complex)).re ∧
        (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x))) :
    (riemannZeta (x : Complex)).re =
      dirichletEtaAlternatingValue x / (1 - (2 : Real) ^ (1 - x)) := by
  let target : Real := (riemannZeta (x : Complex)).re
  let etaQuot : Real :=
    dirichletEtaAlternatingValue x / (1 - (2 : Real) ^ (1 - x))
  have hlower :=
    openUnitInterval_zetaRe_reversedEtaBracket_lower_tendsto hx hx_lt_one
  have hupper :=
    openUnitInterval_zetaRe_reversedEtaBracket_upper_tendsto hx hx_lt_one
  have hlower_event : ∀ᶠ M : Nat in atTop,
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x)) ≤ target := by
    filter_upwards [hzeta] with M hM
    simpa [target] using hM.1
  have hupper_event : ∀ᶠ M : Nat in atTop,
      target ≤
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
          (1 - (2 : Real) ^ (1 - x)) := by
    filter_upwards [hzeta] with M hM
    simpa [target] using hM.2
  have htarget_to_etaQuot :
      Tendsto (fun _ : Nat => target) atTop (nhds etaQuot) := by
    simpa [target, etaQuot] using
      tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
        hlower_event hupper_event
  have htarget_const :
      Tendsto (fun _ : Nat => target) atTop (nhds target) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique htarget_const htarget_to_etaQuot

/--
Eventual membership in the reversed real-zeta eta brackets is enough to prove
the scalar eta/zeta equality on the open unit interval.
-/
theorem openUnitInterval_etaZetaFormula_of_eventually_zetaRe_mem_reversed_etaBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1)
    (hzeta : ∀ᶠ M : Nat in atTop,
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x)) ≤
          (riemannZeta (x : Complex)).re ∧
        (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x))) :
    dirichletEtaAlternatingValue x =
      (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re := by
  have hzeta_eq :=
    openUnitInterval_zetaRe_eq_etaQuotient_of_eventually_mem_reversed_etaBracket
      hx hx_lt_one hzeta
  have hcoef_ne : 1 - (2 : Real) ^ (1 - x) ≠ 0 :=
    ne_of_lt (openUnitInterval_etaZetaMultiplier_neg hx hx_lt_one)
  rw [hzeta_eq]
  field_simp [hcoef_ne]

/-- The reversed real-zeta interval widths shrink to zero on `(0, 1)`. -/
theorem openUnitInterval_zetaRe_reversedEtaBracket_width_tendsto_zero
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1) :
    Tendsto (fun M : Nat =>
      (((2 * M + 1 : Nat) : Real)) ^ (-x) /
        ((2 : Real) ^ (1 - x) - 1)) atTop (nhds 0) := by
  have hsubseq : Tendsto (fun M : Nat => 2 * M) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  have hbase := dirichletEtaTerm_tendsto_zero_of_pos (x := x) hx
  have hcomp := hbase.comp hsubseq
  have hscaled :
      Tendsto (fun M : Nat =>
        (((2 * M + 1 : Nat) : Real)) ^ (-x) *
          (((2 : Real) ^ (1 - x) - 1)⁻¹)) atTop (nhds (0 * (((2 : Real) ^ (1 - x) - 1)⁻¹))) := by
    have hconst :
        Tendsto (fun _ : Nat => (((2 : Real) ^ (1 - x) - 1)⁻¹)) atTop
          (nhds (((2 : Real) ^ (1 - x) - 1)⁻¹)) :=
      tendsto_const_nhds
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using hcomp.mul hconst
  simpa [div_eq_mul_inv] using hscaled

/--
If the zeta-continuation candidate lies in every finite even/odd eta bracket,
then the scalar eta/zeta continuation equality follows by squeezing the bracket
width to zero.
-/
theorem openUnitInterval_etaZetaFormula_of_forall_zetaTarget_mem_evenOddBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1)
    (hbracket : ∀ M : Nat,
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
          (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ∧
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) :
    dirichletEtaAlternatingValue x =
      (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re := by
  let target : Real :=
    (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re
  have hbound : ∀ M : Nat,
      |dirichletEtaAlternatingValue x - target| ≤
        (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
    intro M
    have hM := hbracket M
    simpa [target] using
      openUnitInterval_etaZetaGap_abs_le_of_zetaTarget_mem_evenOddBracket
        hx hx_lt_one M hM.1 hM.2
  have hsubseq : Tendsto (fun M : Nat => 2 * M) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  have hwidth_tendsto :
      Tendsto (fun M : Nat =>
        (((2 * M + 1 : Nat) : Real)) ^ (-x)) atTop (nhds 0) := by
    have hbase := dirichletEtaTerm_tendsto_zero_of_pos (x := x) hx
    have hcomp := hbase.comp hsubseq
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using hcomp
  have hgap_tendsto_zero :
      Tendsto (fun _ : Nat => |dirichletEtaAlternatingValue x - target|)
        atTop (nhds 0) := by
    exact squeeze_zero (fun _ => abs_nonneg _) hbound hwidth_tendsto
  have hgap_tendsto_const :
      Tendsto (fun _ : Nat => |dirichletEtaAlternatingValue x - target|)
        atTop (nhds |dirichletEtaAlternatingValue x - target|) :=
    tendsto_const_nhds
  have hgap_abs_zero :
      |dirichletEtaAlternatingValue x - target| = 0 :=
    tendsto_nhds_unique hgap_tendsto_const hgap_tendsto_zero
  have hgap_zero :
      dirichletEtaAlternatingValue x - target = 0 :=
    abs_eq_zero.mp hgap_abs_zero
  have hformula : dirichletEtaAlternatingValue x = target :=
    sub_eq_zero.mp hgap_zero
  simpa [target] using hformula

/--
The scalar eta/zeta equality places the zeta-continuation candidate in every
finite even/odd eta bracket.
-/
theorem forall_zetaTarget_mem_evenOddBracket_of_openUnitInterval_etaZetaFormula
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1)
    (hformula :
      dirichletEtaAlternatingValue x =
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re) :
    ∀ M : Nat,
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
          (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ∧
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) := by
  intro M
  constructor
  · rw [← hformula]
    exact dirichletEta_evenPartialSum_le_alternatingValue hx M
  · rw [← hformula]
    exact dirichletEta_alternatingValue_le_oddPartialSum hx M

/--
Pointwise characterization of the remaining scalar eta/zeta continuation task:
it is equivalent to placing the zeta-continuation candidate in every finite
even/odd eta bracket.
-/
theorem openUnitInterval_etaZetaFormula_iff_forall_zetaTarget_mem_evenOddBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    (dirichletEtaAlternatingValue x =
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re) ↔
      ∀ M : Nat,
        (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
            (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ∧
          (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
            (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) :=
  ⟨forall_zetaTarget_mem_evenOddBracket_of_openUnitInterval_etaZetaFormula
      hx hx_lt_one,
    openUnitInterval_etaZetaFormula_of_forall_zetaTarget_mem_evenOddBracket
      hx hx_lt_one⟩

/--
Pointwise scalar eta/zeta equality is equivalent to all finite reversed
`Re zeta` interval estimates.
-/
theorem openUnitInterval_etaZetaFormula_iff_forall_zetaRe_mem_reversed_etaBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    (dirichletEtaAlternatingValue x =
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re) ↔
      ∀ M : Nat,
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
              (1 - (2 : Real) ^ (1 - x)) ≤
            (riemannZeta (x : Complex)).re ∧
          (riemannZeta (x : Complex)).re ≤
            (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
              (1 - (2 : Real) ^ (1 - x)) := by
  rw [openUnitInterval_etaZetaFormula_iff_forall_zetaTarget_mem_evenOddBracket
    hx hx_lt_one]
  constructor
  · intro hbracket M
    exact
      (openUnitInterval_zetaTarget_mem_evenOddBracket_iff_zetaRe_mem_reversed_etaBracket
        hx hx_lt_one M).1 (hbracket M)
  · intro hzeta M
    exact
      (openUnitInterval_zetaTarget_mem_evenOddBracket_iff_zetaRe_mem_reversed_etaBracket
        hx hx_lt_one M).2 (hzeta M)

/--
Pointwise scalar eta/zeta equality is equivalent to eventual membership in the
reversed shrinking `Re zeta` eta brackets.
-/
theorem openUnitInterval_etaZetaFormula_iff_eventually_zetaRe_mem_reversed_etaBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    (dirichletEtaAlternatingValue x =
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re) ↔
      ∀ᶠ M : Nat in atTop,
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
              (1 - (2 : Real) ^ (1 - x)) ≤
            (riemannZeta (x : Complex)).re ∧
          (riemannZeta (x : Complex)).re ≤
            (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
              (1 - (2 : Real) ^ (1 - x)) := by
  constructor
  · intro hformula
    exact Eventually.of_forall
      ((openUnitInterval_etaZetaFormula_iff_forall_zetaRe_mem_reversed_etaBracket
        hx hx_lt_one).1 hformula)
  · intro hzeta
    exact
      openUnitInterval_etaZetaFormula_of_eventually_zetaRe_mem_reversed_etaBracket
        hx hx_lt_one hzeta

/--
The regularized half-tail residual after `M` blocks has the same explicit
closed-form bound as the scaled eta even-partial-sum residual.
-/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_norm_le
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)‖ ≤
      (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real) ^ (-x)) := by
  rw [zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue hx]
  exact zmodTwoRegularizedHalfTail_partialSum_error_norm_le hx M
end

end ComplexCompactExhaustion

end RiemannHypothesisProject
