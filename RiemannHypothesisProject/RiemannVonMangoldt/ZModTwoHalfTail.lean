import RiemannHypothesisProject.RiemannVonMangoldt.ZModRegularizedTail

/-!
# ZMod two regularized half-tail bridges

This module contains the ZMod-two regularized half-tail estimates, eta comparisons, and endpoint constructors that feed the open-unit-interval zeta route.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/-- The `m`th regularized half-tail term for the mod-2 eta route. -/
noncomputable def zmodTwoRegularizedHalfTailTerm (x : Real) (m : Nat) : Complex :=
  ((((m : Real) + (1 : Real) / (2 : Real) : Real) : Complex) ^
      (-(x : Complex)) -
    (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))

/-- The mod-2 regularized half-tail term is the complex cast of a real difference. -/
theorem zmodTwoRegularizedHalfTailTerm_eq_ofReal (x : Real) (m : Nat) :
    zmodTwoRegularizedHalfTailTerm x m =
      (((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) -
        (((m + 1 : Nat) : Real) ^ (-x)) : Real) := by
  have ha_pos : 0 < (m : Real) + (1 : Real) / (2 : Real) := by
    positivity
  have hb_pos : 0 < ((m + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_pos m
  have ha_cpow :
      ((((m : Real) + (1 : Real) / (2 : Real) : Real) : Complex) ^
          (-(x : Complex))) =
        ((((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) : Real) : Complex) := by
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    exact (Complex.ofReal_cpow ha_pos.le (-x)).symm
  have hb_cpow :
      (((m + 1 : Nat) : Complex) ^ (-(x : Complex))) =
        ((((m + 1 : Nat) : Real) ^ (-x) : Real) : Complex) := by
    rw [show ((m + 1 : Nat) : Complex) =
        ((((m + 1 : Nat) : Real) : Real) : Complex) by norm_num]
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    exact (Complex.ofReal_cpow hb_pos.le (-x)).symm
  rw [zmodTwoRegularizedHalfTailTerm, ha_cpow, hb_cpow, Complex.ofReal_sub]

/-- The mod-2 regularized half-tail term has zero imaginary part. -/
theorem zmodTwoRegularizedHalfTailTerm_im_eq_zero (x : Real) (m : Nat) :
    (zmodTwoRegularizedHalfTailTerm x m).im = 0 := by
  rw [zmodTwoRegularizedHalfTailTerm_eq_ofReal]
  simp

/-- The real part of a mod-2 regularized half-tail term is its real drop. -/
theorem zmodTwoRegularizedHalfTailTerm_re_eq (x : Real) (m : Nat) :
    (zmodTwoRegularizedHalfTailTerm x m).re =
      ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) -
        (((m + 1 : Nat) : Real) ^ (-x)) := by
  rw [zmodTwoRegularizedHalfTailTerm_eq_ofReal]
  simp

/-- The real part of the mod-2 regularized half-tail term is positive. -/
theorem zmodTwoRegularizedHalfTailTerm_re_pos
    {x : Real} (hx : 0 < x) (m : Nat) :
    0 < (zmodTwoRegularizedHalfTailTerm x m).re := by
  rw [zmodTwoRegularizedHalfTailTerm_eq_ofReal]
  simp
  have ha_pos : 0 < (m : Real) + (2 : Real)⁻¹ := by
    positivity
  have hlt :
      (m : Real) + (2 : Real)⁻¹ < (m : Real) + 1 := by
    norm_num
  exact Real.rpow_lt_rpow_of_neg ha_pos hlt (show -x < 0 by linarith)

/-- The norm of a mod-2 regularized half-tail term is its positive real value. -/
theorem zmodTwoRegularizedHalfTailTerm_norm_eq
    {x : Real} (hx : 0 < x) (m : Nat) :
    ‖zmodTwoRegularizedHalfTailTerm x m‖ =
      ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) -
        (((m + 1 : Nat) : Real) ^ (-x)) := by
  have hpos :
      0 <
        ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) -
          (((m + 1 : Nat) : Real) ^ (-x)) := by
    simpa [zmodTwoRegularizedHalfTailTerm_eq_ofReal] using
      zmodTwoRegularizedHalfTailTerm_re_pos hx m
  rw [zmodTwoRegularizedHalfTailTerm_eq_ofReal]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]

/--
Concrete norm control for the mod-2 regularized half-tail term.

The regularization gains one power: the term is bounded by the summable
majorant `x * (m + 1/2)^(-x - 1)` for every `x > 0`.
-/
theorem zmodTwoRegularizedHalfTailTerm_norm_le
    {x : Real} (hx : 0 < x) (m : Nat) :
    ‖zmodTwoRegularizedHalfTailTerm x m‖ ≤
      x * ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x - 1) := by
  have hmem : (1 : Nat) ∈ Finset.Ico 1 (2 + 1) := by
    simp
  simpa [zmodTwoRegularizedHalfTailTerm] using
    (zmodAdditiveCharacter_scaledResiduePowerDiff_norm_le
      (N := 2) (x := x) (r := 1) hx hmem m)

/-- The concrete mod-2 half-tail majorant is summable for every `x > 0`. -/
theorem summable_zmodTwoRegularizedHalfTail_majorant
    {x : Real} (hx : 0 < x) :
    Summable fun m : Nat =>
      x * ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x - 1) := by
  have hmem : (1 : Nat) ∈ Finset.Ico 1 (2 + 1) := by
    simp
  simpa using
    (summable_zmodAdditiveCharacter_scaledResiduePowerDiff_majorant
      (N := 2) (x := x) (r := 1) hx hmem)

/-- The mod-2 regularized half-tail terms are norm-summable for every `x > 0`. -/
theorem summable_norm_zmodTwoRegularizedHalfTailTerm
    {x : Real} (hx : 0 < x) :
    Summable fun m : Nat => ‖zmodTwoRegularizedHalfTailTerm x m‖ := by
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) ?_
    (summable_zmodTwoRegularizedHalfTail_majorant hx)
  intro m
  exact zmodTwoRegularizedHalfTailTerm_norm_le hx m

/-- The mod-2 regularized half-tail series is summable for every `x > 0`. -/
theorem summable_zmodTwoRegularizedHalfTailTerm
    {x : Real} (hx : 0 < x) :
    Summable fun m : Nat => zmodTwoRegularizedHalfTailTerm x m := by
  rw [← summable_norm_iff]
  exact summable_norm_zmodTwoRegularizedHalfTailTerm hx

/-- Removing a finite cutoff leaves exactly the shifted regularized half-tail. -/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_eq_shifted_tsum
    {x : Real} (hx : 0 < x) (M : Nat) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x) =
      ∑' n : Nat, zmodTwoRegularizedHalfTailTerm x (n + M) := by
  let f : Nat -> Complex := fun m => zmodTwoRegularizedHalfTailTerm x m
  have hf : Summable f := by
    simpa [f] using summable_zmodTwoRegularizedHalfTailTerm hx
  have hsplit :
      (Finset.range M).sum f + (∑' n : Nat, f (n + M)) =
        ∑' m : Nat, f m :=
    hf.sum_add_tsum_nat_add M
  rw [← hsplit]
  simp [f]

/-- Every finite-cutoff residual of the regularized half-tail is real. -/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_im_eq_zero
    {x : Real} (hx : 0 < x) (M : Nat) :
    (((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)).im) = 0 := by
  let f : Nat -> Complex := fun n => zmodTwoRegularizedHalfTailTerm x (n + M)
  have hf : Summable f := by
    have hbase := summable_zmodTwoRegularizedHalfTailTerm hx
    simpa [f] using (summable_nat_add_iff (f := fun m : Nat =>
      zmodTwoRegularizedHalfTailTerm x m) M).mpr hbase
  rw [zmodTwoRegularizedHalfTail_tsum_sub_partialSum_eq_shifted_tsum hx M]
  change ((∑' n : Nat, f n).im) = 0
  rw [Complex.im_tsum hf]
  simp [f, zmodTwoRegularizedHalfTailTerm_im_eq_zero]

/-- Every finite-cutoff residual of the regularized half-tail is positive. -/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_re_pos
    {x : Real} (hx : 0 < x) (M : Nat) :
    0 < (((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)).re) := by
  let f : Nat -> Complex := fun n => zmodTwoRegularizedHalfTailTerm x (n + M)
  have hf : Summable f := by
    have hbase := summable_zmodTwoRegularizedHalfTailTerm hx
    simpa [f] using (summable_nat_add_iff (f := fun m : Nat =>
      zmodTwoRegularizedHalfTailTerm x m) M).mpr hbase
  have hfre : Summable fun n : Nat => (f n).re := by
    rcases hf with ⟨a, ha⟩
    exact ⟨a.re, Complex.hasSum_re ha⟩
  have hnonneg : forall n : Nat, 0 ≤ (f n).re := by
    intro n
    exact (zmodTwoRegularizedHalfTailTerm_re_pos hx (n + M)).le
  have hpos0 : 0 < (f 0).re := by
    simpa [f] using zmodTwoRegularizedHalfTailTerm_re_pos hx M
  rw [zmodTwoRegularizedHalfTail_tsum_sub_partialSum_eq_shifted_tsum hx M]
  change 0 < ((∑' n : Nat, f n).re)
  rw [Complex.re_tsum hf]
  exact hfre.tsum_pos hnonneg 0 hpos0

/--
The exact norm of a finite-cutoff residual is the shifted real-part tail.
-/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_norm_eq_shifted_re_tsum
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)‖ =
      ∑' n : Nat, (zmodTwoRegularizedHalfTailTerm x (n + M)).re := by
  let R : Complex :=
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
      (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)
  let f : Nat -> Complex := fun n => zmodTwoRegularizedHalfTailTerm x (n + M)
  have hf : Summable f := by
    have hbase := summable_zmodTwoRegularizedHalfTailTerm hx
    simpa [f] using (summable_nat_add_iff (f := fun m : Nat =>
      zmodTwoRegularizedHalfTailTerm x m) M).mpr hbase
  have him : R.im = 0 := by
    simpa [R] using
      zmodTwoRegularizedHalfTail_tsum_sub_partialSum_im_eq_zero hx M
  have hpos : 0 < R.re := by
    simpa [R] using
      zmodTwoRegularizedHalfTail_tsum_sub_partialSum_re_pos hx M
  have hR : R = (R.re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using him
  have hres :
      R = ∑' n : Nat, zmodTwoRegularizedHalfTailTerm x (n + M) := by
    simpa [R] using
      zmodTwoRegularizedHalfTail_tsum_sub_partialSum_eq_shifted_tsum hx M
  calc
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)‖ =
        ‖R‖ := by rfl
    _ = ‖(R.re : Complex)‖ := congrArg norm hR
    _ = R.re := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    _ = (∑' n : Nat, zmodTwoRegularizedHalfTailTerm x (n + M)).re := by
          rw [hres]
    _ = ∑' n : Nat,
        (zmodTwoRegularizedHalfTailTerm x (n + M)).re := by
          rw [Complex.re_tsum hf]

/--
Finite half-tail cutoffs have an explicit residual bound by the shifted
summable majorant tail.
-/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_norm_le_majorant_tail
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)‖ ≤
      ∑' n : Nat,
        x * (((n + M : Nat) : Real) + (1 : Real) / (2 : Real)) ^ (-x - 1) := by
  let f : Nat -> Complex := fun m => zmodTwoRegularizedHalfTailTerm x m
  let g : Nat -> Real := fun m =>
    x * ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x - 1)
  have hf : Summable f := by
    simpa [f] using summable_zmodTwoRegularizedHalfTailTerm hx
  have hg : Summable g := by
    simpa [g] using summable_zmodTwoRegularizedHalfTail_majorant hx
  have hgtail : Summable fun n : Nat => g (n + M) := by
    exact (summable_nat_add_iff (f := g) M).mpr hg
  have htail_norm :
      ‖∑' n : Nat, f (n + M)‖ ≤ ∑' n : Nat, g (n + M) := by
    refine tsum_of_norm_bounded hgtail.hasSum ?_
    intro n
    simpa [f, g, Nat.cast_add, add_assoc, add_left_comm, add_comm] using
      zmodTwoRegularizedHalfTailTerm_norm_le hx (n + M)
  have hsplit :
      (Finset.range M).sum f + (∑' n : Nat, f (n + M)) =
        ∑' m : Nat, f m := by
    exact hf.sum_add_tsum_nat_add M
  calc
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)‖ =
        ‖∑' n : Nat, f (n + M)‖ := by
          rw [← hsplit]
          simp [f]
    _ ≤ ∑' n : Nat, g (n + M) := htail_norm
    _ =
        ∑' n : Nat,
          x * (((n + M : Nat) : Real) + (1 : Real) / (2 : Real)) ^
            (-x - 1) := by
          rfl

/--
The exact mod-2 nonendpoint regularized Hurwitz-tail theorem.

For the eta route the only nonendpoint residue is `r = 1` modulo `2`, so the
90% boundary target can be attacked by this single half-tail identity rather
than the all-moduli regularized-tail theorem.
-/
def ZModTwoRegularizedHalfTailHurwitzFormula : Prop :=
  forall x : Real,
    forall (_hx : 0 < x),
      x < 1 ->
        (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
          HurwitzZeta.hurwitzZeta
              (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
              (x : Complex) -
            HurwitzZeta.hurwitzZeta
              ((1 : Real) : UnitAddCircle) (x : Complex)

/--
The mod-2 half-tail term is exactly `2^x` times a two-term eta block.

This is the term-level normalization behind the half-tail attack: no analytic
continuation is used here, only the positive-real branch of `cpow`.
-/
theorem zmodTwoRegularizedHalfTailTerm_eq_scaled_etaBlock
    (x : Real) (m : Nat) :
    zmodTwoRegularizedHalfTailTerm x m =
      (((2 : Real) ^ x : Real) : Complex) *
        (dirichletEtaComplexSeriesTerm x (2 * m) +
          dirichletEtaComplexSeriesTerm x (2 * m + 1)) := by
  have htwo_pos : 0 < (2 : Real) := by norm_num
  have htwo_nonneg : 0 <= (2 : Real) := htwo_pos.le
  have hodd_pos : 0 < (2 : Real) * (m : Real) + 1 := by positivity
  have heven_pos : 0 < (2 : Real) * (m : Real) + 1 + 1 := by positivity
  have hm1_pos : 0 < ((m + 1 : Nat) : Real) := by
    exact_mod_cast (Nat.succ_pos m)
  have hhalf :
      (m : Real) + (1 : Real) / (2 : Real) =
        ((2 : Real) * (m : Real) + 1) / (2 : Real) := by
    ring
  have hodd_scale_real :
      ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) =
        (2 : Real) ^ x * (((2 : Real) * (m : Real) + 1) ^ (-x)) := by
    calc
      ((m : Real) + (1 : Real) / (2 : Real)) ^ (-x) =
          (((2 : Real) * (m : Real) + 1) / (2 : Real)) ^ (-x) := by
            rw [hhalf]
      _ = (((2 : Real) * (m : Real) + 1) ^ (-x)) /
            ((2 : Real) ^ (-x)) := by
            rw [Real.div_rpow hodd_pos.le htwo_nonneg]
      _ = (2 : Real) ^ x * (((2 : Real) * (m : Real) + 1) ^ (-x)) := by
            rw [Real.rpow_neg htwo_nonneg x]
            field_simp [Real.rpow_pos_of_pos htwo_pos x]
  have heven_scale_real :
      ((m + 1 : Nat) : Real) ^ (-x) =
        (2 : Real) ^ x * (((2 : Real) * (m : Real) + 1 + 1) ^ (-x)) := by
    have hdouble :
        (2 : Real) * (m : Real) + 1 + 1 =
          (2 : Real) * ((m + 1 : Nat) : Real) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring
    calc
      ((m + 1 : Nat) : Real) ^ (-x) =
          (((2 : Real) * (m : Real) + 1 + 1) / (2 : Real)) ^ (-x) := by
            rw [hdouble]
            field_simp [htwo_pos.ne']
      _ = (((2 : Real) * (m : Real) + 1 + 1) ^ (-x)) /
            ((2 : Real) ^ (-x)) := by
            rw [Real.div_rpow heven_pos.le htwo_nonneg]
      _ = (2 : Real) ^ x * (((2 : Real) * (m : Real) + 1 + 1) ^ (-x)) := by
            rw [Real.rpow_neg htwo_nonneg x]
            field_simp [Real.rpow_pos_of_pos htwo_pos x]
  rw [zmodTwoRegularizedHalfTailTerm]
  have hpow_even : (-1 : Real) ^ (2 * m) = 1 := by
    rw [Even.neg_one_pow]
    exact even_two_mul m
  have hpow_odd : (-1 : Real) ^ (2 * m + 1) = -1 := by
    rw [Odd.neg_one_pow]
    exact Nat.not_even_iff_odd.mp (Nat.not_even_two_mul_add_one m)
  simp [dirichletEtaComplexSeriesTerm, dirichletEtaSeriesTerm, hpow_even,
    hpow_odd, Nat.cast_add, Nat.cast_mul]
  have hhalf_nonneg : 0 <= (m : Real) + (1 : Real) / 2 := by positivity
  have hodd_scale_complex :
      ((((m : Real) + (1 : Real) / 2 : Real) : Complex) ^
          (-(x : Complex))) =
        (((2 : Real) ^ x : Real) : Complex) *
          ((((2 : Real) * (m : Real) + 1) ^ (-x) : Real) : Complex) := by
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    rw [← Complex.ofReal_cpow hhalf_nonneg, hodd_scale_real,
      Complex.ofReal_mul]
  have heven_scale_complex :
      (((m + 1 : Nat) : Complex) ^ (-(x : Complex))) =
        (((2 : Real) ^ x : Real) : Complex) *
          ((((2 : Real) * (m : Real) + 1 + 1) ^ (-x) : Real) : Complex) := by
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    change (((((m + 1 : Nat) : Real) : Complex) ^ ((-x : Real) : Complex)) =
        (((2 : Real) ^ x : Real) : Complex) *
          ((((2 : Real) * (m : Real) + 1 + 1) ^ (-x) : Real) : Complex))
    rw [← Complex.ofReal_cpow hm1_pos.le, heven_scale_real,
      Complex.ofReal_mul]
  rw [show (2 : Complex)⁻¹ = (((1 : Real) / (2 : Real) : Real) : Complex) by
    norm_num]
  have hodd_scale_complex' :
      (((m : Complex) + (((1 : Real) / (2 : Real) : Real) : Complex)) ^
          (-(x : Complex))) =
        (((2 : Real) ^ x : Real) : Complex) *
          ((((2 : Real) * (m : Real) + 1) ^ (-x) : Real) : Complex) := by
    simpa [Complex.ofReal_add] using hodd_scale_complex
  have heven_scale_complex' :
      (((m : Complex) + 1) ^ (-(x : Complex))) =
        (((2 : Real) ^ x : Real) : Complex) *
          ((((2 : Real) * (m : Real) + 1 + 1) ^ (-x) : Real) : Complex) := by
    simpa [Nat.cast_add] using heven_scale_complex
  rw [hodd_scale_complex', heven_scale_complex']
  ring

/--
Finite regularized half-tail blocks are scaled even-length eta partial sums.
-/
theorem zmodTwoRegularizedHalfTail_partialSum_eq_scaled_etaPartialSum
    (x : Real) (M : Nat) :
    (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x) =
      (((2 : Real) ^ x : Real) : Complex) *
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih,
        show 2 * (M + 1) = (2 * M + 1) + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        zmodTwoRegularizedHalfTailTerm_eq_scaled_etaBlock x M]
      ring

/--
The regularized mod-2 half-tail sums to the scaled eta value on `0 < x`.

This closes the eta-normalization part of the half-tail route; the remaining
Hurwitz comparison is exactly the published-source half-tail formula above.
-/
theorem zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue
    {x : Real} (hx : 0 < x) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
      (((2 : Real) ^ x : Real) : Complex) *
        (dirichletEtaAlternatingValue x : Complex) := by
  have hmem : (1 : Nat) ∈ Finset.Ico 1 (2 + 1) := by
    simp
  have hsummable :
      Summable fun m : Nat => zmodTwoRegularizedHalfTailTerm x m := by
    simpa [zmodTwoRegularizedHalfTailTerm] using
      (summable_zmodAdditiveCharacter_scaledResiduePowerDiff
        (N := 2) (x := x) (r := 1) hx hmem)
  have hsubseq : Tendsto (fun M : Nat => 2 * M) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  have heta_tendsto :
      Tendsto
        (fun M : Nat =>
          (((2 : Real) ^ x : Real) : Complex) *
            (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x))
        atTop
        (nhds ((((2 : Real) ^ x : Real) : Complex) *
          (dirichletEtaAlternatingValue x : Complex))) := by
    exact
      tendsto_const_nhds.mul
        ((dirichletEtaComplexPartialSums_tendsto_alternatingValue hx).comp
          hsubseq)
  have htail_tendsto :
      Tendsto
        (fun M : Nat =>
          (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x))
        atTop
        (nhds ((((2 : Real) ^ x : Real) : Complex) *
          (dirichletEtaAlternatingValue x : Complex))) := by
    refine heta_tendsto.congr ?_
    intro M
    exact (zmodTwoRegularizedHalfTail_partialSum_eq_scaled_etaPartialSum x M).symm
  exact ((Summable.hasSum_iff_tendsto_nat hsummable).mpr htail_tendsto).tsum_eq

/-- The regularized mod-2 half-tail sum has zero imaginary part. -/
theorem zmodTwoRegularizedHalfTail_tsum_im_eq_zero
    {x : Real} (hx : 0 < x) :
    ((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m)).im = 0 := by
  rw [zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue hx]
  simp

/-- The regularized mod-2 half-tail sum is strictly positive on the real axis. -/
theorem zmodTwoRegularizedHalfTail_tsum_re_pos
    {x : Real} (hx : 0 < x) :
    0 < ((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m)).re := by
  rw [zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue hx]
  simp
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) x)
    (dirichletEtaAlternatingValue_pos_of_pos hx)

/--
The norm of the regularized mod-2 half-tail sum is its positive scaled eta
value.
-/
theorem zmodTwoRegularizedHalfTail_tsum_norm_eq
    {x : Real} (hx : 0 < x) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m)‖ =
      (2 : Real) ^ x * dirichletEtaAlternatingValue x := by
  rw [zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue hx]
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 2) x),
    abs_of_pos (dirichletEtaAlternatingValue_pos_of_pos hx)]

/--
The Hurwitz side of the mod-2 half-tail identity is exactly the scaled eta
`LFunction` value.

Together with `zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue`,
this shows that the remaining analytic content of the 90% half-tail route is
precisely the alternating eta value theorem on `(0, 1)`.
-/
theorem zmodTwo_hurwitzSub_eq_scaled_etaLFunction (s : Complex) :
    HurwitzZeta.hurwitzZeta
        (((1 : Real) / (2 : Real) : Real) : UnitAddCircle) s -
      HurwitzZeta.hurwitzZeta
        ((1 : Real) : UnitAddCircle) s =
      (2 : Complex) ^ s * dirichletEtaLFunction s := by
  have hhalf :
      ZMod.toAddCircle (1 : ZMod 2) =
        (((1 : Real) / (2 : Real) : Real) : UnitAddCircle) := by
    rw [show (1 : ZMod 2) = ((1 : Nat) : ZMod 2) by rfl]
    rw [ZMod.toAddCircle_natCast]
    norm_num
  have hzero :
      ZMod.toAddCircle (0 : ZMod 2) =
        ((1 : Real) : UnitAddCircle) := by
    calc
      ZMod.toAddCircle (0 : ZMod 2) =
          (((0 : Real)) : UnitAddCircle) := by
        rw [show (0 : ZMod 2) = ((0 : Nat) : ZMod 2) by rfl]
        rw [ZMod.toAddCircle_natCast]
        norm_num
      _ = ((1 : Real) : UnitAddCircle) := by
        symm
        simp [AddCircle.coe_period]
  have heta := dirichletEtaLFunction_eq_hurwitzZeta_modTwo s
  rw [dirichletEtaHurwitzModTwoValue, hhalf, hzero] at heta
  rw [heta]
  rw [← mul_assoc]
  rw [← Complex.cpow_add _ _ (by norm_num : (2 : Complex) ≠ 0)]
  rw [show s + -s = (0 : Complex) by ring]
  simp

/--
The remaining mod-2 half-tail Hurwitz error is exactly the scaled eta
alternating-value error.

This is the current no-wiring normal form of the 90% gap.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_eq_scaled_etaLFunctionGap
    {x : Real} (hx : 0 < x) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex)) =
      (((2 : Real) ^ x : Real) : Complex) *
        ((dirichletEtaAlternatingValue x : Complex) -
          dirichletEtaLFunction (x : Complex)) := by
  have htail := zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue hx
  have hhurwitz := zmodTwo_hurwitzSub_eq_scaled_etaLFunction (x : Complex)
  have hscale :
      (2 : Complex) ^ (x : Complex) =
        (((2 : Real) ^ x : Real) : Complex) := by
    exact (Complex.ofReal_cpow (show 0 <= (2 : Real) by norm_num) x).symm
  rw [htail, hhurwitz, hscale]
  ring

/--
The nonendpoint regularized-tail theorem supplies the older all-residue target;
the endpoint residue is automatic.
-/
theorem zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula) :
    ZModAdditiveCharacterRegularizedTailHurwitzFormula := by
  intro N _ x hx hlt r hr
  have hr_bounds := Finset.mem_Ico.mp hr
  have hr_le_N : r ≤ N := Nat.lt_succ_iff.mp hr_bounds.2
  by_cases hrN : r = N
  · subst r
    exact regularizedHurwitzTail_eq_hurwitzZeta_sub_of_endpoint
      (N := N) x
  · have hr_lt_N : r < N := Nat.lt_of_le_of_ne hr_le_N hrN
    exact htail N x hx hlt r
      (Finset.mem_Ico.mpr ⟨hr_bounds.1, hr_lt_N⟩)

/--
The isolated regularized Hurwitz-tail theorem supplies the existing
`ZMod.LFunction` boundary-value target.
-/
theorem zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    ZModAdditiveCharacterBoundaryValueLFunctionFormula := by
  intro N _ j hj x hx hlt
  exact
    zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_regularizedTail
      (N := N) (j := j) hj hx (htail N x hx hlt)

/--
The nonendpoint regularized Hurwitz-tail theorem supplies the existing
`ZMod.LFunction` boundary-value target; the endpoint residue is filled
automatically.
-/
theorem zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_regularizedTailHurwitzNonendpoint
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula) :
    ZModAdditiveCharacterBoundaryValueLFunctionFormula :=
  zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_regularizedTailHurwitz
    (zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint htail)

/--
Ordinary conditional-series form of the remaining theorem, with the target
written as Mathlib's analytically continued `ZMod.LFunction`.
-/
def ZModAdditiveCharacterConditionalLSeriesLFunctionFormula : Prop :=
  forall (N : Nat) [NeZero N] (j : ZMod N),
    forall (_hj : j ≠ 0),
      forall x : Real,
        forall (_hx : 0 < x),
          x < 1 ->
            (∑'[SummationFilter.conditional Nat] n : Nat,
              LSeries.term
                (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
                (x : Complex) n) =
              ZMod.LFunction
                (fun k : ZMod N => ZMod.stdAddChar (j * k))
                (x : Complex)

/--
The checked boundary-value target supplies the conditional-L-series value
target.
-/
theorem zmodAdditiveCharacterShiftedConditionalLSeriesExpZetaFormula_of_boundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    ZModAdditiveCharacterShiftedConditionalLSeriesExpZetaFormula := by
  intro N _ j hj x hx hlt
  calc
    (∑'[SummationFilter.conditional Nat] n : Nat,
      LSeries.term
        (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
        (x : Complex) (n + 1)) =
        zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
          (x := x) hx :=
      zmodAdditiveCharacterBoundaryValue_eq_conditional_shifted_lseriesTerm
        hj hx
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) :=
      hvalue N j hj x hx hlt

/--
Conversely, the conditional-L-series value target supplies the checked
boundary-value target.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_shiftedConditionalLSeries
    (hseries : ZModAdditiveCharacterShiftedConditionalLSeriesExpZetaFormula) :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro N _ j hj x hx hlt
  calc
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj (x := x) hx =
        (∑'[SummationFilter.conditional Nat] n : Nat,
          LSeries.term
            (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
            (x : Complex) (n + 1)) := by
      rw [zmodAdditiveCharacterBoundaryValue_eq_conditional_shifted_lseriesTerm
        hj hx]
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) :=
      hseries N j hj x hx hlt

/--
The checked boundary-value theorem and the conditional-L-series theorem are
equivalent.  This is the current hard analytic interface in Mathlib-native
Dirichlet-series language.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_iff_shiftedConditionalLSeries :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula <->
      ZModAdditiveCharacterShiftedConditionalLSeriesExpZetaFormula :=
  ⟨zmodAdditiveCharacterShiftedConditionalLSeriesExpZetaFormula_of_boundaryValue,
    zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_shiftedConditionalLSeries⟩

/--
The checked boundary-value target supplies the ordinary conditional-L-series
value target.
-/
theorem zmodAdditiveCharacterConditionalLSeriesExpZetaFormula_of_boundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    ZModAdditiveCharacterConditionalLSeriesExpZetaFormula := by
  intro N _ j hj x hx hlt
  calc
    (∑'[SummationFilter.conditional Nat] n : Nat,
      LSeries.term
        (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
        (x : Complex) n) =
        zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
          (x := x) hx :=
      zmodAdditiveCharacterBoundaryValue_eq_conditional_lseriesTerm hj hx
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) :=
      hvalue N j hj x hx hlt

/--
Conversely, the ordinary conditional-L-series value target supplies the checked
boundary-value target.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_conditionalLSeries
    (hseries : ZModAdditiveCharacterConditionalLSeriesExpZetaFormula) :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro N _ j hj x hx hlt
  calc
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj (x := x) hx =
        (∑'[SummationFilter.conditional Nat] n : Nat,
          LSeries.term
            (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
            (x : Complex) n) := by
      rw [zmodAdditiveCharacterBoundaryValue_eq_conditional_lseriesTerm
        hj hx]
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) :=
      hseries N j hj x hx hlt

/--
The checked boundary-value theorem and the ordinary conditional-L-series theorem
are equivalent.  This is the Mathlib-native hard analytic interface after the
Dirichlet-test convergence work.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_iff_conditionalLSeries :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula <->
      ZModAdditiveCharacterConditionalLSeriesExpZetaFormula :=
  ⟨zmodAdditiveCharacterConditionalLSeriesExpZetaFormula_of_boundaryValue,
    zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_conditionalLSeries⟩

/--
The `LFunction`-valued boundary target supplies the `expZeta`-valued boundary
target using Mathlib's additive-character analytic-continuation theorem.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunction
    (hlfunc : ZModAdditiveCharacterBoundaryValueLFunctionFormula) :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro N _ j hj x hx hlt
  calc
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
        ZMod.LFunction
          (fun k : ZMod N => ZMod.stdAddChar (j * k))
          (x : Complex) :=
      hlfunc N j hj x hx hlt
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) := by
      simpa using
        (ZMod.LFunction_stdAddChar_eq_expZeta
          j (x : Complex) (Or.inl hj))

/--
The isolated regularized Hurwitz-tail theorem supplies the `expZeta`-valued
boundary target through Mathlib's `ZMod.LFunction` continuation.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula :=
  zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunction
    (zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_regularizedTailHurwitz
      htail)

/--
The nonendpoint regularized Hurwitz-tail theorem supplies the `expZeta`-valued
boundary target through the automatic endpoint residue and Mathlib's
`ZMod.LFunction` continuation.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitzNonendpoint
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula) :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula :=
  zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
    (zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint htail)

/--
Conversely, the `expZeta`-valued boundary target supplies the `LFunction`-
valued boundary target.  Thus the expZeta side is no longer a separate
obligation once Mathlib's `ZMod.LFunction` continuation is used.
-/
theorem zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_expZeta
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    ZModAdditiveCharacterBoundaryValueLFunctionFormula := by
  intro N _ j hj x hx hlt
  calc
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
        (x := x) hx =
        HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex) :=
      hvalue N j hj x hx hlt
    _ = ZMod.LFunction
          (fun k : ZMod N => ZMod.stdAddChar (j * k))
          (x : Complex) := by
      simpa using
        (ZMod.LFunction_stdAddChar_eq_expZeta
          j (x : Complex) (Or.inl hj)).symm

/--
The boundary-value theorem is equivalent to its Mathlib `ZMod.LFunction`
version.  This isolates the remaining hard input as conditional-series
continuation to `ZMod.LFunction`.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_iff_lFunction :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula <->
      ZModAdditiveCharacterBoundaryValueLFunctionFormula :=
  ⟨zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_expZeta,
    zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunction⟩

/--
The `LFunction`-valued boundary target supplies the ordinary conditional-series
`LFunction` target.
-/
theorem zmodAdditiveCharacterConditionalLSeriesLFunctionFormula_of_boundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueLFunctionFormula) :
    ZModAdditiveCharacterConditionalLSeriesLFunctionFormula := by
  intro N _ j hj x hx hlt
  calc
    (∑'[SummationFilter.conditional Nat] n : Nat,
      LSeries.term
        (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
        (x : Complex) n) =
        zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj
          (x := x) hx :=
      zmodAdditiveCharacterBoundaryValue_eq_conditional_lseriesTerm hj hx
    _ = ZMod.LFunction
          (fun k : ZMod N => ZMod.stdAddChar (j * k))
          (x : Complex) :=
      hvalue N j hj x hx hlt

/--
Conversely, the ordinary conditional-series `LFunction` target supplies the
checked boundary-value `LFunction` target.
-/
theorem zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_conditionalLSeries
    (hseries : ZModAdditiveCharacterConditionalLSeriesLFunctionFormula) :
    ZModAdditiveCharacterBoundaryValueLFunctionFormula := by
  intro N _ j hj x hx hlt
  calc
    zmodAdditiveCharacterBoundaryValue (N := N) (j := j) hj (x := x) hx =
        (∑'[SummationFilter.conditional Nat] n : Nat,
          LSeries.term
            (fun m : Nat => ZMod.stdAddChar (j * (m : ZMod N)))
            (x : Complex) n) := by
      rw [zmodAdditiveCharacterBoundaryValue_eq_conditional_lseriesTerm
        hj hx]
    _ = ZMod.LFunction
          (fun k : ZMod N => ZMod.stdAddChar (j * k))
          (x : Complex) :=
      hseries N j hj x hx hlt

/--
The boundary-value `LFunction` theorem and ordinary conditional-series
`LFunction` theorem are equivalent.
-/
theorem zmodAdditiveCharacterBoundaryValueLFunctionFormula_iff_conditionalLSeries :
    ZModAdditiveCharacterBoundaryValueLFunctionFormula <->
      ZModAdditiveCharacterConditionalLSeriesLFunctionFormula :=
  ⟨zmodAdditiveCharacterConditionalLSeriesLFunctionFormula_of_boundaryValue,
    zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_conditionalLSeries⟩

/--
The ordinary conditional-series theorem with `expZeta` target is equivalent to
the same theorem with Mathlib's `ZMod.LFunction` target.
-/
theorem zmodAdditiveCharacterConditionalLSeriesExpZetaFormula_iff_lFunction :
    ZModAdditiveCharacterConditionalLSeriesExpZetaFormula <->
      ZModAdditiveCharacterConditionalLSeriesLFunctionFormula := by
  constructor
  · intro hseries
    exact
      zmodAdditiveCharacterConditionalLSeriesLFunctionFormula_of_boundaryValue
        (zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_expZeta
          (zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_conditionalLSeries
            hseries))
  · intro hseries
    exact
      zmodAdditiveCharacterConditionalLSeriesExpZetaFormula_of_boundaryValue
        (zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunction
          (zmodAdditiveCharacterBoundaryValueLFunctionFormula_of_conditionalLSeries
            hseries))

/--
Source-shaped Abel-boundary theorem for nonzero finite additive characters.

This is the reusable Mathlib-shaped analytic input still missing from the eta
route: for `0 < x < 1`, the Abel-damped additive-character series should tend
to the corresponding exponential zeta value.
-/
def ZModAdditiveCharacterAbelExpZetaBoundaryFormula : Prop :=
  forall (N : Nat) [NeZero N] (j : ZMod N),
    j ≠ 0 ->
      forall x : Real,
        0 < x ->
          x < 1 ->
            Tendsto
              (fun z : Complex =>
                ∑' n : Nat,
                  zmodAdditiveCharacterAbelSeriesTerm j x n * z ^ n)
              ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
              (nhds (HurwitzZeta.expZeta (ZMod.toAddCircle j) (x : Complex)))

/--
The sharper boundary-value theorem implies the original Abel-limit source
target.  Thus the remaining additive-character obligation can be stated as an
equality of the checked Dirichlet boundary value with `expZeta`.
-/
theorem zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_boundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    ZModAdditiveCharacterAbelExpZetaBoundaryFormula := by
  intro N _ j hj x hx hlt
  have hboundary :=
    zmodAdditiveCharacterAbelPowerSeries_tendsto_boundaryValue
      (N := N) (j := j) hj (x := x) hx
  have htarget := hvalue N j hj x hx hlt
  simpa [htarget] using hboundary

/--
The isolated regularized Hurwitz-tail theorem supplies the original
source-shaped Abel-boundary theorem.
-/
theorem zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    ZModAdditiveCharacterAbelExpZetaBoundaryFormula :=
  zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_boundaryValue
    (zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      htail)

/--
The nonendpoint regularized Hurwitz-tail theorem supplies the original
source-shaped Abel-boundary theorem; the endpoint residue is automatic.
-/
theorem zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_regularizedTailHurwitzNonendpoint
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula) :
    ZModAdditiveCharacterAbelExpZetaBoundaryFormula :=
  zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_regularizedTailHurwitz
    (zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint htail)

/--
Conversely, the original Abel-limit source theorem identifies the checked
Dirichlet boundary value with `expZeta`, by uniqueness of the radial Abel
limit.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_abelExpZetaBoundaryFormula
    (habel : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro N _ j hj x hx hlt
  have hboundary :=
    zmodAdditiveCharacterAbelPowerSeries_tendsto_boundaryValue
      (N := N) (j := j) hj (x := x) hx
  have htarget := habel N j hj x hx hlt
  exact tendsto_nhds_unique hboundary htarget

/--
The old Abel-limit source theorem and the sharpened checked-boundary-value
equality are equivalent.  Future analytic work may prove either form.
-/
theorem zmodAdditiveCharacterBoundaryValueExpZetaFormula_iff_abelExpZetaBoundaryFormula :
    ZModAdditiveCharacterBoundaryValueExpZetaFormula <->
      ZModAdditiveCharacterAbelExpZetaBoundaryFormula :=
  ⟨zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_boundaryValue,
    zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_abelExpZetaBoundaryFormula⟩

/--
The source-shaped `ZMod 2` boundary-value target needed by the eta route.

This is the exact specialization of
`ZModAdditiveCharacterBoundaryValueExpZetaFormula` at the nontrivial mod-2
additive character, so future analytic work can avoid proving the all-moduli
statement first.
-/
def ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula : Prop :=
  forall x : Real,
    forall hx : 0 < x,
      x < 1 ->
        zmodAdditiveCharacterBoundaryValue
            (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx =
          HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex)

/--
The general checked boundary-value theorem specializes to the source-shaped
`ZMod 2` eta target.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro x hx_pos hx_lt_one
  simpa using
    hvalue 2 (1 : ZMod 2) (by decide) x hx_pos hx_lt_one

/--
The isolated regularized Hurwitz-tail theorem supplies the source-shaped
`ZMod 2` eta boundary target.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzFormula) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_zmodBoundaryValue
    (zmodAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
      htail)

/--
The nonendpoint regularized Hurwitz-tail theorem supplies the source-shaped
`ZMod 2` eta boundary target; the endpoint residue is automatic.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitzNonendpoint
    (htail : ZModAdditiveCharacterRegularizedTailHurwitzNonendpointFormula) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedTailHurwitz
    (zmodAdditiveCharacterRegularizedTailHurwitzFormula_of_nonendpoint htail)

/--
The mod-2 half-tail identity is enough for the source-shaped `ZMod 2`
boundary theorem.

This removes the all-moduli/nonendpoint regularized-tail obligation from the
eta route: after specializing to modulus `2`, `Finset.Ico 1 2` contains only
the residue `1`.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_regularizedHalfTailHurwitz
    (htail : ZModTwoRegularizedHalfTailHurwitzFormula) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro x hx hlt
  have htail_nonendpoint :
      forall r : Nat,
        r ∈ Finset.Ico 1 2 ->
          (∑' m : Nat,
            ((((m : Real) + (r : Real) / (2 : Real) : Real) : Complex) ^
                (-(x : Complex)) -
              (((m + 1 : Nat) : Complex) ^ (-(x : Complex))))) =
            HurwitzZeta.hurwitzZeta
                (((r : Real) / (2 : Real) : Real) : UnitAddCircle)
                (x : Complex) -
              HurwitzZeta.hurwitzZeta
                ((1 : Real) : UnitAddCircle) (x : Complex) := by
    intro r hr
    have hr_bounds := Finset.mem_Ico.mp hr
    have hr_eq_one : r = 1 := by
      omega
    subst r
    simpa [zmodTwoRegularizedHalfTailTerm] using htail x hx hlt
  calc
    zmodAdditiveCharacterBoundaryValue
        (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx =
        ZMod.LFunction
          (fun k : ZMod 2 => ZMod.stdAddChar ((1 : ZMod 2) * k))
          (x : Complex) :=
      zmodAdditiveCharacterBoundaryValue_eq_lFunction_of_regularizedTail_nonendpoint
        (N := 2) (j := (1 : ZMod 2)) (by decide)
        (x := x) hx htail_nonendpoint
    _ = HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
        (x : Complex) := by
      simpa using
        (ZMod.LFunction_stdAddChar_eq_expZeta
          (1 : ZMod 2) (x : Complex) (Or.inl (by decide)))

/--
The eta series term is negative the nontrivial `ZMod 2` additive-character
Abel term.
-/
theorem dirichletEtaComplexSeriesTerm_eq_neg_zmodTwoAdditiveCharacterAbelSeriesTerm
    (x : Real) (n : Nat) :
    dirichletEtaComplexSeriesTerm x n =
      -zmodAdditiveCharacterAbelSeriesTerm (1 : ZMod 2) x n := by
  let k : ZMod 2 := ((n + 1 : Nat) : ZMod 2)
  have hk :
      (1 : ZMod 2) * ((n + 1 : Nat) : ZMod 2) = k := by
    simp [k]
  have hparity : dirichletEtaParity k = (-1 : Complex) ^ n := by
    simpa [k] using dirichletEtaParity_natCast_succ n
  have hnegChar : (-1 : Complex) ^ n = -ZMod.stdAddChar k := by
    simpa [hparity] using (congrFun dirichletEtaParity_eq_neg_stdAddChar k)
  have hchar : ZMod.stdAddChar k = -((-1 : Complex) ^ n) := by
    rw [hnegChar]
    ring
  unfold dirichletEtaComplexSeriesTerm dirichletEtaSeriesTerm
    zmodAdditiveCharacterAbelSeriesTerm zmodAdditiveCharacterCoeff
  rw [hk, hchar]
  norm_num

/--
For the nontrivial `ZMod 2` additive character, the checked Dirichlet boundary
value is the negative of the canonical eta alternating-series value.
-/
theorem zmodTwoAdditiveCharacterBoundaryValue_eq_neg_dirichletEtaAlternatingValue
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue
        (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx =
      -(dirichletEtaAlternatingValue x : Complex) := by
  have hone : (1 : ZMod 2) ≠ 0 := by
    decide
  have hboundary :=
    zmodAdditiveCharacterBoundaryValue_spec
      (N := 2) (j := (1 : ZMod 2)) hone (x := x) hx
  have heta := (dirichletEtaComplexPartialSums_tendsto_alternatingValue hx).neg
  have hadd_to_eta : Tendsto
      (fun n : Nat => (Finset.range n).sum
        (zmodAdditiveCharacterAbelSeriesTerm (1 : ZMod 2) x))
      atTop (nhds (-(dirichletEtaAlternatingValue x : Complex))) := by
    convert heta using 1
    ext n
    calc
      (Finset.range n).sum (zmodAdditiveCharacterAbelSeriesTerm (1 : ZMod 2) x) =
          (Finset.range n).sum (fun i : Nat => -dirichletEtaComplexSeriesTerm x i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have h :=
              dirichletEtaComplexSeriesTerm_eq_neg_zmodTwoAdditiveCharacterAbelSeriesTerm x i
            rw [h]
            simp
      _ = - (Finset.range n).sum (dirichletEtaComplexSeriesTerm x) := by
            rw [Finset.sum_neg_distrib]
  exact tendsto_nhds_unique hboundary hadd_to_eta

/--
The residue-prefix factor in the `ZMod 2` Abel integral is the concrete
odd-floor switch: it is `0` on even prefixes and `-1` on odd prefixes.
-/
theorem zmodTwoAdditiveCharacterCoeff_Icc_zero_residuePrefix_eq_if
    (n : Nat) :
    (∑ k ∈ Finset.Icc 0 (n % 2),
      (if k = 0 then 0 else
        ZMod.stdAddChar ((1 : ZMod 2) * (k : ZMod 2)))) =
      if n % 2 = 0 then (0 : Complex) else -1 := by
  have hcases : n % 2 = 0 ∨ n % 2 = 1 := by
    have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    omega
  rcases hcases with hmod | hmod
  · simp [hmod]
  · rw [hmod]
    have hIcc : Finset.Icc 0 1 = ({0, 1} : Finset Nat) := by
      decide
    rw [hIcc]
    simp [zmodTwo_stdAddChar_one]

/--
The checked `ZMod 2` boundary value in fully explicit Abel-kernel form.

Only the odd floor intervals contribute; this is the concrete scalar kernel
left for comparison with Mathlib's continued Hurwitz/L-function value.
-/
theorem zmodTwoAdditiveCharacterBoundaryValue_eq_floorParityKernelIntegral
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue
        (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx =
      (0 : Complex) -
        ∫ t in Set.Ioi (1 : Real),
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
  rw [zmodAdditiveCharacterBoundaryValue_eq_residuePrefixKernelIntegral
    (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx]
  simp_rw [zmodTwoAdditiveCharacterCoeff_Icc_zero_residuePrefix_eq_if]

/--
The canonical eta alternating value is exactly the explicit odd-floor Abel
kernel integral.

The remaining 90% gate is therefore the comparison of this concrete integral,
or equivalently the half-tail sum it represents, with the Hurwitz/zeta
continuation value.
-/
theorem dirichletEtaAlternatingValue_eq_floorParityKernelIntegral
    {x : Real} (hx : 0 < x) :
    (dirichletEtaAlternatingValue x : Complex) =
      ∫ t in Set.Ioi (1 : Real),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
  have hboundary :=
    zmodTwoAdditiveCharacterBoundaryValue_eq_neg_dirichletEtaAlternatingValue
      (x := x) hx
  have hkernel :=
    zmodTwoAdditiveCharacterBoundaryValue_eq_floorParityKernelIntegral
      (x := x) hx
  calc
    (dirichletEtaAlternatingValue x : Complex) =
        -zmodAdditiveCharacterBoundaryValue
          (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx := by
          rw [hboundary]
          ring
    _ =
        -((0 : Complex) -
          ∫ t in Set.Ioi (1 : Real),
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) := by
          rw [hkernel]
    _ =
        ∫ t in Set.Ioi (1 : Real),
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
          ring
end

end ComplexCompactExhaustion

end RiemannHypothesisProject