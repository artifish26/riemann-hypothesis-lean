import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointConstantEnclosures
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Quarter-line digamma enclosures for M100-DF6D4

This module rewrites the imaginary part of the quarter-line digamma value as a
positive reciprocal series.  An integral comparison then encloses every
infinite tail between an arctangent correction and that correction plus the
first omitted reciprocal term.  The result is the common analytic interface
used by the 44 DF6D4 sine-transform certificates.
-/

namespace RiemannHypothesisProject.Experiments.M100

open Filter

noncomputable section

def suzukiDF6D4DigammaSummand (n : Nat) (t : Real) : Real :=
  (t / 2) /
    (((n : Real) + 1 / 4) ^ 2 + (t / 2) ^ 2)

private theorem im_inv_sub
    {d y : Real} (hd : 0 < d) :
    (((d : Complex)⁻¹ -
        ((d : Complex) + (y : Complex) * Complex.I)⁻¹).im) =
      y / (d ^ 2 + y ^ 2) := by
  have hdne : d ≠ 0 := hd.ne'
  have hden : d ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hd, sq_nonneg y]
  rw [Complex.sub_im, Complex.inv_im, Complex.inv_im]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    mul_one, zero_add, neg_zero]
  field_simp [hdne, hden]
  ring

private theorem gaussDigammaSeriesTerm_im (n : Nat) (t : Real) :
    (ComplexCompactExhaustion.gaussDigammaSeriesTerm
      ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n).im =
      suzukiDF6D4DigammaSummand n t := by
  let d : Real := (n : Real) + 1 / 4
  let y : Real := t / 2
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hcancel :
      ComplexCompactExhaustion.gaussDigammaSeriesTerm
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n =
        (1 / (n + 1 : Complex)) -
          ((d : Complex) + (y : Complex) * Complex.I)⁻¹ := by
    dsimp only [d, y]
    unfold ComplexCompactExhaustion.gaussDigammaSeriesTerm
    push_cast
    congr 2
    ring
  rw [hcancel, Complex.sub_im]
  have hfirst : (1 / (n + 1 : Complex)).im = 0 := by
    norm_num [Complex.div_im, Complex.normSq_apply]
  rw [hfirst, zero_sub]
  have hinv := im_inv_sub (d := d) (y := y) hd
  have hdIm : ((d : Complex)⁻¹).im = 0 := by
    rw [Complex.inv_im]
    simp
  rw [Complex.sub_im, hdIm, zero_sub] at hinv
  unfold suzukiDF6D4DigammaSummand
  dsimp only [d, y] at hinv
  linarith

theorem suzukiDF6D4_digamma_im_eq_tsum (t : Real) :
    (Complex.digamma
      ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I)).im =
      ∑' n : Nat, suzukiDF6D4DigammaSummand n t := by
  have hcomplex := digamma_quarterLine_sub_eq_tsum t
  have hz : 0 < (((1 / 4 : Complex) +
      (t / 2 : Real) * Complex.I)).re := by simp
  have hz0 : 0 < ((1 / 4 : Complex)).re := by simp
  have hsum :=
    (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz).sub
      (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz0)
  have hbase := ComplexCompactExhaustion.digamma_ofReal_eq_deriv_logGamma
    (x := (1 / 4 : Real)) (by norm_num)
  have him := congrArg Complex.im hcomplex
  rw [Complex.sub_im, Complex.im_tsum hsum] at him
  have hbaseIm : (Complex.digamma (1 / 4 : Complex)).im = 0 := by
    have hbase' : Complex.digamma (1 / 4 : Complex) =
        ((deriv (Real.log ∘ Real.Gamma) (1 / 4) : Real) : Complex) := by
      convert hbase using 1
      all_goals norm_num
    rw [hbase']
    simp
  rw [hbaseIm, sub_zero] at him
  rw [show (∑' n : Nat,
      (ComplexCompactExhaustion.gaussDigammaSeriesTerm
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
        ComplexCompactExhaustion.gaussDigammaSeriesTerm
          (1 / 4 : Complex) n).im) =
      ∑' n : Nat, suzukiDF6D4DigammaSummand n t by
        apply tsum_congr
        intro n
        rw [Complex.sub_im, gaussDigammaSeriesTerm_im]
        have hzero :
            (ComplexCompactExhaustion.gaussDigammaSeriesTerm
              (1 / 4 : Complex) n).im = 0 := by
          have hreal := gaussDigammaSeriesTerm_im n 0
          norm_num [suzukiDF6D4DigammaSummand] at hreal ⊢
          exact hreal
        rw [hzero, sub_zero]] at him
  exact him

private theorem hasDerivAt_arctan_div
    {y x : Real} (hx : x ≠ 0) :
    HasDerivAt (fun u : Real => Real.arctan (y / u))
      (-y / (x ^ 2 + y ^ 2)) x := by
  have hdiv : HasDerivAt (fun u : Real => y / u) (-y / x ^ 2) x := by
    convert! (hasDerivAt_const x y).div (hasDerivAt_id x) hx using 1
    simp only [id_eq, zero_mul, mul_one, zero_sub]
  convert hdiv.arctan using 1
  field_simp [hx]

private theorem integral_digammaSummand_eq (y d : Real) (hd : 0 < d) :
    (∫ x in d..d + 1, y / (x ^ 2 + y ^ 2)) =
      Real.arctan (y / d) - Real.arctan (y / (d + 1)) := by
  have hderiv : ∀ x ∈ Set.uIcc d (d + 1),
      HasDerivAt (fun u : Real => -Real.arctan (y / u))
        (y / (x ^ 2 + y ^ 2)) x := by
    intro x hx
    have hinterval : d ≤ d + 1 := by linarith
    rw [Set.uIcc_of_le hinterval] at hx
    have hxd : d ≤ x := hx.1
    convert! (hasDerivAt_arctan_div (y := y) (x := x)
      (by linarith)).neg using 1
    simp only [neg_div, neg_neg]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · apply ContinuousOn.intervalIntegrable
    intro x hx
    have hinterval : d ≤ d + 1 := by linarith
    rw [Set.uIcc_of_le hinterval] at hx
    have hxpos : 0 < x := hd.trans_le hx.1
    have hden : x ^ 2 + y ^ 2 ≠ 0 := by
      nlinarith [sq_pos_of_pos hxpos, sq_nonneg y]
    exact (continuousAt_const.div
      ((continuousAt_id.pow 2).add continuousAt_const)
      (by simpa only [Pi.add_apply, Pi.pow_apply, id_eq] using hden)).continuousWithinAt

private theorem digammaSummand_antitoneOn (y : Real) (hy : 0 ≤ y) :
    AntitoneOn (fun x : Real => y / (x ^ 2 + y ^ 2)) (Set.Ici 0) := by
  rcases hy.eq_or_lt with rfl | hypos
  · simpa only [zero_div] using
      (antitoneOn_const : AntitoneOn (fun _ : Real => (0 : Real)) (Set.Ici 0))
  intro a ha b hb hab
  apply div_le_div_of_nonneg_left hypos.le
  · nlinarith [sq_pos_of_pos hypos]
  · nlinarith [mul_self_le_mul_self ha hab]

private theorem digammaArctan_diff_bounds (n : Nat) {t : Real} (ht : 0 ≤ t) :
    suzukiDF6D4DigammaSummand (n + 1) t ≤
      Real.arctan ((t / 2) / ((n : Real) + 1 / 4)) -
        Real.arctan ((t / 2) / ((n : Real) + 1 / 4 + 1)) ∧
    Real.arctan ((t / 2) / ((n : Real) + 1 / 4)) -
        Real.arctan ((t / 2) / ((n : Real) + 1 / 4 + 1)) ≤
      suzukiDF6D4DigammaSummand n t := by
  let y := t / 2
  let d := (n : Real) + 1 / 4
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hanti := (digammaSummand_antitoneOn y hy).mono
    (show Set.Icc d (d + 1) ⊆ Set.Ici 0 by intro x hx; exact (hd.le.trans hx.1))
  have hanti' : AntitoneOn (fun x : Real => y / (x ^ 2 + y ^ 2))
      (Set.Icc d (d + (1 : Nat))) := by
    simpa only [Nat.cast_one] using hanti
  have hlower := hanti'.sum_le_integral (x₀ := d) (a := 1)
  have hupper := hanti'.integral_le_sum (x₀ := d) (a := 1)
  norm_num at hlower hupper
  rw [integral_digammaSummand_eq y d hd] at hlower hupper
  constructor
  · unfold suzukiDF6D4DigammaSummand
    dsimp only [y, d] at hlower ⊢
    push_cast at hlower ⊢
    convert hlower using 1
    all_goals ring
  · unfold suzukiDF6D4DigammaSummand
    dsimp only [y, d] at hupper ⊢
    exact hupper

theorem summable_suzukiDF6D4DigammaSummand (t : Real) :
    Summable (fun n : Nat => suzukiDF6D4DigammaSummand n t) := by
  have hz : 0 < (((1 / 4 : Complex) +
      (t / 2 : Real) * Complex.I)).re := by simp
  have hz0 : 0 < ((1 / 4 : Complex)).re := by simp
  have hsum :=
    (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz).sub
      (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz0)
  have himsum := hsum.mapL Complex.imCLM
  refine himsum.congr ?_
  intro n
  change
    (ComplexCompactExhaustion.gaussDigammaSeriesTerm
        ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
      ComplexCompactExhaustion.gaussDigammaSeriesTerm
        (1 / 4 : Complex) n).im = suzukiDF6D4DigammaSummand n t
  rw [Complex.sub_im, gaussDigammaSeriesTerm_im]
  have hzero := gaussDigammaSeriesTerm_im n 0
  norm_num [suzukiDF6D4DigammaSummand] at hzero ⊢
  exact hzero

def suzukiDF6D4DigammaArctanTail (n : Nat) (t : Real) : Real :=
  Real.arctan ((t / 2) / ((n : Real) + 1 / 4))

private theorem suzukiDF6D4DigammaArctanTail_succ (n : Nat) (t : Real) :
    suzukiDF6D4DigammaArctanTail (n + 1) t =
      Real.arctan ((t / 2) / ((n : Real) + 1 / 4 + 1)) := by
  unfold suzukiDF6D4DigammaArctanTail
  congr 2
  push_cast
  ring

private theorem digammaArctan_diff_bounds' (n : Nat) {t : Real} (ht : 0 ≤ t) :
    suzukiDF6D4DigammaSummand (n + 1) t ≤
        suzukiDF6D4DigammaArctanTail n t - suzukiDF6D4DigammaArctanTail (n + 1) t ∧
      suzukiDF6D4DigammaArctanTail n t - suzukiDF6D4DigammaArctanTail (n + 1) t ≤ suzukiDF6D4DigammaSummand n t := by
  rw [suzukiDF6D4DigammaArctanTail_succ]
  exact digammaArctan_diff_bounds n ht

private theorem suzukiDF6D4DigammaSummand_nonneg (n : Nat) {t : Real} (ht : 0 ≤ t) :
    0 ≤ suzukiDF6D4DigammaSummand n t := by
  unfold suzukiDF6D4DigammaSummand
  positivity

private theorem suzukiDF6D4DigammaArctanTail_tendsto_zero (N : Nat) (t : Real) :
    Tendsto (fun k : Nat => suzukiDF6D4DigammaArctanTail (N + k) t) atTop (nhds 0) := by
  have hcast : Tendsto (fun k : Nat => ((N + k : Nat) : Real)) atTop atTop :=
    by
      simpa only [Function.comp_def, Nat.add_comm] using
        (tendsto_natCast_atTop_atTop (R := Real)).comp (tendsto_add_atTop_nat N)
  have hden : Tendsto (fun k : Nat => ((N + k : Nat) : Real) + 1 / 4)
      atTop atTop := tendsto_atTop_add_const_right _ _ hcast
  have hratio : Tendsto
      (fun k : Nat => (t / 2) / (((N + k : Nat) : Real) + 1 / 4))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  change Tendsto
    (fun k : Nat => Real.arctan ((t / 2) /
      (((N + k : Nat) : Real) + 1 / 4))) atTop (nhds 0)
  simpa only [Function.comp_def, Real.arctan_zero] using
    Real.continuous_arctan.continuousAt.tendsto.comp hratio

private theorem suzukiDF6D4DigammaArctanDiff_hasSum (N : Nat) {t : Real} (ht : 0 ≤ t) :
    HasSum (fun k : Nat => suzukiDF6D4DigammaArctanTail (N + k) t -
      suzukiDF6D4DigammaArctanTail (N + k + 1) t) (suzukiDF6D4DigammaArctanTail N t) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg ?_ _).2 ?_
  · intro k
    have h := (digammaArctan_diff_bounds (N + k) ht).1
    have hf := suzukiDF6D4DigammaSummand_nonneg (N + k + 1) ht
    dsimp only [suzukiDF6D4DigammaArctanTail]
    apply hf.trans
    have heq : (((N + k + 1 : Nat) : Real) + 1 / 4) =
        ((N + k : Nat) : Real) + 1 / 4 + 1 := by
      push_cast
      ring
    rw [heq]
    exact h
  · have htel : ∀ k : Nat,
        (∑ i ∈ Finset.range k,
          (suzukiDF6D4DigammaArctanTail (N + i) t - suzukiDF6D4DigammaArctanTail (N + i + 1) t)) =
          suzukiDF6D4DigammaArctanTail N t - suzukiDF6D4DigammaArctanTail (N + k) t := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          calc
            suzukiDF6D4DigammaArctanTail N t - suzukiDF6D4DigammaArctanTail (N + k) t +
                (suzukiDF6D4DigammaArctanTail (N + k) t - suzukiDF6D4DigammaArctanTail (N + k + 1) t) =
              suzukiDF6D4DigammaArctanTail N t - suzukiDF6D4DigammaArctanTail (N + k + 1) t := by ring
            _ = suzukiDF6D4DigammaArctanTail N t - suzukiDF6D4DigammaArctanTail (N + k.succ) t := by
              apply congrArg (fun m : Nat =>
                suzukiDF6D4DigammaArctanTail N t - suzukiDF6D4DigammaArctanTail m t)
              omega
    simp_rw [htel]
    simpa using tendsto_const_nhds.sub (suzukiDF6D4DigammaArctanTail_tendsto_zero N t)

theorem suzukiDF6D4DigammaTail_bounds (N : Nat) {t : Real} (ht : 0 ≤ t) :
    suzukiDF6D4DigammaArctanTail N t ≤ ∑' k : Nat, suzukiDF6D4DigammaSummand (N + k) t ∧
      (∑' k : Nat, suzukiDF6D4DigammaSummand (N + k) t) ≤
        suzukiDF6D4DigammaArctanTail N t + suzukiDF6D4DigammaSummand N t := by
  have hfull := summable_suzukiDF6D4DigammaSummand t
  have htail : Summable (fun k : Nat => suzukiDF6D4DigammaSummand (N + k) t) :=
    hfull.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have htailSucc : Summable (fun k : Nat => suzukiDF6D4DigammaSummand (N + k + 1) t) :=
    hfull.comp_injective (fun a b h => by omega)
  have hdiff := suzukiDF6D4DigammaArctanDiff_hasSum N ht
  have hdiffSummable := hdiff.summable
  constructor
  · rw [← hdiff.tsum_eq]
    exact hdiffSummable.tsum_le_tsum
      (fun k => (digammaArctan_diff_bounds' (N + k) ht).2) htail
  · have hsuccLe : (∑' k : Nat, suzukiDF6D4DigammaSummand (N + k + 1) t) ≤
        suzukiDF6D4DigammaArctanTail N t := by
      rw [← hdiff.tsum_eq]
      exact htailSucc.tsum_le_tsum
        (fun k => (digammaArctan_diff_bounds' (N + k) ht).1) hdiffSummable
    rw [htail.tsum_eq_zero_add]
    calc
      suzukiDF6D4DigammaSummand (N + 0) t +
          (∑' b : Nat, suzukiDF6D4DigammaSummand (N + (b + 1)) t) =
        (∑' k : Nat, suzukiDF6D4DigammaSummand (N + k + 1) t) + suzukiDF6D4DigammaSummand N t := by
          rw [Nat.add_zero, add_comm]
          congr 1
      _ ≤ suzukiDF6D4DigammaArctanTail N t + suzukiDF6D4DigammaSummand N t := by
        simpa only [add_comm] using add_le_add_left hsuccLe (suzukiDF6D4DigammaSummand N t)

/-! ## Second-order tail enclosure -/

private theorem suzukiDF6D4_q_le_trapezoidAverage
    {d y : Real} (hd : 0 < d) (hy : 0 ≤ y) (hyd : y ≤ d) :
    y / (d * (d + 1) + y ^ 2) ≤
      (y / (d ^ 2 + y ^ 2) + y / ((d + 1) ^ 2 + y ^ 2)) / 2 := by
  have hA : 0 < d ^ 2 + y ^ 2 := by positivity
  have hB : 0 < (d + 1) ^ 2 + y ^ 2 := by positivity
  have hC : 0 < d * (d + 1) + y ^ 2 := by positivity
  field_simp
  nlinarith [sq_nonneg y, mul_nonneg hy (sub_nonneg.mpr hyd)]

private theorem suzukiDF6D4_trapezoidError_rational
    {d y : Real} (hd : 0 < d) (hy : 0 ≤ y) (hyd : y ≤ d) :
    (y / (d ^ 2 + y ^ 2) + y / ((d + 1) ^ 2 + y ^ 2)) / 2 -
          y / (d * (d + 1) + y ^ 2) +
          (y / (d * (d + 1) + y ^ 2)) ^ 3 / 3 ≤
      y / 3 * (1 / d ^ 3 - 1 / (d + 1) ^ 3) := by
  have hA : 0 < d ^ 2 + y ^ 2 := by positivity
  have hB : 0 < (d + 1) ^ 2 + y ^ 2 := by positivity
  have hC : 0 < d * (d + 1) + y ^ 2 := by positivity
  have hd1 : 0 < d + 1 := by positivity
  have hy2 : y ^ 2 ≤ d ^ 2 := by nlinarith
  by_cases hyz : y = 0
  · simp [hyz]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hyz)
  have hdiff :
      (y / (d ^ 2 + y ^ 2) + y / ((d + 1) ^ 2 + y ^ 2)) / 2 -
          y / (d * (d + 1) + y ^ 2) =
        y * (d ^ 2 + d - y ^ 2) /
          (2 * (d ^ 2 + y ^ 2) * ((d + 1) ^ 2 + y ^ 2) *
            (d * (d + 1) + y ^ 2)) := by
    field_simp
    ring
  have hnum0 : 0 ≤ d ^ 2 + d - y ^ 2 := by nlinarith
  have hnum : d ^ 2 + d - y ^ 2 ≤ d * (d + 1) := by nlinarith
  have hprod :
      d ^ 2 * (d + 1) ^ 2 * (d * (d + 1)) ≤
        (d ^ 2 + y ^ 2) * ((d + 1) ^ 2 + y ^ 2) *
          (d * (d + 1) + y ^ 2) := by
    gcongr <;> nlinarith [sq_nonneg y]
  have hscaled :
      (d ^ 2 + d - y ^ 2) * (d ^ 2 * (d + 1) ^ 2) ≤
        (d ^ 2 + y ^ 2) * ((d + 1) ^ 2 + y ^ 2) *
          (d * (d + 1) + y ^ 2) := by
    calc
      (d ^ 2 + d - y ^ 2) * (d ^ 2 * (d + 1) ^ 2) ≤
          (d * (d + 1)) * (d ^ 2 * (d + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = d ^ 2 * (d + 1) ^ 2 * (d * (d + 1)) := by ring
      _ ≤ _ := hprod
  have havg :
      (y / (d ^ 2 + y ^ 2) + y / ((d + 1) ^ 2 + y ^ 2)) / 2 -
          y / (d * (d + 1) + y ^ 2) ≤
        y / (2 * d ^ 2 * (d + 1) ^ 2) := by
    rw [hdiff]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hscaled
      (show 0 ≤ 2 * y by positivity)]
  have hq :
      y / (d * (d + 1) + y ^ 2) ≤ y / (d * (d + 1)) := by
    gcongr
    nlinarith [sq_nonneg y]
  have hqcube :
      (y / (d * (d + 1) + y ^ 2)) ^ 3 / 3 ≤
        y / (3 * d * (d + 1) ^ 3) := by
    calc
      (y / (d * (d + 1) + y ^ 2)) ^ 3 / 3 ≤
          (y / (d * (d + 1))) ^ 3 / 3 := by gcongr
      _ ≤ y / (3 * d * (d + 1) ^ 3) := by
        field_simp
        nlinarith
  have hcombine :
      y / (2 * d ^ 2 * (d + 1) ^ 2) +
          y / (3 * d * (d + 1) ^ 3) ≤
        y / 3 * (1 / d ^ 3 - 1 / (d + 1) ^ 3) := by
    field_simp
    nlinarith
  linarith

private theorem suzukiDF6D4_arctan_cubic_bounds
    {x : Real} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 3 / 3 ≤ Real.arctan x ∧ Real.arctan x ≤ x := by
  have hnorm : ‖x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  let f : Nat → Real := fun n => x ^ (2 * n + 1) / (2 * n + 1 : Nat)
  have hanti : Antitone f := by
    intro n m hnm
    dsimp only [f]
    apply div_le_div₀
    · positivity
    · exact pow_le_pow_of_le_one hx0 hx1.le (by omega)
    · positivity
    · exact_mod_cast (show 2 * n + 1 ≤ 2 * m + 1 by omega)
  have htend := (Real.hasSum_arctan hnorm).tendsto_sum_nat
  have htend' : Tendsto
      (fun n => ∑ i ∈ Finset.range n, (-1) ^ i * f i)
      atTop (nhds (Real.arctan x)) := by
    simpa only [f, mul_div_assoc] using htend
  have hlower := hanti.alternating_series_le_tendsto htend' 1
  have hupper := hanti.tendsto_le_alternating_series htend' 0
  norm_num [f, Finset.sum_range_succ] at hlower hupper
  exact ⟨by linarith, hupper⟩

private theorem suzukiDF6D4_arctan_diff_eq
    {d y : Real} (hd : 0 < d) :
    Real.arctan (y / d) - Real.arctan (y / (d + 1)) =
      Real.arctan (y / (d * (d + 1) + y ^ 2)) := by
  rw [sub_eq_add_neg, ← Real.arctan_neg]
  rw [Real.arctan_add (by
    have hnonneg : 0 ≤ y / d * (y / (d + 1)) := by
      rw [div_mul_div_comm]
      apply div_nonneg
      · nlinarith [sq_nonneg y]
      · positivity
    nlinarith)]
  congr 1
  have hC : d * (d + 1) + y ^ 2 ≠ 0 := by positivity
  field_simp [ne_of_gt hd, hC]
  ring

private theorem suzukiDF6D4_localTrapezoid_error
    {d y : Real} (hd : 0 < d) (hy : 0 ≤ y) (hyd : y ≤ d) :
    |(y / (d ^ 2 + y ^ 2) + y / ((d + 1) ^ 2 + y ^ 2)) / 2 -
        (Real.arctan (y / d) - Real.arctan (y / (d + 1)))| ≤
      y / 3 * (1 / d ^ 3 - 1 / (d + 1) ^ 3) := by
  let q := y / (d * (d + 1) + y ^ 2)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg y, mul_pos hd (by positivity : 0 < d + 1)]
  have hqavg := suzukiDF6D4_q_le_trapezoidAverage hd hy hyd
  have hatan := suzukiDF6D4_arctan_cubic_bounds hq0 hq1
  have hC : 0 ≤ y / 3 * (1 / d ^ 3 - 1 / (d + 1) ^ 3) := by
    have : 1 / (d + 1) ^ 3 ≤ 1 / d ^ 3 := by
      gcongr
      linarith
    positivity
  rw [suzukiDF6D4_arctan_diff_eq hd]
  apply abs_le.2
  constructor
  · dsimp only [q] at hqavg hatan
    linarith
  · dsimp only [q] at hqavg hatan
    linarith [suzukiDF6D4_trapezoidError_rational hd hy hyd]

/-- The trapezoid correction has a fixed sign.  This turns the previous
symmetric `N⁻³` tail allowance into a one-sided allowance without changing
the frozen cutoff. -/
private theorem suzukiDF6D4_localTrapezoid_error_nonneg
    {d y : Real} (hd : 0 < d) (hy : 0 ≤ y) (hyd : y ≤ d) :
    0 ≤ (y / (d ^ 2 + y ^ 2) +
          y / ((d + 1) ^ 2 + y ^ 2)) / 2 -
        (Real.arctan (y / d) - Real.arctan (y / (d + 1))) := by
  let q := y / (d * (d + 1) + y ^ 2)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hq1 : q < 1 := by
    dsimp only [q]
    rw [div_lt_one (by positivity)]
    nlinarith [sq_nonneg y, mul_pos hd (by positivity : 0 < d + 1)]
  have hqavg := suzukiDF6D4_q_le_trapezoidAverage hd hy hyd
  have hatan := suzukiDF6D4_arctan_cubic_bounds hq0 hq1
  rw [suzukiDF6D4_arctan_diff_eq hd]
  dsimp only [q] at hatan
  linarith

private theorem suzukiDF6D4_hasSum_sub_succ
    (u : Nat → Real) (hanti : Antitone u)
    (hzero : Tendsto u atTop (nhds 0)) :
    HasSum (fun k => u k - u (k + 1)) (u 0) := by
  refine (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => sub_nonneg.mpr (hanti (by omega))) _).2 ?_
  have htel : ∀ k : Nat,
      (∑ i ∈ Finset.range k, (u i - u (i + 1))) = u 0 - u k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  simp_rw [htel]
  simpa using tendsto_const_nhds.sub hzero

/-- Trapezoid-corrected center for the complete digamma-series tail. -/
def suzukiDF6D4DigammaTailCenter (n : Nat) (t : Real) : Real :=
  suzukiDF6D4DigammaArctanTail n t +
    suzukiDF6D4DigammaSummand n t / 2

/-- Telescoping second-order error allowance.  At the frozen cutoff it is of
order `N⁻³`, while the original integral-test allowance was of order `N⁻²`. -/
def suzukiDF6D4DigammaTailCorrection (n : Nat) (t : Real) : Real :=
  (t / 2) / 3 / (((n : Real) + 1 / 4) ^ 3)

private theorem suzukiDF6D4DigammaTailCorrection_hasSum
    (N : Nat) {t : Real} (ht : 0 ≤ t) :
    HasSum (fun k => suzukiDF6D4DigammaTailCorrection (N + k) t -
      suzukiDF6D4DigammaTailCorrection (N + k + 1) t)
      (suzukiDF6D4DigammaTailCorrection N t) := by
  let u : Nat → Real := fun k => suzukiDF6D4DigammaTailCorrection (N + k) t
  have hanti : Antitone u := by
    intro k l hkl
    unfold u suzukiDF6D4DigammaTailCorrection
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · gcongr
  have hcast : Tendsto (fun k : Nat => ((N + k : Nat) : Real))
      atTop atTop := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (tendsto_natCast_atTop_atTop (R := Real)).comp
        (tendsto_add_atTop_nat N)
  have hden : Tendsto
      (fun k : Nat => (((N + k : Nat) : Real) + 1 / 4) ^ 3)
      atTop atTop :=
    (tendsto_pow_atTop (show 3 ≠ 0 by norm_num)).comp
      (tendsto_atTop_add_const_right _ _ hcast)
  have hzero : Tendsto u atTop (nhds 0) := by
    unfold u suzukiDF6D4DigammaTailCorrection
    exact tendsto_const_nhds.div_atTop hden
  simpa only [u, Nat.add_zero, Nat.add_assoc] using
    suzukiDF6D4_hasSum_sub_succ u hanti hzero

private theorem suzukiDF6D4DigammaHalfSummand_hasSum
    (N : Nat) {t : Real} (ht : 0 ≤ t) :
    HasSum (fun k => suzukiDF6D4DigammaSummand (N + k) t / 2 -
      suzukiDF6D4DigammaSummand (N + k + 1) t / 2)
      (suzukiDF6D4DigammaSummand N t / 2) := by
  let u : Nat → Real := fun k => suzukiDF6D4DigammaSummand (N + k) t / 2
  have hanti : Antitone u := by
    intro k l hkl
    unfold u suzukiDF6D4DigammaSummand
    apply div_le_div_of_nonneg_right _ (by norm_num)
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · gcongr
  have hsum := summable_suzukiDF6D4DigammaSummand t
  have hterm : Tendsto
      (fun k : Nat => suzukiDF6D4DigammaSummand (N + k) t)
      atTop (nhds 0) := by
    exact (hsum.comp_injective
      (fun _ _ h => Nat.add_left_cancel h)).tendsto_atTop_zero
  have hzero : Tendsto u atTop (nhds 0) := by
    unfold u
    simpa only [zero_div] using hterm.div_const 2
  simpa only [u, Nat.add_zero, Nat.add_assoc] using
    suzukiDF6D4_hasSum_sub_succ u hanti hzero

private theorem suzukiDF6D4DigammaArctanTail_hasSum
    (N : Nat) {t : Real} (ht : 0 ≤ t) :
    HasSum (fun k => suzukiDF6D4DigammaArctanTail (N + k) t -
      suzukiDF6D4DigammaArctanTail (N + k + 1) t)
      (suzukiDF6D4DigammaArctanTail N t) := by
  let u : Nat → Real := fun k => suzukiDF6D4DigammaArctanTail (N + k) t
  have hanti : Antitone u := by
    intro k l hkl
    unfold u suzukiDF6D4DigammaArctanTail
    apply Real.arctan_strictMono.monotone
    apply div_le_div_of_nonneg_left (by positivity)
    · positivity
    · gcongr
  have hcast : Tendsto (fun k : Nat => ((N + k : Nat) : Real))
      atTop atTop := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (tendsto_natCast_atTop_atTop (R := Real)).comp
        (tendsto_add_atTop_nat N)
  have hden : Tendsto
      (fun k : Nat => ((N + k : Nat) : Real) + 1 / 4)
      atTop atTop := tendsto_atTop_add_const_right _ _ hcast
  have hratio : Tendsto
      (fun k : Nat => (t / 2) / (((N + k : Nat) : Real) + 1 / 4))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hden
  have hzero : Tendsto u atTop (nhds 0) := by
    change Tendsto
      (fun k : Nat => Real.arctan ((t / 2) /
        (((N + k : Nat) : Real) + 1 / 4))) atTop (nhds 0)
    simpa only [Function.comp_def, Real.arctan_zero] using
      Real.continuous_arctan.continuousAt.tendsto.comp hratio
  simpa only [u, Nat.add_zero, Nat.add_assoc] using
    suzukiDF6D4_hasSum_sub_succ u hanti hzero

/-- Second-order enclosure for the complete reciprocal-series tail.  It keeps
the frozen `N = 16384` prefix and replaces the first-omitted-term uncertainty
by the telescoping correction `y / (3 d_N^3)`. -/
theorem suzukiDF6D4DigammaTail_secondOrder_bounds
    (N : Nat) {t : Real} (ht : 0 ≤ t)
    (hsmall : t / 2 ≤ (N : Real) + 1 / 4) :
    suzukiDF6D4DigammaTailCenter N t ≤
        ∑' k : Nat, suzukiDF6D4DigammaSummand (N + k) t ∧
      (∑' k : Nat, suzukiDF6D4DigammaSummand (N + k) t) ≤
        suzukiDF6D4DigammaTailCenter N t +
          suzukiDF6D4DigammaTailCorrection N t := by
  have hA := suzukiDF6D4DigammaArctanTail_hasSum N ht
  have hF := suzukiDF6D4DigammaHalfSummand_hasSum N ht
  have hC := suzukiDF6D4DigammaTailCorrection_hasSum N ht
  have hB : HasSum
      (fun k => suzukiDF6D4DigammaTailCenter (N + k) t -
        suzukiDF6D4DigammaTailCenter (N + k + 1) t)
      (suzukiDF6D4DigammaTailCenter N t) := by
    convert hA.add hF using 1
    · ext k
      simp only [suzukiDF6D4DigammaTailCenter]
      ring
    · simp only [suzukiDF6D4DigammaTailCenter]
  have hUpper := hB.add hC
  have htail : Summable
      (fun k : Nat => suzukiDF6D4DigammaSummand (N + k) t) :=
    (summable_suzukiDF6D4DigammaSummand t).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)
  constructor
  · rw [← hB.tsum_eq]
    exact hB.summable.tsum_le_tsum (fun k => by
      let d : Real := (N + k : Nat) + 1 / 4
      let y : Real := t / 2
      have hd : 0 < d := by unfold d; positivity
      have hy : 0 ≤ y := by unfold y; positivity
      have hyd : y ≤ d := by
        unfold y d
        push_cast
        linarith
      have hlocal := suzukiDF6D4_localTrapezoid_error_nonneg hd hy hyd
      unfold suzukiDF6D4DigammaTailCenter
        suzukiDF6D4DigammaSummand suzukiDF6D4DigammaArctanTail
      dsimp only [d, y] at hlocal
      push_cast at hlocal ⊢
      rw [show ((N : Real) + k + 1 + 1 / 4) =
          (N : Real) + k + 1 / 4 + 1 by ring]
      ring_nf at hlocal ⊢
      nlinarith) htail
  · rw [← hUpper.tsum_eq]
    exact htail.tsum_le_tsum (fun k => by
      let d : Real := (N + k : Nat) + 1 / 4
      let y : Real := t / 2
      have hd : 0 < d := by unfold d; positivity
      have hy : 0 ≤ y := by unfold y; positivity
      have hyd : y ≤ d := by
        unfold y d
        push_cast
        linarith
      have hlocal := suzukiDF6D4_localTrapezoid_error hd hy hyd
      unfold suzukiDF6D4DigammaTailCenter
        suzukiDF6D4DigammaTailCorrection suzukiDF6D4DigammaSummand
        suzukiDF6D4DigammaArctanTail
      dsimp only [d, y] at hlocal
      push_cast at hlocal ⊢
      rw [show ((N : Real) + k + 1 + 1 / 4) =
          (N : Real) + k + 1 / 4 + 1 by ring]
      rw [abs_le] at hlocal
      ring_nf at hlocal ⊢
      nlinarith) hUpper.summable

end
end RiemannHypothesisProject.Experiments.M100
