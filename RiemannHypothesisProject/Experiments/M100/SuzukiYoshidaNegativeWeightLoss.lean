import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaAmbientFourierLeakage

/-!
# Normalized negative-weight loss for M100-DF6D5B3F-E

This module proves the exact cutoff-44 cardinal-sine majorant for the negative
part of Suzuki's normalized Fourier multiplier.  The zero crossing is kept
explicit: the loss is `log (z / |u|)` on `[-z,z]`, rather than the broader raw
`-log |u|` loss on `[-1,1]` used to construct the common graph completion.
-/

namespace RiemannHypothesisProject.Experiments.M100
noncomputable section

open MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 800000 in

theorem nat_reciprocal_sq_tail_from_45 :
    (∑' n : Nat, 1 / ((n + 45 : Nat) : Real) ^ 2) ≤ (1 / 44 : Real) := by
  let g : Nat → Real := fun n => 1 / ((n + 44 : Nat) : Real)
  have hg_tendsto : Tendsto g atTop (𝓝 0) := by
    have hden : Tendsto (fun n : Nat => ((n + 44 : Nat) : Real))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_add_atTop_nat 44)
    convert hden.inv_tendsto_atTop using 1
    ext n
    simp [g]
  have htel : HasSum (fun n => g n - g (n + 1)) (1 / 44 : Real) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have hsumfun : (fun n : Nat =>
          ∑ i ∈ Finset.range n, (g i - g (i + 1))) =
          fun n : Nat => g 0 - g n := by
        funext n
        calc
          (∑ i ∈ Finset.range n, (g i - g (i + 1))) =
              -(∑ i ∈ Finset.range n, (g (i + 1) - g i)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = g 0 - g n := by
            rw [Finset.sum_range_sub]
            ring
      rw [hsumfun]
      have hconst : Tendsto (fun _ : Nat => (1 / 44 : Real)) atTop
          (𝓝 (1 / 44 : Real)) := tendsto_const_nhds
      have hlim := hconst.sub hg_tendsto
      simpa [g] using hlim
    · intro n
      dsimp only [g]
      apply sub_nonneg.mpr
      gcongr
      norm_num
  have hs : Summable (fun n : Nat => 1 / ((n + 45 : Nat) : Real) ^ 2) := by
    have hbase := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    change Summable ((fun n : Nat => 1 / (n : Real) ^ 2) ∘
      fun n : Nat => n + 45)
    exact hbase.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  calc
    (∑' n : Nat, 1 / ((n + 45 : Nat) : Real) ^ 2) ≤
        ∑' n : Nat, (g n - g (n + 1)) := by
      apply hs.tsum_le_tsum
      · intro n
        dsimp only [g]
        have ha : (0 : Real) < (n + 44 : Nat) := by positivity
        have hb : (0 : Real) < (n + 45 : Nat) := by positivity
        have hab : ((n + 45 : Nat) : Real) =
            ((n + 44 : Nat) : Real) + 1 := by
          push_cast
          ring
        calc
          1 / ((n + 45 : Nat) : Real) ^ 2 ≤
              1 / (((n + 44 : Nat) : Real) * (n + 45 : Nat)) := by
            apply one_div_le_one_div_of_le
            · positivity
            · rw [hab]
              nlinarith
          _ = 1 / ((n + 44 : Nat) : Real) -
                1 / ((n + 45 : Nat) : Real) := by
            field_simp
            rw [hab]
            ring
      · exact htel.summable
    _ = (1 / 44 : Real) := htel.tsum_eq

set_option maxHeartbeats 800000 in
theorem cutoff44HighIndex_reciprocal_sq_tsum_le :
    (∑' j : Cutoff44HighIndex, 1 / (j.1 : Real) ^ 2) ≤ (2 / 44 : Real) := by
  let high : Set Int := {n | n ∉ Finset.Icc (-44 : Int) 44}
  let base : Int → Real := fun n => 1 / (n : Real) ^ 2
  let f : Int → Real := high.indicator base
  have hbase : Summable base := by
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  have hf : Summable f := hbase.indicator high
  have hspos : Summable (fun n : Nat => f (n : Int)) := by
    exact hf.comp_injective (fun a b h => Int.ofNat_inj.mp h)
  have hsneg : Summable (fun n : Nat => f (-(n + 1 : Nat) : Int)) := by
    exact hf.comp_injective (fun a b h => by omega)
  have hpos : (∑' n : Nat, f n) ≤ (1 / 44 : Real) := by
    have hsplit := hspos.sum_add_tsum_nat_add 45
    have hzero : (∑ n ∈ Finset.range 45, f n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < 45 := Finset.mem_range.mp hn
      simp [f, high, base, Finset.mem_Icc]
      omega
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    have heq : (∑' i : Nat, f (i + 45 : Nat)) =
        ∑' i : Nat, 1 / ((i + 45 : Nat) : Real) ^ 2 := by
      apply tsum_congr
      intro n
      rw [show f (n + 45 : Nat) = base (n + 45 : Nat) by
        apply Set.indicator_of_mem
        simp [high, Finset.mem_Icc]
        omega]
      simp [base]
    rw [heq]
    exact nat_reciprocal_sq_tail_from_45
  have hneg : (∑' n : Nat, f (-(n + 1 : Nat) : Int)) ≤
      (1 / 44 : Real) := by
    have hsplit := hsneg.sum_add_tsum_nat_add 44
    have hzero : (∑ n ∈ Finset.range 44,
        f (-(n + 1 : Nat) : Int)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnlt : n < 44 := Finset.mem_range.mp hn
      simp [f, high, base, Finset.mem_Icc]
      omega
    rw [hzero, zero_add] at hsplit
    rw [← hsplit]
    have heq : (∑' i : Nat, f (-(i + 44 + 1 : Nat) : Int)) =
        ∑' i : Nat, 1 / ((i + 45 : Nat) : Real) ^ 2 := by
      apply tsum_congr
      intro n
      rw [show f (-(n + 44 + 1 : Nat) : Int) =
          base (-(n + 44 + 1 : Nat) : Int) by
        apply Set.indicator_of_mem
        simp [high, Finset.mem_Icc]
        omega]
      change 1 / ((-(n + 44 + 1 : Nat) : Int) : Real) ^ 2 =
        1 / ((n + 45 : Nat) : Real) ^ 2
      apply congrArg (fun x : Real => 1 / x)
      push_cast
      ring
    rw [heq]
    exact nat_reciprocal_sq_tail_from_45
  have hall : (∑' n : Int, f n) ≤ (2 / 44 : Real) := by
    rw [tsum_of_nat_of_neg_add_one hspos hsneg]
    have hneg' : (∑' n : Nat, f (-((n : Int) + 1))) ≤
        (1 / 44 : Real) := by
      convert hneg using 1
      apply tsum_congr
      intro n
      congr 1
    calc
      (∑' n : Nat, f n) + ∑' n : Nat, f (-((n : Int) + 1)) ≤
          (1 / 44 : Real) + 1 / 44 := add_le_add hpos hneg'
      _ = 2 / 44 := by norm_num
  have hsub : (∑' j : Cutoff44HighIndex, 1 / (j.1 : Real) ^ 2) =
      ∑' n : Int, f n := by
    rw [← tsum_subtype]
    change (∑' j : {n : Int // n ∉ Finset.Icc (-44 : Int) 44},
        1 / (j.1 : Real) ^ 2) = _
    rfl
  rw [hsub]
  exact hall

set_option maxHeartbeats 1200000 in
theorem cardinalSineCutoff44TailDensity_le_reciprocal_sq
    {z x : Real} (hz0 : 0 ≤ z) (hz45 : z < 45) (hx : |x| ≤ z) :
    cardinalSineCutoff44TailDensity x ≤
      2 * x ^ 2 / (44 * (1 - z / 45) ^ 2) := by
  let gap : Real := 1 - z / 45
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  have hrecip : Summable (fun j : Cutoff44HighIndex =>
      1 / (j.1 : Real) ^ 2) := by
    exact (Real.summable_one_div_int_pow.mpr (by norm_num)).subtype _
  have hpoint : ∀ j : Cutoff44HighIndex,
      Real.sinc (Real.pi * (x + (j.1 : Real))) ^ 2 ≤
        (x ^ 2 / gap ^ 2) * (1 / (j.1 : Real) ^ 2) := by
    intro j
    have hjCases : j.1 < -44 ∨ 44 < j.1 := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using j.2
    have hjAbs : (45 : Real) ≤ |(j.1 : Real)| := by
      rcases hjCases with hj | hj
      · rw [abs_of_nonpos]
        · exact_mod_cast (show (45 : Int) ≤ -j.1 by omega)
        · exact_mod_cast (show j.1 ≤ 0 by omega)
      · rw [abs_of_nonneg]
        · exact_mod_cast (show (45 : Int) ≤ j.1 by omega)
        · exact_mod_cast (show (0 : Int) ≤ j.1 by omega)
    have hjPos : 0 < |(j.1 : Real)| := lt_of_lt_of_le (by norm_num) hjAbs
    have hdenLower : |(j.1 : Real)| * gap ≤ |x + (j.1 : Real)| := by
      have htriangle : |(j.1 : Real)| - |x| ≤ |x + (j.1 : Real)| := by
        have h := abs_sub_abs_le_abs_sub (j.1 : Real) (-x)
        simpa [sub_eq_add_neg, add_comm] using h
      have hzScale : z ≤ |(j.1 : Real)| * (z / 45) := by
        by_cases hz : z = 0
        · simp [hz]
        · have hzpos : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz)
          have hzdiv : 0 ≤ z / 45 := div_nonneg hz0 (by norm_num)
          have hmul := mul_le_mul_of_nonneg_right hjAbs hzdiv
          calc
            z = 45 * (z / 45) := by ring
            _ ≤ |(j.1 : Real)| * (z / 45) := hmul
      calc
        |(j.1 : Real)| * gap =
            |(j.1 : Real)| - |(j.1 : Real)| * (z / 45) := by
          dsimp only [gap]
          ring
        _ ≤ |(j.1 : Real)| - z := sub_le_sub_left hzScale _
        _ ≤ |(j.1 : Real)| - |x| := sub_le_sub_left hx _
        _ ≤ |x + (j.1 : Real)| := htriangle
    have hdenPos : 0 < |x + (j.1 : Real)| :=
      lt_of_lt_of_le (mul_pos hjPos hgap) hdenLower
    have hsumNe : x + (j.1 : Real) ≠ 0 := by
      simpa only [abs_pos] using hdenPos
    have hargNe : Real.pi * (x + (j.1 : Real)) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero hsumNe
    have hshift :
        Real.sin (Real.pi * (x + (j.1 : Real))) ^ 2 =
          Real.sin (Real.pi * x) ^ 2 := by
      rw [show Real.pi * (x + (j.1 : Real)) =
          Real.pi * x + j.1 * Real.pi by ring,
        Real.sin_add_int_mul_pi, mul_pow]
      have hsign : ((-1 : Real) ^ j.1) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul]
        rw [mul_comm, ← Int.cast_negOnePow]
        norm_num [Int.negOnePow_two_mul]
      rw [hsign, one_mul]
    have hsinSq : Real.sin (Real.pi * x) ^ 2 ≤
        Real.pi ^ 2 * x ^ 2 := by
      have hs : |Real.sin (Real.pi * x)| ≤ |Real.pi * x| :=
        Real.abs_sin_le_abs
      have hs2 := mul_self_le_mul_self (abs_nonneg _) hs
      simpa only [← pow_two, sq_abs, mul_pow] using hs2
    have hfirst : Real.sinc (Real.pi * (x + (j.1 : Real))) ^ 2 ≤
        x ^ 2 / (x + (j.1 : Real)) ^ 2 := by
      rw [Real.sinc_of_ne_zero hargNe, div_pow, hshift]
      have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
      have hscaled : Real.sin (Real.pi * x) ^ 2 / Real.pi ^ 2 ≤ x ^ 2 := by
        rw [div_le_iff₀ hpiSq]
        simpa [mul_comm] using hsinSq
      calc
        Real.sin (Real.pi * x) ^ 2 /
              (Real.pi * (x + (j.1 : Real))) ^ 2 =
            (Real.sin (Real.pi * x) ^ 2 / Real.pi ^ 2) /
              (x + (j.1 : Real)) ^ 2 := by
          field_simp [Real.pi_ne_zero, hsumNe]
        _ ≤ x ^ 2 / (x + (j.1 : Real)) ^ 2 :=
          div_le_div_of_nonneg_right hscaled (sq_nonneg _)
    have hsqLower : (|(j.1 : Real)| * gap) ^ 2 ≤
        |x + (j.1 : Real)| ^ 2 := by
      simpa only [pow_two] using
        mul_self_le_mul_self
          (mul_nonneg hjPos.le hgap.le) hdenLower
    have hinv : 1 / |x + (j.1 : Real)| ^ 2 ≤
        1 / (|(j.1 : Real)| * gap) ^ 2 := by
      exact one_div_le_one_div_of_le (pow_pos (mul_pos hjPos hgap) 2) hsqLower
    apply hfirst.trans
    calc
      x ^ 2 / (x + (j.1 : Real)) ^ 2 =
          x ^ 2 * (1 / |x + (j.1 : Real)| ^ 2) := by
        rw [sq_abs]
        ring
      _ ≤ x ^ 2 * (1 / (|(j.1 : Real)| * gap) ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (sq_nonneg x)
      _ = (x ^ 2 / gap ^ 2) * (1 / (j.1 : Real) ^ 2) := by
        rw [mul_pow, sq_abs]
        field_simp [hgap.ne', hjPos.ne']
  rw [cardinalSineCutoff44TailDensity_eq_tsum_high]
  have hterms := summable_sq_sinc_pi_mul_add_int x
  have hleft : Summable (fun j : Cutoff44HighIndex =>
      Real.sinc (Real.pi * (x + (j.1 : Real))) ^ 2) := hterms.subtype _
  calc
    (∑' j : Cutoff44HighIndex,
        Real.sinc (Real.pi * (x + (j.1 : Real))) ^ 2) ≤
        ∑' j : Cutoff44HighIndex,
          (x ^ 2 / gap ^ 2) * (1 / (j.1 : Real) ^ 2) :=
      hleft.tsum_le_tsum hpoint (hrecip.mul_left _)
    _ = (x ^ 2 / gap ^ 2) *
        (∑' j : Cutoff44HighIndex, 1 / (j.1 : Real) ^ 2) := by
      rw [tsum_mul_left]
    _ ≤ (x ^ 2 / gap ^ 2) * (2 / 44) := by
      exact mul_le_mul_of_nonneg_left cutoff44HighIndex_reciprocal_sq_tsum_le
        (div_nonneg (sq_nonneg x) (sq_nonneg gap))
    _ = 2 * x ^ 2 / (44 * (1 - z / 45) ^ 2) := by
      dsimp only [gap]
      field_simp [hgap.ne']

set_option maxHeartbeats 1200000 in
theorem integral_sq_mul_log_div_self {z : Real} (hz : 0 < z) :
    (∫ u in (0 : Real)..z, u ^ 2 * Real.log (z / u)) = z ^ 3 / 9 := by
  let F : Real → Real := fun u =>
    (1 / 3 : Real) * u ^ 3 * (Real.log z - Real.log u) +
      (1 / 9 : Real) * u ^ 3
  have hint : IntervalIntegrable (fun u : Real =>
      u ^ 2 * Real.log (z / u)) volume 0 z := by
    have hconst : IntervalIntegrable (fun u : Real => u ^ 2 * Real.log z)
        volume 0 z := by
      have hc : Continuous (fun u : Real => u ^ 2 * Real.log z) :=
        (continuous_id.pow 2).mul continuous_const
      exact hc.intervalIntegrable 0 z
    have hlog : IntervalIntegrable (fun u : Real => u ^ 2 * Real.log u)
        volume 0 z := by
      exact intervalIntegral.intervalIntegrable_log'.continuousOn_mul
        (continuous_id.pow 2).continuousOn
    apply (hconst.sub hlog).congr
    intro u hu
    by_cases hu0 : u = 0
    · simp [hu0]
    · change u ^ 2 * Real.log z - u ^ 2 * Real.log u =
        u ^ 2 * Real.log (z / u)
      rw [Real.log_div hz.ne' hu0]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := F) (fa := 0) (fb := z ^ 3 / 9) (hint := hint)]
  · ring
  · exact hz
  · intro u hu
    have huPos : 0 < u := hu.1
    have hcube := ((hasDerivAt_id u).pow 3).const_mul (1 / 3 : Real)
    have hlog := (hasDerivAt_const u (Real.log z)).sub
      (Real.hasDerivAt_log huPos.ne')
    have hlast := ((hasDerivAt_id u).pow 3).const_mul (1 / 9 : Real)
    have hderiv := (hcube.mul hlog).add hlast
    convert hderiv using 1
    · ext y
      rfl
    · simp only [Pi.pow_apply, id_eq, Pi.sub_apply] at *
      rw [Real.log_div hz.ne' huPos.ne']
      field_simp [huPos.ne']
      ring
  · have hlogpow : Tendsto (fun u : Real => Real.log u * u ^ 3)
        (𝓝[>] 0) (𝓝 0) := by
      convert
        (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : Real) < 3))
          using 1
      ext u
      exact congrArg (fun t : Real => Real.log u * t)
        (Real.rpow_natCast u 3).symm
    have hpow : Tendsto (fun u : Real => u ^ 3) (𝓝[>] 0) (𝓝 0) := by
      have hc : ContinuousAt (fun u : Real => u ^ 3) 0 := by fun_prop
      exact tendsto_nhdsWithin_of_tendsto_nhds (by simpa using hc.tendsto)
    have hfirst : Tendsto (fun u : Real =>
        (u ^ 3 / 3) * (Real.log z - Real.log u))
        (𝓝[>] 0) (𝓝 0) := by
      have hconstPart := (hpow.div_const (3 : Real)).mul_const (Real.log z)
      have hlogPart : Tendsto (fun u : Real => (u ^ 3 / 3) * Real.log u)
          (𝓝[>] 0) (𝓝 0) := by
        convert hlogpow.const_mul (1 / 3 : Real) using 1
        · funext u
          ring
        · norm_num
      convert hconstPart.sub hlogPart using 1
      · funext u
        ring
      · norm_num
    have hlast : Tendsto (fun u : Real => u ^ 3 / 9)
        (𝓝[>] 0) (𝓝 0) := by simpa using hpow.div_const 9
    convert hfirst.add hlast using 1
    · funext u
      simp only [F]
      ring
    · norm_num
  · have hz0 : z ≠ 0 := hz.ne'
    have hcont : ContinuousAt F z := by
      unfold F
      fun_prop
    have heval : F z = z ^ 3 / 9 := by
      simp only [F, sub_self, mul_zero, zero_add]
      ring
    simpa [heval] using
      tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto

theorem intervalIntegrable_sq_mul_log_div_self {z : Real} (hz : 0 < z) :
    IntervalIntegrable (fun u : Real => u ^ 2 * Real.log (z / u))
      volume 0 z := by
  have hconst : IntervalIntegrable (fun u : Real => u ^ 2 * Real.log z)
      volume 0 z := by
    have hc : Continuous (fun u : Real => u ^ 2 * Real.log z) :=
      (continuous_id.pow 2).mul continuous_const
    exact hc.intervalIntegrable 0 z
  have hlog : IntervalIntegrable (fun u : Real => u ^ 2 * Real.log u)
      volume 0 z := by
    exact intervalIntegral.intervalIntegrable_log'.continuousOn_mul
      (continuous_id.pow 2).continuousOn
  apply (hconst.sub hlog).congr
  intro u hu
  have huPos : 0 < u := by
    rw [uIoc_of_le hz.le] at hu
    exact hu.1
  change u ^ 2 * Real.log z - u ^ 2 * Real.log u =
    u ^ 2 * Real.log (z / u)
  rw [Real.log_div hz.ne' huPos.ne']
  ring

set_option maxHeartbeats 1200000 in
theorem cardinalSineCutoff44_negativeLogMoment_le
    {z : Real} (hz : 0 < z) (hz45 : z < 45) :
    (∫ u in -z..z,
      Real.log (z / |u|) * cardinalSineCutoff44TailDensity u) ≤
        4 * z ^ 3 / (9 * 44 * (1 - z / 45) ^ 2) := by
  let g : Real → Real := fun u =>
    Real.log (z / |u|) * cardinalSineCutoff44TailDensity u
  let upper : Real → Real := fun u =>
    (2 / (44 * (1 - z / 45) ^ 2)) *
      (u ^ 2 * Real.log (z / u))
  have hgap : 0 < 1 - z / 45 := by linarith
  have hpos : IntervalIntegrable g volume 0 z := by
    have hconst : IntervalIntegrable (fun u : Real =>
        Real.log z * cardinalSineCutoff44TailDensity u) volume 0 z := by
      exact Continuous.intervalIntegrable
        (continuous_const.mul continuous_cardinalSineCutoff44TailDensity) 0 z
    have hlog : IntervalIntegrable (fun u : Real =>
        Real.log u * cardinalSineCutoff44TailDensity u) volume 0 z := by
      exact intervalIntegral.intervalIntegrable_log'.mul_continuousOn
        continuous_cardinalSineCutoff44TailDensity.continuousOn
    apply (hconst.sub hlog).congr
    intro u hu
    have huPos : 0 < u := by
      rw [uIoc_of_le hz.le] at hu
      exact hu.1
    change Real.log z * cardinalSineCutoff44TailDensity u -
        Real.log u * cardinalSineCutoff44TailDensity u = g u
    dsimp only [g]
    rw [show |u| = u by exact abs_of_pos huPos,
      Real.log_div hz.ne' huPos.ne']
    ring
  have hnegComp : IntervalIntegrable (fun u : Real => g (-u)) volume 0 z := by
    have hconst : IntervalIntegrable (fun u : Real =>
        Real.log z * cardinalSineCutoff44TailDensity (-u)) volume 0 z := by
      exact Continuous.intervalIntegrable
        (continuous_const.mul
          (continuous_cardinalSineCutoff44TailDensity.comp continuous_neg)) 0 z
    have hlog : IntervalIntegrable (fun u : Real =>
        Real.log u * cardinalSineCutoff44TailDensity (-u)) volume 0 z := by
      exact intervalIntegral.intervalIntegrable_log'.mul_continuousOn
        (continuous_cardinalSineCutoff44TailDensity.comp continuous_neg).continuousOn
    apply (hconst.sub hlog).congr
    intro u hu
    have huPos : 0 < u := by
      rw [uIoc_of_le hz.le] at hu
      exact hu.1
    change Real.log z * cardinalSineCutoff44TailDensity (-u) -
        Real.log u * cardinalSineCutoff44TailDensity (-u) = g (-u)
    dsimp only [g]
    rw [show |-u| = u by simp [abs_of_pos huPos],
      Real.log_div hz.ne' huPos.ne']
    ring
  have hupper : IntervalIntegrable upper volume 0 z := by
    exact (intervalIntegrable_sq_mul_log_div_self hz).const_mul _
  have hpointPos : ∀ u ∈ Icc (0 : Real) z, g u ≤ upper u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [g, upper, hu0]
    · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hlogNonneg : 0 ≤ Real.log (z / u) := by
        apply Real.log_nonneg
        exact (one_le_div₀ huPos).mpr hu.2
      have htail := cardinalSineCutoff44TailDensity_le_reciprocal_sq
        hz.le hz45 (by rw [abs_of_pos huPos]; exact hu.2)
      dsimp only [g, upper]
      rw [abs_of_pos huPos]
      have htail' : cardinalSineCutoff44TailDensity u ≤
          (2 / (44 * (1 - z / 45) ^ 2)) * u ^ 2 := by
        calc
        cardinalSineCutoff44TailDensity u ≤
            2 * u ^ 2 / (44 * (1 - z / 45) ^ 2) := htail
        _ = (2 / (44 * (1 - z / 45) ^ 2)) * u ^ 2 := by ring
      calc
        Real.log (z / u) * cardinalSineCutoff44TailDensity u ≤
            Real.log (z / u) *
              ((2 / (44 * (1 - z / 45) ^ 2)) * u ^ 2) :=
          mul_le_mul_of_nonneg_left htail' hlogNonneg
        _ = (2 / (44 * (1 - z / 45) ^ 2)) *
              (u ^ 2 * Real.log (z / u)) := by ring
  have hpointNeg : ∀ u ∈ Icc (0 : Real) z, g (-u) ≤ upper u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [g, upper, hu0]
    · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hlogNonneg : 0 ≤ Real.log (z / u) := by
        apply Real.log_nonneg
        exact (one_le_div₀ huPos).mpr hu.2
      have htail := cardinalSineCutoff44TailDensity_le_reciprocal_sq
        hz.le hz45 (x := -u) (by simpa [abs_of_pos huPos] using hu.2)
      dsimp only [g, upper]
      rw [show |-u| = u by simp [abs_of_pos huPos]]
      have htail' : cardinalSineCutoff44TailDensity (-u) ≤
          (2 / (44 * (1 - z / 45) ^ 2)) * u ^ 2 := by
        calc
        cardinalSineCutoff44TailDensity (-u) ≤
            2 * (-u) ^ 2 / (44 * (1 - z / 45) ^ 2) := htail
        _ = (2 / (44 * (1 - z / 45) ^ 2)) * u ^ 2 := by ring
      calc
        Real.log (z / u) * cardinalSineCutoff44TailDensity (-u) ≤
            Real.log (z / u) *
              ((2 / (44 * (1 - z / 45) ^ 2)) * u ^ 2) :=
          mul_le_mul_of_nonneg_left htail' hlogNonneg
        _ = (2 / (44 * (1 - z / 45) ^ 2)) *
              (u ^ 2 * Real.log (z / u)) := by ring
  have hposBound : (∫ u in (0 : Real)..z, g u) ≤
      2 * z ^ 3 / (9 * 44 * (1 - z / 45) ^ 2) := by
    have hmono := intervalIntegral.integral_mono_on hz.le hpos hupper hpointPos
    dsimp only [upper] at hmono
    rw [intervalIntegral.integral_const_mul,
      integral_sq_mul_log_div_self hz] at hmono
    convert hmono using 1
    all_goals field_simp [hgap.ne']
  have hnegBound : (∫ u in -z..(0 : Real), g u) ≤
      2 * z ^ 3 / (9 * 44 * (1 - z / 45) ^ 2) := by
    have hnegEq : (∫ u in -z..(0 : Real), g u) =
        ∫ u in (0 : Real)..z, g (-u) := by
      simpa only [neg_zero] using
        (intervalIntegral.integral_comp_neg (f := g) (a := 0) (b := z)).symm
    rw [hnegEq]
    have hmono := intervalIntegral.integral_mono_on hz.le hnegComp hupper hpointNeg
    dsimp only [upper] at hmono
    rw [intervalIntegral.integral_const_mul,
      integral_sq_mul_log_div_self hz] at hmono
    convert hmono using 1
    all_goals field_simp [hgap.ne']
  change (∫ u in -z..z, g u) ≤ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := (0 : Real))]
  · have hsum := add_le_add hnegBound hposBound
    calc
      (∫ x in -z..0, g x) + ∫ x in 0..z, g x ≤
          2 * (2 * z ^ 3 / (9 * 44 * (1 - z / 45) ^ 2)) := by
        linarith
      _ = 4 * z ^ 3 / (9 * 44 * (1 - z / 45) ^ 2) := by ring
  · have hrev : IntervalIntegrable (fun x : Real => g (-x)) volume z 0 :=
      hnegComp.symm
    apply (IntervalIntegrable.iff_comp_neg (f := g) (a := -z) (b := 0)).mpr
    simpa only [neg_neg, neg_zero] using hrev
  · exact hpos

theorem intervalIntegrable_log_zeroCrossing_div_abs
    {z : Real} (hz : 0 < z) :
    IntervalIntegrable (fun u : Real => Real.log (z / |u|))
      volume (-z) z := by
  have hlogabs : IntervalIntegrable (fun u : Real => Real.log |u|)
      volume (-z) z := by
    have h := MeromorphicOn.id.intervalIntegrable_log_norm
      (a := -z) (b := z)
    change IntervalIntegrable (fun u : Real => Real.log |u|) volume (-z) z at h
    exact h
  have hconst : IntervalIntegrable (fun _ : Real => Real.log z)
      volume (-z) z := continuous_const.intervalIntegrable _ _
  have hbase : IntervalIntegrable
      (fun u : Real => Real.log z - Real.log |u|)
      volume (-z) z := hconst.sub hlogabs
  apply hbase.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  have hne : ∀ᵐ u : Real ∂volume, u ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, setOf_eq_eq_singleton] using
      (MeasureTheory.measure_singleton (μ := volume) (0 : Real))
  filter_upwards [hne] with u hu
  intro _
  rw [Real.log_div hz.ne' (abs_ne_zero.mpr hu)]

theorem intervalIntegrable_cardinalSineCutoff44_negativeLogMoment
    {z : Real} (hz : 0 < z) :
    IntervalIntegrable (fun u : Real =>
      Real.log (z / |u|) * cardinalSineCutoff44TailDensity u)
      volume (-z) z :=
  (intervalIntegrable_log_zeroCrossing_div_abs hz).mul_continuousOn
    continuous_cardinalSineCutoff44TailDensity.continuousOn

theorem scaled_cardinalSineCutoff44_negativeWeightMoment_le :
    (∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
        suzukiDF6D5B3FENegativeWeightThreshold,
      (2 * suzukiProjectAStar) *
        (suzukiDF6D5B3FENormalizedNegativeWeight ξ *
          cardinalSineCutoff44TailDensity
            ((2 * suzukiProjectAStar) * ξ))) ≤
      suzukiDF6D4DF0NegativeWeightLoss := by
  let c : Real := 2 * suzukiProjectAStar
  let z : Real := suzukiDF6D4DF0ZeroCrossing
  let f : Real → Real := fun u =>
    Real.log (z / |u|) * cardinalSineCutoff44TailDensity u
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (by norm_num) suzukiProjectAStar_pos
  have hscaled := intervalIntegral.smul_integral_comp_mul_left f c
    (a := -suzukiDF6D5B3FENegativeWeightThreshold)
    (b := suzukiDF6D5B3FENegativeWeightThreshold)
  have hleft : c * (-suzukiDF6D5B3FENegativeWeightThreshold) = -z := by
    dsimp only [c, z]
    rw [mul_neg, suzukiDF6D5B3FE_twoA_mul_negativeWeightThreshold]
  have hright : c * suzukiDF6D5B3FENegativeWeightThreshold = z := by
    exact suzukiDF6D5B3FE_twoA_mul_negativeWeightThreshold
  have hmoment := cardinalSineCutoff44_negativeLogMoment_le
    suzukiDF6D4DF0ZeroCrossing_pos
    suzukiDF6D4DF0ZeroCrossing_lt_45
  unfold suzukiDF6D4DF0NegativeWeightLoss at hmoment ⊢
  rw [intervalIntegral.integral_const_mul]
  change c • (∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
    suzukiDF6D5B3FENegativeWeightThreshold, f (c * ξ)) ≤ _
  rw [hscaled, hleft, hright]
  exact hmoment

theorem suzukiDF6D5B3FENormalizedNegativeWeight_nonneg_on
    {ξ : Real}
    (hξ : ξ ∈ Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold) :
    0 ≤ suzukiDF6D5B3FENormalizedNegativeWeight ξ := by
  by_cases hξ0 : ξ = 0
  · simp [suzukiDF6D5B3FENormalizedNegativeWeight, hξ0]
  · have hc : 0 < 2 * suzukiProjectAStar :=
      mul_pos (by norm_num) suzukiProjectAStar_pos
    have habsξ : |ξ| ≤ suzukiDF6D5B3FENegativeWeightThreshold :=
      (abs_le.mpr hξ)
    have habsScaled : |(2 * suzukiProjectAStar) * ξ| ≤
        suzukiDF6D4DF0ZeroCrossing := by
      rw [abs_mul, abs_of_pos hc]
      calc
        (2 * suzukiProjectAStar) * |ξ| ≤
            (2 * suzukiProjectAStar) *
              suzukiDF6D5B3FENegativeWeightThreshold :=
          mul_le_mul_of_nonneg_left habsξ hc.le
        _ = suzukiDF6D4DF0ZeroCrossing :=
          suzukiDF6D5B3FE_twoA_mul_negativeWeightThreshold
    unfold suzukiDF6D5B3FENormalizedNegativeWeight
    apply Real.log_nonneg
    exact (one_le_div₀ (abs_pos.mpr (mul_ne_zero hc.ne' hξ0))).mpr habsScaled

theorem intervalIntegrable_scaled_cardinalSineCutoff44_negativeWeightMoment :
    IntervalIntegrable (fun ξ : Real =>
      (2 * suzukiProjectAStar) *
        (suzukiDF6D5B3FENormalizedNegativeWeight ξ *
          cardinalSineCutoff44TailDensity
            ((2 * suzukiProjectAStar) * ξ))) volume
      (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold := by
  let c : Real := 2 * suzukiProjectAStar
  let z : Real := suzukiDF6D4DF0ZeroCrossing
  let f : Real → Real := fun u =>
    Real.log (z / |u|) * cardinalSineCutoff44TailDensity u
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact mul_ne_zero (by norm_num) suzukiProjectAStar_pos.ne'
  have hcomp :=
    (intervalIntegrable_cardinalSineCutoff44_negativeLogMoment
      suzukiDF6D4DF0ZeroCrossing_pos).comp_mul_left (c := c)
  have hleft : (-z) / c =
      -suzukiDF6D5B3FENegativeWeightThreshold := by
    unfold suzukiDF6D5B3FENegativeWeightThreshold
    dsimp only [c, z]
    ring
  have hright : z / c =
      suzukiDF6D5B3FENegativeWeightThreshold := by
    rfl
  rw [hleft, hright] at hcomp
  have hscaled := hcomp.const_mul c
  convert hscaled using 1
  funext ξ
  rfl

theorem intervalIntegrable_suzukiDF6D5B3FENormalizedNegativeWeight :
    IntervalIntegrable suzukiDF6D5B3FENormalizedNegativeWeight volume
      (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold := by
  let c : Real := 2 * suzukiProjectAStar
  let z : Real := suzukiDF6D4DF0ZeroCrossing
  let f : Real → Real := fun u => Real.log (z / |u|)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact mul_ne_zero (by norm_num) suzukiProjectAStar_pos.ne'
  have hcomp :=
    (intervalIntegrable_log_zeroCrossing_div_abs
      suzukiDF6D4DF0ZeroCrossing_pos).comp_mul_left (c := c)
  have hleft : (-z) / c =
      -suzukiDF6D5B3FENegativeWeightThreshold := by
    unfold suzukiDF6D5B3FENegativeWeightThreshold
    dsimp only [c, z]
    ring
  have hright : z / c =
      suzukiDF6D5B3FENegativeWeightThreshold := by
    rfl
  rw [hleft, hright] at hcomp
  exact hcomp

theorem norm_sq_fourier_cutoff44HighExponential_linearCombination_le_tailDensity
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (l : Cutoff44HighIndex →₀ Complex) :
    ∀ᵐ ξ ∂(volume : Measure Real),
      ‖(FourierTransform.fourier
        (Finsupp.linearCombination Complex cutoff44HighExponential l) :
          SuzukiL2) ξ‖ ^ 2 ≤
        (l.sum fun _ c => ‖c‖ ^ 2) *
          ((2 * suzukiProjectAStar) *
            cardinalSineCutoff44TailDensity
              ((2 * suzukiProjectAStar) * ξ)) := by
  let coeffSq : Real := l.sum fun _ c => ‖c‖ ^ 2
  have hcoeff : 0 ≤ coeffSq :=
    Finsupp.sum_nonneg fun _ _ => sq_nonneg _
  have hfourier :=
    fourier_cutoff44HighExponential_linearCombination_coe_ae hsource l
  filter_upwards [hfourier] with ξ hξ
  rw [hξ]
  have hcs := norm_finset_sum_mul_sq_le l.support
    (fun j => l j)
    (fun j => ((Real.sqrt (2 * suzukiProjectAStar) *
      Real.sinc (Real.pi *
        (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex))
  apply hcs.trans
  rw [cardinalSineCutoff44TailDensity_eq_tsum_high]
  have hsqrt : Real.sqrt (2 * suzukiProjectAStar) ^ 2 =
      2 * suzukiProjectAStar := Real.sq_sqrt
        (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)
  have hsummable : Summable (fun j : Cutoff44HighIndex =>
      Real.sinc (Real.pi *
        (2 * suzukiProjectAStar * ξ + (j.1 : Real))) ^ 2) :=
    (summable_sq_sinc_pi_mul_add_int
      (2 * suzukiProjectAStar * ξ)).subtype _
  have hsum := hsummable.sum_le_tsum l.support
    (fun j hj => sq_nonneg _)
  have hzEq :
      (∑ i ∈ l.support,
        ‖((Real.sqrt (2 * suzukiProjectAStar) *
          Real.sinc (Real.pi *
            (2 * suzukiProjectAStar * ξ + (i.1 : Real))) : Real) :
              Complex)‖ ^ 2) =
        (2 * suzukiProjectAStar) *
          ∑ i ∈ l.support, Real.sinc (Real.pi *
            (2 * suzukiProjectAStar * ξ + (i.1 : Real))) ^ 2 := by
    simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, hsqrt]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sq_abs]
  rw [hzEq]
  change coeffSq * ((2 * suzukiProjectAStar) *
      ∑ i ∈ l.support, Real.sinc (Real.pi *
        (2 * suzukiProjectAStar * ξ + (i.1 : Real))) ^ 2) ≤
    coeffSq * ((2 * suzukiProjectAStar) *
      ∑' j : Cutoff44HighIndex, Real.sinc (Real.pi *
        (2 * suzukiProjectAStar * ξ + (j.1 : Real))) ^ 2)
  apply mul_le_mul_of_nonneg_left _ hcoeff
  exact mul_le_mul_of_nonneg_left hsum
    (mul_nonneg (by norm_num) suzukiProjectAStar_pos.le)

set_option maxHeartbeats 1200000 in
theorem cutoff44HighExponential_linearCombination_normalizedNegativeWeightLoss
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (l : Cutoff44HighIndex →₀ Complex) :
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy
        (Finsupp.linearCombination Complex cutoff44HighExponential l) ≤
      suzukiDF6D4DF0NegativeWeightLoss *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
  let v := Finsupp.linearCombination Complex cutoff44HighExponential l
  let coeffSq : Real := l.sum fun _ c => ‖c‖ ^ 2
  let amplitude : Real → Complex := fun ξ => ∑ j ∈ l.support,
    l j * ((Real.sqrt (2 * suzukiProjectAStar) *
      Real.sinc (Real.pi *
        (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex)
  have hcoeff : 0 ≤ coeffSq := by
    dsimp only [coeffSq]
    exact Finsupp.sum_nonneg fun _ _ => sq_nonneg _
  have hamp : Continuous amplitude := by
    unfold amplitude
    fun_prop
  have hdensity : Continuous (fun ξ : Real => ‖amplitude ξ‖ ^ 2) :=
    hamp.norm.pow 2
  have hfourier :=
    fourier_cutoff44HighExponential_linearCombination_coe_ae hsource l
  have hleftExplicit : IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * ‖amplitude ξ‖ ^ 2)
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold :=
    intervalIntegrable_suzukiDF6D5B3FENormalizedNegativeWeight.mul_continuousOn
      hdensity.continuousOn
  have hleft : IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2)
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold := by
    apply hleftExplicit.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).2
    filter_upwards [hfourier] with ξ hξ
    intro _
    rw [hξ]
  have hright : IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        (coeffSq * ((2 * suzukiProjectAStar) *
          cardinalSineCutoff44TailDensity
            ((2 * suzukiProjectAStar) * ξ))))
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold := by
    have hscaled :=
      intervalIntegrable_scaled_cardinalSineCutoff44_negativeWeightMoment.const_mul
        coeffSq
    convert hscaled using 1
    funext ξ
    ring
  have hpointBase :=
    norm_sq_fourier_cutoff44HighExponential_linearCombination_le_tailDensity
      hsource l
  have hpoint : (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2) ≤ᵐ[
      volume.restrict
        (Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
          suzukiDF6D5B3FENegativeWeightThreshold)]
      (fun ξ : Real =>
        suzukiDF6D5B3FENormalizedNegativeWeight ξ *
          (coeffSq * ((2 * suzukiProjectAStar) *
            cardinalSineCutoff44TailDensity
              ((2 * suzukiProjectAStar) * ξ)))) := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hpointBase] with ξ hξ
    intro hmem
    exact mul_le_mul_of_nonneg_left hξ
      (suzukiDF6D5B3FENormalizedNegativeWeight_nonneg_on hmem)
  have hmono := intervalIntegral.integral_mono_ae_restrict
    (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)
    hleft hright hpoint
  have hfactor :
      (∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
          suzukiDF6D5B3FENegativeWeightThreshold,
        suzukiDF6D5B3FENormalizedNegativeWeight ξ *
          (coeffSq * ((2 * suzukiProjectAStar) *
            cardinalSineCutoff44TailDensity
              ((2 * suzukiProjectAStar) * ξ)))) =
        coeffSq *
          (∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
              suzukiDF6D5B3FENegativeWeightThreshold,
            (2 * suzukiProjectAStar) *
              (suzukiDF6D5B3FENormalizedNegativeWeight ξ *
                cardinalSineCutoff44TailDensity
                  ((2 * suzukiProjectAStar) * ξ))) := by
    conv_rhs => rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ξ hξ
    ring
  calc
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy
        (Finsupp.linearCombination Complex cutoff44HighExponential l) =
        ∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
          suzukiDF6D5B3FENegativeWeightThreshold,
        suzukiDF6D5B3FENormalizedNegativeWeight ξ *
          ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2 := rfl
    _ ≤ ∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
          suzukiDF6D5B3FENegativeWeightThreshold,
        suzukiDF6D5B3FENormalizedNegativeWeight ξ *
          (coeffSq * ((2 * suzukiProjectAStar) *
            cardinalSineCutoff44TailDensity
              ((2 * suzukiProjectAStar) * ξ))) := hmono
    _ = coeffSq *
          (∫ ξ in -suzukiDF6D5B3FENegativeWeightThreshold..
              suzukiDF6D5B3FENegativeWeightThreshold,
            (2 * suzukiProjectAStar) *
              (suzukiDF6D5B3FENormalizedNegativeWeight ξ *
                cardinalSineCutoff44TailDensity
                  ((2 * suzukiProjectAStar) * ξ))) := hfactor
    _ ≤ coeffSq * suzukiDF6D4DF0NegativeWeightLoss :=
      mul_le_mul_of_nonneg_left
        scaled_cardinalSineCutoff44_negativeWeightMoment_le hcoeff
    _ = suzukiDF6D4DF0NegativeWeightLoss *
        ‖Finsupp.linearCombination Complex cutoff44HighExponential l‖ ^ 2 := by
      rw [norm_sq_cutoff44HighExponential_linearCombination]
      dsimp only [coeffSq]
      ring

theorem exists_cutoff44HighExponential_linearCombination_tendsto_of_mem_closure
    {v : SuzukiL2}
    (hv : v ∈ cutoff44HighExponentialSubspace.topologicalClosure) :
    ∃ l : Nat → (Cutoff44HighIndex →₀ Complex),
      Tendsto (fun n =>
        Finsupp.linearCombination Complex cutoff44HighExponential (l n))
        atTop (𝓝 v) := by
  have hvSet : v ∈ closure (cutoff44HighExponentialSubspace : Set SuzukiL2) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hv
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp hvSet
  have hexists : ∀ n : Nat, ∃ l : Cutoff44HighIndex →₀ Complex,
      Finsupp.linearCombination Complex cutoff44HighExponential l = w n := by
    intro n
    exact Finsupp.mem_span_range_iff_exists_finsupp.mp (hw n)
  choose l hl using hexists
  refine ⟨l, ?_⟩
  convert hwlim using 1
  funext n
  exact hl n

theorem exists_ae_tendsto_fourier_subsequence_of_mem_cutoff44HighClosure
    {v : SuzukiL2}
    (hv : v ∈ cutoff44HighExponentialSubspace.topologicalClosure) :
    ∃ l : Nat → (Cutoff44HighIndex →₀ Complex), ∃ ns : Nat → Nat,
      StrictMono ns ∧
      Tendsto (fun n =>
        Finsupp.linearCombination Complex cutoff44HighExponential (l (ns n)))
        atTop (𝓝 v) ∧
      ∀ᵐ ξ ∂(volume : Measure Real),
        Tendsto (fun n =>
          (FourierTransform.fourier
            (Finsupp.linearCombination Complex cutoff44HighExponential
              (l (ns n))) : SuzukiL2) ξ)
          atTop
          (𝓝 ((FourierTransform.fourier v : SuzukiL2) ξ)) := by
  obtain ⟨l, hlim⟩ :=
    exists_cutoff44HighExponential_linearCombination_tendsto_of_mem_closure hv
  have hfourierLim : Tendsto (fun n =>
      FourierTransform.fourier
        (Finsupp.linearCombination Complex cutoff44HighExponential (l n)))
      atTop (𝓝 (FourierTransform.fourier v : SuzukiL2)) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto v).comp hlim
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hfourierLim
  obtain ⟨ns, hns, hAE⟩ := hmeasure.exists_seq_tendsto_ae
  refine ⟨l, ns, hns, hlim.comp hns.tendsto_atTop, ?_⟩
  exact hAE

theorem intervalIntegrable_cutoff44HighExponential_linearCombination_normalizedNegativeWeight
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (l : Cutoff44HighIndex →₀ Complex) :
    IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        ‖(FourierTransform.fourier
          (Finsupp.linearCombination Complex cutoff44HighExponential l) :
            SuzukiL2) ξ‖ ^ 2)
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold := by
  let amplitude : Real → Complex := fun ξ => ∑ j ∈ l.support,
    l j * ((Real.sqrt (2 * suzukiProjectAStar) *
      Real.sinc (Real.pi *
        (2 * suzukiProjectAStar * ξ + (j.1 : Real))) : Real) : Complex)
  have hamp : Continuous amplitude := by
    unfold amplitude
    fun_prop
  have hdensity : Continuous (fun ξ : Real => ‖amplitude ξ‖ ^ 2) :=
    hamp.norm.pow 2
  have hfourier :=
    fourier_cutoff44HighExponential_linearCombination_coe_ae hsource l
  have hexplicit : IntervalIntegrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ * ‖amplitude ξ‖ ^ 2)
      volume (-suzukiDF6D5B3FENegativeWeightThreshold)
        suzukiDF6D5B3FENegativeWeightThreshold :=
    intervalIntegrable_suzukiDF6D5B3FENormalizedNegativeWeight.mul_continuousOn
      hdensity.continuousOn
  apply hexplicit.congr_ae
  apply (ae_restrict_iff' measurableSet_uIoc).2
  filter_upwards [hfourier] with ξ hξ
  intro _
  rw [hξ]

theorem integrable_cutoff44HighExponential_linearCombination_normalizedNegativeWeight
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (l : Cutoff44HighIndex →₀ Complex) :
    Integrable (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        ‖(FourierTransform.fourier
          (Finsupp.linearCombination Complex cutoff44HighExponential l) :
            SuzukiL2) ξ‖ ^ 2)
      (volume.restrict
        (Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
          suzukiDF6D5B3FENegativeWeightThreshold)) := by
  change IntegrableOn (fun ξ : Real =>
      suzukiDF6D5B3FENormalizedNegativeWeight ξ *
        ‖(FourierTransform.fourier
          (Finsupp.linearCombination Complex cutoff44HighExponential l) :
            SuzukiL2) ξ‖ ^ 2)
    (Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold) volume
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le
    (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)]
  exact
    intervalIntegrable_cutoff44HighExponential_linearCombination_normalizedNegativeWeight
      hsource l

theorem suzukiDF6D4DF0NegativeWeightLoss_nonneg :
    0 ≤ suzukiDF6D4DF0NegativeWeightLoss := by
  unfold suzukiDF6D4DF0NegativeWeightLoss
  have hgap : 0 < 1 - suzukiDF6D4DF0ZeroCrossing / 45 := by
    linarith [suzukiDF6D4DF0ZeroCrossing_lt_45]
  exact div_nonneg
    (mul_nonneg (by norm_num) (pow_nonneg suzukiDF6D4DF0ZeroCrossing_pos.le 3))
    (mul_nonneg (by norm_num) (sq_nonneg _))

set_option maxHeartbeats 1200000 in
theorem cutoff44HighExponentialClosure_normalizedNegativeWeightLoss
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {v : SuzukiL2}
    (hv : v ∈ cutoff44HighExponentialSubspace.topologicalClosure) :
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy v ≤
      suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2 := by
  obtain ⟨l, ns, hns, hlim, hAE⟩ :=
    exists_ae_tendsto_fourier_subsequence_of_mem_cutoff44HighClosure hv
  let w : Nat → SuzukiL2 := fun n =>
    Finsupp.linearCombination Complex cutoff44HighExponential (l (ns n))
  let band : Set Real :=
    Icc (-suzukiDF6D5B3FENegativeWeightThreshold)
      suzukiDF6D5B3FENegativeWeightThreshold
  let μ : Measure Real := volume.restrict band
  let G : Nat → Real → Real := fun n ξ =>
    suzukiDF6D5B3FENormalizedNegativeWeight ξ *
      ‖(FourierTransform.fourier (w n) : SuzukiL2) ξ‖ ^ 2
  let f : Real → Real := fun ξ =>
    suzukiDF6D5B3FENormalizedNegativeWeight ξ *
      ‖(FourierTransform.fourier v : SuzukiL2) ξ‖ ^ 2
  have hlim' : Tendsto w atTop (𝓝 v) := hlim
  have hGf : ∀ᵐ ξ ∂μ, Tendsto (fun n => G n ξ) atTop (𝓝 (f ξ)) := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    filter_upwards [hAE] with ξ hξ
    intro hmem
    exact tendsto_const_nhds.mul (hξ.norm.pow 2)
  have hGint : ∀ n, Integrable (G n) μ := by
    intro n
    exact
      integrable_cutoff44HighExponential_linearCombination_normalizedNegativeWeight
        hsource (l (ns n))
  have hGnonneg : ∀ n, 0 ≤ᵐ[μ] G n := by
    intro n
    apply (ae_restrict_iff' measurableSet_Icc).2
    exact Eventually.of_forall fun ξ hξ =>
      mul_nonneg (suzukiDF6D5B3FENormalizedNegativeWeight_nonneg_on hξ)
        (sq_nonneg _)
  have hfnonneg : 0 ≤ᵐ[μ] f := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    exact Eventually.of_forall fun ξ hξ =>
      mul_nonneg (suzukiDF6D5B3FENormalizedNegativeWeight_nonneg_on hξ)
        (sq_nonneg _)
  have hsetIntegral (n : Nat) :
      (∫ ξ, G n ξ ∂μ) =
        suzukiDF6D5B3FENormalizedNegativeWeightEnergy (w n) := by
    dsimp only [μ, band, G]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)]
    rfl
  have hlinEq (n : Nat) :
      (∫⁻ ξ, ‖G n ξ‖ₑ ∂μ) =
        ENNReal.ofReal
          (suzukiDF6D5B3FENormalizedNegativeWeightEnergy (w n)) := by
    calc
      (∫⁻ ξ, ‖G n ξ‖ₑ ∂μ) = ∫⁻ ξ, ENNReal.ofReal (G n ξ) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hGnonneg n] with ξ hξ
        rw [← ofReal_norm, Real.norm_of_nonneg hξ]
      _ = ENNReal.ofReal (∫ ξ, G n ξ ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal (hGint n) (hGnonneg n)).symm
      _ = ENNReal.ofReal
          (suzukiDF6D5B3FENormalizedNegativeWeightEnergy (w n)) := by
        rw [hsetIntegral]
  have hlinBound : ∀ n,
      (∫⁻ ξ, ‖G n ξ‖ₑ ∂μ) ≤
        ENNReal.ofReal
          (suzukiDF6D4DF0NegativeWeightLoss * ‖w n‖ ^ 2) := by
    intro n
    rw [hlinEq]
    apply ENNReal.ofReal_le_ofReal
    exact cutoff44HighExponential_linearCombination_normalizedNegativeWeightLoss
      hsource (l (ns n))
  have hboundTendsto : Tendsto (fun n =>
      ENNReal.ofReal
        (suzukiDF6D4DF0NegativeWeightLoss * ‖w n‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal
        (suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2))) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    exact tendsto_const_nhds.mul (hlim'.norm.pow 2)
  have hliminfUpper :
      liminf (fun n => ∫⁻ ξ, ‖G n ξ‖ₑ ∂μ) atTop ≤
        ENNReal.ofReal
          (suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2) := by
    exact (Filter.liminf_le_liminf (Eventually.of_forall hlinBound)).trans_eq
      hboundTendsto.liminf_eq
  have hfatou := lintegral_enorm_le_liminf_of_tendsto hGf
    (fun n => (hGint n).aestronglyMeasurable.aemeasurable.enorm)
  have hlinTarget :
      (∫⁻ ξ, ‖f ξ‖ₑ ∂μ) ≤
        ENNReal.ofReal
          (suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2) :=
    hfatou.trans hliminfUpper
  have hliminfNeTop :
      liminf (fun n => ∫⁻ ξ, ‖G n ξ‖ₑ ∂μ) atTop ≠ ⊤ := by
    apply ne_of_lt
    exact lt_of_le_of_lt hliminfUpper ENNReal.ofReal_lt_top
  have hfint : Integrable f μ := integrable_of_tendsto hGf
    (fun n => (hGint n).aestronglyMeasurable) hliminfNeTop
  have hsetTarget :
      (∫ ξ, f ξ ∂μ) = suzukiDF6D5B3FENormalizedNegativeWeightEnergy v := by
    dsimp only [μ, band, f]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le
        (neg_le_self suzukiDF6D5B3FENegativeWeightThreshold_pos.le)]
    rfl
  apply (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg suzukiDF6D4DF0NegativeWeightLoss_nonneg (sq_nonneg ‖v‖))).mp
  calc
    ENNReal.ofReal (suzukiDF6D5B3FENormalizedNegativeWeightEnergy v) =
        ENNReal.ofReal (∫ ξ, f ξ ∂μ) := by rw [hsetTarget]
    _ = ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂μ :=
      ofReal_integral_eq_lintegral_ofReal hfint hfnonneg
    _ = ∫⁻ ξ, ‖f ξ‖ₑ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hfnonneg] with ξ hξ
      rw [← ofReal_norm, Real.norm_of_nonneg hξ]
    _ ≤ ENNReal.ofReal
        (suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2) := hlinTarget

/-- The Fatou closure estimate applies uniformly on both ambient parity tails.
This is the correctly normalized negative-weight statement supplied by DF0;
it deliberately does not assert a bound for the broader raw graph loss. -/
theorem suzukiDF6D5B3FEAmbientNormalizedNegativeWeightLoss_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (v : SuzukiL2)
    (hv : v ∈ suzukiDF6D5B3TEvenAmbientFarSubspace ∨
      v ∈ suzukiDF6D5B3TOddAmbientFarSubspace) :
    suzukiDF6D5B3FENormalizedNegativeWeightEnergy v ≤
      suzukiDF6D4DF0NegativeWeightLoss * ‖v‖ ^ 2 := by
  apply cutoff44HighExponentialClosure_normalizedNegativeWeightLoss hsource
  rcases hv with heven | hodd
  · exact suzukiDF6D5B3TEvenAmbientFarSubspace_le_cutoff44HighClosure heven
  · exact suzukiDF6D5B3TOddAmbientFarSubspace_le_cutoff44HighClosure hodd

/-- The checked Fatou theorem fills the corrected shared B3F-E negative-loss
receiver. -/
theorem suzukiDF6D5B3FEAmbientNegativeWeightLoss_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiDF6D5B3FEAmbientNegativeWeightLoss := by
  intro v hv
  exact suzukiDF6D5B3FEAmbientNormalizedNegativeWeightLoss_of_source
    hsource v hv

/-- The exact leakage theorem and corrected normalized-loss theorem assemble
the two sharp B3F-E parity bounds on the canonical B2S receivers. -/
theorem suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source
    (hsource : SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) :
    SuzukiDF6D5B3FEEvenSharpEnergyLower
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) ∧
      SuzukiDF6D5B3FEOddSharpEnergyLower
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  exact suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_ambientCardinalSine
    hsource
    (suzukiDF6D5B3FEAmbientFourierLeakage_of_source hsource)
    (suzukiDF6D5B3FEAmbientNegativeWeightLoss_of_source hsource)

end
end RiemannHypothesisProject.Experiments.M100
