import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisCleanup
import RiemannHypothesisProject.RiemannVonMangoldt.ZModTwoHalfTail

/-!
# Floor-parity kernel estimates

This module contains the measurable floor-parity switch, concrete Abel-kernel integrability and tail estimates, and finite-integral comparison with eta partial sums.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/-- The explicit odd-floor switch in the `ZMod 2` Abel kernel is measurable. -/
theorem measurable_zmodTwoFloorParitySwitch :
    Measurable fun t : Real =>
      if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1 := by
  have hfloor : Measurable fun t : Real => ⌊t⌋₊ :=
    Nat.measurable_floor
  have hmod : Measurable fun t : Real => ⌊t⌋₊ % 2 :=
    (measurable_of_countable fun n : Nat => n % 2).comp hfloor
  refine Measurable.ite ?_ measurable_const measurable_const
  exact MeasurableSet.preimage (measurableSet_singleton 0) hmod

/-- The absolute value of the concrete odd-floor Abel kernel has the expected
`x * t^(-x-1)` majorant on the positive ray. -/
theorem zmodTwoFloorParityKernel_norm_le
    {x t : Real} (hx : 0 < x) (ht : 0 < t) :
    ‖(-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
        (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ ≤
      x * t ^ (-x - 1) := by
  have hnonneg : 0 ≤ x * t ^ (-x - 1) :=
    mul_nonneg hx.le (Real.rpow_nonneg ht.le _)
  have hpow_norm :
      ‖(t : Complex) ^ (-(x : Complex) - 1)‖ =
        t ^ (-x - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp
  have hneg_norm : ‖-(x : Complex)‖ = x := by
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  by_cases hparity : ⌊t⌋₊ % 2 = 0
  · simpa [hparity] using hnonneg
  · calc
      ‖(-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ =
          x * t ^ (-x - 1) := by
            rw [if_neg hparity, norm_mul, norm_mul, hneg_norm,
              hpow_norm, norm_neg, norm_one]
            ring
      _ ≤ x * t ^ (-x - 1) := le_rfl

/-- The concrete odd-floor Abel kernel is integrable on every positive tail. -/
theorem integrableOn_zmodTwoFloorParityKernel
    {x T : Real} (hx : 0 < x) (hT : 0 < T) :
    IntegrableOn
      (fun t : Real =>
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
      (Set.Ioi T) := by
  have hmajor :
      IntegrableOn (fun t : Real => x * t ^ (-x - 1)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (a := -x - 1) (by linarith) hT).const_mul x
  rw [IntegrableOn] at hmajor ⊢
  refine hmajor.mono' ?_ ?_
  · have hpow_cont :
        ContinuousOn
          (fun t : Real => (t : Complex) ^ (-(x : Complex) - 1))
          (Set.Ioi T) := by
      intro t ht
      exact
        (Complex.continuousAt_ofReal_cpow_const t
          (-(x : Complex) - 1)
          (Or.inr (ne_of_gt (hT.trans ht)))).continuousWithinAt
    have hpow_aesm :
        AEStronglyMeasurable
          (fun t : Real => (t : Complex) ^ (-(x : Complex) - 1))
          (volume.restrict (Set.Ioi T)) :=
      hpow_cont.aestronglyMeasurable measurableSet_Ioi
    exact
      ((aestronglyMeasurable_const.mul hpow_aesm).mul
        measurable_zmodTwoFloorParitySwitch.aestronglyMeasurable.restrict)
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact zmodTwoFloorParityKernel_norm_le hx (hT.trans ht)

/--
The explicit odd-floor Abel kernel has a sharp elementary tail bound.

This is the concrete analytic control needed to pass between finite odd-floor
kernel pieces and the regularized half-tail comparison.
-/
theorem zmodTwoFloorParityKernel_tail_norm_le
    {x T : Real} (hx : 0 < x) (hT : 1 ≤ T) :
    ‖∫ t in Set.Ioi T,
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ ≤
      T ^ (-x) := by
  have hT_pos : 0 < T := zero_lt_one.trans_le hT
  have hkernel_int :
      IntegrableOn
        (fun t : Real =>
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
        (Set.Ioi T) :=
    integrableOn_zmodTwoFloorParityKernel hx hT_pos
  have hnorm_int :
      IntegrableOn
        (fun t : Real =>
          ‖(-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖)
        (Set.Ioi T) :=
    hkernel_int.norm
  have hmajor_int :
      IntegrableOn (fun t : Real => x * t ^ (-x - 1)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (a := -x - 1) (by linarith) hT_pos).const_mul x
  have hmajor_eval :
      (∫ t in Set.Ioi T, x * t ^ (-x - 1)) = T ^ (-x) := by
    rw [integral_const_mul,
      integral_Ioi_rpow_of_lt (a := -x - 1) (by linarith) hT_pos]
    rw [show -x - 1 + 1 = -x by ring]
    field_simp [show (-x) ≠ 0 by linarith]
  calc
    ‖∫ t in Set.Ioi T,
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ ≤
        ∫ t in Set.Ioi T,
          ‖(-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ := by
          exact norm_integral_le_integral_norm _
    _ ≤ ∫ t in Set.Ioi T, x * t ^ (-x - 1) := by
          refine setIntegral_mono_on hnorm_int hmajor_int measurableSet_Ioi ?_
          intro t ht
          exact zmodTwoFloorParityKernel_norm_le hx (hT_pos.trans ht)
    _ = T ^ (-x) := hmajor_eval

/--
On a positive finite interval, the positive `x * t^(-x-1)` cpow kernel
integrates to the endpoint drop of `t^(-x)`.
-/
theorem intervalIntegral_posCpowKernel_eq_sub
    {x a b : Real} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in a..b, (x : Complex) * (t : Complex) ^ (-(x : Complex) - 1)) =
      (a : Complex) ^ (-(x : Complex)) -
        (b : Complex) ^ (-(x : Complex)) := by
  have hxC_ne : (x : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hr_ne : (-(x : Complex) - 1 : Complex) ≠ -1 := by
    intro h
    have hneg : -(x : Complex) = 0 := by
      simpa [sub_eq_add_neg, add_assoc] using
        congrArg (fun z : Complex => z + 1) h
    exact (neg_ne_zero.mpr hxC_ne) hneg
  have hzero_not : (0 : Real) ∉ Set.uIcc a b :=
    Set.notMem_uIcc_of_lt ha hb
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cpow (a := a) (b := b)
    (r := (-(x : Complex) - 1))
    (Or.inr ⟨hr_ne, hzero_not⟩)]
  rw [show (-(x : Complex) - 1 + 1 : Complex) = -(x : Complex) by ring]
  field_simp [hxC_ne, neg_ne_zero.mpr hxC_ne]
  ring

/--
Each odd floor-parity slab computes exactly one two-term eta block.

This turns the explicit `ZMod 2` Abel kernel from a global bounded tail into
checked finite pieces that match the regularized half-tail normalization.
-/
theorem zmodTwoFloorParityKernel_oddIntervalIntegral_eq_etaBlock
    {x : Real} (hx : 0 < x) (m : Nat) :
    (∫ t in (((2 * m + 1 : Nat) : Real))..
        (((2 * m + 2 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
      dirichletEtaComplexSeriesTerm x (2 * m) +
        dirichletEtaComplexSeriesTerm x (2 * m + 1) := by
  let a : Real := ((2 * m + 1 : Nat) : Real)
  let b : Real := ((2 * m + 2 : Nat) : Real)
  have ha_pos : 0 < a := by
    positivity
  have hb_pos : 0 < b := by
    positivity
  have hab : a < b := by
    dsimp [a, b]
    norm_num
  have hcongr :
      (∫ t in a..b,
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
        ∫ t in a..b, (x : Complex) *
          (t : Complex) ^ (-(x : Complex) - 1) := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro t ht
    have htIoo : t ∈ Set.Ioo a b := by
      simpa [Set.uIoo_of_le hab.le] using ht
    have hfloor : ⌊t⌋₊ = 2 * m + 1 := by
      refine Nat.floor_eq_on_Ico (R := Real) (2 * m + 1) t ?_
      constructor
      · simpa [a] using htIoo.1.le
      · have hb_eq : b = ((2 * m + 1 : Nat) + 1 : Nat) := by
          dsimp [b]
        simpa [hb_eq] using htIoo.2
    have hodd : ⌊t⌋₊ % 2 ≠ 0 := by
      rw [hfloor]
      omega
    simp [hodd]
  have hA_cpow :
      (a : Complex) ^ (-(x : Complex)) =
        ((((2 * m : Nat) : Real) + 1) ^ (-x) : Real) := by
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    have ha_nonneg : 0 ≤ a := ha_pos.le
    rw [← Complex.ofReal_cpow ha_nonneg]
    congr 1
    simp [a, Nat.cast_add, Nat.cast_mul]
  have hB_base :
      b = (((2 * m + 1 : Nat) : Real) + 1) := by
    simp [b, Nat.cast_add, Nat.cast_mul]
    ring
  have hB_cpow :
      (b : Complex) ^ (-(x : Complex)) =
        ((((2 * m + 1 : Nat) : Real) + 1) ^ (-x) : Real) := by
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    have hb_nonneg : 0 ≤ b := hb_pos.le
    rw [← Complex.ofReal_cpow hb_nonneg]
    rw [hB_base]
  have hpow_even : (-1 : Real) ^ (2 * m) = 1 := by
    rw [Even.neg_one_pow]
    exact even_two_mul m
  have hpow_odd : (-1 : Real) ^ (2 * m + 1) = -1 := by
    rw [Odd.neg_one_pow]
    exact Nat.not_even_iff_odd.mp (Nat.not_even_two_mul_add_one m)
  calc
    (∫ t in (((2 * m + 1 : Nat) : Real))..
        (((2 * m + 2 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
        ∫ t in a..b, (x : Complex) *
          (t : Complex) ^ (-(x : Complex) - 1) := by
          simpa [a, b] using hcongr
    _ = (a : Complex) ^ (-(x : Complex)) -
          (b : Complex) ^ (-(x : Complex)) :=
          intervalIntegral_posCpowKernel_eq_sub hx ha_pos hb_pos
    _ = dirichletEtaComplexSeriesTerm x (2 * m) +
          dirichletEtaComplexSeriesTerm x (2 * m + 1) := by
          rw [hA_cpow, hB_cpow]
          simp [dirichletEtaComplexSeriesTerm, dirichletEtaSeriesTerm,
            hpow_even, hpow_odd, Nat.cast_add, Nat.cast_mul]
          ring

/-- The concrete floor-parity kernel is interval-integrable on positive finite intervals. -/
theorem intervalIntegrable_zmodTwoFloorParityKernel
    {x a b : Real} (hx : 0 < x) (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable
      (fun t : Real =>
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
      volume a b := by
  rcases le_total a b with hab | hba
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
    exact
      (integrableOn_zmodTwoFloorParityKernel hx ha).mono_set
        Set.Ioo_subset_Ioi_self
  · have hba_int :
        IntervalIntegrable
          (fun t : Real =>
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
          volume b a := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hba]
      exact
        (integrableOn_zmodTwoFloorParityKernel hx hb).mono_set
          Set.Ioo_subset_Ioi_self
    exact hba_int.symm

/-- The even floor-parity slabs contribute zero to the concrete kernel. -/
theorem zmodTwoFloorParityKernel_evenIntervalIntegral_eq_zero
    (x : Real) (m : Nat) :
    (∫ t in (((2 * m + 2 : Nat) : Real))..
        (((2 * m + 3 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) = 0 := by
  let a : Real := ((2 * m + 2 : Nat) : Real)
  let b : Real := ((2 * m + 3 : Nat) : Real)
  have hab : a < b := by
    dsimp [a, b]
    norm_num
  have hzero :
      (∫ t in a..b,
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
        ∫ _t in a..b, (0 : Complex) := by
    refine intervalIntegral.integral_congr_uIoo ?_
    intro t ht
    have htIoo : t ∈ Set.Ioo a b := by
      simpa [Set.uIoo_of_le hab.le] using ht
    have hfloor : ⌊t⌋₊ = 2 * m + 2 := by
      refine Nat.floor_eq_on_Ico (R := Real) (2 * m + 2) t ?_
      constructor
      · simpa [a] using htIoo.1.le
      · have hb_eq : b = ((2 * m + 2 : Nat) + 1 : Nat) := by
          dsimp [b]
        simpa [hb_eq] using htIoo.2
    have heven : ⌊t⌋₊ % 2 = 0 := by
      rw [hfloor]
      omega
    simp [heven]
  calc
    (∫ t in (((2 * m + 2 : Nat) : Real))..
        (((2 * m + 3 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
        ∫ _t in a..b, (0 : Complex) := by
          simpa [a, b] using hzero
    _ = 0 := by
          simp

/--
Over the full two-unit block from one odd endpoint to the next, the
floor-parity kernel contributes exactly the corresponding eta block.
-/
theorem zmodTwoFloorParityKernel_blockIntervalIntegral_eq_etaBlock
    {x : Real} (hx : 0 < x) (m : Nat) :
    (∫ t in (((2 * m + 1 : Nat) : Real))..
        (((2 * m + 3 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
      dirichletEtaComplexSeriesTerm x (2 * m) +
        dirichletEtaComplexSeriesTerm x (2 * m + 1) := by
  let a : Real := ((2 * m + 1 : Nat) : Real)
  let b : Real := ((2 * m + 2 : Nat) : Real)
  let c : Real := ((2 * m + 3 : Nat) : Real)
  have ha_pos : 0 < a := by
    positivity
  have hb_pos : 0 < b := by
    positivity
  have hc_pos : 0 < c := by
    positivity
  have hab_int :
      IntervalIntegrable
        (fun t : Real =>
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
        volume a b :=
    intervalIntegrable_zmodTwoFloorParityKernel hx ha_pos hb_pos
  have hbc_int :
      IntervalIntegrable
        (fun t : Real =>
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
        volume b c :=
    intervalIntegrable_zmodTwoFloorParityKernel hx hb_pos hc_pos
  calc
    (∫ t in (((2 * m + 1 : Nat) : Real))..
        (((2 * m + 3 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
        (∫ t in a..b,
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) +
          ∫ t in b..c,
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
          simpa [a, b, c] using
            (intervalIntegral.integral_add_adjacent_intervals
              hab_int hbc_int).symm
    _ = dirichletEtaComplexSeriesTerm x (2 * m) +
          dirichletEtaComplexSeriesTerm x (2 * m + 1) + 0 := by
          rw [zmodTwoFloorParityKernel_oddIntervalIntegral_eq_etaBlock hx m]
          rw [zmodTwoFloorParityKernel_evenIntervalIntegral_eq_zero x m]
    _ = dirichletEtaComplexSeriesTerm x (2 * m) +
          dirichletEtaComplexSeriesTerm x (2 * m + 1) := by
          simp

/--
Finite cutoffs of the concrete floor-parity kernel are exactly the even-length
eta partial sums.
-/
theorem zmodTwoFloorParityKernel_finiteIntegral_eq_etaPartialSum
    {x : Real} (hx : 0 < x) (M : Nat) :
    (∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
      (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x) := by
  induction M with
  | zero =>
      simp
  | succ M ih =>
      have hend_pos : 0 < (((2 * M + 1 : Nat) : Real)) := by
        positivity
      have hsucc_pos : 0 < (((2 * M + 3 : Nat) : Real)) := by
        positivity
      have hmain_int :
          IntervalIntegrable
            (fun t : Real =>
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
            volume (1 : Real) (((2 * M + 1 : Nat) : Real)) :=
        intervalIntegrable_zmodTwoFloorParityKernel hx zero_lt_one hend_pos
      have hblock_int :
          IntervalIntegrable
            (fun t : Real =>
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
            volume (((2 * M + 1 : Nat) : Real))
              (((2 * M + 3 : Nat) : Real)) :=
        intervalIntegrable_zmodTwoFloorParityKernel hx hend_pos hsucc_pos
      have hsucc_cast :
          ((2 * (M + 1) + 1 : Nat) : Real) =
            ((2 * M + 3 : Nat) : Real) := by
        norm_num
        ring
      have hadd :
          (∫ t in (1 : Real)..(((2 * (M + 1) + 1 : Nat) : Real)),
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
            (∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) +
            ∫ t in (((2 * M + 1 : Nat) : Real))..
                (((2 * M + 3 : Nat) : Real)),
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
        simpa [hsucc_cast] using
          (intervalIntegral.integral_add_adjacent_intervals
            hmain_int hblock_int).symm
      calc
        (∫ t in (1 : Real)..(((2 * (M + 1) + 1 : Nat) : Real)),
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) =
            (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x) +
              (dirichletEtaComplexSeriesTerm x (2 * M) +
                dirichletEtaComplexSeriesTerm x (2 * M + 1)) := by
              rw [hadd, ih,
                zmodTwoFloorParityKernel_blockIntervalIntegral_eq_etaBlock hx M]
        _ = (Finset.range (2 * (M + 1))).sum
              (dirichletEtaComplexSeriesTerm x) := by
              rw [show 2 * (M + 1) = (2 * M + 1) + 1 by omega]
              rw [Finset.sum_range_succ]
              rw [show 2 * M + 1 = 2 * M + 1 by rfl]
              rw [Finset.sum_range_succ]
              ring

/--
The regularized half-tail finite sums are exactly scaled finite integrals of
the concrete floor-parity kernel.
-/
theorem zmodTwoRegularizedHalfTail_partialSum_eq_scaled_floorParityKernelIntegral
    {x : Real} (hx : 0 < x) (M : Nat) :
    (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x) =
      (((2 : Real) ^ x : Real) : Complex) *
        ∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
  rw [zmodTwoRegularizedHalfTail_partialSum_eq_scaled_etaPartialSum]
  rw [zmodTwoFloorParityKernel_finiteIntegral_eq_etaPartialSum hx]

/--
The finite floor-parity kernel cutoffs approximate the eta boundary value with
the explicit tail bound inherited from the positive-ray kernel estimate.
-/
theorem dirichletEtaAlternatingValue_sub_floorParityKernel_finiteIntegral_norm_le
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(dirichletEtaAlternatingValue x : Complex) -
        ∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ ≤
      (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
  let T : Real := ((2 * M + 1 : Nat) : Real)
  have hT_ge : (1 : Real) ≤ T := by
    dsimp [T]
    norm_num [Nat.cast_add, Nat.cast_mul]
  have hT_pos : 0 < T := zero_lt_one.trans_le hT_ge
  have hinterval :
      IntervalIntegrable
        (fun t : Real =>
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
        volume (1 : Real) T :=
    intervalIntegrable_zmodTwoFloorParityKernel hx zero_lt_one hT_pos
  have htail :
      IntegrableOn
        (fun t : Real =>
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))
        (Set.Ioi T) :=
    integrableOn_zmodTwoFloorParityKernel hx hT_pos
  have hsplit :
      (∫ t in (1 : Real)..T,
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)) +
        ∫ t in Set.Ioi T,
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) =
        ∫ t in Set.Ioi (1 : Real),
          (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) :=
    intervalIntegral.integral_interval_add_Ioi' hinterval htail
  have herror :
      ‖(dirichletEtaAlternatingValue x : Complex) -
          ∫ t in (1 : Real)..T,
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ ≤
        T ^ (-x) := by
    calc
      ‖(dirichletEtaAlternatingValue x : Complex) -
          ∫ t in (1 : Real)..T,
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ =
          ‖∫ t in Set.Ioi T,
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
            (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ := by
            rw [dirichletEtaAlternatingValue_eq_floorParityKernelIntegral hx]
            rw [← hsplit]
            abel_nf
      _ ≤ T ^ (-x) :=
          zmodTwoFloorParityKernel_tail_norm_le hx hT_ge
  simpa [T] using herror

/--
The even eta partial sums inherit the same explicit error estimate from the
finite floor-parity kernel cutoffs.
-/
theorem dirichletEtaAlternatingValue_sub_evenPartialSum_norm_le
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(dirichletEtaAlternatingValue x : Complex) -
        (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)‖ ≤
      (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
  rw [← zmodTwoFloorParityKernel_finiteIntegral_eq_etaPartialSum hx M]
  exact
    dirichletEtaAlternatingValue_sub_floorParityKernel_finiteIntegral_norm_le
      hx M

/--
The regularized half-tail finite sums approximate the scaled eta value with the
same concrete tail bound, multiplied by the positive scaling factor `2^x`.
-/
theorem zmodTwoRegularizedHalfTail_partialSum_error_norm_le
    {x : Real} (hx : 0 < x) (M : Nat) :
    ‖(((2 : Real) ^ x : Real) : Complex) *
        (dirichletEtaAlternatingValue x : Complex) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x)‖ ≤
      (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real) ^ (-x)) := by
  have hscale_nonneg : 0 ≤ (2 : Real) ^ x :=
    Real.rpow_nonneg (by norm_num) x
  have hscale_norm :
      ‖(((2 : Real) ^ x : Real) : Complex)‖ = (2 : Real) ^ x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]
  rw [zmodTwoRegularizedHalfTail_partialSum_eq_scaled_floorParityKernelIntegral hx M]
  calc
    ‖(((2 : Real) ^ x : Real) : Complex) *
        (dirichletEtaAlternatingValue x : Complex) -
        (((2 : Real) ^ x : Real) : Complex) *
          ∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
            (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
              (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ =
        ‖(((2 : Real) ^ x : Real) : Complex) *
          ((dirichletEtaAlternatingValue x : Complex) -
            ∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1))‖ := by
          ring_nf
    _ =
        ‖(((2 : Real) ^ x : Real) : Complex)‖ *
          ‖(dirichletEtaAlternatingValue x : Complex) -
            ∫ t in (1 : Real)..(((2 * M + 1 : Nat) : Real)),
              (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
                (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1)‖ := by
          rw [norm_mul]
    _ ≤ (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real) ^ (-x)) := by
          rw [hscale_norm]
          exact mul_le_mul_of_nonneg_left
            (dirichletEtaAlternatingValue_sub_floorParityKernel_finiteIntegral_norm_le
              hx M)
            hscale_nonneg

/--
The regularized half-tail residual is exactly the scaled even eta partial-sum
residual.
-/
theorem zmodTwoRegularizedHalfTail_tsum_sub_partialSum_eq_scaled_etaPartialSum_error
    {x : Real} (hx : 0 < x) (M : Nat) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (Finset.range M).sum (zmodTwoRegularizedHalfTailTerm x) =
      (((2 : Real) ^ x : Real) : Complex) *
        ((dirichletEtaAlternatingValue x : Complex) -
          (Finset.range (2 * M)).sum (dirichletEtaComplexSeriesTerm x)) := by
  rw [zmodTwoRegularizedHalfTail_tsum_eq_scaled_etaAlternatingValue hx,
    zmodTwoRegularizedHalfTail_partialSum_eq_scaled_etaPartialSum]
  ring
end

end ComplexCompactExhaustion

end RiemannHypothesisProject
