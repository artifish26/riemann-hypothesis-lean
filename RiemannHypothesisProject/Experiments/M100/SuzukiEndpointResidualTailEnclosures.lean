import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFineConstantEnclosures

/-!
# Shared complete residual-tail enclosures for M100-DF6D4

FT3 and DF1 use the same leading inverse-square tail after the explicit
residual prefix ends at mode `600`.  This module proves that quantity from the
Basel sum and encloses it with exact rational interval arithmetic.  Later
even/odd structured-tail modules build on this common analytic source rather
than importing the Arb decimal.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

open RationalInterval

/-! ## Uniform inverse-power tails -/

/-- Complete inverse-`p` tail beginning at mode `N + 1`, in the real-power
form used by the sum-integral comparison theorem. -/
def suzukiDF6D4InversePowerTail (p N : Nat) : Real :=
  ∑' j : Nat, (((N + 1 + j : Nat) : Real) ^ (-(p : Real)))

theorem suzukiDF6D4InversePowerTail_eq_tsum_one_div (p N : Nat) :
    suzukiDF6D4InversePowerTail p N =
      ∑' j : Nat, 1 / (((N + 1 + j : Nat) : Real) ^ p) := by
  unfold suzukiDF6D4InversePowerTail
  congr 1
  funext j
  have hbase : 0 ≤ (((N + 1 + j : Nat) : Real)) := by positivity
  rw [Real.rpow_neg hbase, Real.rpow_natCast]
  simp only [one_div]

/-- Integral-test bound for every inverse-power tail needed by the structured
and geometric DF6D4 residual estimates. -/
theorem suzukiDF6D4InversePowerTail_le
    (p N : Nat) (hp : 2 ≤ p) (hN : 1 ≤ N) :
    suzukiDF6D4InversePowerTail p N ≤
      1 / (((p - 1 : Nat) : Real) * (N : Real) ^ (p - 1)) := by
  have hNpos : (0 : Real) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hpReal : (2 : Real) ≤ p := by exact_mod_cast hp
  have hexponent : -(p : Real) < -1 := by linarith
  have hintegrable :
      MeasureTheory.IntegrableOn
        (fun x : Real => x ^ (-(p : Real))) (Set.Ioi (N : Real)) :=
    integrableOn_Ioi_rpow_of_lt hexponent hNpos
  unfold suzukiDF6D4InversePowerTail
  apply Real.tsum_le_of_sum_range_le
  · intro j
    exact Real.rpow_nonneg (by positivity) _
  · intro k
    have hmono :
        AntitoneOn (fun x : Real => x ^ (-(p : Real)))
          (Set.Icc (N : Real) ((N : Real) + k)) :=
      (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
        (neg_nonpos.mpr (Nat.cast_nonneg p))).mono
        (fun x hx => hNpos.trans_le hx.1)
    have hsum := AntitoneOn.sum_le_integral hmono
    calc
      ∑ j ∈ Finset.range k,
          (((N + 1 + j : Nat) : Real) ^ (-(p : Real))) ≤
          ∫ x in (N : Real)..(N : Real) + k, x ^ (-(p : Real)) := by
            simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
              add_assoc, add_comm, add_left_comm] using hsum
      _ ≤ ∫ x : Real in Set.Ioi (N : Real), x ^ (-(p : Real)) := by
        rw [intervalIntegral.integral_of_le
          (le_add_of_nonneg_right (Nat.cast_nonneg k))]
        apply MeasureTheory.setIntegral_mono_set hintegrable
          _ Set.Ioc_subset_Ioi_self.eventuallyLE
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
        exact Real.rpow_nonneg (hNpos.trans hx).le _
      _ = 1 / (((p - 1 : Nat) : Real) * (N : Real) ^ (p - 1)) := by
        rw [integral_Ioi_rpow_of_lt hexponent hNpos]
        have hpOne : 1 ≤ p := by omega
        rw [show -(p : Real) + 1 = -((p - 1 : Nat) : Real) by
          rw [Nat.cast_sub hpOne]
          push_cast
          ring]
        rw [Real.rpow_neg hNpos.le, Real.rpow_natCast]
        have hpSubPos : (0 : Real) < (p - 1 : Nat) := by
          exact_mod_cast (by omega : 0 < p - 1)
        field_simp

/-- Exact rational upper interval supplied by the integral test. -/
def suzukiDF6D4InversePowerTailInterval (p N : Nat) : RationalInterval :=
  ⟨0, 1 / (((p - 1 : Nat) : Rat) * (N : Rat) ^ (p - 1))⟩

theorem suzukiDF6D4InversePowerTailInterval_contains
    (p N : Nat) (hp : 2 ≤ p) (hN : 1 ≤ N) :
    (suzukiDF6D4InversePowerTailInterval p N).Contains
      (suzukiDF6D4InversePowerTail p N) := by
  unfold RationalInterval.Contains suzukiDF6D4InversePowerTailInterval
  constructor
  · norm_num
    exact tsum_nonneg fun j => Real.rpow_nonneg (by positivity) _
  ·
    have hpOne : 1 ≤ p := by omega
    convert suzukiDF6D4InversePowerTail_le p N hp hN using 1
    norm_num [Nat.cast_sub hpOne]

/-! ## Finite Abel bounds -/

/-- A quantitative finite form of Abel summation.  It isolates the only
analytic input needed by the even oscillatory tail: a uniform bound for the
unweighted partial sums. -/
theorem suzukiDF6D4NormSumRangeSMul_le
    (f : Nat → Real) (z : Nat → Complex) (B : Real)
    (hf0 : ∀ n, 0 ≤ f n) (hfanti : Antitone f) (hB0 : 0 ≤ B)
    (hpartial : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ B) (n : Nat) :
    ‖∑ i ∈ Finset.range n, f i • z i‖ ≤ B * f 0 := by
  by_cases hn : n = 0
  · subst n
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    exact mul_nonneg hB0 (hf0 0)
  rw [Finset.sum_range_by_parts]
  calc
    ‖f (n - 1) • (∑ i ∈ Finset.range n, z i) -
        ∑ i ∈ Finset.range (n - 1),
          (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖ ≤
        ‖f (n - 1) • ∑ i ∈ Finset.range n, z i‖ +
          ‖∑ i ∈ Finset.range (n - 1),
            (f (i + 1) - f i) • ∑ j ∈ Finset.range (i + 1), z j‖ :=
      norm_sub_le _ _
    _ ≤ f (n - 1) * B +
        ∑ i ∈ Finset.range (n - 1), (f i - f (i + 1)) * B := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
        exact mul_le_mul_of_nonneg_left (hpartial n) (hf0 _)
      · refine (norm_sum_le _ _).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        have hdiff : 0 ≤ f i - f (i + 1) :=
          sub_nonneg.mpr (hfanti (Nat.le_succ i))
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonpos (sub_nonpos.mpr (hfanti (Nat.le_succ i)))]
        have hrewrite : -(f (i + 1) - f i) = f i - f (i + 1) := by ring
        rw [hrewrite]
        exact mul_le_mul_of_nonneg_left (hpartial (i + 1)) hdiff
    _ = B * f 0 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

/-- Uniform partial-sum bound for the unit-circle geometric sequence.  This
is the exact denominator appearing in the DF6D4 even-tail Dirichlet
remainder. -/
theorem suzukiDF6D4GeometricPartialSumNorm_le
    (theta : Real) (htheta : Real.sin (theta / 2) ≠ 0) (n : Nat) :
    ‖∑ j ∈ Finset.range n,
        (Complex.exp (Complex.I * theta)) ^ j‖ ≤
      1 / |Real.sin (theta / 2)| := by
  let q : Complex := Complex.exp (Complex.I * theta)
  have hdenom : ‖q - 1‖ = 2 * |Real.sin (theta / 2)| := by
    dsimp [q]
    rw [Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul]
    norm_num
  have habspos : 0 < |Real.sin (theta / 2)| := abs_pos.mpr htheta
  have hdenompos : 0 < ‖q - 1‖ := by
    rw [hdenom]
    positivity
  have hq : q ≠ 1 := sub_ne_zero.mp (norm_pos_iff.mp hdenompos)
  change ‖∑ j ∈ Finset.range n, q ^ j‖ ≤ _
  rw [geom_sum_eq hq, norm_div, hdenom]
  calc
    ‖q ^ n - 1‖ / (2 * |Real.sin (theta / 2)|) ≤
        2 / (2 * |Real.sin (theta / 2)|) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc
        ‖q ^ n - 1‖ ≤ ‖q ^ n‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [q]
    _ = 1 / |Real.sin (theta / 2)| := by
      field_simp

theorem suzukiDF6D4ExpIMulPow_re (theta : Real) (k : Nat) :
    ((Complex.exp (Complex.I * theta)) ^ k).re =
      Real.cos ((k : Real) * theta) := by
  rw [← Complex.exp_nat_mul]
  simp [Complex.exp_re]

theorem suzukiDF6D4ExpIMulPow_im (theta : Real) (k : Nat) :
    ((Complex.exp (Complex.I * theta)) ^ k).im =
      Real.sin ((k : Real) * theta) := by
  rw [← Complex.exp_nat_mul]
  simp [Complex.exp_im]

/-- Finite phase-shifted inverse-square sums satisfy the sharp Dirichlet
remainder bound used after an explicit cutoff. -/
theorem suzukiDF6D4FiniteOscillatoryInverseSquareTailNorm_le
    (theta : Real) (htheta : Real.sin (theta / 2) ≠ 0) (N n : Nat) :
    ‖∑ j ∈ Finset.range n,
        (1 / (((N + 1 + j : Nat) : Real) ^ 2)) •
          (Complex.exp (Complex.I * theta)) ^ (N + 1 + j)‖ ≤
      (1 / |Real.sin (theta / 2)|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
  let f : Nat → Real := fun j =>
    1 / (((N + 1 + j : Nat) : Real) ^ 2)
  let q : Complex := Complex.exp (Complex.I * theta)
  have hf0 : ∀ j, 0 ≤ f j := by
    intro j
    dsimp [f]
    positivity
  have hfanti : Antitone f := by
    intro a b hab
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr
  have hpartial : ∀ m, ‖∑ j ∈ Finset.range m, q ^ (N + 1 + j)‖ ≤
      1 / |Real.sin (theta / 2)| := by
    intro m
    calc
      ‖∑ j ∈ Finset.range m, q ^ (N + 1 + j)‖ =
          ‖q ^ (N + 1) * ∑ j ∈ Finset.range m, q ^ j‖ := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [← pow_add]
      _ = ‖∑ j ∈ Finset.range m, q ^ j‖ := by
        rw [norm_mul, norm_pow]
        simp [q]
      _ ≤ 1 / |Real.sin (theta / 2)| := by
        simpa [q] using
          suzukiDF6D4GeometricPartialSumNorm_le theta htheta m
  simpa only [f, q] using
    suzukiDF6D4NormSumRangeSMul_le f
      (fun j => q ^ (N + 1 + j)) (1 / |Real.sin (theta / 2)|)
      hf0 hfanti (by positivity) hpartial n

/-- Absolute summability needed to pass the finite Abel estimate to the
complete oscillatory inverse-square tail. -/
theorem suzukiDF6D4OscillatoryInverseSquareTail_summable
    (theta : Real) (N : Nat) :
    Summable (fun j : Nat =>
      (1 / (((N + 1 + j : Nat) : Real) ^ 2)) •
        (Complex.exp (Complex.I * theta)) ^ (N + 1 + j)) := by
  have hbase : Summable (fun k : Nat => 1 / ((k : Real) ^ 2)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun j : Nat =>
      1 / (((N + 1 + j : Nat) : Real) ^ 2)) := by
    have h := (summable_nat_add_iff
      (f := fun k : Nat => 1 / ((k : Real) ^ 2)) (N + 1)).2 hbase
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  refine hshift.of_norm_bounded fun j => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_pow]
  simp

/-- Sharp complete Dirichlet remainder for the phase-shifted oscillatory
inverse-square tail. -/
theorem suzukiDF6D4OscillatoryInverseSquareTailNorm_le
    (theta : Real) (htheta : Real.sin (theta / 2) ≠ 0) (N : Nat) :
    ‖∑' j : Nat,
        (1 / (((N + 1 + j : Nat) : Real) ^ 2)) •
          (Complex.exp (Complex.I * theta)) ^ (N + 1 + j)‖ ≤
      (1 / |Real.sin (theta / 2)|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
  have hsummable :=
    suzukiDF6D4OscillatoryInverseSquareTail_summable theta N
  apply le_of_tendsto hsummable.hasSum.tendsto_sum_nat.norm
  exact Filter.Eventually.of_forall fun n =>
    suzukiDF6D4FiniteOscillatoryInverseSquareTailNorm_le
      theta htheta N n

/-- Sine-coordinate form of the complete oscillatory tail estimate. -/
theorem suzukiDF6D4SineInverseSquareTailAbs_le
    (theta : Real) (htheta : Real.sin (theta / 2) ≠ 0) (N : Nat) :
    |∑' j : Nat,
        Real.sin (((N + 1 + j : Nat) : Real) * theta) /
          (((N + 1 + j : Nat) : Real) ^ 2)| ≤
      (1 / |Real.sin (theta / 2)|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
  let g : Nat → Complex := fun j =>
    (1 / (((N + 1 + j : Nat) : Real) ^ 2)) •
      (Complex.exp (Complex.I * theta)) ^ (N + 1 + j)
  have hg : Summable g := by
    simpa only [g] using
      suzukiDF6D4OscillatoryInverseSquareTail_summable theta N
  have him : (∑' j : Nat, g j).im =
      ∑' j : Nat,
        Real.sin (((N + 1 + j : Nat) : Real) * theta) /
          (((N + 1 + j : Nat) : Real) ^ 2) := by
    rw [Complex.im_tsum hg]
    apply tsum_congr
    intro j
    simp only [g, Complex.smul_im, suzukiDF6D4ExpIMulPow_im, smul_eq_mul]
    ring
  calc
    |∑' j : Nat,
        Real.sin (((N + 1 + j : Nat) : Real) * theta) /
          (((N + 1 + j : Nat) : Real) ^ 2)| = |(∑' j : Nat, g j).im| := by
      rw [him]
    _ ≤ ‖∑' j : Nat, g j‖ := Complex.abs_im_le_norm _
    _ ≤ (1 / |Real.sin (theta / 2)|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
      simpa only [g] using
        suzukiDF6D4OscillatoryInverseSquareTailNorm_le theta htheta N

/-- Cosine-coordinate form of the complete oscillatory tail estimate. -/
theorem suzukiDF6D4CosineInverseSquareTailAbs_le
    (theta : Real) (htheta : Real.sin (theta / 2) ≠ 0) (N : Nat) :
    |∑' j : Nat,
        Real.cos (((N + 1 + j : Nat) : Real) * theta) /
          (((N + 1 + j : Nat) : Real) ^ 2)| ≤
      (1 / |Real.sin (theta / 2)|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
  let g : Nat → Complex := fun j =>
    (1 / (((N + 1 + j : Nat) : Real) ^ 2)) •
      (Complex.exp (Complex.I * theta)) ^ (N + 1 + j)
  have hg : Summable g := by
    simpa only [g] using
      suzukiDF6D4OscillatoryInverseSquareTail_summable theta N
  have hre : (∑' j : Nat, g j).re =
      ∑' j : Nat,
        Real.cos (((N + 1 + j : Nat) : Real) * theta) /
          (((N + 1 + j : Nat) : Real) ^ 2) := by
    rw [Complex.re_tsum hg]
    apply tsum_congr
    intro j
    simp only [g, Complex.smul_re, suzukiDF6D4ExpIMulPow_re, smul_eq_mul]
    ring
  calc
    |∑' j : Nat,
        Real.cos (((N + 1 + j : Nat) : Real) * theta) /
          (((N + 1 + j : Nat) : Real) ^ 2)| = |(∑' j : Nat, g j).re| := by
      rw [hre]
    _ ≤ ‖∑' j : Nat, g j‖ := Complex.abs_re_le_norm _
    _ ≤ (1 / |Real.sin (theta / 2)|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
      simpa only [g] using
        suzukiDF6D4OscillatoryInverseSquareTailNorm_le theta htheta N

/-- The order-`n^-11` coordinate remainder has the exact squared-tail bound
used by both the FT3 even and DF1 odd certificates. -/
theorem suzukiDF6D4FrozenTwentySecondPowerTail_le :
    suzukiDF6D4InversePowerTail 22 600 ≤
      1 / (21 * (600 : Real) ^ 21) := by
  simpa using suzukiDF6D4InversePowerTail_le 22 600 (by norm_num) (by norm_num)

theorem suzukiDF6D4FrozenTwentySecondPowerTailInterval_audit :
    (suzukiDF6D4InversePowerTailInterval 22 600).upper =
      (1 / (21 * 600 ^ 21) : Rat) := by
  native_decide

/-- Complete inverse-square tail beginning at mode `N + 1`. -/
def suzukiDF6D4InverseSquareTail (N : Nat) : Real :=
  ∑' j : Nat, 1 / (((N + 1 + j : Nat) : Real) ^ 2)

theorem suzukiDF6D4InverseSquareTail_eq_inversePowerTail (N : Nat) :
    suzukiDF6D4InverseSquareTail N = suzukiDF6D4InversePowerTail 2 N := by
  rw [suzukiDF6D4InversePowerTail_eq_tsum_one_div]
  rfl

/-- The sine-square tail is centered at half of the ordinary inverse-square
tail, with the sharp doubled-angle Dirichlet remainder. -/
theorem suzukiDF6D4SineSquareInverseSquareTailCenteredAbs_le
    (theta : Real) (htheta : Real.sin theta ≠ 0) (N : Nat) :
    |(∑' j : Nat,
        Real.sin (((N + 1 + j : Nat) : Real) * theta) ^ 2 /
          (((N + 1 + j : Nat) : Real) ^ 2)) -
        (1 / 2) * suzukiDF6D4InverseSquareTail N| ≤
      (1 / 2) * ((1 / |Real.sin theta|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2))) := by
  let inv : Nat → Real := fun j =>
    1 / (((N + 1 + j : Nat) : Real) ^ 2)
  let cosTerm : Nat → Real := fun j =>
    Real.cos (((N + 1 + j : Nat) : Real) * (2 * theta)) /
      (((N + 1 + j : Nat) : Real) ^ 2)
  let sinSqTerm : Nat → Real := fun j =>
    Real.sin (((N + 1 + j : Nat) : Real) * theta) ^ 2 /
      (((N + 1 + j : Nat) : Real) ^ 2)
  have hinv : Summable inv := by
    have hbase : Summable (fun k : Nat => 1 / ((k : Real) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have h := (summable_nat_add_iff
      (f := fun k : Nat => 1 / ((k : Real) ^ 2)) (N + 1)).2 hbase
    simpa only [inv, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  let g : Nat → Complex := fun j =>
    (1 / (((N + 1 + j : Nat) : Real) ^ 2)) •
      (Complex.exp (Complex.I * ((2 * theta : Real) : Complex))) ^
        (N + 1 + j)
  have hg : Summable g := by
    simpa only [g] using
      suzukiDF6D4OscillatoryInverseSquareTail_summable (2 * theta) N
  have hgre : Summable (fun j => (g j).re) := by
    rcases hg with ⟨a, ha⟩
    exact ⟨a.re, Complex.hasSum_re ha⟩
  have hcos : Summable cosTerm := by
    refine hgre.congr fun j => ?_
    simp only [g, cosTerm, Complex.smul_re,
      suzukiDF6D4ExpIMulPow_re, smul_eq_mul]
    ring
  have hidentity : (∑' j : Nat, sinSqTerm j) =
      (1 / 2) * (suzukiDF6D4InverseSquareTail N -
        ∑' j : Nat, cosTerm j) := by
    calc
      (∑' j : Nat, sinSqTerm j) =
          ∑' j : Nat, (1 / 2) * (inv j - cosTerm j) := by
        apply tsum_congr
        intro j
        simp only [sinSqTerm, inv, cosTerm]
        rw [Real.sin_sq_eq_half_sub]
        ring
      _ = (1 / 2) * ((∑' j : Nat, inv j) -
          ∑' j : Nat, cosTerm j) := by
        rw [tsum_mul_left, hinv.tsum_sub hcos]
      _ = (1 / 2) * (suzukiDF6D4InverseSquareTail N -
          ∑' j : Nat, cosTerm j) := by
        rfl
  have hangle : (2 * theta) / 2 = theta := by ring
  have hcosBound : |∑' j : Nat, cosTerm j| ≤
      (1 / |Real.sin theta|) *
        (1 / (((N + 1 : Nat) : Real) ^ 2)) := by
    simpa only [cosTerm, hangle] using
      suzukiDF6D4CosineInverseSquareTailAbs_le
        (2 * theta) (by simpa only [hangle] using htheta) N
  change |(∑' j : Nat, sinSqTerm j) -
    (1 / 2) * suzukiDF6D4InverseSquareTail N| ≤ _
  rw [hidentity]
  have hcenter :
      (1 / 2) * (suzukiDF6D4InverseSquareTail N -
          ∑' j : Nat, cosTerm j) -
        (1 / 2) * suzukiDF6D4InverseSquareTail N =
      -(1 / 2) * (∑' j : Nat, cosTerm j) := by ring
  rw [hcenter, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left hcosBound (by norm_num)

/-- The complete tail is exactly the Basel value minus the frozen prefix. -/
theorem suzukiDF6D4InverseSquareTail_eq (N : Nat) :
    suzukiDF6D4InverseSquareTail N =
      Real.pi ^ 2 / 6 -
        ∑ n ∈ Finset.range (N + 1), 1 / ((n : Real) ^ 2) := by
  have hsplit := hasSum_zeta_two.summable.sum_add_tsum_nat_add (N + 1)
  have htail :
      (∑ n ∈ Finset.range (N + 1), 1 / ((n : Real) ^ 2)) +
          suzukiDF6D4InverseSquareTail N =
        ∑' n : Nat, 1 / ((n : Real) ^ 2) := by
    simpa only [suzukiDF6D4InverseSquareTail, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hsplit
  rw [hasSum_zeta_two.tsum_eq] at htail
  linarith

/-- Exact rational version of the finite Basel prefix. -/
def suzukiDF6D4InverseSquarePrefixRat (N : Nat) : Rat :=
  ∑ n ∈ Finset.range (N + 1), 1 / ((n : Rat) ^ 2)

theorem suzukiDF6D4InverseSquarePrefixRat_cast (N : Nat) :
    (suzukiDF6D4InverseSquarePrefixRat N : Real) =
      ∑ n ∈ Finset.range (N + 1), 1 / ((n : Real) ^ 2) := by
  unfold suzukiDF6D4InverseSquarePrefixRat
  push_cast
  rfl

def suzukiDF6D4PiSquareOverSixInterval : RationalInterval :=
  RationalInterval.scale (1 / 6)
    (suzukiDF6D4PiInterval.powNonneg 2)

theorem suzukiDF6D4PiSquareOverSixInterval_contains :
    suzukiDF6D4PiSquareOverSixInterval.Contains (Real.pi ^ 2 / 6) := by
  have hsq := RationalInterval.contains_powNonneg 2
    (by norm_num [suzukiDF6D4PiInterval])
    suzukiDF6D4PiInterval_contains
  have hscale := RationalInterval.contains_scale (1 / 6) hsq
  unfold suzukiDF6D4PiSquareOverSixInterval
  convert hscale using 1
  norm_num
  ring

def suzukiDF6D4InverseSquareTailInterval (N : Nat) : RationalInterval :=
  suzukiDF6D4PiSquareOverSixInterval.sub
    (RationalInterval.point (suzukiDF6D4InverseSquarePrefixRat N))

theorem suzukiDF6D4InverseSquareTailInterval_contains (N : Nat) :
    (suzukiDF6D4InverseSquareTailInterval N).Contains
      (suzukiDF6D4InverseSquareTail N) := by
  have hprefix := RationalInterval.contains_point
    (suzukiDF6D4InverseSquarePrefixRat N)
  have hsub := RationalInterval.contains_sub
    suzukiDF6D4PiSquareOverSixInterval_contains hprefix
  rw [suzukiDF6D4InverseSquareTail_eq]
  unfold suzukiDF6D4InverseSquareTailInterval
  rw [← suzukiDF6D4InverseSquarePrefixRat_cast]
  exact hsub

/-- Frozen common FT3/DF1 leading-tail enclosure at residual cutoff `600`. -/
def suzukiDF6D4FrozenInverseSquareTailInterval : RationalInterval :=
  RationalInterval.roundOut 1000000000000000000
    (suzukiDF6D4InverseSquareTailInterval 600)

theorem suzukiDF6D4FrozenInverseSquareTailInterval_contains :
    suzukiDF6D4FrozenInverseSquareTailInterval.Contains
      (suzukiDF6D4InverseSquareTail 600) := by
  exact RationalInterval.contains_roundOut (by norm_num)
    (suzukiDF6D4InverseSquareTailInterval_contains 600)

/-- Exact audit against the independently reproduced 192-bit FT3/DF1 range. -/
theorem suzukiDF6D4FrozenInverseSquareTailInterval_audit :
    (1665278549382287 / 1000000000000000000 : Rat) ≤
        suzukiDF6D4FrozenInverseSquareTailInterval.lower ∧
      suzukiDF6D4FrozenInverseSquareTailInterval.upper ≤
        (1665278549382288 / 1000000000000000000 : Rat) := by
  native_decide

end

end RiemannHypothesisProject.Experiments.M100
