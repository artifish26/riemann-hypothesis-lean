import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCardinalSinePartition

/-!
# Cutoff-44 cardinal-sine leakage for M100-DF6D5B3F-E

This module packages the normalized low-frequency leakage integral and reduces
it exactly to the 89 translated cardinal-sine-square integrals.  Identifying
those integrals with the independently frozen DF0 sine-integral primitives is
kept as the next normalization bridge.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped BigOperators

/-- The normalized low-frequency half-width used by the cutoff-44 estimate. -/
def cardinalSineCutoff44Window : Real := 97 / 4

/-- Total unresolved cardinal-sine mass on the normalized low-frequency
window. -/
def cardinalSineCutoff44Leakage : Real :=
  ∫ x in -cardinalSineCutoff44Window..cardinalSineCutoff44Window,
    cardinalSineCutoff44TailDensity x

private theorem continuous_cardinalSineCutoff44Term (n : Int) :
    Continuous (fun x : Real =>
      Real.sinc (Real.pi * (x + n)) ^ 2) := by
  fun_prop

/-- The leakage integral is the window length minus the 89 resolved-mode
integrals. -/
theorem cardinalSineCutoff44Leakage_eq_sum :
    cardinalSineCutoff44Leakage =
      2 * cardinalSineCutoff44Window -
        ∑ n ∈ Finset.Icc (-44 : Int) 44,
          ∫ x in -cardinalSineCutoff44Window..cardinalSineCutoff44Window,
            Real.sinc (Real.pi * (x + n)) ^ 2 := by
  have hlow : IntervalIntegrable cardinalSineCutoff44LowDensity
      volume (-cardinalSineCutoff44Window) cardinalSineCutoff44Window := by
    apply Continuous.intervalIntegrable
    unfold cardinalSineCutoff44LowDensity
    fun_prop
  have hone : IntervalIntegrable (fun _ : Real => (1 : Real))
      volume (-cardinalSineCutoff44Window) cardinalSineCutoff44Window :=
    continuous_const.intervalIntegrable _ _
  unfold cardinalSineCutoff44Leakage cardinalSineCutoff44TailDensity
  rw [intervalIntegral.integral_sub hone hlow]
  rw [intervalIntegral.integral_const]
  unfold cardinalSineCutoff44LowDensity
  rw [intervalIntegral.integral_finsetSum]
  · norm_num [cardinalSineCutoff44Window]
  · intro n hn
    exact (continuous_cardinalSineCutoff44Term n).intervalIntegrable _ _

theorem cardinalSineCutoff44Leakage_nonneg :
    0 ≤ cardinalSineCutoff44Leakage := by
  unfold cardinalSineCutoff44Leakage
  apply intervalIntegral.integral_nonneg
  · norm_num [cardinalSineCutoff44Window]
  · intro x hx
    exact cardinalSineCutoff44TailDensity_nonneg x

/-! ## Exact primitive for one translated cardinal-sine square -/

/-- A globally defined primitive candidate for `sinc (pi*x)^2`.  The quotient
has value zero at the origin under Lean's field convention; its removable
singularity is handled explicitly in the subsequent endpoint bridge. -/
def cardinalSineSqPrimitive (x : Real) : Real :=
  (∫ t in (0 : Real)..2 * Real.pi * x, Real.sinc t) / Real.pi +
    (Real.cos (2 * Real.pi * x) - 1) / (2 * Real.pi ^ 2 * x)

/-- Away from the removable singularity, the candidate has derivative exactly
the squared normalized cardinal sine. -/
theorem hasDerivAt_cardinalSineSqPrimitive
    {x : Real} (hx : x ≠ 0) :
    HasDerivAt cardinalSineSqPrimitive
      (Real.sinc (Real.pi * x) ^ 2) x := by
  have hi : HasDerivAt
      (fun x : Real => ∫ t in (0 : Real)..2 * Real.pi * x, Real.sinc t)
      (Real.sinc (2 * Real.pi * x) * (2 * Real.pi)) x := by
    have hright := intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable
        (0 : Real) (2 * Real.pi * x))
      (Real.continuous_sinc.stronglyMeasurableAtFilter volume _)
      Real.continuous_sinc.continuousAt
    have hcomp :=
      hright.comp x ((hasDerivAt_id x).const_mul (2 * Real.pi))
    have hcomp' : HasDerivAt
        ((fun u : Real => ∫ t in (0 : Real)..u, Real.sinc t) ∘
          fun y : Real => 2 * Real.pi * y)
        (Real.sinc (2 * Real.pi * x) * (2 * Real.pi)) x := by
      simpa only [mul_one] using hcomp
    apply hcomp'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => rfl
  have hcos : HasDerivAt
      (fun x : Real => Real.cos (2 * Real.pi * x) - 1)
      (-Real.sin (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa only [Function.comp_apply, id_eq, mul_one, one_mul, mul_assoc] using
      (((Real.hasDerivAt_cos (2 * Real.pi * x)).comp x
        ((hasDerivAt_id x).const_mul (2 * Real.pi))).sub_const 1)
  have hden : HasDerivAt (fun x : Real => 2 * Real.pi ^ 2 * x)
      (2 * Real.pi ^ 2) x := by
    have hmul := (hasDerivAt_id x).const_mul (2 * Real.pi ^ 2)
    have heq : (fun y : Real => 2 * Real.pi ^ 2 * y) =ᶠ[nhds x]
        fun y : Real => 2 * Real.pi ^ 2 * id y :=
      Filter.Eventually.of_forall fun y => rfl
    simpa only [mul_one] using hmul.congr_of_eventuallyEq heq
  have hcorr := hcos.div hden (mul_ne_zero
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 Real.pi_ne_zero)) hx)
  have htotal := hi.div_const Real.pi |>.add hcorr
  change HasDerivAt cardinalSineSqPrimitive _ x at htotal
  convert htotal using 1
  · rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
    rw [Real.sinc_of_ne_zero (mul_ne_zero
      (mul_ne_zero (by norm_num) Real.pi_ne_zero) hx)]
    field_simp [hx, Real.pi_ne_zero]
    rw [show Real.pi * x * 2 = 2 * (Real.pi * x) by ring]
    rw [Real.sin_two_mul, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

/-- The quotient correction has a removable origin and a globally continuous
cardinal-sine form. -/
theorem cardinalSineSqPrimitive_correction (x : Real) :
    (Real.cos (2 * Real.pi * x) - 1) / (2 * Real.pi ^ 2 * x) =
      -x * Real.sinc (Real.pi * x) ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]
    field_simp [hx, Real.pi_ne_zero]
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]

theorem continuous_cardinalSineSqPrimitive :
    Continuous cardinalSineSqPrimitive := by
  rw [show cardinalSineSqPrimitive = fun x : Real =>
      (∫ t in (0 : Real)..2 * Real.pi * x, Real.sinc t) / Real.pi -
        x * Real.sinc (Real.pi * x) ^ 2 by
    funext x
    rw [cardinalSineSqPrimitive, cardinalSineSqPrimitive_correction x]
    ring]
  apply Continuous.sub
  · apply Continuous.div_const
    fun_prop
  · fun_prop

theorem cardinalSineSqPrimitive_neg (x : Real) :
    cardinalSineSqPrimitive (-x) = -cardinalSineSqPrimitive x := by
  have hneg := intervalIntegral.integral_comp_neg
    (fun t : Real => Real.sinc t)
    (a := (0 : Real)) (b := 2 * Real.pi * x)
  simp only [Real.sinc_neg, neg_zero] at hneg
  have hint :
      (∫ t in (0 : Real)..-(2 * Real.pi * x), Real.sinc t) =
        -(∫ t in (0 : Real)..2 * Real.pi * x, Real.sinc t) := by
    rw [intervalIntegral.integral_symm]
    exact congrArg Neg.neg hneg.symm
  rw [cardinalSineSqPrimitive, cardinalSineSqPrimitive]
  rw [show 2 * Real.pi * -x = -(2 * Real.pi * x) by ring, hint]
  rw [Real.cos_neg]
  ring

/-- Fundamental-theorem evaluation from the removable origin to an arbitrary
real endpoint. -/
theorem integral_sq_sinc_pi_zero (b : Real) :
    (∫ x in (0 : Real)..b, Real.sinc (Real.pi * x) ^ 2) =
      cardinalSineSqPrimitive b - cardinalSineSqPrimitive 0 := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [intervalIntegral.integral_symm]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      hb (a := b) (b := (0 : Real))
      (f := cardinalSineSqPrimitive)
      (f' := fun x : Real => Real.sinc (Real.pi * x) ^ 2)
      (fun x hx => hasDerivAt_cardinalSineSqPrimitive hx.2.ne)
      ((by fun_prop : Continuous (fun x : Real =>
        Real.sinc (Real.pi * x) ^ 2)).intervalIntegrable _ _)
      (continuous_cardinalSineSqPrimitive.continuousAt.mono_left inf_le_left)
      (continuous_cardinalSineSqPrimitive.continuousAt.mono_left inf_le_left)
    linarith
  · simp
  · exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
      hb (a := (0 : Real)) (b := b)
      (f := cardinalSineSqPrimitive)
      (f' := fun x : Real => Real.sinc (Real.pi * x) ^ 2)
      (fun x hx => hasDerivAt_cardinalSineSqPrimitive hx.1.ne')
      ((by fun_prop : Continuous (fun x : Real =>
        Real.sinc (Real.pi * x) ^ 2)).intervalIntegrable _ _)
      (continuous_cardinalSineSqPrimitive.continuousAt.mono_left inf_le_left)
      (continuous_cardinalSineSqPrimitive.continuousAt.mono_left inf_le_left)

/-- Exact primitive evaluation for every interval, including intervals that
cross the cardinal-sine resonance at zero. -/
theorem integral_sq_sinc_pi (a b : Real) :
    (∫ x in a..b, Real.sinc (Real.pi * x) ^ 2) =
      cardinalSineSqPrimitive b - cardinalSineSqPrimitive a := by
  have hint : ∀ c d : Real, IntervalIntegrable
      (fun x : Real => Real.sinc (Real.pi * x) ^ 2) volume c d := by
    intro c d
    exact (by fun_prop : Continuous (fun x : Real =>
      Real.sinc (Real.pi * x) ^ 2)).intervalIntegrable c d
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 a) (hint a b)
  rw [integral_sq_sinc_pi_zero a, integral_sq_sinc_pi_zero b] at hadd
  linarith

theorem integral_sq_sinc_pi_add_int (n : Int) :
    (∫ x in -cardinalSineCutoff44Window..cardinalSineCutoff44Window,
      Real.sinc (Real.pi * (x + n)) ^ 2) =
      cardinalSineSqPrimitive (cardinalSineCutoff44Window + n) -
        cardinalSineSqPrimitive (-cardinalSineCutoff44Window + n) := by
  rw [intervalIntegral.integral_comp_add_right
    (fun x : Real => Real.sinc (Real.pi * x) ^ 2) (n : Real)]
  exact integral_sq_sinc_pi _ _

/-- The full cutoff leakage is now a finite sum of explicit primitive endpoint
differences. -/
theorem cardinalSineCutoff44Leakage_eq_primitive_sum :
    cardinalSineCutoff44Leakage =
      2 * cardinalSineCutoff44Window -
        ∑ n ∈ Finset.Icc (-44 : Int) 44,
          (cardinalSineSqPrimitive (cardinalSineCutoff44Window + n) -
            cardinalSineSqPrimitive
              (-cardinalSineCutoff44Window + n)) := by
  rw [cardinalSineCutoff44Leakage_eq_sum]
  apply congrArg (fun z : Real => 2 * cardinalSineCutoff44Window - z)
  apply Finset.sum_congr rfl
  intro n hn
  exact integral_sq_sinc_pi_add_int n

theorem sum_cardinalSineSqPrimitive_upper_reindex :
    (∑ n ∈ Finset.Icc (-44 : Int) 44,
      cardinalSineSqPrimitive (cardinalSineCutoff44Window + n)) =
      ∑ i ∈ Finset.range 89,
        cardinalSineSqPrimitive
          (((273 : Int) - 4 * (i : Int) : Int) / 4 : Rat) := by
  have hset : (Finset.range 89).image
      (fun i : Nat => (44 : Int) - (i : Int)) =
        Finset.Icc (-44 : Int) 44 := by
    ext n
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨i, hi, rfl⟩
      constructor <;> omega
    · intro hn
      let i : Nat := (44 - n).toNat
      have hi0 : 0 ≤ 44 - n := by omega
      have hiCast : (i : Int) = 44 - n := by
        exact Int.toNat_of_nonneg hi0
      refine ⟨i, ?_, ?_⟩
      · omega
      · omega
  rw [← hset, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    unfold cardinalSineCutoff44Window
    push_cast
    norm_num
    ring
  · intro a ha b hb hab
    have hab' : (a : Int) = (b : Int) := by
      exact (@sub_right_inj Int _ (44 : Int) (a : Int) (b : Int)).mp
        (by simpa using hab)
    exact_mod_cast hab'

theorem sum_cardinalSineSqPrimitive_lower_eq_neg_upper :
    (∑ n ∈ Finset.Icc (-44 : Int) 44,
      cardinalSineSqPrimitive (-cardinalSineCutoff44Window + n)) =
      -(∑ n ∈ Finset.Icc (-44 : Int) 44,
        cardinalSineSqPrimitive (cardinalSineCutoff44Window + n)) := by
  have hset : (Finset.Icc (-44 : Int) 44).image (fun n : Int => -n) =
      Finset.Icc (-44 : Int) 44 := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨m, hm, rfl⟩
      constructor <;> omega
    · intro hn
      exact ⟨-n, by omega, by omega⟩
  rw [← hset, Finset.sum_image]
  · rw [hset]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Int.cast_neg]
    rw [show -cardinalSineCutoff44Window + -(n : Real) =
        -(cardinalSineCutoff44Window + n) by ring,
      cardinalSineSqPrimitive_neg]
  · intro a ha b hb hab
    exact neg_injective hab

/-- Symmetry and exact reindexing reduce the leakage to the 89 positive-side
primitive values used by DF0. -/
theorem cardinalSineCutoff44Leakage_eq_reindexed_primitive_sum :
    cardinalSineCutoff44Leakage =
      2 * (cardinalSineCutoff44Window -
        ∑ i ∈ Finset.range 89,
          cardinalSineSqPrimitive
            (((273 : Int) - 4 * (i : Int) : Int) / 4 : Rat)) := by
  rw [cardinalSineCutoff44Leakage_eq_primitive_sum]
  rw [Finset.sum_sub_distrib,
    sum_cardinalSineSqPrimitive_lower_eq_neg_upper,
    sum_cardinalSineSqPrimitive_upper_reindex]
  ring

end

end RiemannHypothesisProject.Experiments.M100
