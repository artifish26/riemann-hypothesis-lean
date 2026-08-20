import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Cardinal-sine partition input for M100-DF6D5B3F-E

This module develops the generic reciprocal-square series identity behind the
DF0 cardinal-sine partition.  It is kept separate from the B3F-E endpoint
receivers so the analytic source theorem and the project normalization bridge
remain distinct.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Complex Filter Set Topology

/-- The differentiated cotangent expansion gives the reciprocal-square series
in the complex upper half-plane. -/
theorem tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq_of_im_pos
    {z : Complex} (hz : 0 < z.im) :
    (∑' n : Int, 1 / (z + n) ^ 2) =
      (Real.pi : Complex) ^ 2 / Complex.sin (Real.pi * z) ^ 2 := by
  have hzUpper : z ∈ UpperHalfPlane.upperHalfPlaneSet := hz
  have hseries :=
    iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow
      (k := 1) (by norm_num) hzUpper
  have hzComplement : z ∈ Complex.integerComplement :=
    UpperHalfPlane.coe_mem_integerComplement ⟨z, hz⟩
  have hsin : Complex.sin (Real.pi * z) ≠ 0 :=
    sin_pi_mul_ne_zero hzComplement
  have harg :
      HasDerivAt (fun w : Complex => (Real.pi : Complex) * w)
        (Real.pi : Complex) z := by
    simpa using (hasDerivAt_id z).const_mul (Real.pi : Complex)
  have hcos :
      HasDerivAt (fun w : Complex => Complex.cos (Real.pi * w))
        (-(Complex.sin (Real.pi * z)) * Real.pi) z := by
    convert (Complex.hasDerivAt_cos (Real.pi * z)).comp z harg using 1 <;>
      rfl
  have hsinDeriv :
      HasDerivAt (fun w : Complex => Complex.sin (Real.pi * w))
        (Complex.cos (Real.pi * z) * Real.pi) z := by
    convert (Complex.hasDerivAt_sin (Real.pi * z)).comp z harg using 1 <;>
      rfl
  have hcotDeriv :
      deriv (fun w : Complex =>
        (Real.pi : Complex) * Complex.cot (Real.pi * w)) z =
        -((Real.pi : Complex) ^ 2) /
          Complex.sin (Real.pi * z) ^ 2 := by
    have hquot := hcos.div hsinDeriv hsin
    have hmul := hquot.const_mul (Real.pi : Complex)
    rw [show (fun w : Complex =>
        (Real.pi : Complex) * Complex.cot (Real.pi * w)) =
      fun w : Complex =>
        (Real.pi : Complex) *
          (Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w)) by
        funext w
        rfl]
    have hderiv := hmul.deriv
    change deriv (fun w : Complex =>
      (Real.pi : Complex) *
        (Complex.cos (Real.pi * w) / Complex.sin (Real.pi * w))) z = _
      at hderiv
    rw [hderiv]
    field_simp
    linear_combination -Complex.sin_sq_add_cos_sq (Real.pi * z)
  rw [iteratedDerivWithin_one,
    derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hzUpper,
    hcotDeriv] at hseries
  norm_num at hseries
  apply neg_injective
  simpa only [one_div, neg_div] using hseries.symm

/-- Real-boundary form of the reciprocal-square identity, still written in
`Complex` so it follows directly from the upper-half-plane expansion. -/
theorem tsum_int_one_div_real_add_sq_eq_pi_sq_div_sin_sq
    {x : Real} (hx : (x : Complex) ∈ Complex.integerComplement) :
    (∑' n : Int, 1 / ((x : Complex) + n) ^ 2) =
      (Real.pi : Complex) ^ 2 /
        Complex.sin (Real.pi * (x : Complex)) ^ 2 := by
  let y : Nat → Real := fun k => 1 / (k + 1 : Real)
  let z : Nat → Complex := fun k => (x : Complex) + (y k : Complex) * I
  have hyPos (k : Nat) : 0 < y k := by
    dsimp [y]
    positivity
  have hyTendsto : Tendsto y atTop (𝓝 0) := by
    simpa only [y] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hzTendsto : Tendsto z atTop (𝓝 (x : Complex)) := by
    dsimp only [z]
    have hyComplex : Tendsto (fun k => (y k : Complex)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hyTendsto
    simpa using tendsto_const_nhds.add (hyComplex.mul_const I)
  have hboundSummable :
      Summable (fun n : Int => 1 / |(n : Real) + x| ^ (2 : Real)) := by
    exact (Real.summable_one_div_int_add_rpow x 2).mpr (by norm_num)
  have htermTendsto (n : Int) :
      Tendsto (fun k => 1 / (z k + n) ^ 2) atTop
        (𝓝 (1 / ((x : Complex) + n) ^ 2)) := by
    have hn : (x : Complex) + (n : Complex) ≠ 0 :=
      integerComplement_add_ne_zero hx n
    have hc : ContinuousAt (fun w : Complex => 1 / (w + n) ^ 2) (x : Complex) := by
      apply ContinuousAt.div continuousAt_const
        ((continuousAt_id.add continuousAt_const).pow 2)
      exact pow_ne_zero 2 hn
    exact hc.tendsto.comp hzTendsto
  have htermBound :
      ∀ᶠ k in atTop, ∀ n : Int,
        ‖1 / (z k + n) ^ 2‖ ≤
          1 / |(n : Real) + x| ^ (2 : Real) := by
    filter_upwards with k
    intro n
    have hn : (x : Complex) + (n : Complex) ≠ 0 :=
      integerComplement_add_ne_zero hx n
    have hxAbsPos : 0 < |(n : Real) + x| := by
      rw [abs_pos]
      intro hzero
      apply hn
      exact Complex.ext (by simpa [add_comm] using hzero) (by simp)
    have hrealPart :
        |(n : Real) + x| ≤ ‖z k + (n : Complex)‖ := by
      simpa [z, add_assoc, add_comm, add_left_comm] using
        Complex.abs_re_le_norm (z k + (n : Complex))
    rw [norm_div, norm_one, norm_pow]
    norm_num
    have hsquares :
        |(n : Real) + x| ^ 2 ≤ ‖z k + (n : Complex)‖ ^ 2 := by
      have hproduct :
          0 ≤ (‖z k + (n : Complex)‖ - |(n : Real) + x|) *
            (‖z k + (n : Complex)‖ + |(n : Real) + x|) :=
        mul_nonneg (sub_nonneg.mpr hrealPart)
          (add_nonneg (norm_nonneg _) (abs_nonneg _))
      nlinarith
    have hinv := inv_anti₀ (pow_pos hxAbsPos 2) hsquares
    simpa only [sq_abs] using hinv
  have hleftTendsto :
      Tendsto (fun k => ∑' n : Int, 1 / (z k + n) ^ 2) atTop
        (𝓝 (∑' n : Int, 1 / ((x : Complex) + n) ^ 2)) := by
    exact tendsto_tsum_of_dominated_convergence hboundSummable
      htermTendsto htermBound
  have hsin : Complex.sin (Real.pi * (x : Complex)) ≠ 0 :=
    sin_pi_mul_ne_zero hx
  have hrightTendsto :
      Tendsto (fun k =>
        (Real.pi : Complex) ^ 2 /
          Complex.sin (Real.pi * z k) ^ 2) atTop
        (𝓝 ((Real.pi : Complex) ^ 2 /
          Complex.sin (Real.pi * (x : Complex)) ^ 2)) := by
    have hc : ContinuousAt (fun w : Complex =>
        (Real.pi : Complex) ^ 2 /
          Complex.sin (Real.pi * w) ^ 2) (x : Complex) := by
      apply ContinuousAt.div continuousAt_const
        ((Complex.continuous_sin.continuousAt.comp
          (continuousAt_const.mul continuousAt_id)).pow 2)
      exact pow_ne_zero 2 hsin
    exact hc.tendsto.comp hzTendsto
  have hrightFromLeft :
      Tendsto (fun k =>
        (Real.pi : Complex) ^ 2 /
          Complex.sin (Real.pi * z k) ^ 2) atTop
        (𝓝 (∑' n : Int, 1 / ((x : Complex) + n) ^ 2)) := by
    apply hleftTendsto.congr'
    filter_upwards with k
    apply
      tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq_of_im_pos
    simp [z, hyPos k]
  exact tendsto_nhds_unique hrightFromLeft hrightTendsto

/-- Real-valued reciprocal-square identity away from the integer lattice. -/
theorem real_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq
    {x : Real} (hx : (x : Complex) ∈ Complex.integerComplement) :
    (∑' n : Int, 1 / (x + n) ^ 2) =
      Real.pi ^ 2 / Real.sin (Real.pi * x) ^ 2 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_tsum]
  simpa only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_intCast, Complex.ofReal_mul,
    Complex.ofReal_sin] using
      tsum_int_one_div_real_add_sq_eq_pi_sq_div_sin_sq hx

/-- The squared cardinal-sine translates form a summable real series. -/
theorem summable_sq_sinc_pi_mul_add_int (x : Real) :
    Summable (fun n : Int => Real.sinc (Real.pi * (x + n)) ^ 2) := by
  by_cases hx : (x : Complex) ∈ Complex.integerComplement
  · have hrecipAbs :
        Summable (fun n : Int => 1 / |(n : Real) + x| ^ (2 : Real)) := by
      exact (Real.summable_one_div_int_add_rpow x 2).mpr (by norm_num)
    have hrecip : Summable (fun n : Int => 1 / (x + n) ^ 2) := by
      apply hrecipAbs.congr
      intro n
      rw [Real.rpow_two, sq_abs]
      congr 2
      ring
    apply (hrecip.mul_left
      (Real.sin (Real.pi * x) ^ 2 / Real.pi ^ 2)).congr
    intro n
    have hxn : x + (n : Real) ≠ 0 := by
      intro hzero
      apply integerComplement_add_ne_zero hx n
      exact_mod_cast hzero
    have harg : Real.pi * (x + (n : Real)) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero hxn
    rw [Real.sinc_of_ne_zero harg]
    have hshift :
        Real.sin (Real.pi * (x + (n : Real))) ^ 2 =
          Real.sin (Real.pi * x) ^ 2 := by
      rw [show Real.pi * (x + (n : Real)) =
          Real.pi * x + n * Real.pi by ring,
        Real.sin_add_int_mul_pi]
      rw [mul_pow]
      have hsign : ((-1 : Real) ^ n) ^ 2 = 1 := by
        rw [← zpow_natCast, ← zpow_mul]
        rw [mul_comm, ← Int.cast_negOnePow]
        norm_num [Int.negOnePow_two_mul]
      rw [hsign, one_mul]
    rw [div_pow, hshift]
    field_simp
  · rw [Complex.mem_integerComplement_iff] at hx
    have hxExists : ∃ m : Int, (m : Complex) = (x : Complex) := by
      simpa only [not_not] using hx
    obtain ⟨m, hm⟩ := hxExists
    have hxReal : x = (m : Real) := by
      exact_mod_cast hm.symm
    subst x
    apply (hasSum_single (-m) ?_).summable
    intro n hn
    have hsum : m + n ≠ 0 := by omega
    have harg :
        Real.pi * ((m : Real) + (n : Real)) ≠ 0 := by
      apply mul_ne_zero Real.pi_ne_zero
      exact_mod_cast hsum
    rw [Real.sinc_of_ne_zero harg]
    rw [show Real.pi * ((m : Real) + (n : Real)) =
        ((m + n : Int) : Real) * Real.pi by push_cast; ring,
      Real.sin_int_mul_pi]
    simp

/-- The integer translates of normalized cardinal sine have squared partition
of unity.  This is the analytic identity used by the cutoff-44 leakage
calculation. -/
theorem tsum_sq_sinc_pi_mul_add_int (x : Real) :
    (∑' n : Int, Real.sinc (Real.pi * (x + n)) ^ 2) = 1 := by
  by_cases hx : (x : Complex) ∈ Complex.integerComplement
  · have hsin : Real.sin (Real.pi * x) ≠ 0 := by
      exact_mod_cast sin_pi_mul_ne_zero hx
    have hterm (n : Int) :
        Real.sinc (Real.pi * (x + n)) ^ 2 =
          (Real.sin (Real.pi * x) ^ 2 / Real.pi ^ 2) *
            (1 / (x + n) ^ 2) := by
      have hxn : x + (n : Real) ≠ 0 := by
        intro hzero
        apply integerComplement_add_ne_zero hx n
        exact_mod_cast hzero
      have harg : Real.pi * (x + (n : Real)) ≠ 0 :=
        mul_ne_zero Real.pi_ne_zero hxn
      rw [Real.sinc_of_ne_zero harg]
      have hshift :
          Real.sin (Real.pi * (x + (n : Real))) ^ 2 =
            Real.sin (Real.pi * x) ^ 2 := by
        rw [show Real.pi * (x + (n : Real)) =
            Real.pi * x + n * Real.pi by ring,
          Real.sin_add_int_mul_pi]
        rw [mul_pow]
        have hsign : ((-1 : Real) ^ n) ^ 2 = 1 := by
          rw [← zpow_natCast, ← zpow_mul]
          rw [mul_comm, ← Int.cast_negOnePow]
          norm_num [Int.negOnePow_two_mul]
        rw [hsign, one_mul]
      rw [div_pow, hshift]
      field_simp
    simp_rw [hterm]
    rw [tsum_mul_left,
      real_tsum_int_one_div_add_sq_eq_pi_sq_div_sin_sq hx]
    field_simp
  · rw [Complex.mem_integerComplement_iff] at hx
    have hxExists : ∃ m : Int, (m : Complex) = (x : Complex) := by
      simpa only [not_not] using hx
    obtain ⟨m, hm⟩ := hxExists
    have hxReal : x = (m : Real) := by
      exact_mod_cast hm.symm
    subst x
    rw [tsum_eq_single (-m)]
    · norm_num
    · intro n hn
      have hsum : m + n ≠ 0 := by
        omega
      have harg :
          Real.pi * ((m : Real) + (n : Real)) ≠ 0 := by
        apply mul_ne_zero Real.pi_ne_zero
        exact_mod_cast hsum
      rw [Real.sinc_of_ne_zero harg]
      rw [show Real.pi * ((m : Real) + (n : Real)) =
          ((m + n : Int) : Real) * Real.pi by push_cast; ring,
        Real.sin_int_mul_pi]
      simp

/-- The contribution of the 89 integer modes from `-44` through `44` to the
cardinal-sine partition. -/
def cardinalSineCutoff44LowDensity (x : Real) : Real :=
  ∑ n ∈ Finset.Icc (-44 : Int) 44,
    Real.sinc (Real.pi * (x + n)) ^ 2

theorem cardinalSineCutoff44LowDensity_nonneg (x : Real) :
    0 ≤ cardinalSineCutoff44LowDensity x := by
  exact Finset.sum_nonneg fun n hn => sq_nonneg _

theorem cardinalSineCutoff44LowDensity_le_one (x : Real) :
    cardinalSineCutoff44LowDensity x ≤ 1 := by
  rw [← tsum_sq_sinc_pi_mul_add_int x]
  exact (summable_sq_sinc_pi_mul_add_int x).sum_le_tsum
    (Finset.Icc (-44 : Int) 44) (fun n hn => by positivity)

/-- The pointwise unresolved cardinal-sine mass beyond the cutoff-44 modes. -/
def cardinalSineCutoff44TailDensity (x : Real) : Real :=
  1 - cardinalSineCutoff44LowDensity x

theorem cardinalSineCutoff44TailDensity_nonneg (x : Real) :
    0 ≤ cardinalSineCutoff44TailDensity x := by
  exact sub_nonneg.mpr (cardinalSineCutoff44LowDensity_le_one x)

end

end RiemannHypothesisProject.Experiments.M100
