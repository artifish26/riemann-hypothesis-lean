import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointDF0Enclosures
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaCutoff44Leakage

/-!
# Cutoff-44 leakage to DF0 normalization bridge

This module isolates the final analytic source evaluation needed to identify
the normalized cardinal-sine leakage integral with DF0's independently frozen
89-term scalar.  The receiving theorem consumes only pointwise primitive
identifications, not an endpoint record.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

theorem cardinalSineSqPrimitive_nat_quarter
    (q : Nat) (hq : q ≠ 0)
    (hcos : Real.cos (suzukiDF6D4DF0QuarterWave q) = 0) :
    cardinalSineSqPrimitive ((q : Real) / 4) =
      (∫ t in (0 : Real)..suzukiDF6D4DF0QuarterWave q, Real.sinc t) *
          Real.pi⁻¹ +
        ((-2 / q : Rat) : Real) * (Real.pi⁻¹ ^ 2) := by
  unfold cardinalSineSqPrimitive suzukiDF6D4DF0QuarterWave
  unfold suzukiDF6D4DF0QuarterWave at hcos
  rw [show 2 * Real.pi * ((q : Real) / 4) =
      ((q : Real) / 2) * Real.pi by ring]
  rw [hcos]
  push_cast
  field_simp [hq, Real.pi_ne_zero]
  ring

theorem cos_suzukiDF6D4DF0QuarterWave_leakageAbsNumerator
    (index : Nat) (hindex : index < 89) :
    Real.cos (suzukiDF6D4DF0QuarterWave
      (suzukiDF6D4DF0LeakageAbsNumerator index)) = 0 := by
  have hodd : Odd (suzukiDF6D4DF0LeakageAbsNumerator index) := by
    interval_cases index <;> native_decide
  obtain ⟨k, hk⟩ := odd_iff_exists_bit1.mp hodd
  rw [hk]
  unfold suzukiDF6D4DF0QuarterWave
  rw [show ((((2 * k + 1 : Nat) : Real) / 2) * Real.pi) =
      (k : Real) * Real.pi + Real.pi / 2 by push_cast; ring]
  rw [Real.cos_add_pi_div_two, Real.sin_nat_mul_pi]
  simp

/-- The actual analytic source evaluations remaining inside DF0: its custom
quarter-sine values must equal the corresponding finite sinc integrals. -/
def SuzukiDF6D5B3FEDF0QuarterSineIntegralEvaluation : Prop :=
  ∀ index : Nat, index < 89 →
    suzukiDF6D4DF0QuarterSineIntegral
        (suzukiDF6D4DF0LeakageAbsNumerator index) =
      ∫ t in (0 : Real)..suzukiDF6D4DF0QuarterWave
        (suzukiDF6D4DF0LeakageAbsNumerator index), Real.sinc t

/-- Source/normalization bridge remaining after the generic cardinal-sine
integral and finite reindexing have been proved. -/
def SuzukiDF6D5B3FECutoff44PrimitiveIdentification : Prop :=
  ∀ index : Nat, index < 89 →
    cardinalSineSqPrimitive
        (((273 : Int) - 4 * (index : Int) : Int) / 4 : Rat) =
      suzukiDF6D4DF0LeakagePrimitive index

/-- The quarter-sine source evaluations imply all 89 signed primitive
identifications; the sign split and endpoint normalization are elementary. -/
theorem suzukiDF6D5B3FECutoff44PrimitiveIdentification_of_quarterSine
    (hsource : SuzukiDF6D5B3FEDF0QuarterSineIntegralEvaluation) :
    SuzukiDF6D5B3FECutoff44PrimitiveIdentification := by
  intro index hindex
  let q := suzukiDF6D4DF0LeakageAbsNumerator index
  have hq : q ≠ 0 :=
    (Nat.ne_zero_iff_zero_lt.mpr
      (suzukiDF6D4DF0LeakageAbsNumerator_pos index hindex))
  have hp := cardinalSineSqPrimitive_nat_quarter q hq
    (cos_suzukiDF6D4DF0QuarterWave_leakageAbsNumerator index hindex)
  have hsource' := hsource index hindex
  change suzukiDF6D4DF0QuarterSineIntegral q = _ at hsource'
  rw [← hsource'] at hp
  by_cases hi : index ≤ 68
  · have hqDef : q = 273 - 4 * index := by
      simp [q, suzukiDF6D4DF0LeakageAbsNumerator, hi]
    have hle : 4 * index ≤ 273 := by omega
    have hx :
        ((((273 : Int) - 4 * (index : Int) : Int) / 4 : Rat) : Real) =
          (q : Real) / 4 := by
      rw [hqDef]
      push_cast
      rw [Nat.cast_sub hle]
      norm_num
    rw [hx]
    rw [hp]
    unfold suzukiDF6D4DF0LeakagePrimitive
    simp [q, suzukiDF6D4DF0LeakageArgumentSign, hi]
  · have hi' : 69 ≤ index := by omega
    have hqDef : q = 4 * index - 273 := by
      simp [q, suzukiDF6D4DF0LeakageAbsNumerator, hi]
    have hle : 273 ≤ 4 * index := by omega
    have hx :
        ((((273 : Int) - 4 * (index : Int) : Int) / 4 : Rat) : Real) =
          -((q : Real) / 4) := by
      rw [hqDef]
      push_cast
      rw [Nat.cast_sub hle]
      norm_num
      ring
    rw [hx, cardinalSineSqPrimitive_neg, hp]
    unfold suzukiDF6D4DF0LeakagePrimitive
    simp [q, suzukiDF6D4DF0LeakageArgumentSign, hi]
    ring

/-- Pointwise identification of the 89 primitive endpoints makes the analytic
cutoff leakage exactly the independently certified DF0 leakage scalar. -/
theorem cardinalSineCutoff44Leakage_eq_suzukiDF6D4DF0LeakageFraction
    (hsource : SuzukiDF6D5B3FECutoff44PrimitiveIdentification) :
    cardinalSineCutoff44Leakage = suzukiDF6D4DF0LeakageFraction := by
  rw [cardinalSineCutoff44Leakage_eq_reindexed_primitive_sum]
  unfold suzukiDF6D4DF0LeakageFraction cardinalSineCutoff44Window
  congr 2
  apply Finset.sum_congr rfl
  intro index hindex
  exact hsource index (Finset.mem_range.mp hindex)

end

end RiemannHypothesisProject.Experiments.M100
