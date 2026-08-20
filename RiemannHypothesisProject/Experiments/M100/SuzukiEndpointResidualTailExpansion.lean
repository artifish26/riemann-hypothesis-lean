import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailEnclosures

/-!
# Geometric residual expansion for M100-DF6D4

The even and odd endpoint scripts expand the normalized resolvent
`(1 - m^2 / n^2)⁻¹` through order four.  This module proves the exact finite
expansion and the denominator-frozen remainder estimate used after mode 600.
It contains no numerical Suzuki envelope or positivity conclusion.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

/-- The finite geometric prefix through exponent `order`. -/
def suzukiDF6D4GeometricPrefix (q : Real) (order : Nat) : Real :=
  ∑ k ∈ Finset.range (order + 1), q ^ k

theorem suzukiDF6D4GeometricPrefix_mul_one_sub
    (q : Real) (order : Nat) :
    suzukiDF6D4GeometricPrefix q order * (1 - q) =
      1 - q ^ (order + 1) := by
  simpa only [suzukiDF6D4GeometricPrefix] using
    geom_sum_mul_neg q (order + 1)

/-- Exact finite expansion of the normalized resolvent, with the geometric
remainder left visible. -/
theorem suzukiDF6D4OneDivOneSub_eq_geometricPrefix_add_remainder
    (q : Real) (order : Nat) (hq : q ≠ 1) :
    1 / (1 - q) = suzukiDF6D4GeometricPrefix q order +
      q ^ (order + 1) / (1 - q) := by
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hgeom := suzukiDF6D4GeometricPrefix_mul_one_sub q order
  field_simp [hden]
  linarith

/-- Freezing the geometric denominator at a larger ratio gives a valid
upper bound while retaining the exact numerator. -/
theorem suzukiDF6D4GeometricRemainder_le_frozenDenominator
    (q qMax : Real) (order : Nat)
    (hq : 0 ≤ q) (hqqMax : q ≤ qMax) (hqMax : qMax < 1) :
    0 ≤ q ^ (order + 1) / (1 - q) ∧
      q ^ (order + 1) / (1 - q) ≤
        q ^ (order + 1) / (1 - qMax) := by
  have hden : 0 < 1 - q := by linarith
  have hdenMax : 0 < 1 - qMax := by linarith
  constructor
  · exact div_nonneg (pow_nonneg hq _) hden.le
  · exact div_le_div_of_nonneg_left (pow_nonneg hq _) hdenMax (by linarith)

/-- Absolute-error form of the exact expansion and frozen-denominator bound. -/
theorem suzukiDF6D4OneDivOneSub_sub_geometricPrefix_abs_le
    (q qMax : Real) (order : Nat)
    (hq : 0 ≤ q) (hqqMax : q ≤ qMax) (hqMax : qMax < 1) :
    |1 / (1 - q) - suzukiDF6D4GeometricPrefix q order| ≤
      q ^ (order + 1) / (1 - qMax) := by
  have hqne : q ≠ 1 := ne_of_lt (hqqMax.trans_lt hqMax)
  have hbound := suzukiDF6D4GeometricRemainder_le_frozenDenominator
    q qMax order hq hqqMax hqMax
  rw [suzukiDF6D4OneDivOneSub_eq_geometricPrefix_add_remainder
    q order hqne]
  have hcancel :
      suzukiDF6D4GeometricPrefix q order +
          q ^ (order + 1) / (1 - q) -
        suzukiDF6D4GeometricPrefix q order =
      q ^ (order + 1) / (1 - q) := by ring
  rw [hcancel, abs_of_nonneg hbound.1]
  exact hbound.2

/-- Order-four specialization used by both frozen endpoint scripts. -/
theorem suzukiDF6D4OrderFourGeometricRemainder_abs_le
    (q qMax : Real) (hq : 0 ≤ q) (hqqMax : q ≤ qMax)
    (hqMax : qMax < 1) :
    |1 / (1 - q) - suzukiDF6D4GeometricPrefix q 4| ≤
      q ^ 5 / (1 - qMax) := by
  simpa using suzukiDF6D4OneDivOneSub_sub_geometricPrefix_abs_le
    q qMax 4 hq hqqMax hqMax

/-- Increasing the tail mode can only decrease the squared row/tail ratio. -/
theorem suzukiDF6D4RatioSquare_le_frozenRatioSquare
    (m n first : Real) (hm : 0 ≤ m) (hfirst : 0 < first)
    (hfirstN : first ≤ n) :
    (m / n) ^ 2 ≤ (m / first) ^ 2 := by
  have hn : 0 < n := hfirst.trans_le hfirstN
  have hratio : m / n ≤ m / first :=
    div_le_div_of_nonneg_left hm hfirst hfirstN
  exact (sq_le_sq₀ (div_nonneg hm hn.le)
    (div_nonneg hm hfirst.le)).2 hratio

/-- Resolvent remainder with its denominator frozen at the first tail mode. -/
theorem suzukiDF6D4OrderFourRatioRemainder_abs_le
    (m n first : Real) (hm : 0 ≤ m) (hfirst : 0 < first)
    (hmFirst : m < first) (hfirstN : first ≤ n) :
    |1 / (1 - (m / n) ^ 2) -
        suzukiDF6D4GeometricPrefix ((m / n) ^ 2) 4| ≤
      ((m / n) ^ 2) ^ 5 / (1 - (m / first) ^ 2) := by
  have hn : 0 < n := hfirst.trans_le hfirstN
  have hq : 0 ≤ (m / n) ^ 2 := sq_nonneg _
  have hqMax : 0 ≤ m / first := div_nonneg hm hfirst.le
  have hratioLt : m / first < 1 := (div_lt_one hfirst).2 hmFirst
  exact suzukiDF6D4OrderFourGeometricRemainder_abs_le
    ((m / n) ^ 2) ((m / first) ^ 2) hq
    (suzukiDF6D4RatioSquare_le_frozenRatioSquare
      m n first hm hfirst hfirstN)
    ((sq_lt_one_iff₀ hqMax).2 hratioLt)

/-- Frozen DF6D4 range: every Galerkin row mode is at most `300` and every
analytic-tail mode is at least `601`. -/
theorem suzukiDF6D4FrozenOrderFourRatioRemainder_abs_le
    (m n : Nat) (hm : m ≤ 300) (hn : 601 ≤ n) :
    |1 / (1 - (((m : Real) / (n : Real)) ^ 2)) -
        suzukiDF6D4GeometricPrefix (((m : Real) / (n : Real)) ^ 2) 4| ≤
      (((m : Real) / (n : Real)) ^ 2) ^ 5 /
        (1 - (((m : Real) / 601) ^ 2)) := by
  have hmFirst : (m : Real) < 601 := by
    exact_mod_cast hm.trans_lt (by norm_num : 300 < 601)
  have hnReal : (601 : Real) ≤ n := by exact_mod_cast hn
  exact suzukiDF6D4OrderFourRatioRemainder_abs_le
    (m : Real) (n : Real) 601 (by positivity) (by norm_num)
    hmFirst hnReal

/-! ## Even and odd convolution-kernel normal forms -/

/-- The even sum of the difference and total-frequency fractions is the
normalized numerator used by the cosine-block tail expansion. -/
theorem suzukiDF6D4EvenConvolutionKernel_eq
    (m n Jm Jn : Real) (hsub : n - m ≠ 0) (hadd : n + m ≠ 0) :
    (1 / 2 : Real) *
        ((Jn - Jm) / (n - m) + (Jm + Jn) / (n + m)) =
      (n * Jn - m * Jm) / (n ^ 2 - m ^ 2) := by
  have hfactor : n ^ 2 - m ^ 2 = (n - m) * (n + m) := by ring
  have hsquare : n ^ 2 - m ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hsub hadd
  field_simp [hsub, hadd, hsquare]
  ring

/-- The odd difference of the two frequency fractions is the normalized
numerator used by the sine-block tail expansion. -/
theorem suzukiDF6D4OddConvolutionKernel_eq
    (m n Jm Jn : Real) (hsub : n - m ≠ 0) (hadd : n + m ≠ 0) :
    (1 / 2 : Real) *
        ((Jn - Jm) / (n - m) - (Jm + Jn) / (n + m)) =
      (m * Jn - n * Jm) / (n ^ 2 - m ^ 2) := by
  have hfactor : n ^ 2 - m ^ 2 = (n - m) * (n + m) := by ring
  have hsquare : n ^ 2 - m ^ 2 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hsub hadd
  field_simp [hsub, hadd, hsquare]
  ring

/-- Even convolution kernel written as a low-degree numerator times the
normalized resolvent `(1 - (m/n)^2)⁻¹`. -/
theorem suzukiDF6D4EvenConvolutionKernel_normalized
    (m n Jm Jn : Real) (hn : n ≠ 0) (hsquare : n ^ 2 - m ^ 2 ≠ 0) :
    (n * Jn - m * Jm) / (n ^ 2 - m ^ 2) =
      (Jn / n - m * Jm / n ^ 2) *
        (1 / (1 - (m / n) ^ 2)) := by
  field_simp [hn, hsquare]

/-- Odd convolution kernel in the same normalized-resolvent form. -/
theorem suzukiDF6D4OddConvolutionKernel_normalized
    (m n Jm Jn : Real) (hn : n ≠ 0) (hsquare : n ^ 2 - m ^ 2 ≠ 0) :
    (m * Jn - n * Jm) / (n ^ 2 - m ^ 2) =
      (m * Jn / n ^ 2 - Jm / n) *
        (1 / (1 - (m / n) ^ 2)) := by
  field_simp [hn, hsquare]

end

end RiemannHypothesisProject.Experiments.M100
