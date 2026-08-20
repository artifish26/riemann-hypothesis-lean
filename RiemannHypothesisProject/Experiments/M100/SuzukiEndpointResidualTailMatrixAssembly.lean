import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointResidualTailEnclosures

/-!
# Residual-tail matrix assembly for M100-DF6D4

This module contains the dimension-independent quadratic estimates used to
turn coordinatewise analytic-tail envelopes into matrix bounds.  It does not
assert a Suzuki asymptotic expansion: the concrete even and odd modules must
prove their coordinatewise envelopes before using these lemmas.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

/-- Weighted Cauchy-Schwarz in the precise diagonal-envelope form used by the
DF6D4 residual-tail certificates. -/
theorem suzukiDF6D4WeightedCauchy
    {d : Nat} (envelope x : Fin d → Real)
    (henvelope : ∀ i, 0 ≤ envelope i) :
    (∑ i, envelope i * |x i|) ^ 2 ≤
      (∑ i, envelope i) * ∑ i, envelope i * (x i) ^ 2 := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => henvelope i)
    (fun i _ => mul_nonneg (henvelope i) (sq_nonneg (x i))) ?_
  intro i _
  rw [mul_pow, sq_abs]
  ring_nf
  exact le_rfl

/-- A coordinatewise product envelope gives the absolute finite dot-product
bound needed before applying weighted Cauchy-Schwarz. -/
theorem suzukiDF6D4AbsDotProduct_le
    {d : Nat} (r envelope x : Fin d → Real) (weight : Real)
    (hr : ∀ i, |r i| ≤ envelope i * weight) :
    |∑ i, x i * r i| ≤ (∑ i, envelope i * |x i|) * weight := by
  calc
    |∑ i, x i * r i| ≤ ∑ i, |x i * r i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (envelope i * |x i|) * weight := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      calc
        |x i| * |r i| ≤ |x i| * (envelope i * weight) :=
          mul_le_mul_of_nonneg_left (hr i) (abs_nonneg _)
        _ = (envelope i * |x i|) * weight := by ring
    _ = (∑ i, envelope i * |x i|) * weight := by
      rw [Finset.sum_mul]

/-- Summing coordinatewise residual envelopes produces the diagonal matrix
bound used for the order-`n^-11` geometric tail:

`sum_k <x,r_k>^2 <= (sum_i E_i) (sum_k w_k^2) sum_i E_i x_i^2`.
-/
theorem suzukiDF6D4TailQuadratic_le_diagonalEnvelope
    {d : Nat} (r : Nat → Fin d → Real)
    (envelope : Fin d → Real) (weight : Nat → Real)
    (henvelope : ∀ i, 0 ≤ envelope i)
    (hweight : ∀ k, 0 ≤ weight k)
    (hr : ∀ k i, |r k i| ≤ envelope i * weight k)
    (hweightSummable : Summable fun k => (weight k) ^ 2)
    (x : Fin d → Real) :
    (∑' k : Nat, (∑ i, x i * r k i) ^ 2) ≤
      (∑ i, envelope i) * (∑' k : Nat, (weight k) ^ 2) *
        ∑ i, envelope i * (x i) ^ 2 := by
  let envelopeSum : Real := ∑ i, envelope i
  let weightedSquare : Real := ∑ i, envelope i * (x i) ^ 2
  have henvelopeSum : 0 ≤ envelopeSum := by
    exact Finset.sum_nonneg fun i _ => henvelope i
  have hweightedSquare : 0 ≤ weightedSquare := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (henvelope i) (sq_nonneg (x i))
  have hcauchy : (∑ i, envelope i * |x i|) ^ 2 ≤
      envelopeSum * weightedSquare := by
    simpa only [envelopeSum, weightedSquare] using
      suzukiDF6D4WeightedCauchy envelope x henvelope
  have hmode : ∀ k,
      (∑ i, x i * r k i) ^ 2 ≤
        (weight k) ^ 2 * (envelopeSum * weightedSquare) := by
    intro k
    have habs := suzukiDF6D4AbsDotProduct_le
      (r k) envelope x (weight k) (hr k)
    have hsumNonneg : 0 ≤ ∑ i, envelope i * |x i| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (henvelope i) (abs_nonneg _)
    have hsquare : (∑ i, x i * r k i) ^ 2 ≤
        ((∑ i, envelope i * |x i|) * weight k) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hsumNonneg (hweight k))).2 habs
    calc
      (∑ i, x i * r k i) ^ 2 ≤
          ((∑ i, envelope i * |x i|) * weight k) ^ 2 := hsquare
      _ = (∑ i, envelope i * |x i|) ^ 2 * (weight k) ^ 2 := by
        ring
      _ ≤ (envelopeSum * weightedSquare) * (weight k) ^ 2 :=
        mul_le_mul_of_nonneg_right hcauchy (sq_nonneg _)
      _ = (weight k) ^ 2 * (envelopeSum * weightedSquare) := by ring
  have hboundSummable : Summable fun k =>
      (weight k) ^ 2 * (envelopeSum * weightedSquare) :=
    hweightSummable.mul_right (envelopeSum * weightedSquare)
  have hresidualSummable : Summable fun k =>
      (∑ i, x i * r k i) ^ 2 :=
    hboundSummable.of_nonneg_of_le (fun k => sq_nonneg _) hmode
  calc
    (∑' k : Nat, (∑ i, x i * r k i) ^ 2) ≤
        ∑' k : Nat, (weight k) ^ 2 *
          (envelopeSum * weightedSquare) :=
      hresidualSummable.tsum_le_tsum hmode hboundSummable
    _ = (∑' k : Nat, (weight k) ^ 2) *
        (envelopeSum * weightedSquare) := by
      rw [tsum_mul_right]
    _ = (∑ i, envelope i) * (∑' k : Nat, (weight k) ^ 2) *
        ∑ i, envelope i * (x i) ^ 2 := by
      simp only [envelopeSum, weightedSquare]
      ring

/-- The squared order-`n^-11` weight sums to the shared inverse-22-power
tail.  This is the scalar quantity used by the even and odd geometric
remainder matrices. -/
theorem suzukiDF6D4OrderElevenWeightSquareTsum_eq (N : Nat) :
    (∑' k : Nat, (1 / (((N + 1 + k : Nat) : Real) ^ 11)) ^ 2) =
      suzukiDF6D4InversePowerTail 22 N := by
  rw [suzukiDF6D4InversePowerTail_eq_tsum_one_div]
  apply tsum_congr
  intro k
  simp only [one_div, inv_pow]
  ring

/-- A coordinatewise order-`n^-11` remainder envelope gives the exact
inverse-22-power diagonal matrix bound used by the DF6D4 scripts. -/
theorem suzukiDF6D4OrderElevenTailQuadratic_le
    {d : Nat} (r : Nat → Fin d → Real)
    (envelope : Fin d → Real) (N : Nat)
    (henvelope : ∀ i, 0 ≤ envelope i)
    (hr : ∀ k i,
      |r k i| ≤ envelope i /
        (((N + 1 + k : Nat) : Real) ^ 11))
    (x : Fin d → Real) :
    (∑' k : Nat, (∑ i, x i * r k i) ^ 2) ≤
      (∑ i, envelope i) * suzukiDF6D4InversePowerTail 22 N *
        ∑ i, envelope i * (x i) ^ 2 := by
  let weight : Nat → Real := fun k =>
    1 / (((N + 1 + k : Nat) : Real) ^ 11)
  have hweight : ∀ k, 0 ≤ weight k := by
    intro k
    positivity
  have hweightSummable : Summable fun k => (weight k) ^ 2 := by
    have hbase : Summable (fun k : Nat => 1 / ((k : Real) ^ 22)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hshift := (summable_nat_add_iff
      (f := fun k : Nat => 1 / ((k : Real) ^ 22)) (N + 1)).2 hbase
    have hpower : Summable fun k : Nat =>
        1 / (((N + 1 + k : Nat) : Real) ^ 22) := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hshift
    refine hpower.congr fun k => ?_
    simp only [weight, one_div, inv_pow]
    ring
  have hr' : ∀ k i, |r k i| ≤ envelope i * weight k := by
    intro k i
    simpa [weight, div_eq_mul_inv] using hr k i
  have hbound := suzukiDF6D4TailQuadratic_le_diagonalEnvelope
    r envelope weight henvelope hweight hr' hweightSummable x
  rw [suzukiDF6D4OrderElevenWeightSquareTsum_eq] at hbound
  exact hbound

/-- Frozen cutoff-600 form of the geometric diagonal-envelope certificate.
Concrete FT3/DF1 work only has to establish its coordinate envelopes and then
instantiate this theorem. -/
theorem suzukiDF6D4FrozenOrderElevenTailQuadratic_le
    {d : Nat} (r : Nat → Fin d → Real)
    (envelope : Fin d → Real)
    (henvelope : ∀ i, 0 ≤ envelope i)
    (hr : ∀ k i,
      |r k i| ≤ envelope i /
        (((601 + k : Nat) : Real) ^ 11))
    (x : Fin d → Real) :
    (∑' k : Nat, (∑ i, x i * r k i) ^ 2) ≤
      (∑ i, envelope i) *
          (1 / (21 * (600 : Real) ^ 21)) *
        ∑ i, envelope i * (x i) ^ 2 := by
  have htail := suzukiDF6D4OrderElevenTailQuadratic_le
    r envelope 600 henvelope (by
      intro k i
      simpa only [Nat.reduceAdd] using hr k i) x
  have henvelopeSum : 0 ≤ ∑ i, envelope i :=
    Finset.sum_nonneg fun i _ => henvelope i
  have hweightedSquare : 0 ≤ ∑ i, envelope i * (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (henvelope i) (sq_nonneg (x i))
  calc
    (∑' k : Nat, (∑ i, x i * r k i) ^ 2) ≤
        (∑ i, envelope i) * suzukiDF6D4InversePowerTail 22 600 *
          ∑ i, envelope i * (x i) ^ 2 := htail
    _ ≤ (∑ i, envelope i) *
          (1 / (21 * (600 : Real) ^ 21)) *
        ∑ i, envelope i * (x i) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          suzukiDF6D4FrozenTwentySecondPowerTail_le henvelopeSum)
        hweightedSquare

/-! ## Rank-one structured inverse-power tails -/

/-- A scalar coefficient bounded by `B / n^p` produces the sharp rank-one
quadratic tail used for each structured moment vector.  Unlike the geometric
remainder estimate, this keeps the full outer-product geometry instead of
replacing it by a diagonal envelope. -/
theorem suzukiDF6D4RankOneCoefficientTail_summable
    {d : Nat} (coefficient : Nat → Real) (vector x : Fin d → Real)
    (B : Real) (p : Nat) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hcoefficient : ∀ k,
      |coefficient k| ≤
        B / (((601 + k : Nat) : Real) ^ p)) :
    Summable fun k : Nat =>
      ((∑ i, x i * vector i) * coefficient k) ^ 2 := by
  let dot : Real := ∑ i, x i * vector i
  have hpower : Summable fun k : Nat =>
      1 / (((601 + k : Nat) : Real) ^ (2 * p)) := by
    have hexponent : 2 ≤ 2 * p := by omega
    have hbase : Summable (fun k : Nat => 1 / ((k : Real) ^ (2 * p))) :=
      Real.summable_one_div_nat_pow.mpr hexponent
    have hshift := (summable_nat_add_iff
      (f := fun k : Nat => 1 / ((k : Real) ^ (2 * p))) 601).2 hbase
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hshift
  have hmajorSummable : Summable fun k : Nat =>
      dot ^ 2 * B ^ 2 *
        (1 / (((601 + k : Nat) : Real) ^ (2 * p))) :=
    hpower.mul_left (dot ^ 2 * B ^ 2)
  apply hmajorSummable.of_nonneg_of_le (fun k => sq_nonneg _)
  intro k
  have hdenom : 0 ≤ (((601 + k : Nat) : Real) ^ p) := by positivity
  have hbound : 0 ≤ B / (((601 + k : Nat) : Real) ^ p) :=
    div_nonneg hB hdenom
  have hsquare : (coefficient k) ^ 2 ≤
      (B / (((601 + k : Nat) : Real) ^ p)) ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) hbound).2 (hcoefficient k)
  change (dot * coefficient k) ^ 2 ≤ _
  calc
    (dot * coefficient k) ^ 2 = dot ^ 2 * (coefficient k) ^ 2 := by ring
    _ ≤ dot ^ 2 * (B / (((601 + k : Nat) : Real) ^ p)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
    _ = dot ^ 2 * B ^ 2 *
        (1 / (((601 + k : Nat) : Real) ^ (2 * p))) := by
      rw [div_pow, ← pow_mul]
      ring

theorem suzukiDF6D4RankOneCoefficientTailQuadratic_le
    {d : Nat} (coefficient : Nat → Real) (vector x : Fin d → Real)
    (B : Real) (p : Nat) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hcoefficient : ∀ k,
      |coefficient k| ≤
        B / (((601 + k : Nat) : Real) ^ p)) :
    (∑' k : Nat,
      ((∑ i, x i * vector i) * coefficient k) ^ 2) ≤
      (B ^ 2 /
          (((2 * p - 1 : Nat) : Real) *
            (600 : Real) ^ (2 * p - 1))) *
        (∑ i, x i * vector i) ^ 2 := by
  let dot : Real := ∑ i, x i * vector i
  have hpower : Summable fun k : Nat =>
      1 / (((601 + k : Nat) : Real) ^ (2 * p)) := by
    have hexponent : 2 ≤ 2 * p := by omega
    have hbase : Summable (fun k : Nat => 1 / ((k : Real) ^ (2 * p))) :=
      Real.summable_one_div_nat_pow.mpr hexponent
    have hshift := (summable_nat_add_iff
      (f := fun k : Nat => 1 / ((k : Real) ^ (2 * p))) 601).2 hbase
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hshift
  have hmajorSummable : Summable fun k : Nat =>
      dot ^ 2 * B ^ 2 *
        (1 / (((601 + k : Nat) : Real) ^ (2 * p))) :=
    hpower.mul_left (dot ^ 2 * B ^ 2)
  have hpoint : ∀ k : Nat,
      (dot * coefficient k) ^ 2 ≤
        dot ^ 2 * B ^ 2 *
          (1 / (((601 + k : Nat) : Real) ^ (2 * p))) := by
    intro k
    have hdenom : 0 ≤ (((601 + k : Nat) : Real) ^ p) := by positivity
    have hbound : 0 ≤ B / (((601 + k : Nat) : Real) ^ p) :=
      div_nonneg hB hdenom
    have hsquare : (coefficient k) ^ 2 ≤
        (B / (((601 + k : Nat) : Real) ^ p)) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hbound).2 (hcoefficient k)
    calc
      (dot * coefficient k) ^ 2 = dot ^ 2 * (coefficient k) ^ 2 := by ring
      _ ≤ dot ^ 2 *
          (B / (((601 + k : Nat) : Real) ^ p)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (sq_nonneg _)
      _ = dot ^ 2 * B ^ 2 *
          (1 / (((601 + k : Nat) : Real) ^ (2 * p))) := by
        rw [div_pow, ← pow_mul]
        ring
  have hsum : Summable fun k : Nat => (dot * coefficient k) ^ 2 :=
    hmajorSummable.of_nonneg_of_le (fun k => sq_nonneg _) hpoint
  have htail := suzukiDF6D4InversePowerTail_le
    (2 * p) 600 (by omega) (by norm_num)
  have htail' :
      (∑' k : Nat, 1 / (((601 + k : Nat) : Real) ^ (2 * p))) ≤
        1 / (((2 * p - 1 : Nat) : Real) *
          (600 : Real) ^ (2 * p - 1)) := by
    rw [← suzukiDF6D4InversePowerTail_eq_tsum_one_div]
    exact htail
  calc
    (∑' k : Nat, ((∑ i, x i * vector i) * coefficient k) ^ 2) =
        ∑' k : Nat, (dot * coefficient k) ^ 2 := by rfl
    _ ≤ ∑' k : Nat,
        dot ^ 2 * B ^ 2 *
          (1 / (((601 + k : Nat) : Real) ^ (2 * p))) :=
      hsum.tsum_le_tsum hpoint hmajorSummable
    _ = (dot ^ 2 * B ^ 2) *
        (∑' k : Nat,
          1 / (((601 + k : Nat) : Real) ^ (2 * p))) := by
      rw [tsum_mul_left]
    _ ≤ (dot ^ 2 * B ^ 2) *
        (1 / (((2 * p - 1 : Nat) : Real) *
          (600 : Real) ^ (2 * p - 1))) :=
      mul_le_mul_of_nonneg_left htail'
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (B ^ 2 /
          (((2 * p - 1 : Nat) : Real) *
            (600 : Real) ^ (2 * p - 1))) *
        (∑ i, x i * vector i) ^ 2 := by
      simp only [dot]
      ring

/-! ## Exact Young splits used by the two parity certificates -/

/-- Scalar Young inequality in the coefficient convention used by the DF6D4
tail scripts. -/
theorem suzukiDF6D4YoungSquare_le
    (alpha a b : Real) (halpha : 0 < alpha) :
    (a + b) ^ 2 ≤
      (1 + alpha) * a ^ 2 + (1 + 1 / alpha) * b ^ 2 := by
  have halphaNe : alpha ≠ 0 := ne_of_gt halpha
  have hsquare : 0 ≤ (alpha * a - b) ^ 2 := sq_nonneg _
  have hmul : 2 * a * b * alpha ≤ alpha ^ 2 * a ^ 2 + b ^ 2 := by
    nlinarith
  have hcross : 2 * a * b ≤ alpha * a ^ 2 + b ^ 2 / alpha := by
    have hdiv : 2 * a * b ≤ (alpha ^ 2 * a ^ 2 + b ^ 2) / alpha :=
      (le_div_iff₀ halpha).2 hmul
    convert hdiv using 1 <;> field_simp [halphaNe]
  have hleft : (1 + alpha) * a ^ 2 = a ^ 2 + alpha * a ^ 2 := by ring
  have hright : (1 + 1 / alpha) * b ^ 2 =
      b ^ 2 + b ^ 2 / alpha := by
    field_simp [halphaNe]
  rw [hleft, hright]
  nlinarith

theorem suzukiDF6D4YoungSquareOneTenth_le (a b : Real) :
    (a + b) ^ 2 ≤ (11 / 10 : Real) * a ^ 2 + 11 * b ^ 2 := by
  have h := suzukiDF6D4YoungSquare_le (1 / 10 : Real) a b (by norm_num)
  norm_num at h ⊢
  exact h

theorem suzukiDF6D4YoungSquareOneTwentieth_le (a b : Real) :
    (a + b) ^ 2 ≤ (21 / 20 : Real) * a ^ 2 + 21 * b ^ 2 := by
  have h := suzukiDF6D4YoungSquare_le (1 / 20 : Real) a b (by norm_num)
  norm_num at h ⊢
  exact h

/-- Summable-tail form of Young's inequality.  This is the exact assembly
used first for structured-plus-geometric tails and then for
main-plus-remainder tails. -/
theorem suzukiDF6D4TailYoung_le
    (alpha : Real) (halpha : 0 < alpha)
    (u v : Nat → Real)
    (hu : Summable fun k => (u k) ^ 2)
    (hv : Summable fun k => (v k) ^ 2) :
    (∑' k : Nat, (u k + v k) ^ 2) ≤
      (1 + alpha) * (∑' k : Nat, (u k) ^ 2) +
        (1 + 1 / alpha) * (∑' k : Nat, (v k) ^ 2) := by
  have hmajor : Summable fun k =>
      (1 + alpha) * (u k) ^ 2 + (1 + 1 / alpha) * (v k) ^ 2 :=
    (hu.mul_left (1 + alpha)).add (hv.mul_left (1 + 1 / alpha))
  have hbound : ∀ k,
      (u k + v k) ^ 2 ≤
        (1 + alpha) * (u k) ^ 2 +
          (1 + 1 / alpha) * (v k) ^ 2 := fun k =>
    suzukiDF6D4YoungSquare_le alpha (u k) (v k) halpha
  have hsum : Summable fun k => (u k + v k) ^ 2 :=
    hmajor.of_nonneg_of_le (fun k => sq_nonneg _) hbound
  calc
    (∑' k : Nat, (u k + v k) ^ 2) ≤
        ∑' k : Nat,
          ((1 + alpha) * (u k) ^ 2 +
            (1 + 1 / alpha) * (v k) ^ 2) :=
      hsum.tsum_le_tsum hbound hmajor
    _ = (1 + alpha) * (∑' k : Nat, (u k) ^ 2) +
        (1 + 1 / alpha) * (∑' k : Nat, (v k) ^ 2) := by
      rw [Summable.tsum_add (hu.mul_left (1 + alpha))
        (hv.mul_left (1 + 1 / alpha)), tsum_mul_left, tsum_mul_left]

theorem suzukiDF6D4TailYoungOneTenth_le
    (u v : Nat → Real)
    (hu : Summable fun k => (u k) ^ 2)
    (hv : Summable fun k => (v k) ^ 2) :
    (∑' k : Nat, (u k + v k) ^ 2) ≤
      (11 / 10 : Real) * (∑' k : Nat, (u k) ^ 2) +
        11 * (∑' k : Nat, (v k) ^ 2) := by
  have h := suzukiDF6D4TailYoung_le
    (1 / 10 : Real) (by norm_num) u v hu hv
  norm_num at h ⊢
  exact h

theorem suzukiDF6D4TailYoungOneTwentieth_le
    (u v : Nat → Real)
    (hu : Summable fun k => (u k) ^ 2)
    (hv : Summable fun k => (v k) ^ 2) :
    (∑' k : Nat, (u k + v k) ^ 2) ≤
      (21 / 20 : Real) * (∑' k : Nat, (u k) ^ 2) +
        21 * (∑' k : Nat, (v k) ^ 2) := by
  have h := suzukiDF6D4TailYoung_le
    (1 / 20 : Real) (by norm_num) u v hu hv
  norm_num at h ⊢
  exact h

end

end RiemannHypothesisProject.Experiments.M100
