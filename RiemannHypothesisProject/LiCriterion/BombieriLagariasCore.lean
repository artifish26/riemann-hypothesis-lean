import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Core power estimates for the Bombieri-Lagarias criterion

This module contains the two elementary ingredients used in the
Bombieri-Lagarias dominant-modulus argument: simultaneous recurrence of a
finite family of unit-circle powers, and a quadratic remainder estimate for
`w ^ n` around `w = 1`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Filter
open scoped Topology

noncomputable section

/-- A finite family of points on the unit circle has a sequence of common
positive powers tending to `1`; the exponents tend to infinity. -/
theorem exists_tendsto_unitCircle_powers_one
    {kappa : Type*} [Fintype kappa]
    (z : kappa -> Circle) :
    exists exponent : Nat -> Nat,
      Tendsto exponent atTop atTop /\
        Tendsto (fun n j => z j ^ exponent n) atTop
          (nhds (1 : kappa -> Circle)) := by
  let powers : Nat -> kappa -> Circle := fun n j => z j ^ n
  obtain ⟨a, phi, hphi_mono, hphi⟩ := CompactSpace.tendsto_subseq powers
  let exponent : Nat -> Nat := fun n => phi (2 * n) - phi n
  have hphi_two : Tendsto (fun n => powers (phi (2 * n))) atTop (nhds a) := by
    have hle : forall n : Nat, n <= 2 * n := by
      intro n
      omega
    have htwo : Tendsto (fun n : Nat => 2 * n) atTop atTop :=
      tendsto_atTop_mono hle tendsto_id
    exact hphi.comp htwo
  have hquotient :
      Tendsto (fun n => powers (phi (2 * n)) * (powers (phi n))⁻¹) atTop
        (nhds (a * a⁻¹)) :=
    hphi_two.mul hphi.inv
  have hquotient_one :
      Tendsto (fun n => powers (phi (2 * n)) * (powers (phi n))⁻¹) atTop
        (nhds (1 : kappa -> Circle)) := by
    simpa using hquotient
  have hpow_eq : forall n : Nat,
      powers (phi (2 * n)) * (powers (phi n))⁻¹ =
        fun j => z j ^ exponent n := by
    intro n
    funext j
    change z j ^ phi (2 * n) * (z j ^ phi n)⁻¹ = z j ^ exponent n
    rw [← pow_sub]
    exact hphi_mono.monotone (by omega)
  have h_exponent_atTop : Tendsto exponent atTop atTop := by
    apply tendsto_atTop_mono' atTop
    . filter_upwards [eventually_gt_atTop 0] with n hn
      change n <= phi (2 * n) - phi n
      apply Nat.le_sub_of_add_le
      have hstep_aux : forall m d : Nat, phi m + d <= phi (m + d) := by
        intro m d
        induction d with
        | zero => simp
        | succ d ih =>
            have hmono_step : phi (m + d) + 1 <= phi (m + (d + 1)) := by
              exact Nat.succ_le_of_lt (hphi_mono (by omega))
            omega
      have hstep : phi n + n <= phi (n + n) := hstep_aux n n
      simpa [two_mul, add_comm] using hstep
    . exact tendsto_id
  refine ⟨exponent, h_exponent_atTop, ?_⟩
  simpa only [hpow_eq] using hquotient_one

/-- The second-order remainder of the power map around `1`. -/
def bombieriLagariasPowerRemainder (w : Complex) (n : Nat) : Complex :=
  w ^ n - 1 - (n : Complex) * (w - 1)

/-- Recurrence for the second-order power remainder. -/
theorem bombieriLagariasPowerRemainder_succ (w : Complex) (n : Nat) :
    bombieriLagariasPowerRemainder w (n + 1) =
      w * bombieriLagariasPowerRemainder w n +
        (n : Complex) * (w - 1) ^ 2 := by
  unfold bombieriLagariasPowerRemainder
  rw [pow_succ]
  push_cast
  ring

/-- A deliberately loose quadratic estimate, uniform for `w` in a fixed
closed disk. -/
theorem norm_bombieriLagariasPowerRemainder_le
    (w : Complex) (q : Real) (hq_one : 1 <= q) (hw : norm w <= q)
    (n : Nat) :
    norm (bombieriLagariasPowerRemainder w n) <=
      (n : Real) ^ 2 * q ^ n * norm (w - 1) ^ 2 := by
  induction n with
  | zero => simp [bombieriLagariasPowerRemainder]
  | succ n ih =>
      rw [bombieriLagariasPowerRemainder_succ]
      calc
        norm (w * bombieriLagariasPowerRemainder w n +
            (n : Complex) * (w - 1) ^ 2) <=
            norm (w * bombieriLagariasPowerRemainder w n) +
              norm ((n : Complex) * (w - 1) ^ 2) := norm_add_le _ _
        _ = norm w * norm (bombieriLagariasPowerRemainder w n) +
              (n : Real) * norm (w - 1) ^ 2 := by
            rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_pow]
            norm_num
        _ <= q * ((n : Real) ^ 2 * q ^ n * norm (w - 1) ^ 2) +
              (n : Real) * norm (w - 1) ^ 2 := by
            gcongr
        _ <= ((n + 1 : Nat) : Real) ^ 2 * q ^ (n + 1) *
              norm (w - 1) ^ 2 := by
            have hqpow : 1 <= q ^ (n + 1) := one_le_pow₀ hq_one
            have hn_nonneg : 0 <= (n : Real) := Nat.cast_nonneg n
            have hn_le : (n : Real) <= 2 * (n : Real) + 1 := by linarith
            have hfactor_nonneg : 0 <= 2 * (n : Real) + 1 := by linarith
            have hn_le_mul :
                (n : Real) <= (2 * (n : Real) + 1) * q ^ (n + 1) :=
              hn_le.trans (le_mul_of_one_le_right hfactor_nonneg hqpow)
            have hscalar :
                q * ((n : Real) ^ 2 * q ^ n) + (n : Real) <=
                  ((n + 1 : Nat) : Real) ^ 2 * q ^ (n + 1) := by
              calc
                q * ((n : Real) ^ 2 * q ^ n) + (n : Real) =
                    (n : Real) ^ 2 * q ^ (n + 1) + (n : Real) := by
                  rw [pow_succ]
                  ring
                _ <= (n : Real) ^ 2 * q ^ (n + 1) +
                    (2 * (n : Real) + 1) * q ^ (n + 1) :=
                  by
                    simpa [add_comm] using
                      (add_le_add_left hn_le_mul
                        ((n : Real) ^ 2 * q ^ (n + 1)))
                _ = ((n + 1 : Nat) : Real) ^ 2 * q ^ (n + 1) := by
                  push_cast
                  ring
            calc
              q * ((n : Real) ^ 2 * q ^ n * norm (w - 1) ^ 2) +
                  (n : Real) * norm (w - 1) ^ 2 =
                  (q * ((n : Real) ^ 2 * q ^ n) + (n : Real)) *
                    norm (w - 1) ^ 2 := by ring
              _ <= (((n + 1 : Nat) : Real) ^ 2 * q ^ (n + 1)) *
                    norm (w - 1) ^ 2 :=
                mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)
              _ = ((n + 1 : Nat) : Real) ^ 2 * q ^ (n + 1) *
                    norm (w - 1) ^ 2 := by ring

/-- The real Li summand is controlled by its linear real part and the
quadratic power remainder. -/
theorem abs_one_sub_pow_re_le
    (u : Complex) (q : Real) (hq_one : 1 <= q)
    (hw : norm (1 + u) <= q) (n : Nat) :
    abs ((1 - (1 + u) ^ n).re) <=
      (n : Real) * abs u.re +
        (n : Real) ^ 2 * q ^ n * norm u ^ 2 := by
  have hremainder :=
    norm_bombieriLagariasPowerRemainder_le (1 + u) q hq_one hw n
  have hdecomp :
      (1 - (1 + u) ^ n).re =
        -(n : Real) * u.re -
          (bombieriLagariasPowerRemainder (1 + u) n).re := by
    unfold bombieriLagariasPowerRemainder
    simp
    ring
  rw [hdecomp]
  calc
    abs (-(n : Real) * u.re -
        (bombieriLagariasPowerRemainder (1 + u) n).re) <=
        abs (-(n : Real) * u.re) +
          abs (bombieriLagariasPowerRemainder (1 + u) n).re :=
      abs_sub _ _
    _ = (n : Real) * abs u.re +
          abs (bombieriLagariasPowerRemainder (1 + u) n).re := by
      rw [abs_mul]
      simp
    _ <= (n : Real) * abs u.re +
        norm (bombieriLagariasPowerRemainder (1 + u) n) := by
      gcongr
      exact Complex.abs_re_le_norm _
    _ <= (n : Real) * abs u.re +
        (n : Real) ^ 2 * q ^ n * norm ((1 + u) - 1) ^ 2 := by
      gcongr
    _ = (n : Real) * abs u.re +
        (n : Real) ^ 2 * q ^ n * norm u ^ 2 := by ring_nf

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
