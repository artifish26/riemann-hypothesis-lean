import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianSchwartzSource
import RiemannHypothesisProject.RiemannWeilShiftedRadius.ProjectWeightEndpoints

/-!
# Polynomial-Gaussian completed-zeta zero-side summability

This module applies the proved bounded-strip rapid decay of the concrete
polynomial-Gaussian source directly to nontrivial zeta-zero arguments.  Trivial
zeroes are removed in the completed-zeta normalization.  The resulting direct
weight is absolutely summable as soon as the separately supplied closed-ball
zero-counting exponent is beaten by the freely chosen Gaussian decay order.

Unlike the generic extension-system endpoints, the analytic estimate here is
pointwise for the actual entire polynomial-Gaussian source.  No global
extension of every Schwartz test is assumed.
-/

namespace RiemannHypothesisProject

noncomputable section

/-- The completed-zeta normalized real zero weight of one concrete
polynomial-Gaussian source. -/
def guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight
    (p : Polynomial Complex) (rho : ZetaZeroSubtype) : Real := by
  classical
  exact if IsTrivialZetaZero (rho : Complex) then 0 else
    (guinandWeilPiPolynomialGaussianSource p
      (riemannWeilZeroArgument (rho : Complex))).re

/-- Bounded-strip rapid decay gives the exact shifted-radius denominator bound
at every completed-zeta normalized zero argument. -/
theorem norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius
    (p : Polynomial Complex) (k : Nat) :
    exists C : Real, 0 <= C /\
      forall rho : ZetaZeroSubtype,
        norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) <=
          C *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) := by
  rcases
      exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_horizontalStrip
        p k (A := (1 / 2 : Real)) (by norm_num) with
    ⟨C, hC⟩
  have hC_nonneg : 0 <= C := by
    have hzero := hC 0 0 (by norm_num)
    exact (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) k)).trans hzero
  refine ⟨C, hC_nonneg, ?_⟩
  intro rho
  classical
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have hfactor_nonneg :
        0 <=
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by positivity
    simpa [guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight, htrivial]
      using mul_nonneg hC_nonneg hfactor_nonneg
  · have hstrip :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    let z := riemannWeilZeroArgument (rho : Complex)
    have hz :
        ((z.re : Complex) + (z.im : Complex) * Complex.I) = z := by
      apply Complex.ext <;> simp
    have hy : |z.im| <= (1 / 2 : Real) := by
      rw [abs_le]
      exact hstrip
    have hweighted :
        norm (guinandWeilPiPolynomialGaussianSource p z) *
            (norm z + 2) ^ k <= C := by
      simpa [z, hz] using hC z.re z.im hy
    have hsource :
        norm (guinandWeilPiPolynomialGaussianSource p z) <=
          C * (1 / (norm z + 2) ^ (k : Real)) :=
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := guinandWeilPiPolynomialGaussianSource p z)
        (zeroArgument := z) (k := k) (bound := C)
        (by simpa using hweighted)
    have hre :
        norm
            ((guinandWeilPiPolynomialGaussianSource p z).re) <=
          norm (guinandWeilPiPolynomialGaussianSource p z) := by
      simpa [Real.norm_eq_abs] using
        Complex.abs_re_le_norm (guinandWeilPiPolynomialGaussianSource p z)
    simpa [guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight, htrivial,
      z] using hre.trans hsource

/-- The exact shifted-radius estimate implies the cutoff-one first-entry shell
bound used by the polynomial-cardinality p-series theorem. -/
theorem norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_closedBallShell
    (p : Polynomial Complex) (k : Nat) (C : Real) (hC : 0 <= C)
    (hshifted :
      forall rho : ZetaZeroSubtype,
        norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) <=
          C *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)))
    (rho : ZetaZeroSubtype) :
    norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) <=
      C *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let n :=
    ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho
  change
    norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho) <=
      C * (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
  have hsource := hshifted rho
  by_cases hn : 1 <= n
  · have hindex : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    have hlower :
        ComplexCompactExhaustion.closedBallZeroArgumentShellLowerBound
            ((n - 1) + 1) <
          norm (riemannWeilZeroArgument (rho : Complex)) := by
      simpa [n, hindex] using
        ComplexCompactExhaustion.closedBallZero_firstEntryIndex_argumentShellLowerBound_lt
          rho
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) <=
          (1 / |((n - 1 : Nat) : Real) + 1| ^ (k : Real)) :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
        (n - 1) (by positivity) hlower
    exact hsource.trans (mul_le_mul_of_nonneg_left hfactor hC)
  · have hn_zero : n = 0 := by omega
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) <= 1 :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_one_of_nonneg_radius
        (norm_nonneg (riemannWeilZeroArgument (rho : Complex)))
        (by positivity)
    have hprefix :
        C *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) <=
          C :=
      (mul_le_mul_of_nonneg_left hfactor hC).trans_eq (mul_one C)
    exact hsource.trans (by simpa [n, hn_zero] using hprefix)

/-- The cutoff-shifted first-entry p-series factor is bounded by the standard
tail factor as soon as the cutoff is positive.  This is the elementary
monotonicity step that lets the polynomial-Gaussian decay match published
zero-counting estimates whose natural cutoff is `2`. -/
theorem closedBallShellPSeriesFactor_add_cutoff_le
    (k n cutoff : Nat) (one_le_cutoff : 1 <= cutoff) :
    (1 /
        |((((n + cutoff) - 1 : Nat) : Real) + 1)| ^ (k : Real)) <=
      (1 / |(n : Real) + 1| ^ (k : Real)) := by
  have hone_le_sum : 1 <= n + cutoff :=
    one_le_cutoff.trans (Nat.le_add_left cutoff n)
  have hindex : (n + cutoff - 1) + 1 = n + cutoff :=
    Nat.sub_add_cancel hone_le_sum
  have hbase_pos : 0 < |(n : Real) + 1| := by
    rw [abs_of_pos]
    · positivity
    · positivity
  have hbase_le :
      |(n : Real) + 1| <=
        |(((n + cutoff - 1 : Nat) : Real) + 1)| := by
    rw [show (((n + cutoff - 1 : Nat) : Real) + 1) =
        ((n + cutoff : Nat) : Real) by exact_mod_cast hindex]
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact_mod_cast Nat.add_le_add_left one_le_cutoff n
  have hpow_le :
      |(n : Real) + 1| ^ (k : Real) <=
        |(((n + cutoff - 1 : Nat) : Real) + 1)| ^ (k : Real) :=
    Real.rpow_le_rpow (abs_nonneg ((n : Real) + 1)) hbase_le (by positivity)
  exact one_div_le_one_div_of_le
    (Real.rpow_pos_of_pos hbase_pos (k : Real)) hpow_le

/-- Absolute convergence of the actual completed-zeta normalized
polynomial-Gaussian zero side for any positive counting cutoff.  In
particular, this applies directly to the cutoff-`2` estimates obtained from
the published Riemann-von-Mangoldt sources. -/
theorem summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_one_le_cutoff
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (one_le_counting_cutoff : 1 <= counting.cutoff)
    (k : Nat)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real)) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  rcases
      norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius
        p k with
    ⟨C, hC, hshifted⟩
  let weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := weight
      cutoff := counting.cutoff
      shellBound := fun _f n =>
        C * (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => C
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hC
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hC (by positivity)
      tail_shellBound_le := by
        intro _f n
        exact mul_le_mul_of_nonneg_left
          (closedBallShellPSeriesFactor_add_cutoff_le
            k n counting.cutoff one_le_counting_cutoff)
          hC
      norm_weight_le_shellBound := by
        intro _f rho
        simpa [weight] using
          norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_closedBallShell
            p k C hC hshifted rho }
  let estimate :=
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay (by rfl)
      (fun _f => by simpa [decay] using growth_add_one_lt_k)
  have hs :=
    estimate.summable_norm_weight
      (guinandWeilPiPolynomialGaussianSchwartz p)
  change
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (weight (guinandWeilPiPolynomialGaussianSchwartz p) rho)) at hs
  simpa [weight] using hs

/-- Absolute convergence of the actual completed-zeta normalized
polynomial-Gaussian zero side.  The only external analytic input is the
separately tracked polynomial zero-counting estimate. -/
theorem summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (k : Nat)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real)) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  exact
    summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_one_le_cutoff
      p counting (by omega) k growth_add_one_lt_k

/-- The published-source parameter regime needs no freely chosen decay order:
cutoff `2` and quadratic shell growth are summable using the fourth-order
polynomial-Gaussian bound. -/
theorem summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_cutoff_two_growth_two
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (counting_growth_eq : counting.growth = 2) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p rho)) := by
  apply
    summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_one_le_cutoff
      p counting (k := 4)
  · omega
  · rw [counting_growth_eq]
    norm_num

/-- Signed summability for every positive counting cutoff follows from the
corresponding absolute-convergence theorem. -/
theorem summable_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_one_le_cutoff
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (one_le_counting_cutoff : 1 <= counting.cutoff)
    (k : Nat)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real)) :
    Summable (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p) :=
  (summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_one_le_cutoff
    p counting one_le_counting_cutoff k growth_add_one_lt_k).of_norm

/-- Signed summability in the cutoff-`2`, quadratic-growth regime delivered by
the published zero-counting adapters. -/
theorem summable_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_cutoff_two_growth_two
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (counting_growth_eq : counting.growth = 2) :
    Summable (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p) :=
  (summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_of_cutoff_two_growth_two
    p counting counting_cutoff_eq counting_growth_eq).of_norm

/-- Signed summability follows from absolute summability. -/
theorem summable_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight
    (p : Polynomial Complex)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (k : Nat)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real)) :
    Summable (guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight p) :=
  (summable_norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight
    p counting counting_cutoff_eq k growth_add_one_lt_k).of_norm

end

end RiemannHypothesisProject
