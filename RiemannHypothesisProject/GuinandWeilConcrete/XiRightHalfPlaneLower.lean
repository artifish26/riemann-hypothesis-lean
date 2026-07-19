import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import RiemannHypothesisProject.GuinandWeilConcrete.ArchimedeanGaussianBounds
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightVertical

/-!
# Quantitative lower bounds for xi on a right vertical line

This module proves a uniform lower bound for the zeta factor on `re s = 3`,
an exponential reciprocal bound for the Archimedean factor, and combines
them with the exact right-half-plane product for Riemann's xi function.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Complex

noncomputable section

/-- The Dirichlet series gives a uniform numerical lower bound for zeta on
the vertical line `re s = 3`. -/
theorem norm_riemannZeta_three_add_I_mul_ge_quarter (T : Real) :
    (1 / 4 : Real) <=
      norm (riemannZeta ((3 : Complex) + Complex.I * T)) := by
  let s : Complex := (3 : Complex) + Complex.I * T
  have hs : 1 < s.re := by simp [s]
  have hsum : Summable (fun n : Nat => 1 / (n + 1 : Complex) ^ s) := by
    have hbase := Complex.summable_one_div_nat_cpow.mpr hs
    have hshift := (summable_nat_add_iff 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using hshift
  have htail :
      riemannZeta s - 1 = ∑' n : Nat, 1 / (n + 2 : Complex) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_add, one_cpow, div_one]
    ring_nf
    apply tsum_congr
    intro n
    congr 2
    push_cast
    ring
  have htwoTail : HasSum (fun n : Nat => 1 / (n + 2 : Real) ^ 2)
      (Real.pi ^ 2 / 6 - 1) := by
    have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_two
    have hvalue :
        Real.pi ^ 2 / 6 - ∑ i ∈ Finset.range 2, 1 / (i : Real) ^ 2 =
          Real.pi ^ 2 / 6 - 1 := by
      norm_num [Finset.sum_range_succ]
    rw [← hvalue]
    refine h.congr ?_
    intro n
    norm_num
  have hnormTerm (n : Nat) :
      norm (1 / (n + 2 : Complex) ^ s) = 1 / (n + 2 : Real) ^ 3 := by
    rw [show (n + 2 : Complex) = ((n + 2 : Nat) : Complex) by norm_num]
    rw [norm_div, norm_one,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 2)]
    simp [s]
  have hcubic : Summable (fun n : Nat => 1 / (n + 2 : Real) ^ 3) := by
    let f : Nat → Real := fun n => 1 / (n : Real) ^ 3
    have hf : Summable f :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hshift : Summable (fun n => f (n + 2)) :=
      (summable_nat_add_iff 2).mpr hf
    simpa only [f, Nat.cast_add, Nat.cast_ofNat] using hshift
  have htermLe (n : Nat) :
      1 / (n + 2 : Real) ^ 3 <= 1 / (n + 2 : Real) ^ 2 := by
    have hn : (1 : Real) <= n + 2 := by
      exact_mod_cast (by omega : 1 <= n + 2)
    have hnpos : 0 < (n + 2 : Real) := lt_of_lt_of_le zero_lt_one hn
    rw [div_le_div_iff_of_pos_left one_pos (pow_pos hnpos 3) (pow_pos hnpos 2)]
    nlinarith [sq_nonneg (n + 2 : Real)]
  have htailNorm : norm (riemannZeta s - 1) <= Real.pi ^ 2 / 6 - 1 := by
    rw [htail]
    calc
      norm (∑' n : Nat, 1 / (n + 2 : Complex) ^ s) <=
          ∑' n : Nat, norm (1 / (n + 2 : Complex) ^ s) := by
        apply norm_tsum_le_tsum_norm
        simpa only [hnormTerm] using hcubic
      _ = ∑' n : Nat, 1 / (n + 2 : Real) ^ 3 := by
        congr 1
        funext n
        exact hnormTerm n
      _ <= ∑' n : Nat, 1 / (n + 2 : Real) ^ 2 := by
        exact hcubic.tsum_le_tsum htermLe htwoTail.summable
      _ = Real.pi ^ 2 / 6 - 1 := htwoTail.tsum_eq
  have hpi : Real.pi ^ 2 / 6 - 1 < 3 / 4 := by
    nlinarith [Real.pi_pos, Real.pi_lt_d2]
  have hreverse : (1 : Real) - norm (riemannZeta s - 1) <=
      norm (riemannZeta s) := by
    have h := norm_add_le ((1 : Complex) - riemannZeta s) (riemannZeta s)
    have hone : (1 : Complex) - riemannZeta s + riemannZeta s = 1 := by ring
    rw [hone, norm_one, norm_sub_rev] at h
    linarith
  rw [show (3 : Complex) + Complex.I * T = s by rfl]
  linarith

/-- The reciprocal Deligne Gamma factor has exponential growth on
`1 + iT`. -/
theorem exists_pos_const_norm_GammaR_oneLine_inv_le_exp :
    exists C : Real, 0 < C /\ forall T : Real,
      norm (Complex.Gammaℝ ((1 : Complex) + Complex.I * T))⁻¹ <=
        C * Real.exp (Real.pi * (abs T + 1)) := by
  obtain ⟨A, hA, hGamma⟩ := exists_pos_const_norm_Gamma_inv_halfLine_le_exp
  refine ⟨Real.sqrt Real.pi * A, mul_pos (Real.sqrt_pos.2 Real.pi_pos) hA, ?_⟩
  intro T
  let s : Complex := (1 : Complex) + Complex.I * T
  have hfactor :
      norm (((Real.pi : Complex) ^ (-s / 2))⁻¹) = Real.sqrt Real.pi := by
    have hexponent : -s / 2 =
        (-1 / 2 : Complex) - ((T / 2 : Real) : Complex) * Complex.I := by
      dsimp only [s]
      push_cast
      ring
    have hre : (-s / 2).re = -(1 / 2 : Real) := by
      rw [hexponent]
      norm_num
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    rw [hre, Real.rpow_neg Real.pi_nonneg, one_div, inv_inv,
      Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hhalf : abs (T / 2) <= abs T := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
    exact div_le_self (abs_nonneg T) (by norm_num)
  have hexp : Real.exp (Real.pi * (abs (T / 2) + 1)) <=
      Real.exp (Real.pi * (abs T + 1)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
  have hGamma' :
      norm (Complex.Gamma (s / 2))⁻¹ <=
        A * Real.exp (Real.pi * (abs T + 1)) := by
    have harg : s / 2 =
        (1 / 2 : Complex) + ((T / 2 : Real) : Complex) * Complex.I := by
      dsimp only [s]
      apply Complex.ext <;> simp
    rw [harg]
    exact (hGamma (T / 2)).trans
      (mul_le_mul_of_nonneg_left hexp hA.le)
  rw [Complex.Gammaℝ_def, mul_inv, norm_mul, hfactor]
  calc
    Real.sqrt Real.pi * norm (Complex.Gamma (s / 2))⁻¹ <=
        Real.sqrt Real.pi *
          (A * Real.exp (Real.pi * (abs T + 1))) :=
      mul_le_mul_of_nonneg_left hGamma' (Real.sqrt_nonneg _)
    _ = Real.sqrt Real.pi * A *
        Real.exp (Real.pi * (abs T + 1)) := by ring

/-- Shifting by two transfers the preceding reciprocal bound to `3 + iT`. -/
theorem exists_pos_const_norm_GammaR_threeLine_inv_le_exp :
    exists C : Real, 0 < C /\ forall T : Real,
      norm (Complex.Gammaℝ ((3 : Complex) + Complex.I * T))⁻¹ <=
        C * Real.exp (Real.pi * (abs T + 1)) := by
  obtain ⟨A, hA, hGamma⟩ := exists_pos_const_norm_GammaR_oneLine_inv_le_exp
  refine ⟨2 * Real.pi * A, by positivity, ?_⟩
  intro T
  let s : Complex := (1 : Complex) + Complex.I * T
  have hs : s ≠ 0 := by
    intro hzero
    have h := congrArg Complex.re hzero
    simp [s] at h
  have hsNorm : 1 <= norm s := by
    calc
      1 <= abs s.re := by simp [s]
      _ <= norm s := Complex.abs_re_le_norm s
  have hrepr : (3 : Complex) + Complex.I * T = s + 2 := by
    dsimp only [s]
    ring
  rw [hrepr, Complex.Gammaℝ_add_two hs]
  have hinv : (Complex.Gammaℝ s * s / 2 / (Real.pi : Complex))⁻¹ =
      (Real.pi : Complex) * 2 * s⁻¹ * (Complex.Gammaℝ s)⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hinv, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_ofNat]
  calc
    Real.pi * 2 * norm s⁻¹ * norm (Complex.Gammaℝ s)⁻¹ <=
        Real.pi * 2 * 1 * norm (Complex.Gammaℝ s)⁻¹ := by
      gcongr
      rw [norm_inv]
      exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hsNorm)).mpr hsNorm
    _ <= Real.pi * 2 * 1 *
        (A * Real.exp (Real.pi * (abs T + 1))) := by
      gcongr
      simpa only [s] using hGamma T
    _ = (2 * Real.pi * A) * Real.exp (Real.pi * (abs T + 1)) := by
      ring

/-- Riemann's xi function has an explicit exponential reciprocal majorant on
the right vertical line `3 + iT`. -/
theorem exists_pos_const_norm_riemannXi_threeLine_inv_le_exp :
    exists C : Real, 0 < C /\ forall T : Real,
      norm (riemannXi ((3 : Complex) + Complex.I * T))⁻¹ <=
        C * Real.exp (Real.pi * (abs T + 1)) := by
  obtain ⟨A, hA, hGamma⟩ := exists_pos_const_norm_GammaR_threeLine_inv_le_exp
  refine ⟨8 * A, by positivity, ?_⟩
  intro T
  let s : Complex := (3 : Complex) + Complex.I * T
  have hsre : 1 < s.re := by simp [s]
  have hsNorm : 1 <= norm s := by
    calc
      1 <= abs s.re := by simp [s]
      _ <= norm s := Complex.abs_re_le_norm s
  have hsSubNorm : 1 <= norm (s - 1) := by
    calc
      1 <= abs (s - 1).re := by simp [s]; norm_num
      _ <= norm (s - 1) := Complex.abs_re_le_norm (s - 1)
  have hzeta : (1 / 4 : Real) <= norm (riemannZeta s) := by
    simpa only [s] using norm_riemannZeta_three_add_I_mul_ge_quarter T
  have hsInv : norm s⁻¹ <= 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hsNorm)).mpr hsNorm
  have hsSubInv : norm (s - 1)⁻¹ <= 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hsSubNorm)).mpr hsSubNorm
  have hzetaInv : norm (riemannZeta s)⁻¹ <= 4 := by
    rw [norm_inv]
    rw [show (4 : Real) = 1 / (1 / 4) by norm_num]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1 / 4) hzeta)
  rw [riemannXi_eq_polynomial_mul_GammaR_mul_riemannZeta hsre]
  have hinv :
      (s * (s - 1) * Complex.Gammaℝ s * riemannZeta s / 2)⁻¹ =
        2 * (riemannZeta s)⁻¹ * (Complex.Gammaℝ s)⁻¹ *
          (s - 1)⁻¹ * s⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  rw [hinv, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofNat]
  have hGammaStep :
      2 * norm (riemannZeta s)⁻¹ * norm (Complex.Gammaℝ s)⁻¹ *
          norm (s - 1)⁻¹ * norm s⁻¹ <=
        2 * norm (riemannZeta s)⁻¹ *
          (A * Real.exp (Real.pi * (abs T + 1))) *
            norm (s - 1)⁻¹ * norm s⁻¹ := by
    gcongr
    simpa only [s] using hGamma T
  calc
    2 * norm (riemannZeta s)⁻¹ * norm (Complex.Gammaℝ s)⁻¹ *
          norm (s - 1)⁻¹ * norm s⁻¹ <=
        2 * norm (riemannZeta s)⁻¹ *
          (A * Real.exp (Real.pi * (abs T + 1))) *
            norm (s - 1)⁻¹ * norm s⁻¹ := hGammaStep
    _ <= 2 * 4 * (A * Real.exp (Real.pi * (abs T + 1))) * 1 * 1 := by
      gcongr
    _ = (8 * A) * Real.exp (Real.pi * (abs T + 1)) := by
      ring

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
