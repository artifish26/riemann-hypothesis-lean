import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.GaussDigamma

/-!
# The reciprocal-series bridge for Gauss's digamma integral

This module identifies the combined Gauss kernel with the limit of its finite
geometric expansions.  The endpoint theorem is deliberately stated as a
limit of natural partial sums; absolute summability and analyticity belong to
the subsequent source-identity layer.
-/

open Filter MeasureTheory

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- A shifted form of the elementary complex-power integral. -/
theorem integral_Ioo_cpow {s : Complex} (hs : -1 < s.re) :
    (∫ x : Real in Set.Ioo 0 1, (x : Complex) ^ s) = 1 / (s + 1) := by
  have h := integral_Ioo_cpow_sub_one (z := s + 1) (by
    rw [Complex.add_re, Complex.one_re]
    linarith)
  convert h using 1 <;> ring

/-- Integrability companion to `integral_Ioo_cpow`. -/
theorem integrableOn_Ioo_cpow {s : Complex} (hs : -1 < s.re) :
    IntegrableOn (fun x : Real => (x : Complex) ^ s) (Set.Ioo (0 : Real) 1) :=
  (intervalIntegral.integrableOn_Ioo_cpow_iff (by norm_num)).2 hs

/-- The classical reciprocal term in Gauss's series for the digamma
function. -/
def gaussDigammaSeriesTerm (z : Complex) (k : Nat) : Complex :=
  1 / (k + 1 : Complex) - 1 / (z + k)

/-- The finite geometric expansion of Gauss's combined kernel. -/
def gaussDigammaPartialIntegrand (z : Complex) (n : Nat) (x : Real) : Complex :=
  ∑ k ∈ Finset.range n,
    ((x : Complex) ^ (k : Complex) - (x : Complex) ^ (z + k - 1))

/-- On `(0,1)`, the finite expansion is the Gauss kernel multiplied by its
geometric cutoff. -/
theorem gaussDigammaPartialIntegrand_eq_mul
    (z : Complex) (n : Nat) {x : Real} (hx : x ∈ Set.Ioo (0 : Real) 1) :
    gaussDigammaPartialIntegrand z n x =
      gaussDigammaIntegrand z x * (1 - (x : Complex) ^ n) := by
  have hx0 : (x : Complex) ≠ 0 := by
    exact_mod_cast hx.1.ne'
  have hx1 : (1 - (x : Complex)) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hx.2.ne')
  rw [gaussDigammaPartialIntegrand, Finset.sum_sub_distrib]
  have hnat :
      (∑ k ∈ Finset.range n, (x : Complex) ^ (k : Complex)) =
        ∑ k ∈ Finset.range n, (x : Complex) ^ k := by
    apply Finset.sum_congr rfl
    intro k _
    exact Complex.cpow_natCast _ _
  have hfactor :
      (∑ k ∈ Finset.range n, (x : Complex) ^ (z + k - 1)) =
        (x : Complex) ^ (z - 1) *
          ∑ k ∈ Finset.range n, (x : Complex) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hx0]
    congr 1
    push_cast
    ring
  rw [hnat, hfactor, gaussDigammaIntegrand]
  have hgeom := geom_sum_mul_neg (x : Complex) n
  field_simp [hx1]
  linear_combination (1 - (x : Complex) ^ (z - 1)) * hgeom

/-- Each finite geometric expansion is integrable on the source interval. -/
theorem integrableOn_gaussDigammaPartialIntegrand
    {z : Complex} (hz : 0 < z.re) (n : Nat) :
    IntegrableOn (gaussDigammaPartialIntegrand z n) (Set.Ioo (0 : Real) 1) := by
  apply integrable_finsetSum (Finset.range n)
  intro k _
  apply Integrable.sub
  · apply integrableOn_Ioo_cpow
    simp only [Complex.natCast_re]
    exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
  · apply integrableOn_Ioo_cpow
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
    linarith

/-- A single finite kernel term integrates to the corresponding reciprocal
difference. -/
theorem integral_gaussDigammaPartialTerm
    {z : Complex} (hz : 0 < z.re) (k : Nat) :
    (∫ x : Real in Set.Ioo 0 1,
      ((x : Complex) ^ (k : Complex) - (x : Complex) ^ (z + k - 1))) =
        gaussDigammaSeriesTerm z k := by
  have hk : -1 < ((k : Nat) : Complex).re := by
    simp only [Complex.natCast_re]
    exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
  have hzk : -1 < (z + (k : Complex) - 1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
    linarith
  rw [integral_sub (integrableOn_Ioo_cpow hk) (integrableOn_Ioo_cpow hzk),
    integral_Ioo_cpow hk, integral_Ioo_cpow hzk, gaussDigammaSeriesTerm]
  congr 2 <;> push_cast <;> ring

/-- The integral of a finite geometric expansion is its reciprocal partial
sum. -/
theorem integral_gaussDigammaPartialIntegrand
    {z : Complex} (hz : 0 < z.re) (n : Nat) :
    (∫ x : Real in Set.Ioo 0 1, gaussDigammaPartialIntegrand z n x) =
      ∑ k ∈ Finset.range n, gaussDigammaSeriesTerm z k := by
  simp only [gaussDigammaPartialIntegrand]
  rw [integral_finsetSum (Finset.range n) (fun k _ => by
      apply Integrable.sub
      · apply integrableOn_Ioo_cpow
        simp only [Complex.natCast_re]
        exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg k)
      · apply integrableOn_Ioo_cpow
        simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
        have hk0 : (0 : Real) ≤ (k : Real) := Nat.cast_nonneg k
        linarith)]
  apply Finset.sum_congr rfl
  intro k _
  exact integral_gaussDigammaPartialTerm hz k

/-- The finite geometric expansions converge under the integral sign to the
combined Gauss kernel. -/
theorem tendsto_integral_gaussDigammaPartialIntegrand
    {z : Complex} (hz : 0 < z.re) :
    Tendsto
      (fun n : Nat =>
        ∫ x : Real in Set.Ioo 0 1, gaussDigammaPartialIntegrand z n x)
      atTop
      (nhds (∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand z x)) := by
  have hgauss := integrableOn_gaussDigammaIntegrand hz
  apply tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Ioo (0 : Real) 1))
    (fun x : Real => 2 * ‖gaussDigammaIntegrand z x‖)
  · intro n
    exact (integrableOn_gaussDigammaPartialIntegrand hz n).aestronglyMeasurable
  · exact hgauss.norm.const_mul 2
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [gaussDigammaPartialIntegrand_eq_mul z n hx, norm_mul]
    have hxnorm : ‖(x : Complex)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2.le
    have hcutoff : ‖1 - (x : Complex) ^ n‖ ≤ 2 := by
      calc
        ‖1 - (x : Complex) ^ n‖ ≤ ‖(1 : Complex)‖ + ‖(x : Complex) ^ n‖ :=
          norm_sub_le _ _
        _ = 1 + ‖(x : Complex)‖ ^ n := by rw [norm_one, norm_pow]
        _ ≤ 1 + 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hxnorm
        _ = 2 := by norm_num
    nlinarith [norm_nonneg (gaussDigammaIntegrand z x)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have heq :
        (fun n : Nat => gaussDigammaPartialIntegrand z n x) =
          (fun n : Nat => gaussDigammaIntegrand z x * (1 - (x : Complex) ^ n)) := by
      funext n
      exact gaussDigammaPartialIntegrand_eq_mul z n hx
    rw [heq]
    have hxnorm : ‖(x : Complex)‖ < 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2
    have hpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hxnorm
    have hcutoff :
        Tendsto (fun n : Nat => 1 - (x : Complex) ^ n) atTop (nhds (1 : Complex)) := by
      convert
        (show Tendsto (fun _ : Nat => (1 : Complex)) atTop (nhds (1 : Complex)) from
          tendsto_const_nhds).sub hpow using 1 <;> simp
    have hconstant :
        Tendsto (fun _ : Nat => gaussDigammaIntegrand z x) atTop
          (nhds (gaussDigammaIntegrand z x)) :=
      tendsto_const_nhds
    simpa using hconstant.mul hcutoff

/-- Gauss's integral is the limit of the classical reciprocal partial sums. -/
theorem tendsto_gaussDigammaSeriesPartialSum
    {z : Complex} (hz : 0 < z.re) :
    Tendsto
      (fun n : Nat => ∑ k ∈ Finset.range n, gaussDigammaSeriesTerm z k)
      atTop
      (nhds (∫ x : Real in Set.Ioo 0 1, gaussDigammaIntegrand z x)) := by
  apply (tendsto_integral_gaussDigammaPartialIntegrand hz).congr'
  filter_upwards with n
  exact integral_gaussDigammaPartialIntegrand hz n

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
