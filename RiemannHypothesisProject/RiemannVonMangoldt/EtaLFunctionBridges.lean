import RiemannHypothesisProject.RiemannVonMangoldt.EtaPartialSumBrackets

/-!
# Eta L-function and boundary bridges

This module contains eta L-function identities, ZMod boundary-value equivalences, regularized Hurwitz-tail gap formulas, and bridge constructors upstream of the final zeta endpoint surface.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section
/--
Pointwise form of the remaining `ZMod 2` boundary theorem.

After the checked sign convention, identifying the nontrivial mod-2 additive
character boundary value with `expZeta` is exactly the same as identifying the
canonical eta alternating value with Mathlib's mod-2 eta `LFunction`.
-/
theorem zmodTwoAdditiveCharacterBoundaryValue_eq_expZeta_iff_etaAlternatingValue_eq_lFunction
    {x : Real} (hx : 0 < x) :
    zmodAdditiveCharacterBoundaryValue
        (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx =
        HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) <->
      (dirichletEtaAlternatingValue x : Complex) =
        dirichletEtaLFunction (x : Complex) := by
  have hboundary :=
    zmodTwoAdditiveCharacterBoundaryValue_eq_neg_dirichletEtaAlternatingValue
      (x := x) hx
  constructor
  · intro hvalue
    calc
      (dirichletEtaAlternatingValue x : Complex) =
          -zmodAdditiveCharacterBoundaryValue
            (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx := by
            rw [hboundary]
            simp
      _ = -HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) := by
            rw [hvalue]
      _ = dirichletEtaLFunction (x : Complex) := by
            rw [<- dirichletEtaLFunction_eq_neg_expZeta_modTwo]
  · intro heta
    calc
      zmodAdditiveCharacterBoundaryValue
          (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx =
          -(dirichletEtaAlternatingValue x : Complex) := hboundary
      _ = -dirichletEtaLFunction (x : Complex) := by
            rw [heta]
      _ = HurwitzZeta.expZeta
          (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) := by
            rw [dirichletEtaLFunction_eq_neg_expZeta_modTwo]
            simp

/--
Away from `0`, the eta L-function is the completed mod-2 L-function divided by
the real gamma factor.  This is Mathlib's even-character completed-L relation
specialized to the eta parity coefficient.
-/
theorem dirichletEtaLFunction_eq_completedLFunction_div_Gamma_of_ne_zero
    {s : Complex} (hs : s ≠ 0) :
    dirichletEtaLFunction s =
      ZMod.completedLFunction dirichletEtaParity s / Complex.Gammaℝ s := by
  change ZMod.LFunction dirichletEtaParity s =
    ZMod.completedLFunction dirichletEtaParity s / Complex.Gammaℝ s
  exact ZMod.LFunction_eq_completed_div_gammaFactor_even
    dirichletEtaParity_even s (Or.inl hs)

/--
On `(0, 1)`, the eta L-function can be read through Mathlib's completed
mod-2 L-function.
-/
theorem dirichletEtaLFunction_eq_completedLFunction_div_Gamma_of_openUnitInterval
    {x : Real} (hx_pos : 0 < x) :
    dirichletEtaLFunction (x : Complex) =
      ZMod.completedLFunction dirichletEtaParity (x : Complex) /
        Complex.Gammaℝ (x : Complex) := by
  exact dirichletEtaLFunction_eq_completedLFunction_div_Gamma_of_ne_zero
    (by exact_mod_cast hx_pos.ne')

/--
Mathlib's completed-L functional equation, specialized to the mod-2 eta
parity coefficient.
-/
theorem dirichletEtaCompletedLFunction_one_sub {s : Complex} (hs : s ≠ 1) :
    ZMod.completedLFunction dirichletEtaParity (1 - s) =
      (2 : Complex) ^ (s - 1) *
        ZMod.completedLFunction (ZMod.dft dirichletEtaParity) s := by
  exact ZMod.completedLFunction_one_sub_even
    dirichletEtaParity_even s (Or.inr dirichletEtaParity_sum_eq_zero)
    (Or.inl hs)

/-- The Fourier transform of the eta parity coefficient vanishes at residue `0`. -/
theorem dirichletEtaParity_dft_zero :
    ZMod.dft dirichletEtaParity (0 : ZMod 2) = 0 := by
  rw [ZMod.dft_apply_zero, dirichletEtaParity_sum_eq_zero]

/-- The Fourier transform of the eta parity coefficient has value `-2` at residue `1`. -/
theorem dirichletEtaParity_dft_one :
    ZMod.dft dirichletEtaParity (1 : ZMod 2) = -2 := by
  rw [ZMod.dft_apply]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by
    ext j
    fin_cases j
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl rfl
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr rfl]
  have hchar : ZMod.stdAddChar (1 : ZMod 2) = (-1 : Complex) := by
    rw [show (1 : ZMod 2) = ((1 : Int) : ZMod 2) by rfl]
    rw [ZMod.stdAddChar_coe]
    norm_num
    rw [show 2 * (Real.pi : Complex) * Complex.I / 2 =
      (Real.pi : Complex) * Complex.I by ring]
    exact Complex.exp_pi_mul_I
  simp [dirichletEtaParity, hchar]
  norm_num

/-- The full two-point Fourier transform of the eta parity coefficient. -/
theorem dirichletEtaParity_dft_eq :
    ZMod.dft dirichletEtaParity =
      fun j : ZMod 2 => if j = 0 then 0 else (-2 : Complex) := by
  funext j
  by_cases hj0 : j = 0
  · subst j
    simp [dirichletEtaParity_dft_zero]
  · have hj1 : j = 1 := by
      fin_cases j
      · exact False.elim (hj0 rfl)
      · rfl
    subst j
    simp [dirichletEtaParity_dft_one]

/--
Completed-L functional equation for eta with the finite Fourier transform
computed explicitly.
-/
theorem dirichletEtaCompletedLFunction_one_sub_explicitDft
    {s : Complex} (hs : s ≠ 1) :
    ZMod.completedLFunction dirichletEtaParity (1 - s) =
      (2 : Complex) ^ (s - 1) *
        ZMod.completedLFunction
          (fun j : ZMod 2 => if j = 0 then 0 else (-2 : Complex)) s := by
  rw [dirichletEtaCompletedLFunction_one_sub hs, dirichletEtaParity_dft_eq]

/--
The L-function of the Fourier-transformed eta parity coefficient is the
nonzero mod-2 exponential zeta branch minus the Riemann zeta branch.
-/
theorem dirichletEtaDftLFunction_eq_expZeta_sub_riemannZeta
    {s : Complex} (hs : s ≠ 1) :
    ZMod.LFunction (ZMod.dft dirichletEtaParity) s =
      HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s -
        riemannZeta s := by
  rw [ZMod.LFunction_dft dirichletEtaParity (Or.inr hs)]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by
    ext j
    fin_cases j
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inl rfl
    · simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      exact Or.inr rfl]
  simp [dirichletEtaParity, HurwitzZeta.expZeta_zero,
    sub_eq_add_neg, add_comm]

/--
The Fourier-transformed eta coefficient has no `0`-residue term, so its
completed-L/gamma relation holds without excluding `s = 0`.
-/
theorem dirichletEtaDftLFunction_eq_completedLFunction_div_Gamma
    (s : Complex) :
    ZMod.LFunction (ZMod.dft dirichletEtaParity) s =
      ZMod.completedLFunction (ZMod.dft dirichletEtaParity) s /
        Complex.Gammaℝ s := by
  exact ZMod.LFunction_eq_completed_div_gammaFactor_even
    (ZMod.dft_even_iff.mpr dirichletEtaParity_even) s
    (Or.inr dirichletEtaParity_dft_zero)

/--
Where the real gamma factor is nonzero, the completed L-function of the
Fourier-transformed eta coefficient is an explicit gamma multiple of an
`expZeta - zeta` difference.
-/
theorem dirichletEtaCompletedDft_eq_Gamma_mul_expZeta_sub_riemannZeta
    {s : Complex} (hgamma : Complex.Gammaℝ s ≠ 0) (hs : s ≠ 1) :
    ZMod.completedLFunction (ZMod.dft dirichletEtaParity) s =
      Complex.Gammaℝ s *
        (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s -
          riemannZeta s) := by
  calc
    ZMod.completedLFunction (ZMod.dft dirichletEtaParity) s =
        (ZMod.completedLFunction (ZMod.dft dirichletEtaParity) s /
          Complex.Gammaℝ s) * Complex.Gammaℝ s := by
          rw [div_mul_cancel₀ _ hgamma]
    _ = (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s -
          riemannZeta s) * Complex.Gammaℝ s := by
          rw [← dirichletEtaDftLFunction_eq_completedLFunction_div_Gamma,
            dirichletEtaDftLFunction_eq_expZeta_sub_riemannZeta hs]
    _ = Complex.Gammaℝ s *
        (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) s -
          riemannZeta s) := by
          ring

/--
On the open real interval `(0, 1)`, the completed transform side in the eta
functional equation has the concrete `Gammaℝ * (expZeta - zeta)` form.
-/
theorem dirichletEtaCompletedDft_eq_Gamma_mul_expZeta_sub_riemannZeta_of_openUnitInterval
    {x : Real} (hx_pos : 0 < x) (hx_lt_one : x < 1) :
    ZMod.completedLFunction (ZMod.dft dirichletEtaParity) (x : Complex) =
      Complex.Gammaℝ (x : Complex) *
        (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) -
          riemannZeta (x : Complex)) := by
  exact dirichletEtaCompletedDft_eq_Gamma_mul_expZeta_sub_riemannZeta
    (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hx_pos))
    (by
      intro h
      have hx_eq_one : x = 1 := by
        have hre := congrArg Complex.re h
        simpa using hre
      linarith)

/--
Concrete completed functional equation for eta on the open real interval:
the transformed side is expressed using the nonzero mod-2 exponential zeta
branch and the ordinary Riemann zeta function.
-/
theorem dirichletEtaCompletedLFunction_one_sub_expZeta_sub_riemannZeta_of_openUnitInterval
    {x : Real} (hx_pos : 0 < x) (hx_lt_one : x < 1) :
    ZMod.completedLFunction dirichletEtaParity (1 - (x : Complex)) =
      (2 : Complex) ^ ((x : Complex) - 1) *
        Complex.Gammaℝ (x : Complex) *
          (HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) -
            riemannZeta (x : Complex)) := by
  rw [dirichletEtaCompletedLFunction_one_sub
    (by
      intro h
      have hx_eq_one : x = 1 := by
        have hre := congrArg Complex.re h
        simpa using hre
      linarith),
    dirichletEtaCompletedDft_eq_Gamma_mul_expZeta_sub_riemannZeta_of_openUnitInterval
      hx_pos hx_lt_one]
  ring

/--
On the half-plane of absolute convergence, the eta L-function agrees with its
Dirichlet series.
-/
theorem dirichletEtaLFunction_eq_LSeries_of_one_lt_re {s : Complex}
    (hs : 1 < s.re) :
    dirichletEtaLFunction s =
      LSeries (fun n : Nat => dirichletEtaParity (n : ZMod 2)) s := by
  simpa [dirichletEtaLFunction] using
    (ZMod.LFunction_eq_LSeries dirichletEtaParity hs)

/--
Mathlib's summation-by-parts integral representation specialized to the
eta-parity coefficient system.

The new input is the exact `0/1` prefix cancellation
`dirichletEtaParity_Icc_one_sum_eq_if`, which supplies the `O(n^0)` hypothesis.
-/
theorem dirichletEtaParity_LSeries_eq_floorPrefixIntegral_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    LSeries (fun n : Nat => dirichletEtaParity (n : ZMod 2)) s =
      s * ∫ t in Set.Ioi (1 : Real),
        (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else 1) *
          (t : Complex) ^ (-(s + 1)) := by
  let etaCoeff : Nat -> Complex := fun n =>
    dirichletEtaParity (n : ZMod 2)
  change LSeries etaCoeff s =
    s * ∫ t in Set.Ioi (1 : Real),
      (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else 1) *
        (t : Complex) ^ (-(s + 1))
  have hS : LSeriesSummable etaCoeff s := by
    simpa [etaCoeff] using
      (ZMod.LSeriesSummable_of_one_lt_re dirichletEtaParity hs)
  have hO :
      (fun n : Nat =>
        ∑ k ∈ Finset.Icc 1 n, etaCoeff k) =O[atTop]
        fun n : Nat => (n : Real) ^ (0 : Real) := by
    simpa [etaCoeff] using
      dirichletEtaParity_Icc_one_partialSums_isBigO_rpow_zero
  calc
    LSeries etaCoeff s =
        s * ∫ t in Set.Ioi (1 : Real),
          (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, etaCoeff k) *
            (t : Complex) ^ (-(s + 1)) :=
          LSeries_eq_mul_integral etaCoeff
            (r := (0 : Real)) (by norm_num)
            (s := s) (by linarith) hS hO
    _ =
        s * ∫ t in Set.Ioi (1 : Real),
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else 1) *
            (t : Complex) ^ (-(s + 1)) := by
          congr 1
          refine setIntegral_congr_fun measurableSet_Ioi ?_
          intro t _
          simp [etaCoeff, dirichletEtaParity_Icc_one_floor_sum_eq_if]

/-- The mod-2 eta L-function has the eta-parity prefix integral on `1 < re s`. -/
theorem dirichletEtaLFunction_eq_floorPrefixIntegral_of_one_lt_re
    {s : Complex} (hs : 1 < s.re) :
    dirichletEtaLFunction s =
      s * ∫ t in Set.Ioi (1 : Real),
        (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else 1) *
          (t : Complex) ^ (-(s + 1)) := by
  rw [dirichletEtaLFunction_eq_LSeries_of_one_lt_re hs,
    dirichletEtaParity_LSeries_eq_floorPrefixIntegral_of_one_lt_re hs]

/--
Right-half-plane canary for the exact odd-floor kernel that remains to be
identified with the continued eta value on `0 < x < 1`.
-/
theorem dirichletEtaLFunction_eq_floorParityKernelIntegral_of_one_lt
    {x : Real} (hx : 1 < x) :
    dirichletEtaLFunction (x : Complex) =
      ∫ t in Set.Ioi (1 : Real),
        (-(x : Complex)) * (t : Complex) ^ (-(x : Complex) - 1) *
          (if ⌊t⌋₊ % 2 = 0 then (0 : Complex) else -1) := by
  rw [dirichletEtaLFunction_eq_floorPrefixIntegral_of_one_lt_re
    (s := (x : Complex)) (by simpa using hx)]
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t _
  by_cases hparity : ⌊t⌋₊ % 2 = 0
  · simp [hparity]
  · simp [hparity, show -((x : Complex) + 1) = -(x : Complex) - 1 by ring]

/--
The positive-indexed eta-parity L-series term is the shifted eta alternating
series term.

Mathlib's `LSeries.term` is indexed by positive natural numbers, with the
`0`th term set to `0`; the project eta series is indexed from `0`.  This lemma
checks the normalization bridge `m = n + 1`.
-/
theorem dirichletEtaParity_lseriesTerm_succ_eq_etaComplexSeriesTerm
    (x : Real) (n : Nat) :
    LSeries.term (fun m : Nat => dirichletEtaParity (m : ZMod 2))
        (x : Complex) (n + 1) =
      dirichletEtaComplexSeriesTerm x n := by
  have hn_ne : n + 1 ≠ 0 := by omega
  have hparity :
      dirichletEtaParity (((n + 1 : Nat) : ZMod 2)) =
        (-1 : Complex) ^ n :=
    dirichletEtaParity_natCast_succ n
  have hbase_nonneg : 0 <= (n : Real) + 1 := by positivity
  have hcast_base :
      ((n + 1 : Nat) : Complex) = (((n : Real) + 1 : Real) : Complex) := by
    norm_num
  have hpow :
      ((n + 1 : Nat) : Complex) ^ (-(x : Complex)) =
        (((n : Real) + 1) ^ (-x) : Real) := by
    rw [hcast_base]
    rw [show -(x : Complex) = ((-x : Real) : Complex) by simp]
    exact (Complex.ofReal_cpow hbase_nonneg (-x)).symm
  rw [LSeries.term_of_ne_zero hn_ne, div_eq_mul_inv, <- Complex.cpow_neg,
    hparity, hpow]
  simp [dirichletEtaComplexSeriesTerm, dirichletEtaSeriesTerm]

/-- The eta complex series is ordinarily summable on the half-plane `1 < x`. -/
theorem summable_dirichletEtaComplexSeriesTerm_of_one_lt
    {x : Real} (hx : 1 < x) :
    Summable (dirichletEtaComplexSeriesTerm x) := by
  have h_lseries :
      Summable
        (LSeries.term (fun n : Nat => dirichletEtaParity (n : ZMod 2))
          (x : Complex)) := by
    simpa [LSeriesSummable] using
      (ZMod.LSeriesSummable_of_one_lt_re dirichletEtaParity
        (by simpa using hx))
  have hshift :
      Summable fun n : Nat =>
        LSeries.term (fun m : Nat => dirichletEtaParity (m : ZMod 2))
          (x : Complex) (Nat.succ n) :=
    h_lseries.comp_injective Nat.succ_injective
  simpa only [Nat.succ_eq_add_one,
    dirichletEtaParity_lseriesTerm_succ_eq_etaComplexSeriesTerm]
    using hshift

/--
On the half-plane of absolute convergence, the ordinary eta alternating-series
sum agrees with the checked mod-2 eta L-function.

This does not solve the `(0, 1)` Abel boundary theorem; it verifies the same
normalization on the side where ordinary L-series convergence is available.
-/
theorem tsum_dirichletEtaComplexSeriesTerm_eq_dirichletEtaLFunction_of_one_lt
    {x : Real} (hx : 1 < x) :
    (∑' n : Nat, dirichletEtaComplexSeriesTerm x n) =
      dirichletEtaLFunction (x : Complex) := by
  let etaCoeff : Nat -> Complex := fun n => dirichletEtaParity (n : ZMod 2)
  have h_lseries :
      Summable (LSeries.term etaCoeff (x : Complex)) := by
    simpa [etaCoeff, LSeriesSummable] using
      (ZMod.LSeriesSummable_of_one_lt_re dirichletEtaParity
        (by simpa using hx))
  have hshift :
      (∑' n : Nat,
          LSeries.term etaCoeff (x : Complex) (n + 1)) =
        ∑' n : Nat, dirichletEtaComplexSeriesTerm x n := by
    apply tsum_congr
    intro n
    simpa [etaCoeff] using
      dirichletEtaParity_lseriesTerm_succ_eq_etaComplexSeriesTerm x n
  have hdecomp :
      (∑' n : Nat, LSeries.term etaCoeff (x : Complex) n) =
        ∑' n : Nat, dirichletEtaComplexSeriesTerm x n := by
    rw [h_lseries.tsum_eq_zero_add]
    simp only [LSeries.term_zero, zero_add]
    exact hshift
  have hlfunction :
      dirichletEtaLFunction (x : Complex) =
        LSeries etaCoeff (x : Complex) := by
    simpa [etaCoeff] using
      dirichletEtaLFunction_eq_LSeries_of_one_lt_re
        (s := (x : Complex)) (by simpa using hx)
  calc
    (∑' n : Nat, dirichletEtaComplexSeriesTerm x n) =
        LSeries etaCoeff (x : Complex) := by
      simpa [LSeries] using hdecomp.symm
    _ = dirichletEtaLFunction (x : Complex) :=
      hlfunction.symm

/--
On the absolutely convergent side, the canonical conditional eta value agrees
with the ordinary eta series sum.
-/
theorem dirichletEtaAlternatingValue_eq_tsum_complex_of_one_lt
    {x : Real} (hx : 1 < x) :
    (dirichletEtaAlternatingValue x : Complex) =
      ∑' n : Nat, dirichletEtaComplexSeriesTerm x n := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hcanonical :=
    dirichletEtaAlternatingValue_hasSum_conditional_complex hx_pos
  have hsummable := summable_dirichletEtaComplexSeriesTerm_of_one_lt hx
  have hordinary :
      HasSum (dirichletEtaComplexSeriesTerm x)
        (∑' n : Nat, dirichletEtaComplexSeriesTerm x n)
        (SummationFilter.conditional Nat) :=
    hsummable.hasSum.mono_left
      (SummationFilter.conditional Nat).le_atTop
  exact hcanonical.unique hordinary

/--
Complex-valued right-half-plane canary for the remaining eta value theorem.

This names the stronger complex equality behind the existing real-part canary:
on `1 < x`, ordinary absolute convergence identifies the canonical eta
alternating value with Mathlib's mod-2 eta `LFunction`.
-/
theorem dirichletEtaAlternatingValue_eq_lFunction_complex_of_one_lt
    {x : Real} (hx : 1 < x) :
    (dirichletEtaAlternatingValue x : Complex) =
      dirichletEtaLFunction (x : Complex) := by
  rw [dirichletEtaAlternatingValue_eq_tsum_complex_of_one_lt hx,
    tsum_dirichletEtaComplexSeriesTerm_eq_dirichletEtaLFunction_of_one_lt hx]

/--
Source-shaped `ZMod 2` right-half-plane canary for the remaining boundary
theorem.
-/
theorem zmodTwoAdditiveCharacterBoundaryValue_eq_expZeta_of_one_lt
    {x : Real} (hx : 1 < x) :
    zmodAdditiveCharacterBoundaryValue
        (N := 2) (j := (1 : ZMod 2)) (by decide)
        (x := x) (lt_trans zero_lt_one hx) =
      HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
        (x : Complex) := by
  exact
    (zmodTwoAdditiveCharacterBoundaryValue_eq_expZeta_iff_etaAlternatingValue_eq_lFunction
      (x := x) (lt_trans zero_lt_one hx)).2
      (dirichletEtaAlternatingValue_eq_lFunction_complex_of_one_lt hx)

/--
Right-half-plane canary for the remaining eta boundary theorem: when `1 < x`,
the project's canonical alternating eta value is the real part of Mathlib's
mod-2 eta L-function.

The hard blocker is to prove the analogous statement on `0 < x < 1`, where it
is no longer an ordinary absolutely convergent L-series identity and requires
the Abel/continuation boundary theorem.
-/
theorem dirichletEtaAlternatingValue_eq_lFunction_re_of_one_lt
    {x : Real} (hx : 1 < x) :
    dirichletEtaAlternatingValue x =
      (dirichletEtaLFunction (x : Complex)).re := by
  have hcomplex :
      (dirichletEtaAlternatingValue x : Complex) =
        dirichletEtaLFunction (x : Complex) := by
    rw [dirichletEtaAlternatingValue_eq_tsum_complex_of_one_lt hx,
      tsum_dirichletEtaComplexSeriesTerm_eq_dirichletEtaLFunction_of_one_lt hx]
  simpa using congrArg Complex.re hcomplex

/--
Right-half-plane complex conditional-sum canary for the remaining eta theorem.

This is the `1 < x` analogue of
`OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula`: the same
conditional summation filter already gives the Mathlib mod-2 L-function value
when ordinary absolute convergence is available.
-/
theorem dirichletEtaComplexConditional_tsum_eq_lFunction_of_one_lt
    {x : Real} (hx : 1 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaComplexSeriesTerm x n) =
      dirichletEtaLFunction (x : Complex) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  rw [dirichletEtaComplexConditional_tsum_eq_alternatingValue hx_pos,
    dirichletEtaAlternatingValue_eq_tsum_complex_of_one_lt hx,
    tsum_dirichletEtaComplexSeriesTerm_eq_dirichletEtaLFunction_of_one_lt hx]

/--
Right-half-plane real conditional-sum canary for the remaining eta theorem.

This is the `1 < x` analogue of
`OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula`.
-/
theorem dirichletEtaConditional_tsum_eq_lFunction_re_of_one_lt
    {x : Real} (hx : 1 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaSeriesTerm x n) =
      (dirichletEtaLFunction (x : Complex)).re := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  rw [dirichletEtaConditional_tsum_eq_alternatingValue hx_pos]
  exact dirichletEtaAlternatingValue_eq_lFunction_re_of_one_lt hx

/--
Right-half-plane Abel-boundary canary for the remaining eta theorem.

This has exactly the same Abel-damped power series and approach filter as
`OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula`, but it is proved on
`1 < x`, where ordinary absolute convergence already identifies the eta series
with Mathlib's mod-2 L-function.
-/
theorem dirichletEtaAbelPowerSeries_tendsto_lFunction_of_one_lt
    {x : Real} (hx : 1 < x) :
    Tendsto
      (fun z : Complex =>
        ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
      ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
      (nhds (dirichletEtaLFunction (x : Complex))) := by
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hAbel := dirichletEtaAbelPowerSeries_tendsto_alternatingValue hx_pos
  have htarget :
      (dirichletEtaAlternatingValue x : Complex) =
        dirichletEtaLFunction (x : Complex) := by
    rw [dirichletEtaAlternatingValue_eq_tsum_complex_of_one_lt hx,
      tsum_dirichletEtaComplexSeriesTerm_eq_dirichletEtaLFunction_of_one_lt hx]
  simpa [htarget] using hAbel

/--
Right-half-plane source-shaped value canary for the remaining eta theorem.

This rewrites the checked `1 < x` eta value identity into the same negative
exponential-zeta target used by the source-shaped `ZMod 2` boundary theorem.
-/
theorem dirichletEtaAlternatingValue_eq_neg_expZeta_modTwo_re_of_one_lt
    {x : Real} (hx : 1 < x) :
    dirichletEtaAlternatingValue x =
      (-HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
        (x : Complex)).re := by
  calc
    dirichletEtaAlternatingValue x =
        (dirichletEtaLFunction (x : Complex)).re :=
      dirichletEtaAlternatingValue_eq_lFunction_re_of_one_lt hx
    _ =
        (-HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
          (x : Complex)).re := by
      rw [dirichletEtaLFunction_eq_neg_expZeta_modTwo]

/--
Right-half-plane complex conditional-sum canary in the source-shaped
negative-exponential-zeta normalization.

The open-unit-interval blocker asks for this normalization after Abel
continuation rather than absolute convergence.
-/
theorem dirichletEtaComplexConditional_tsum_eq_neg_expZeta_modTwo_of_one_lt
    {x : Real} (hx : 1 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaComplexSeriesTerm x n) =
      -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
        (x : Complex) := by
  calc
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaComplexSeriesTerm x n) =
        dirichletEtaLFunction (x : Complex) :=
      dirichletEtaComplexConditional_tsum_eq_lFunction_of_one_lt hx
    _ =
        -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
          (x : Complex) :=
      dirichletEtaLFunction_eq_neg_expZeta_modTwo (x : Complex)

/--
Right-half-plane real conditional-sum canary in the source-shaped
negative-exponential-zeta normalization.
-/
theorem dirichletEtaConditional_tsum_eq_neg_expZeta_modTwo_re_of_one_lt
    {x : Real} (hx : 1 < x) :
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaSeriesTerm x n) =
      (-HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
        (x : Complex)).re := by
  calc
    (∑'[SummationFilter.conditional Nat] n : Nat,
      dirichletEtaSeriesTerm x n) =
        (dirichletEtaLFunction (x : Complex)).re :=
      dirichletEtaConditional_tsum_eq_lFunction_re_of_one_lt hx
    _ =
        (-HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
          (x : Complex)).re := by
      rw [dirichletEtaLFunction_eq_neg_expZeta_modTwo]

/--
Right-half-plane Abel-boundary canary in the source-shaped negative
exponential-zeta normalization.

This is the exact `1 < x` analogue of
`OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula`.
-/
theorem dirichletEtaAbelPowerSeries_tendsto_neg_expZeta_modTwo_of_one_lt
    {x : Real} (hx : 1 < x) :
    Tendsto
      (fun z : Complex =>
        ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
      ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
      (nhds
        (-HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2))
          (x : Complex))) := by
  simpa [dirichletEtaLFunction_eq_neg_expZeta_modTwo] using
    dirichletEtaAbelPowerSeries_tendsto_lFunction_of_one_lt hx

/-- On even indices, the eta-parity L-series term is the negative zeta term. -/
theorem dirichletEtaParity_even_lseriesTerm (s : Complex) (k : Nat) :
    LSeries.term (fun n : Nat => dirichletEtaParity (n : ZMod 2)) s (2 * k) =
      -LSeries.term (fun _ : Nat => (1 : Complex)) s (2 * k) := by
  rcases k with _ | k
  · simp
  · have hne : 2 * (k + 1) ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero hne, LSeries.term_of_ne_zero hne]
    have hcast : (((2 * (k + 1) : Nat) : ZMod 2)) = 0 := by
      rw [Nat.cast_mul]
      exact mul_eq_zero_of_left (by decide : (2 : ZMod 2) = 0) _
    simp [hcast, div_eq_mul_inv]

/-- On odd indices, the eta-parity L-series term agrees with the zeta term. -/
theorem dirichletEtaParity_odd_lseriesTerm (s : Complex) (k : Nat) :
    LSeries.term (fun n : Nat => dirichletEtaParity (n : ZMod 2)) s (2 * k + 1) =
      LSeries.term (fun _ : Nat => (1 : Complex)) s (2 * k + 1) := by
  have hne : 2 * k + 1 ≠ 0 := by omega
  rw [LSeries.term_of_ne_zero hne, LSeries.term_of_ne_zero hne]
  have hcast : (((2 * k + 1 : Nat) : ZMod 2)) = 1 := by
    rw [Nat.cast_add, Nat.cast_mul]
    change (2 : ZMod 2) * (k : ZMod 2) + (1 : ZMod 2) = 1
    rw [mul_eq_zero_of_left (by decide : (2 : ZMod 2) = 0)]
    simp
  simp [hcast]

/--
The even-indexed zeta L-series term is `2^(-s)` times the corresponding
ordinary zeta L-series term.
-/
theorem lseries_one_even_lseriesTerm (s : Complex) (k : Nat) :
    LSeries.term (fun _ : Nat => (1 : Complex)) s (2 * k) =
      (2 : Complex) ^ (-s) *
        LSeries.term (fun _ : Nat => (1 : Complex)) s k := by
  rcases k with _ | k
  · simp
  · have hk : k + 1 ≠ 0 := by omega
    have h2k : 2 * (k + 1) ≠ 0 := by omega
    rw [LSeries.term_of_ne_zero h2k, LSeries.term_of_ne_zero hk]
    rw [Complex.cpow_neg]
    rw [show ((2 * (k + 1) : Nat) : Complex) ^ s =
        (2 : Complex) ^ s * ((k + 1 : Nat) : Complex) ^ s by
      simpa using Complex.natCast_mul_natCast_cpow 2 (k + 1) s]
    field_simp [Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by norm_num : (2 : Complex) ≠ 0)),
      Complex.cpow_ne_zero_iff.mpr
        (Or.inl (by exact_mod_cast hk :
          ((k + 1 : Nat) : Complex) ≠ 0))]

/-- The even-indexed zeta subseries is `2^(-s) * zeta(s)` on `1 < re s`. -/
theorem lseries_one_evenSubseries_eq {s : Complex} (hs : 1 < s.re) :
    (∑' k : Nat, LSeries.term (fun _ : Nat => (1 : Complex)) s (2 * k)) =
      (2 : Complex) ^ (-s) * riemannZeta s := by
  calc
    (∑' k : Nat, LSeries.term (fun _ : Nat => (1 : Complex)) s (2 * k))
        = ∑' k : Nat,
            (2 : Complex) ^ (-s) *
              LSeries.term (fun _ : Nat => (1 : Complex)) s k := by
          exact tsum_congr (lseries_one_even_lseriesTerm s)
    _ = (2 : Complex) ^ (-s) *
          (∑' k : Nat, LSeries.term (fun _ : Nat => (1 : Complex)) s k) := by
          rw [tsum_mul_left]
    _ = (2 : Complex) ^ (-s) *
          LSeries (fun _ : Nat => (1 : Complex)) s := rfl
    _ = (2 : Complex) ^ (-s) * riemannZeta s := by
          change (2 : Complex) ^ (-s) * LSeries (1 : Nat → Complex) s =
            (2 : Complex) ^ (-s) * riemannZeta s
          rw [LSeries_one_eq_riemannZeta hs]

/-- The mod-2 eta L-function is complex differentiable everywhere. -/
theorem differentiable_dirichletEtaLFunction :
    Differentiable Complex dirichletEtaLFunction := by
  change Differentiable Complex (ZMod.LFunction dirichletEtaParity)
  exact ZMod.differentiable_LFunction_of_sum_zero
    dirichletEtaParity_sum_eq_zero

/-- The mod-2 eta L-function is analytic at every complex point. -/
theorem analyticAt_dirichletEtaLFunction (s : Complex) :
    AnalyticAt Complex dirichletEtaLFunction s :=
  differentiable_dirichletEtaLFunction.analyticAt s

/--
Source-shaped identification of the real alternating eta value with the
mod-2 eta L-function on `(0, 1)`.

This is now separated from the zeta multiplier identity, so future work can
attack the Abel/continuation step independently.
-/
def OpenUnitIntervalDirichletEtaLFunctionValueFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        dirichletEtaAlternatingValue x =
          (dirichletEtaLFunction (x : Complex)).re

/--
Conditional-sum form of the eta boundary-value theorem on `(0, 1)`.

This is the same mathematical content as
`OpenUnitIntervalDirichletEtaLFunctionValueFormula`, but it exposes the exact
summation filter that future Abel-limit work should target.
-/
def OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        (∑'[SummationFilter.conditional Nat] n : Nat,
          dirichletEtaSeriesTerm x n) =
          (dirichletEtaLFunction (x : Complex)).re

/--
Complex conditional-sum form of the eta boundary-value theorem on `(0, 1)`.

This is the natural target for an Abel theorem: the conditional eta series
should be the boundary value of the analytic mod-2 eta L-function.
-/
def OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        (∑'[SummationFilter.conditional Nat] n : Nat,
          dirichletEtaComplexSeriesTerm x n) =
          dirichletEtaLFunction (x : Complex)

/--
Abel-boundary form of the remaining eta theorem.

For each `0 < x < 1`, the Abel-damped eta power series should tend to the
mod-2 eta L-function value as the damping parameter approaches `1` from the
left.  Mathlib's Abel theorem then converts this boundary statement into the
conditional-sum statement above.
-/
def OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        Tendsto
          (fun z : Complex =>
            ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
          ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
          (nhds (dirichletEtaLFunction (x : Complex)))

/--
Hurwitz-zeta form of the Abel-boundary eta theorem.  The target value is the
explicit mod-2 Hurwitz combination unfolded from Mathlib's `ZMod.LFunction`.
-/
def OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        Tendsto
          (fun z : Complex =>
            ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
          ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
          (nhds (dirichletEtaHurwitzModTwoValue (x : Complex)))

/--
Exponential-zeta form of the Abel-boundary eta theorem.  Since the eta
coefficient is negative the nontrivial additive character on `ZMod 2`, this is
equivalent to the L-function and Hurwitz formulations above.
-/
def OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        Tendsto
          (fun z : Complex =>
            ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
          ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
          (nhds (-HurwitzZeta.expZeta
            (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex)))

/--
The general nonzero additive-character Abel-boundary theorem specializes to
the eta exponential-zeta boundary theorem at the nontrivial character of
`ZMod 2`.
-/
theorem openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula := by
  intro x hx_pos hx_lt_one
  have hsource :=
    hadd 2 (1 : ZMod 2) (by decide) x hx_pos hx_lt_one
  have hfun :
      (fun z : Complex =>
        ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n) =
        fun z : Complex =>
          -(∑' n : Nat,
            zmodAdditiveCharacterAbelSeriesTerm (1 : ZMod 2) x n * z ^ n) := by
    funext z
    calc
      (∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n) =
          ∑' n : Nat,
            -(zmodAdditiveCharacterAbelSeriesTerm (1 : ZMod 2) x n * z ^ n) := by
            refine tsum_congr ?_
            intro n
            rw [
              dirichletEtaComplexSeriesTerm_eq_neg_zmodTwoAdditiveCharacterAbelSeriesTerm
                x n]
            ring
      _ =
          -(∑' n : Nat,
            zmodAdditiveCharacterAbelSeriesTerm (1 : ZMod 2) x n * z ^ n) := by
            rw [tsum_neg]
  rw [hfun]
  simpa using hsource.neg

/--
The checked-boundary-value additive-character theorem supplies the eta
exponential-zeta Abel-boundary theorem through the equivalent reusable
additive-character Abel-limit source theorem.
-/
theorem openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
    (zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_boundaryValue hvalue)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem supplies the eta
exponential-zeta Abel-boundary theorem directly.
-/
theorem openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula := by
  intro x hx_pos hx_lt_one
  have hvalue_x := hvalue x hx_pos hx_lt_one
  have hboundary_x :=
    zmodTwoAdditiveCharacterBoundaryValue_eq_neg_dirichletEtaAlternatingValue
      (x := x) hx_pos
  have htarget :
      -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) =
        (dirichletEtaAlternatingValue x : Complex) := by
    rw [← hvalue_x, hboundary_x]
    simp
  simpa [htarget] using dirichletEtaAbelPowerSeries_tendsto_alternatingValue hx_pos

/--
Conversely, the eta exponential-zeta Abel-boundary theorem identifies the
checked `ZMod 2` boundary value with the analytic continuation value.  Thus the
remaining eta-route theorem can be stated either as an Abel-boundary theorem or
as the source-shaped checked-boundary-value equality.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_etaExpZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  intro x hx_pos hx_lt_one
  have hAbel :
      Tendsto
        (fun z : Complex =>
          ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
        ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
        (nhds (dirichletEtaAlternatingValue x : Complex)) :=
    dirichletEtaAbelPowerSeries_tendsto_alternatingValue hx_pos
  have hExp := hexp x hx_pos hx_lt_one
  have heta :
      (dirichletEtaAlternatingValue x : Complex) =
        -HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) :=
    tendsto_nhds_unique hAbel hExp
  have hboundary :=
    zmodTwoAdditiveCharacterBoundaryValue_eq_neg_dirichletEtaAlternatingValue
      (x := x) hx_pos
  calc
    zmodAdditiveCharacterBoundaryValue
        (N := 2) (j := (1 : ZMod 2)) (by decide) (x := x) hx_pos =
        -(dirichletEtaAlternatingValue x : Complex) := by
          simpa using hboundary
    _ = HurwitzZeta.expZeta
        (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) := by
          rw [heta]
          simp

/--
The eta exponential-zeta Abel-boundary theorem and the source-shaped `ZMod 2`
checked-boundary-value theorem are equivalent.
-/
theorem openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  ⟨zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_etaExpZetaBoundary,
    openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodTwoBoundaryValue⟩

/-- The Hurwitz-boundary theorem supplies the L-function boundary theorem. -/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_hurwitzBoundary
    (hhurwitz : OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula) :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula := by
  intro x hx_pos hx_lt_one
  simpa [dirichletEtaLFunction_eq_hurwitzZeta_modTwo] using
    hhurwitz x hx_pos hx_lt_one

/-- The L-function boundary theorem supplies the explicit Hurwitz-boundary form. -/
theorem openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_lFunctionBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula := by
  intro x hx_pos hx_lt_one
  simpa [dirichletEtaLFunction_eq_hurwitzZeta_modTwo] using
    habel x hx_pos hx_lt_one

/-- The L-function and explicit Hurwitz formulations of the Abel-boundary theorem coincide. -/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_hurwitzBoundary :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula <->
      OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula :=
  ⟨openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_lFunctionBoundary,
    openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_hurwitzBoundary⟩

/-- The exponential-zeta boundary theorem supplies the L-function boundary theorem. -/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula := by
  intro x hx_pos hx_lt_one
  simpa [dirichletEtaLFunction_eq_neg_expZeta_modTwo] using
    hexp x hx_pos hx_lt_one

/-- The L-function boundary theorem supplies the exponential-zeta boundary form. -/
theorem openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_lFunctionBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula := by
  intro x hx_pos hx_lt_one
  simpa [dirichletEtaLFunction_eq_neg_expZeta_modTwo] using
    habel x hx_pos hx_lt_one

/-- The L-function and exponential-zeta formulations of the Abel-boundary theorem coincide. -/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_expZetaBoundary :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula <->
      OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula :=
  ⟨openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_lFunctionBoundary,
    openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary⟩

/--
The L-function Abel-boundary theorem is equivalent to the source-shaped `ZMod 2`
checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  constructor
  · intro habel
    exact
      zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_etaExpZetaBoundary
        (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_lFunctionBoundary
          habel)
  · intro hvalue
    exact
      openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary
        (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodTwoBoundaryValue
          hvalue)

/--
The explicit Hurwitz Abel-boundary theorem is equivalent to the source-shaped
`ZMod 2` checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  constructor
  · intro hhurwitz
    exact
      (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_zmodTwoBoundaryValue).1
        (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_hurwitzBoundary
          hhurwitz)
  · intro hvalue
    exact
      openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_lFunctionBoundary
        ((openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_zmodTwoBoundaryValue).2
          hvalue)

/--
The reusable nonzero additive-character Abel theorem supplies the eta
L-function boundary theorem through its `ZMod 2` specialization.
-/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The checked-boundary-value additive-character theorem also supplies the eta
L-function Abel-boundary theorem, via its equivalent Abel-limit formulation.
-/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_zmodAdditiveCharacter
    (zmodAdditiveCharacterAbelExpZetaBoundaryFormula_of_boundaryValue hvalue)

/--
The checked-boundary-value additive-character theorem also supplies the explicit
Hurwitz-boundary eta formulation.
-/
theorem openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula :=
  openUnitIntervalDirichletEtaAbelHurwitzBoundaryFormula_of_lFunctionBoundary
    (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_zmodBoundaryValue
      hvalue)

/--
Mathlib's Abel limit theorem turns the Abel-boundary eta theorem into the
complex conditional-sum boundary theorem.
-/
theorem openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_abelBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula := by
  intro x hx_pos hx_lt_one
  have hAbel :
      Tendsto
        (fun z : Complex =>
          ∑' n : Nat, dirichletEtaComplexSeriesTerm x n * z ^ n)
        ((nhdsWithin (1 : Real) (Set.Iio 1)).map Complex.ofReal)
        (nhds (dirichletEtaAlternatingValue x : Complex)) :=
    dirichletEtaAbelPowerSeries_tendsto_alternatingValue hx_pos
  have hBoundary := habel x hx_pos hx_lt_one
  have hvalue :
      dirichletEtaLFunction (x : Complex) =
        (dirichletEtaAlternatingValue x : Complex) :=
    tendsto_nhds_unique hBoundary hAbel
  rw [dirichletEtaComplexConditional_tsum_eq_alternatingValue hx_pos]
  exact hvalue.symm

/--
The complex conditional-sum boundary theorem gives the Abel-boundary theorem,
because the Abel-damped eta power series already tends to the canonical
alternating eta value.
-/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_complexConditionalSum
    (hetaComplex :
      OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula) :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula := by
  intro x hx_pos hx_lt_one
  have hvalue :
      dirichletEtaLFunction (x : Complex) =
        (dirichletEtaAlternatingValue x : Complex) := by
    exact (hetaComplex x hx_pos hx_lt_one).symm.trans
      (dirichletEtaComplexConditional_tsum_eq_alternatingValue hx_pos)
  simpa [hvalue] using
    dirichletEtaAbelPowerSeries_tendsto_alternatingValue hx_pos

/--
The Abel-boundary and complex conditional-sum formulations of the eta boundary
theorem are equivalent.
-/
theorem openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_complexConditionalSum :
    OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula <->
      OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula :=
  ⟨openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_abelBoundary,
    openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_complexConditionalSum⟩

/--
The complex conditional eta boundary theorem is equivalent to the source-shaped
`ZMod 2` checked-boundary-value theorem.  This packages the Mathlib Abel theorem
step and the checked finite-character boundary value into one reusable bridge.
-/
theorem openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula := by
  constructor
  · intro hetaComplex
    exact
      (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_zmodTwoBoundaryValue).1
        (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_complexConditionalSum
          hetaComplex)
  · intro hvalue
    exact
      openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_abelBoundary
        ((openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_iff_zmodTwoBoundaryValue).2
          hvalue)

/--
The conditional-sum boundary theorem gives the canonical eta-value boundary
theorem, since the conditional eta `tsum` is the canonical alternating value.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_conditionalSum
    (hetaSum : OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula := by
  intro x hx_pos hx_lt_one
  rw [← dirichletEtaConditional_tsum_eq_alternatingValue hx_pos]
  exact hetaSum x hx_pos hx_lt_one

/--
The older canonical eta-value boundary theorem gives the conditional-sum
version.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_valueFormula
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula) :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula := by
  intro x hx_pos hx_lt_one
  rw [dirichletEtaConditional_tsum_eq_alternatingValue hx_pos]
  exact hetaValue x hx_pos hx_lt_one

/-- The eta value and conditional-sum boundary formulations are equivalent. -/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_iff_conditionalSum :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula <->
      OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula :=
  ⟨openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_valueFormula,
    openUnitIntervalDirichletEtaLFunctionValueFormula_of_conditionalSum⟩

/--
A complex conditional-sum boundary theorem gives the real-valued eta boundary
formula consumed by the real-axis route.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_complexConditionalSum
    (hetaComplex :
      OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula := by
  intro x hx_pos hx_lt_one
  have hreal := congrArg Complex.re (hetaComplex x hx_pos hx_lt_one)
  rw [dirichletEtaComplexConditional_tsum_eq_alternatingValue hx_pos] at hreal
  simpa using hreal

/--
The Abel-boundary eta theorem gives the real-valued eta boundary formula
consumed by the real-axis route.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_abelBoundary
    (habel : OpenUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_of_complexConditionalSum
    (openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_abelBoundary
      habel)

/--
The exponential-zeta Abel-boundary eta theorem gives the real-valued eta
boundary formula consumed by the real-axis route.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_expZetaBoundary
    (hexp : OpenUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_of_abelBoundary
    (openUnitIntervalDirichletEtaAbelLFunctionBoundaryFormula_of_expZetaBoundary
      hexp)

/--
The reusable nonzero additive-character Abel theorem supplies the real-valued
eta boundary formula through its `ZMod 2` specialization.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodAdditiveCharacter
    (hadd : ZModAdditiveCharacterAbelExpZetaBoundaryFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_of_expZetaBoundary
    (openUnitIntervalDirichletEtaAbelExpZetaBoundaryFormula_of_zmodAdditiveCharacter
      hadd)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem supplies the
real-valued eta boundary formula directly through the nontrivial character.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula := by
  intro x hx_pos hx_lt_one
  have hone : (1 : ZMod 2) ≠ 0 := by
    decide
  have hboundary :
      zmodAdditiveCharacterBoundaryValue
          (N := 2) (j := (1 : ZMod 2)) hone (x := x) hx_pos =
        -(dirichletEtaAlternatingValue x : Complex) := by
    simpa using
      zmodTwoAdditiveCharacterBoundaryValue_eq_neg_dirichletEtaAlternatingValue
        (x := x) hx_pos
  have hsource :
      zmodAdditiveCharacterBoundaryValue
          (N := 2) (j := (1 : ZMod 2)) hone (x := x) hx_pos =
        HurwitzZeta.expZeta (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) :=
    hvalue x hx_pos hx_lt_one
  have hetaComplex :
      dirichletEtaLFunction (x : Complex) =
        (dirichletEtaAlternatingValue x : Complex) := by
    calc
      dirichletEtaLFunction (x : Complex) =
          -HurwitzZeta.expZeta
            (ZMod.toAddCircle (1 : ZMod 2)) (x : Complex) := by
            rw [dirichletEtaLFunction_eq_neg_expZeta_modTwo]
      _ =
          -zmodAdditiveCharacterBoundaryValue
            (N := 2) (j := (1 : ZMod 2)) hone (x := x) hx_pos := by
            rw [hsource.symm]
      _ = (dirichletEtaAlternatingValue x : Complex) := by
            rw [hboundary]
            simp
  have hreal := congrArg Complex.re hetaComplex
  simpa using hreal.symm

/--
The sharpened checked-boundary-value additive-character theorem supplies the
real-valued eta boundary formula through its `ZMod 2` source-shaped
specialization.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodTwoBoundaryValue
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_zmodBoundaryValue
      hvalue)

/--
The source-shaped `ZMod 2` checked-boundary-value theorem supplies the
conditional-sum eta boundary formula through the canonical value formulation.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_zmodTwoBoundaryValue
    (hvalue : ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula :=
  openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_valueFormula
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodTwoBoundaryValue
      hvalue)

/--
The sharpened all-`ZMod` checked-boundary-value theorem supplies the
conditional-sum eta boundary formula through its `ZMod 2` specialization.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_zmodBoundaryValue
    (hvalue : ZModAdditiveCharacterBoundaryValueExpZetaFormula) :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula :=
  openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_zmodTwoBoundaryValue
    (zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_zmodBoundaryValue
      hvalue)

/--
Real-valuedness bridge for the eta L-function on the open unit interval.

This is the missing analytic input needed to turn the real-part eta formulae
back into the complex boundary-value theorem.
-/
def OpenUnitIntervalDirichletEtaLFunctionRealValued : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        (dirichletEtaLFunction (x : Complex)).im = 0

/--
The real-part eta value theorem recovers the complex conditional-sum theorem
once the eta L-function is known to be real-valued on `(0, 1)`.
-/
theorem openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_lFunctionValueFormula_and_realValued
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaReal : OpenUnitIntervalDirichletEtaLFunctionRealValued) :
    OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula := by
  intro x hx_pos hx_lt_one
  rw [dirichletEtaComplexConditional_tsum_eq_alternatingValue hx_pos]
  apply Complex.ext
  · simpa using hetaValue x hx_pos hx_lt_one
  · simp [hetaReal x hx_pos hx_lt_one]

/--
Under eta real-valuedness on `(0, 1)`, the real-part eta value theorem implies
the source-shaped `ZMod 2` checked-boundary-value theorem.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunctionValueFormula_and_realValued
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula)
    (hetaReal : OpenUnitIntervalDirichletEtaLFunctionRealValued) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  (openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue).1
    (openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_lFunctionValueFormula_and_realValued
      hetaValue hetaReal)

/--
Under eta real-valuedness on `(0, 1)`, the conditional-sum eta theorem implies
the source-shaped `ZMod 2` checked-boundary-value theorem.
-/
theorem zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_conditionalSum_and_realValued
    (hetaSum : OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula)
    (hetaReal : OpenUnitIntervalDirichletEtaLFunctionRealValued) :
    ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunctionValueFormula_and_realValued
    (openUnitIntervalDirichletEtaLFunctionValueFormula_of_conditionalSum
      hetaSum)
    hetaReal

/--
With eta real-valuedness on `(0, 1)`, the real-part eta value theorem is
equivalent to the source-shaped `ZMod 2` checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_iff_zmodTwoBoundaryValue_of_realValued
    (hetaReal : OpenUnitIntervalDirichletEtaLFunctionRealValued) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  ⟨fun hetaValue =>
      zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_lFunctionValueFormula_and_realValued
        hetaValue hetaReal,
    openUnitIntervalDirichletEtaLFunctionValueFormula_of_zmodTwoBoundaryValue⟩

/--
With eta real-valuedness on `(0, 1)`, the conditional-sum eta theorem is
equivalent to the source-shaped `ZMod 2` checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue_of_realValued
    (hetaReal : OpenUnitIntervalDirichletEtaLFunctionRealValued) :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  ⟨fun hetaSum =>
      zmodTwoAdditiveCharacterBoundaryValueExpZetaFormula_of_conditionalSum_and_realValued
        hetaSum hetaReal,
    openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_of_zmodTwoBoundaryValue⟩

/--
Real-part form of the zeta multiplier identity for the mod-2 eta L-function
on `(0, 1)`.

The expected complex identity is
`eta(s) = (1 - 2^(1-s)) * zeta(s)`; this real-part formulation is exactly the
shape needed by the real-axis zero-free route.
-/
def OpenUnitIntervalDirichletEtaLFunctionZetaRealFormula : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        (dirichletEtaLFunction (x : Complex)).re =
          (1 - (2 : Real) ^ (1 - x)) *
            (riemannZeta (x : Complex)).re

/--
Right-half-plane source identity for the mod-2 eta L-function.

This is the Dirichlet-series-domain form of
`eta(s) = (1 - 2^(1-s)) * zeta(s)`.
-/
def DirichletEtaLFunctionZetaFormulaOnRightHalfPlane : Prop :=
  forall s : Complex,
    1 < s.re ->
      dirichletEtaLFunction s =
        (1 - (2 : Complex) ^ (1 - s)) * riemannZeta s

/--
The mod-2 eta L-function satisfies
`eta(s) = (1 - 2^(1-s)) * zeta(s)` on the half-plane of absolute convergence.

The proof splits both L-series into even and odd subseries, uses the parity
coefficient on each subseries, and computes the even zeta subseries as
`2^(-s) * zeta(s)`.
-/
theorem dirichletEtaLFunctionZetaFormulaOnRightHalfPlane :
    DirichletEtaLFunctionZetaFormulaOnRightHalfPlane := by
  intro s hs
  let etaCoeff : Nat → Complex := fun n => dirichletEtaParity (n : ZMod 2)
  let oneCoeff : Nat → Complex := (1 : Nat → Complex)
  have h_eta_summ : Summable (LSeries.term etaCoeff s) := by
    simpa [etaCoeff, LSeriesSummable] using
      (ZMod.LSeriesSummable_of_one_lt_re dirichletEtaParity hs)
  have h_one_summ : Summable (LSeries.term oneCoeff s) := by
    change Summable (LSeries.term (1 : Nat → Complex) s)
    simpa [LSeriesSummable] using
      (LSeriesHasSum_one hs).LSeriesSummable
  have h_eta_even_summ :
      Summable fun k : Nat => LSeries.term etaCoeff s (2 * k) :=
    h_eta_summ.comp_injective (mul_right_injective₀ (two_ne_zero' Nat))
  have h_eta_odd_summ :
      Summable fun k : Nat => LSeries.term etaCoeff s (2 * k + 1) :=
    h_eta_summ.comp_injective
      ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' Nat)))
  have h_one_even_summ :
      Summable fun k : Nat => LSeries.term oneCoeff s (2 * k) :=
    h_one_summ.comp_injective (mul_right_injective₀ (two_ne_zero' Nat))
  have h_one_odd_summ :
      Summable fun k : Nat => LSeries.term oneCoeff s (2 * k + 1) :=
    h_one_summ.comp_injective
      ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' Nat)))
  have h_eta_split :
      LSeries etaCoeff s =
        (∑' k : Nat, LSeries.term etaCoeff s (2 * k)) +
          (∑' k : Nat, LSeries.term etaCoeff s (2 * k + 1)) := by
    simpa [LSeries] using
      (tsum_even_add_odd h_eta_even_summ h_eta_odd_summ).symm
  have h_one_split :
      LSeries oneCoeff s =
        (∑' k : Nat, LSeries.term oneCoeff s (2 * k)) +
          (∑' k : Nat, LSeries.term oneCoeff s (2 * k + 1)) := by
    simpa [LSeries] using
      (tsum_even_add_odd h_one_even_summ h_one_odd_summ).symm
  have h_eta_even :
      (∑' k : Nat, LSeries.term etaCoeff s (2 * k)) =
        -(∑' k : Nat, LSeries.term oneCoeff s (2 * k)) := by
    calc
      (∑' k : Nat, LSeries.term etaCoeff s (2 * k))
          = ∑' k : Nat, -LSeries.term oneCoeff s (2 * k) := by
            exact tsum_congr (by
              intro k
              exact dirichletEtaParity_even_lseriesTerm s k)
      _ = -(∑' k : Nat, LSeries.term oneCoeff s (2 * k)) := by
            rw [tsum_neg]
  have h_eta_odd :
      (∑' k : Nat, LSeries.term etaCoeff s (2 * k + 1)) =
        (∑' k : Nat, LSeries.term oneCoeff s (2 * k + 1)) := by
    exact tsum_congr (by
      intro k
      exact dirichletEtaParity_odd_lseriesTerm s k)
  have h_even := lseries_one_evenSubseries_eq (s := s) hs
  have hzeta : LSeries oneCoeff s = riemannZeta s := by
    change LSeries (1 : Nat → Complex) s = riemannZeta s
    exact LSeries_one_eq_riemannZeta hs
  have h_eta_lseries :
      LSeries etaCoeff s =
        riemannZeta s - 2 * ((2 : Complex) ^ (-s) * riemannZeta s) := by
    let evenOne :=
      (∑' k : Nat, LSeries.term oneCoeff s (2 * k))
    let oddOne :=
      (∑' k : Nat, LSeries.term oneCoeff s (2 * k + 1))
    have h_eta_as : LSeries etaCoeff s = -evenOne + oddOne := by
      rw [h_eta_split, h_eta_even, h_eta_odd]
    have hzeta_split : riemannZeta s = evenOne + oddOne := by
      rw [← hzeta, h_one_split]
    have hodd : oddOne = riemannZeta s - evenOne := by
      rw [hzeta_split]
      ring
    have heven : evenOne = (2 : Complex) ^ (-s) * riemannZeta s := by
      unfold evenOne
      change (∑' k : Nat,
          LSeries.term (fun _ : Nat => (1 : Complex)) s (2 * k)) =
        (2 : Complex) ^ (-s) * riemannZeta s
      exact h_even
    rw [h_eta_as, hodd, heven]
    ring
  have heta_lfun :
      dirichletEtaLFunction s = LSeries etaCoeff s := by
    simpa [etaCoeff] using dirichletEtaLFunction_eq_LSeries_of_one_lt_re hs
  rw [heta_lfun, h_eta_lseries]
  rw [show (2 : Complex) ^ (1 - s) =
      2 * (2 : Complex) ^ (-s) by
    rw [show 1 - s = (1 : Complex) + (-s) by ring]
    rw [Complex.cpow_add _ _ (by norm_num : (2 : Complex) ≠ 0)]
    norm_num]
  ring

/--
Regular-domain analytic continuation of the eta/zeta multiplier identity.
-/
def DirichletEtaLFunctionZetaFormulaOnRegularSet : Prop :=
  forall s : Complex,
    s ≠ 1 ->
      dirichletEtaLFunction s =
        (1 - (2 : Complex) ^ (1 - s)) * riemannZeta s

/--
The right-half-plane eta/zeta identity extends to the whole punctured plane by
analytic continuation.

This leaves the Dirichlet-series algebraic identity as the remaining source
work and discharges the continuation step in Lean.
-/
theorem dirichletEtaLFunctionZetaFormulaOnRegularSet_of_rightHalfPlane
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    DirichletEtaLFunctionZetaFormulaOnRegularSet := by
  intro s hs
  have hpc : IsPreconnected (({(1 : Complex)} : Set Complex)ᶜ) := by
    have hrank : 1 < Module.rank Real Complex := by
      rw [Complex.rank_real_complex]
      norm_num
    exact (isConnected_compl_singleton_of_one_lt_rank
      (E := Complex) hrank (1 : Complex)).isPreconnected
  have htwo_mem : (2 : Complex) ∈ (({(1 : Complex)} : Set Complex)ᶜ) := by
    norm_num
  have hf : AnalyticOnNhd Complex dirichletEtaLFunction
      (({(1 : Complex)} : Set Complex)ᶜ) := by
    intro z hz
    exact analyticAt_dirichletEtaLFunction z
  have hg : AnalyticOnNhd Complex
      (fun z : Complex =>
        (1 - (2 : Complex) ^ (1 - z)) * riemannZeta z)
      (({(1 : Complex)} : Set Complex)ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_)
      isOpen_compl_singleton
    have hpow : DifferentiableAt Complex
        (fun z : Complex => (2 : Complex) ^ (1 - z)) z := by
      fun_prop
    exact (((differentiableAt_const 1).sub hpow).mul
      (differentiableAt_riemannZeta hz)).differentiableWithinAt
  have hfg_eventually :
      Filter.EventuallyEq (nhds (2 : Complex))
        dirichletEtaLFunction
        (fun z : Complex =>
          (1 - (2 : Complex) ^ (1 - z)) * riemannZeta z) := by
    have hright :
        Filter.Eventually (fun z : Complex => 1 < z.re)
          (nhds (2 : Complex)) := by
      exact (Complex.continuous_re.tendsto (2 : Complex)).eventually
        (lt_mem_nhds (show 1 < (2 : Complex).re by norm_num))
    filter_upwards [hright] with z hz
    exact hetaRight z hz
  have heqOn : Set.EqOn
      dirichletEtaLFunction
      (fun z : Complex =>
        (1 - (2 : Complex) ^ (1 - z)) * riemannZeta z)
      (({(1 : Complex)} : Set Complex)ᶜ) := by
    exact hf.eqOn_of_preconnected_of_eventuallyEq
      hg hpc htwo_mem hfg_eventually
  exact heqOn (by simpa using hs)

/--
The complex regular-domain eta/zeta identity gives the real-part source target
needed on `(0, 1)`.
-/
theorem openUnitIntervalDirichletEtaLFunctionZetaRealFormula_of_regularSet
    (hetaRegular : DirichletEtaLFunctionZetaFormulaOnRegularSet) :
    OpenUnitIntervalDirichletEtaLFunctionZetaRealFormula := by
  intro x hx_pos hx_lt_one
  have hx_ne : (x : Complex) ≠ 1 := by
    intro h
    have hx_eq : x = 1 := by
      exact_mod_cast h
    linarith
  have hcomplex := congrArg Complex.re
    (hetaRegular (x : Complex) hx_ne)
  have hpow :
      (2 : Complex) ^ (1 - (x : Complex)) =
        (((2 : Real) ^ (1 - x) : Real) : Complex) := by
    rw [show 1 - (x : Complex) = ((1 - x : Real) : Complex) by
      simp [Complex.ofReal_sub]]
    exact (Complex.ofReal_cpow (show 0 ≤ (2 : Real) by norm_num)
      (1 - x)).symm
  rw [hcomplex, hpow]
  simp

/--
The right-half-plane eta/zeta identity is enough to fill the real-interval
L-function/zeta obligation, because Lean now supplies the analytic-continuation
step.
-/
theorem openUnitIntervalDirichletEtaLFunctionZetaRealFormula_of_rightHalfPlane
    (hetaRight : DirichletEtaLFunctionZetaFormulaOnRightHalfPlane) :
    OpenUnitIntervalDirichletEtaLFunctionZetaRealFormula :=
  openUnitIntervalDirichletEtaLFunctionZetaRealFormula_of_regularSet
    (dirichletEtaLFunctionZetaFormulaOnRegularSet_of_rightHalfPlane
      hetaRight)

/-- The eta/zeta identity holds on the punctured plane. -/
theorem dirichletEtaLFunctionZetaFormulaOnRegularSet :
    DirichletEtaLFunctionZetaFormulaOnRegularSet :=
  dirichletEtaLFunctionZetaFormulaOnRegularSet_of_rightHalfPlane
    dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/--
Zeta conjugation on the regular domain makes the eta L-function real-valued on
the open unit interval.

This uses the checked punctured-plane eta/zeta identity; the zeta conjugation
input is kept local to avoid forcing a counting-layer import into this axis
decomposition module.
-/
theorem openUnitIntervalDirichletEtaLFunctionRealValued_of_zetaConjugationFormulaOnRegularSet
    (hzetaConj : forall s : Complex,
      s ≠ 1 ->
        riemannZeta (conj s) = conj (riemannZeta s)) :
    OpenUnitIntervalDirichletEtaLFunctionRealValued := by
  intro x hx_pos hx_lt_one
  have hx_ne : (x : Complex) ≠ 1 := by
    intro h
    have hx_eq : x = 1 := by
      exact_mod_cast h
    linarith
  have hpow :
      (2 : Complex) ^ (1 - (x : Complex)) =
        (((2 : Real) ^ (1 - x) : Real) : Complex) := by
    rw [show 1 - (x : Complex) = ((1 - x : Real) : Complex) by
      simp [Complex.ofReal_sub]]
    exact (Complex.ofReal_cpow (show 0 ≤ (2 : Real) by norm_num)
      (1 - x)).symm
  have hzeta_real :
      riemannZeta (x : Complex) = conj (riemannZeta (x : Complex)) := by
    simpa using hzetaConj (x : Complex) hx_ne
  have hzeta_im :
      (riemannZeta (x : Complex)).im = 0 := by
    have h := congrArg Complex.im hzeta_real
    simp at h
    linarith
  rw [dirichletEtaLFunctionZetaFormulaOnRegularSet (x : Complex) hx_ne,
    hpow]
  simp [hzeta_im]

/--
With regular-domain zeta conjugation, the real-part eta value theorem is
equivalent to the source-shaped `ZMod 2` checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_iff_zmodTwoBoundaryValue_of_zetaConjugationFormulaOnRegularSet
    (hzetaConj : forall s : Complex,
      s ≠ 1 ->
        riemannZeta (conj s) = conj (riemannZeta s)) :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_iff_zmodTwoBoundaryValue_of_realValued
    (openUnitIntervalDirichletEtaLFunctionRealValued_of_zetaConjugationFormulaOnRegularSet
      hzetaConj)

/--
With regular-domain zeta conjugation, the conditional-sum eta theorem is
equivalent to the source-shaped `ZMod 2` checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue_of_zetaConjugationFormulaOnRegularSet
    (hzetaConj : forall s : Complex,
      s ≠ 1 ->
        riemannZeta (conj s) = conj (riemannZeta s)) :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue_of_realValued
    (openUnitIntervalDirichletEtaLFunctionRealValued_of_zetaConjugationFormulaOnRegularSet
      hzetaConj)

/-- The eta L-function is real-valued on the open unit interval. -/
theorem openUnitIntervalDirichletEtaLFunctionRealValued :
    OpenUnitIntervalDirichletEtaLFunctionRealValued :=
  openUnitIntervalDirichletEtaLFunctionRealValued_of_zetaConjugationFormulaOnRegularSet
    riemannZetaConjugationFormulaOnRegularSet

/-- On `(0, 1)`, the mod-2 Hurwitz difference is real-valued. -/
theorem zmodTwo_hurwitzSub_im_eq_zero_of_openUnitInterval
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    (HurwitzZeta.hurwitzZeta
        (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
        (x : Complex) -
      HurwitzZeta.hurwitzZeta
        ((1 : Real) : UnitAddCircle) (x : Complex)).im = 0 := by
  rw [zmodTwo_hurwitzSub_eq_scaled_etaLFunction (x : Complex)]
  have hscale :
      (2 : Complex) ^ (x : Complex) =
        (((2 : Real) ^ x : Real) : Complex) := by
    exact (Complex.ofReal_cpow (show 0 ≤ (2 : Real) by norm_num) x).symm
  rw [hscale]
  simp [openUnitIntervalDirichletEtaLFunctionRealValued x hx hx_lt_one]

/-- On `(0, 1)`, the remaining regularized half-tail/Hurwitz gap is real. -/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_im_eq_zero_of_openUnitInterval
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    ((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex))).im = 0 := by
  rw [zmodTwoRegularizedHalfTail_hurwitzGap_eq_scaled_etaLFunctionGap hx]
  simp [openUnitIntervalDirichletEtaLFunctionRealValued x hx hx_lt_one]

/--
On `(0, 1)`, the real part of the remaining half-tail/Hurwitz gap is exactly
the positive scale times the real eta/`LFunction` gap.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_re_eq_scaled_realGap
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    ((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex))).re =
      (2 : Real) ^ x *
        (dirichletEtaAlternatingValue x -
          (dirichletEtaLFunction (x : Complex)).re) := by
  rw [zmodTwoRegularizedHalfTail_hurwitzGap_eq_scaled_etaLFunctionGap hx]
  simp [openUnitIntervalDirichletEtaLFunctionRealValued x hx hx_lt_one]

/--
On `(0, 1)`, the norm of the remaining half-tail/Hurwitz gap is the positive
scale times the absolute real eta/`LFunction` gap.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_norm_eq_scaled_abs_realGap
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex))‖ =
      (2 : Real) ^ x *
        |dirichletEtaAlternatingValue x -
          (dirichletEtaLFunction (x : Complex)).re| := by
  rw [zmodTwoRegularizedHalfTail_hurwitzGap_eq_scaled_etaLFunctionGap hx]
  have hscale_nonneg : 0 ≤ (2 : Real) ^ x :=
    Real.rpow_nonneg (by norm_num) x
  have hdiff :
      (dirichletEtaAlternatingValue x : Complex) -
          dirichletEtaLFunction (x : Complex) =
        ((dirichletEtaAlternatingValue x -
          (dirichletEtaLFunction (x : Complex)).re : Real) : Complex) := by
    apply Complex.ext
    · simp
    · simp [openUnitIntervalDirichletEtaLFunctionRealValued x hx hx_lt_one]
  rw [hdiff, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hscale_nonneg]

/--
The real-part eta value theorem recovers the complex conditional-sum theorem,
using the checked zeta conjugation formula to supply eta real-valuedness.
-/
theorem openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_lFunctionValueFormula
    (hetaValue : OpenUnitIntervalDirichletEtaLFunctionValueFormula) :
    OpenUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula :=
  openUnitIntervalDirichletEtaComplexConditionalSumLFunctionFormula_of_lFunctionValueFormula_and_realValued
    hetaValue openUnitIntervalDirichletEtaLFunctionRealValued

/--
The real-part eta value theorem is equivalent to the source-shaped `ZMod 2`
checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaLFunctionValueFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalDirichletEtaLFunctionValueFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  openUnitIntervalDirichletEtaLFunctionValueFormula_iff_zmodTwoBoundaryValue_of_realValued
    openUnitIntervalDirichletEtaLFunctionRealValued

/--
The conditional-sum eta theorem is equivalent to the source-shaped `ZMod 2`
checked-boundary-value theorem.
-/
theorem openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue :
    OpenUnitIntervalDirichletEtaConditionalSumLFunctionFormula <->
      ZModTwoAdditiveCharacterBoundaryValueExpZetaFormula :=
  openUnitIntervalDirichletEtaConditionalSumLFunctionFormula_iff_zmodTwoBoundaryValue_of_realValued
    openUnitIntervalDirichletEtaLFunctionRealValued

/-- The real-part eta L-function/zeta identity holds on `(0, 1)`. -/
theorem openUnitIntervalDirichletEtaLFunctionZetaRealFormula :
    OpenUnitIntervalDirichletEtaLFunctionZetaRealFormula :=
  openUnitIntervalDirichletEtaLFunctionZetaRealFormula_of_rightHalfPlane
    dirichletEtaLFunctionZetaFormulaOnRightHalfPlane

/--
On `(0, 1)`, the real part of the remaining half-tail/Hurwitz gap is exactly
the positive scale times the real eta/zeta continuation gap.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_re_eq_scaled_etaZetaGap
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    ((∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex))).re =
      (2 : Real) ^ x *
        (dirichletEtaAlternatingValue x -
          (1 - (2 : Real) ^ (1 - x)) *
            (riemannZeta (x : Complex)).re) := by
  rw [zmodTwoRegularizedHalfTail_hurwitzGap_re_eq_scaled_realGap hx hx_lt_one]
  rw [openUnitIntervalDirichletEtaLFunctionZetaRealFormula x hx hx_lt_one]

/--
On `(0, 1)`, the norm of the remaining half-tail/Hurwitz gap is the positive
scale times the absolute real eta/zeta continuation gap.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_norm_eq_scaled_abs_etaZetaGap
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex))‖ =
      (2 : Real) ^ x *
        |dirichletEtaAlternatingValue x -
          (1 - (2 : Real) ^ (1 - x)) *
            (riemannZeta (x : Complex)).re| := by
  rw [zmodTwoRegularizedHalfTail_hurwitzGap_norm_eq_scaled_abs_realGap
    hx hx_lt_one]
  rw [openUnitIntervalDirichletEtaLFunctionZetaRealFormula x hx hx_lt_one]

/--
A single finite eta bracket for the zeta-continuation candidate gives a concrete
norm bound for the actual regularized half-tail/Hurwitz gap.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_norm_le_scaled_etaBracketWidth
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1) (M : Nat)
    (hzeta_even :
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re)
    (hzeta_odd :
      (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
        (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) :
    ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex))‖ ≤
      (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
  rw [zmodTwoRegularizedHalfTail_hurwitzGap_norm_eq_scaled_abs_etaZetaGap
    hx hx_lt_one]
  exact mul_le_mul_of_nonneg_left
    (openUnitInterval_etaZetaGap_abs_le_of_zetaTarget_mem_evenOddBracket
      hx hx_lt_one M hzeta_even hzeta_odd)
    (Real.rpow_nonneg (by norm_num) x)

/--
Direct squeeze criterion for the actual regularized half-tail/Hurwitz gap: if
its norm is bounded by the shrinking eta bracket width at every cutoff, then
the pointwise half-tail Hurwitz identity follows.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzFormula_of_forall_gap_norm_le_scaled_etaBracketWidth
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1)
    (hbound : ∀ M : Nat,
      ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
          (HurwitzZeta.hurwitzZeta
              (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
              (x : Complex) -
            HurwitzZeta.hurwitzZeta
              ((1 : Real) : UnitAddCircle) (x : Complex))‖ ≤
        (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real)) ^ (-x)) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  let gap : Complex :=
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
      (HurwitzZeta.hurwitzZeta
          (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex))
  have hsubseq : Tendsto (fun M : Nat => 2 * M) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  have hwidth_tendsto :
      Tendsto (fun M : Nat =>
        (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real)) ^ (-x))
        atTop (nhds 0) := by
    have hbase := dirichletEtaTerm_tendsto_zero_of_pos (x := x) hx
    have hcomp := hbase.comp hsubseq
    have hconst :
        Tendsto (fun _ : Nat => (2 : Real) ^ x) atTop
          (nhds ((2 : Real) ^ x)) :=
      tendsto_const_nhds
    have hscaled := hconst.mul hcomp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using hscaled
  have hgap_tendsto_zero :
      Tendsto (fun _ : Nat => ‖gap‖) atTop (nhds 0) := by
    exact squeeze_zero (fun _ => norm_nonneg gap)
      (fun M => by simpa [gap] using hbound M)
      hwidth_tendsto
  have hgap_tendsto_const :
      Tendsto (fun _ : Nat => ‖gap‖) atTop (nhds ‖gap‖) :=
    tendsto_const_nhds
  have hnorm_zero : ‖gap‖ = 0 :=
    tendsto_nhds_unique hgap_tendsto_const hgap_tendsto_zero
  have hgap_zero : gap = 0 := norm_eq_zero.mp hnorm_zero
  exact sub_eq_zero.mp (by simpa [gap] using hgap_zero)

/--
Eventual squeeze criterion for the actual regularized half-tail/Hurwitz gap:
it is enough to have the shrinking eta-width bound for all sufficiently large
cutoffs.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzFormula_of_eventually_gap_norm_le_scaled_etaBracketWidth
    {x : Real} (hx : 0 < x) (_hx_lt_one : x < 1)
    (hbound : ∀ᶠ M : Nat in atTop,
      ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
          (HurwitzZeta.hurwitzZeta
              (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
              (x : Complex) -
            HurwitzZeta.hurwitzZeta
              ((1 : Real) : UnitAddCircle) (x : Complex))‖ ≤
        (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real)) ^ (-x)) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  let gap : Complex :=
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
      (HurwitzZeta.hurwitzZeta
          (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex))
  have hsubseq : Tendsto (fun M : Nat => 2 * M) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    refine eventually_atTop.2 ⟨b, ?_⟩
    intro M hM
    nlinarith
  have hwidth_tendsto :
      Tendsto (fun M : Nat =>
        (2 : Real) ^ x * (((2 * M + 1 : Nat) : Real)) ^ (-x))
        atTop (nhds 0) := by
    have hbase := dirichletEtaTerm_tendsto_zero_of_pos (x := x) hx
    have hcomp := hbase.comp hsubseq
    have hconst :
        Tendsto (fun _ : Nat => (2 : Real) ^ x) atTop
          (nhds ((2 : Real) ^ x)) :=
      tendsto_const_nhds
    have hscaled := hconst.mul hcomp
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul] using hscaled
  have hgap_tendsto_zero :
      Tendsto (fun _ : Nat => ‖gap‖) atTop (nhds 0) := by
    have hgap_bound : ∀ᶠ M : Nat in atTop,
        ‖gap‖ ≤ (2 : Real) ^ x *
          (((2 * M + 1 : Nat) : Real)) ^ (-x) := by
      filter_upwards [hbound] with M hM
      simpa [gap] using hM
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg gap)
      hgap_bound hwidth_tendsto
  have hgap_tendsto_const :
      Tendsto (fun _ : Nat => ‖gap‖) atTop (nhds ‖gap‖) :=
    tendsto_const_nhds
  have hnorm_zero : ‖gap‖ = 0 :=
    tendsto_nhds_unique hgap_tendsto_const hgap_tendsto_zero
  have hgap_zero : gap = 0 := norm_eq_zero.mp hnorm_zero
  exact sub_eq_zero.mp (by simpa [gap] using hgap_zero)

/--
If the zeta-continuation candidate lies in every finite eta bracket, then the
actual regularized half-tail/Hurwitz gap is zero.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzGap_eq_zero_of_forall_zetaTarget_mem_evenOddBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1)
    (hbracket : ∀ M : Nat,
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
          (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ∧
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
        (HurwitzZeta.hurwitzZeta
            (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
            (x : Complex) -
          HurwitzZeta.hurwitzZeta
            ((1 : Real) : UnitAddCircle) (x : Complex)) = 0 := by
  have hformula :=
    openUnitInterval_etaZetaFormula_of_forall_zetaTarget_mem_evenOddBracket
      hx hx_lt_one hbracket
  have hnorm_zero :
      ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
          (HurwitzZeta.hurwitzZeta
              (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
              (x : Complex) -
            HurwitzZeta.hurwitzZeta
              ((1 : Real) : UnitAddCircle) (x : Complex))‖ = 0 := by
    rw [zmodTwoRegularizedHalfTail_hurwitzGap_norm_eq_scaled_abs_etaZetaGap
      hx hx_lt_one]
    rw [hformula]
    simp
  exact norm_eq_zero.mp hnorm_zero

/--
The all-cutoffs eta bracket criterion supplies the exact mod-2 half-tail
Hurwitz identity pointwise on the open unit interval.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzFormula_of_forall_zetaTarget_mem_evenOddBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1)
    (hbracket : ∀ M : Nat,
      (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) ≤
          (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ∧
        (1 - (2 : Real) ^ (1 - x)) * (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x)) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  exact sub_eq_zero.mp
    (zmodTwoRegularizedHalfTail_hurwitzGap_eq_zero_of_forall_zetaTarget_mem_evenOddBracket
      hx hx_lt_one hbracket)

/--
Eventual membership in the reversed real-zeta eta brackets supplies the exact
mod-2 half-tail Hurwitz identity pointwise on the open unit interval.
-/
theorem zmodTwoRegularizedHalfTail_hurwitzFormula_of_eventually_zetaRe_mem_reversed_etaBracket
    {x : Real} (hx : 0 < x) (hx_lt_one : x < 1)
    (hzeta : ∀ᶠ M : Nat in atTop,
      (Finset.range (2 * M + 1)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x)) ≤
          (riemannZeta (x : Complex)).re ∧
        (riemannZeta (x : Complex)).re ≤
          (Finset.range (2 * M)).sum (dirichletEtaSeriesTerm x) /
            (1 - (2 : Real) ^ (1 - x))) :
    (∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) =
      HurwitzZeta.hurwitzZeta
          (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
          (x : Complex) -
        HurwitzZeta.hurwitzZeta
          ((1 : Real) : UnitAddCircle) (x : Complex) := by
  have heta :=
    openUnitInterval_etaZetaFormula_of_eventually_zetaRe_mem_reversed_etaBracket
      hx hx_lt_one hzeta
  have hnorm_zero :
      ‖(∑' m : Nat, zmodTwoRegularizedHalfTailTerm x m) -
          (HurwitzZeta.hurwitzZeta
              (((1 : Real) / (2 : Real) : Real) : UnitAddCircle)
              (x : Complex) -
            HurwitzZeta.hurwitzZeta
              ((1 : Real) : UnitAddCircle) (x : Complex))‖ = 0 := by
    rw [zmodTwoRegularizedHalfTail_hurwitzGap_norm_eq_scaled_abs_etaZetaGap
      hx hx_lt_one]
    rw [heta]
    simp
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
end

end ComplexCompactExhaustion

end RiemannHypothesisProject
