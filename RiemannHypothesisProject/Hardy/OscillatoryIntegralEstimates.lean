import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Module
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Hardy oscillatory integral estimates

This module formalizes the first- and second-derivative exponential-integral
estimates used in the Hardy argument.  The source phase is kept explicit so
that its derivative and dyadic curvature bounds can feed the stationary and
nonstationary ranges without an abstract phase API.
-/

open Complex MeasureTheory Set

namespace RiemannHypothesisProject

namespace Hardy

noncomputable section

/-- Discrete Bonnet inequality: Abel summation bounds a weighted sum by a
uniform bound for its partial sums times the endpoint weight plus discrete
variation. -/
theorem norm_sum_range_smul_le_partialSum_mul_variation
    (q : Nat → Real) (z : Nat → Complex) (n : Nat) (C : Real)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, z i‖ ≤ C) :
    ‖∑ i ∈ Finset.range n, q i • z i‖ ≤
      |q (n - 1)| * C +
        (∑ i ∈ Finset.range (n - 1), |q (i + 1) - q i|) * C := by
  rw [Finset.sum_range_by_parts]
  calc
    ‖q (n - 1) • (∑ i ∈ Finset.range n, z i) -
        ∑ i ∈ Finset.range (n - 1),
          (q (i + 1) - q i) • (∑ j ∈ Finset.range (i + 1), z j)‖ ≤
        ‖q (n - 1) • (∑ i ∈ Finset.range n, z i)‖ +
          ‖∑ i ∈ Finset.range (n - 1),
            (q (i + 1) - q i) •
              (∑ j ∈ Finset.range (i + 1), z j)‖ := norm_sub_le _ _
    _ ≤ |q (n - 1)| * C +
        ∑ i ∈ Finset.range (n - 1), |q (i + 1) - q i| * C := by
      apply add_le_add
      · simpa [norm_smul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left (hpartial n le_rfl) (abs_nonneg (q (n - 1)))
      · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [Finset.mem_range] at hi
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by omega))
          (abs_nonneg (q (i + 1) - q i))
    _ = |q (n - 1)| * C +
        (∑ i ∈ Finset.range (n - 1), |q (i + 1) - q i|) * C := by
      rw [Finset.sum_mul]

/-- Exact discrete Bonnet inequality for a nonnegative antitone weight. -/
theorem norm_sum_range_smul_le_of_antitone_nonneg
    (q : Nat → Real) (z : Nat → Complex) (n : Nat) (C : Real)
    (hanti : ∀ i, i + 1 < n → q (i + 1) ≤ q i)
    (hq0 : ∀ i, 0 ≤ q i)
    (hpartial : ∀ k ≤ n, ‖∑ i ∈ Finset.range k, z i‖ ≤ C) :
    ‖∑ i ∈ Finset.range n, q i • z i‖ ≤ q 0 * C := by
  have hC : 0 ≤ C := by
    simpa using hpartial 0 (Nat.zero_le n)
  by_cases hn : n = 0
  · subst n
    simp [mul_nonneg (hq0 0) hC]
  have hvariation :
      ∑ i ∈ Finset.range (n - 1), |q (i + 1) - q i| =
        q 0 - q (n - 1) := by
    calc
      ∑ i ∈ Finset.range (n - 1), |q (i + 1) - q i| =
          ∑ i ∈ Finset.range (n - 1), (q i - q (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        rw [abs_of_nonpos]
        · ring
        · exact sub_nonpos.mpr (hanti i (by omega))
      _ = q 0 - q (n - 1) := by
        induction n - 1 with
        | zero => simp
        | succ k ih =>
            rw [Finset.sum_range_succ, ih]
            ring
  have hbase := norm_sum_range_smul_le_partialSum_mul_variation
    q z n C hpartial
  refine hbase.trans ?_
  rw [abs_of_nonneg (hq0 (n - 1)), hvariation]
  ring_nf
  exact le_rfl

/-- Exact discrete Bonnet inequality for a nonpositive antitone weight,
using partial sums from the right endpoint. -/
theorem norm_sum_range_smul_le_of_antitone_nonpos
    (q : Nat → Real) (z : Nat → Complex) (n : Nat) (C : Real)
    (hanti : ∀ i, i + 1 < n → q (i + 1) ≤ q i)
    (hq0 : ∀ i, q i ≤ 0)
    (hpartial : ∀ k ≤ n,
      ‖∑ i ∈ Finset.range k, z (n - 1 - i)‖ ≤ C) :
    ‖∑ i ∈ Finset.range n, q i • z i‖ ≤ -(q (n - 1)) * C := by
  let qr : Nat → Real := fun i => -(q (n - 1 - i))
  let zr : Nat → Complex := fun i => z (n - 1 - i)
  have hqrAnti : ∀ i, i + 1 < n → qr (i + 1) ≤ qr i := by
    intro i hi
    dsimp only [qr]
    apply neg_le_neg
    have hj : n - 1 - (i + 1) + 1 = n - 1 - i := by omega
    simpa only [hj] using hanti (n - 1 - (i + 1)) (by omega)
  have hqrNonneg : ∀ i, 0 ≤ qr i := by
    intro i
    exact neg_nonneg.mpr (hq0 _)
  have hr := norm_sum_range_smul_le_of_antitone_nonneg
    qr zr n C hqrAnti hqrNonneg (by simpa [zr] using hpartial)
  have hsum :
      ∑ i ∈ Finset.range n, qr i • zr i =
        -(∑ i ∈ Finset.range n, q i • z i) := by
    calc
      ∑ i ∈ Finset.range n, qr i • zr i =
          -(∑ i ∈ Finset.range n,
            q (n - 1 - i) • z (n - 1 - i)) := by
        simp [qr, zr, Finset.sum_neg_distrib]
      _ = -(∑ i ∈ Finset.range n, q i • z i) := by
        exact congrArg Neg.neg (Finset.sum_range_reflect
          (fun i => q i • z i) n)
  rw [hsum, norm_neg] at hr
  simpa [qr] using hr

/-- Positive Bonnet inequality for an arbitrary finite interval partition. -/
theorem norm_sum_partition_integral_smul_le_of_antitone_nonneg
    (w : Nat → Real) (h : Real → Complex) (p : Nat → Real)
    (n : Nat) (C : Real)
    (hanti : ∀ i, i + 1 < n → w (i + 1) ≤ w i)
    (hq0 : ∀ i, 0 ≤ w i)
    (hint : ∀ i < n, IntervalIntegrable h volume (p i) (p (i + 1)))
    (hprimitive : ∀ k ≤ n, ‖∫ t in p 0..p k, h t‖ ≤ C) :
    ‖∑ i ∈ Finset.range n,
        w i • (∫ t in p i..p (i + 1), h t)‖ ≤ w 0 * C := by
  apply norm_sum_range_smul_le_of_antitone_nonneg
    w
    (fun i => ∫ t in p i..p (i + 1), h t) n C hanti hq0
  intro k hk
  rw [intervalIntegral.sum_integral_adjacent_intervals]
  · exact hprimitive k hk
  · intro i hi
    exact hint i (hi.trans_le hk)

/-- Negative Bonnet inequality for an arbitrary finite interval partition,
using primitives based at the right endpoint. -/
theorem norm_sum_partition_integral_smul_le_of_antitone_nonpos
    (w : Nat → Real) (h : Real → Complex) (p : Nat → Real)
    (n : Nat) (C : Real)
    (hanti : ∀ i, i + 1 < n → w (i + 1) ≤ w i)
    (hq0 : ∀ i, w i ≤ 0)
    (hint : ∀ i < n, IntervalIntegrable h volume (p i) (p (i + 1)))
    (hprimitive : ∀ k ≤ n, ‖∫ t in p (n - k)..p n, h t‖ ≤ C) :
    ‖∑ i ∈ Finset.range n,
        w i • (∫ t in p i..p (i + 1), h t)‖ ≤ -(w (n - 1)) * C := by
  apply norm_sum_range_smul_le_of_antitone_nonpos
    w (fun i => ∫ t in p i..p (i + 1), h t) n C hanti hq0
  intro k hk
  have hsumData :
      ∑ i ∈ Finset.range k,
          (∫ t in p (n - 1 - i)..p (n - 1 - i + 1), h t) =
        ∫ t in p (n - k)..p n, h t ∧
      IntervalIntegrable h volume (p (n - k)) (p n) := by
    induction k with
    | zero =>
        constructor
        · simp
        · exact (IntervalIntegrable.refl :
            IntervalIntegrable h volume (p n) (p n))
    | succ k ih =>
        have hk' : k ≤ n := (Nat.le_of_succ_le hk)
        obtain ⟨ihsum, ihint⟩ := ih hk'
        have hleft : n - 1 - k = n - (k + 1) := by omega
        have hbridge : n - (k + 1) + 1 = n - k := by omega
        have hleftInt := hint (n - (k + 1)) (by omega)
        have hleftInt' : IntervalIntegrable h volume
            (p (n - (k + 1))) (p (n - k)) := by
          simpa only [hbridge] using hleftInt
        constructor
        · rw [Finset.sum_range_succ, ihsum, hleft, hbridge, add_comm]
          exact intervalIntegral.integral_add_adjacent_intervals hleftInt' ihint
        · exact hleftInt'.trans ihint
  rw [hsumData.1]
  exact hprimitive k hk

/-- Every interval primitive of the unit-frequency complex exponential has
norm at most two.  This is the cancellation input in the source
first-derivative argument. -/
theorem norm_integral_exp_I_mul_le_two (a b : Real) :
    ‖∫ t in a..b, Complex.exp (Complex.I * t)‖ ≤ 2 := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have heval := integral_exp_mul_complex
    (a := a) (b := b) (c := Complex.I) hI
  rw [heval, norm_div, Complex.norm_I, div_one]
  calc
    ‖Complex.exp (Complex.I * b) - Complex.exp (Complex.I * a)‖ ≤
        ‖Complex.exp (Complex.I * b)‖ +
          ‖Complex.exp (Complex.I * a)‖ := norm_sub_le _ _
    _ = 2 := by
      simp [Complex.norm_exp]
      norm_num

/-- Bonnet's exact finite-partition bound specialized to the exponential
primitive used in the first-derivative test. -/
theorem norm_sum_partition_exp_integral_smul_le_of_antitone_nonneg
    (q F : Real → Real) (p : Nat → Real) (n : Nat)
    (hanti : ∀ i, i + 1 < n → q (p (i + 1)) ≤ q (p i))
    (hq0 : ∀ i, 0 ≤ q (p i)) :
    ‖∑ i ∈ Finset.range n, q (p i) •
        (∫ u in F (p i)..F (p (i + 1)),
          Complex.exp (Complex.I * u))‖ ≤ 2 * q (p 0) := by
  have h := norm_sum_partition_integral_smul_le_of_antitone_nonneg
    (fun i => q (p i)) (fun u : Real => Complex.exp (Complex.I * u))
    (fun i => F (p i))
    n 2
    (fun i hi => hanti i hi) hq0
    (fun i hi => (by fun_prop : Continuous
      (fun u : Real => Complex.exp (Complex.I * u))).intervalIntegrable
        (F (p i)) (F (p (i + 1))))
    (fun k hk => norm_integral_exp_I_mul_le_two (F (p 0)) (F (p k)))
  simpa [mul_comm] using h

/-- Right-endpoint Bonnet bound specialized to the unit-frequency complex
exponential and a nonpositive antitone weight. -/
theorem norm_sum_partition_exp_integral_smul_le_of_antitone_nonpos
    (q F : Real → Real) (p : Nat → Real) (n : Nat)
    (hanti : ∀ i, i + 1 < n → q (p (i + 1)) ≤ q (p i))
    (hq0 : ∀ i, q (p i) ≤ 0) :
    ‖∑ i ∈ Finset.range n, q (p i) •
        (∫ u in F (p i)..F (p (i + 1)),
          Complex.exp (Complex.I * u))‖ ≤
      -(q (p (n - 1))) * 2 := by
  exact norm_sum_partition_integral_smul_le_of_antitone_nonpos
    (fun i => q (p i)) (fun u : Real => Complex.exp (Complex.I * u))
    (fun i => F (p i)) n 2
    (fun i hi => hanti i hi) hq0
    (fun i hi => (by fun_prop : Continuous
      (fun u : Real => Complex.exp (Complex.I * u))).intervalIntegrable
        (F (p i)) (F (p (i + 1))))
    (fun k hk => norm_integral_exp_I_mul_le_two
      (F (p (n - k))) (F (p n)))

/-- Positive-slope finite-partition estimate for the exact reciprocal
weights in the first-derivative test. -/
theorem norm_sum_partition_exp_integral_div_slope_le
    {F F' : Real → Real} {a b m : Real} (p : Nat → Real) (n : Nat)
    (hm0 : 0 < m) (hp : ∀ i, p i ∈ Set.uIcc a b)
    (hpmono : Monotone p) (hF'mono : MonotoneOn F' (Set.uIcc a b))
    (hF'pos : ∀ t ∈ Set.uIcc a b, 0 < F' t)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∑ i ∈ Finset.range n, (1 / F' (p i)) •
        (∫ u in F (p i)..F (p (i + 1)),
          Complex.exp (Complex.I * u))‖ ≤ 2 / m := by
  have hrecipAnti :=
    (show AntitoneOn (fun t => 1 / F' t) (Set.uIcc a b) by
      intro x hx y hy hxy
      exact one_div_le_one_div_of_le (hF'pos x hx) (hF'mono hx hy hxy))
  have hsum := norm_sum_partition_exp_integral_smul_le_of_antitone_nonneg
    (fun t => 1 / F' t) F p n
    (fun i hi => hrecipAnti (hp i) (hp (i + 1)) (hpmono (Nat.le_succ i)))
    (fun i => one_div_nonneg.mpr (hF'pos (p i) (hp i)).le)
  refine hsum.trans ?_
  have hrecipBound : 1 / F' (p 0) ≤ 1 / m := by
    have habs := one_div_le_one_div_of_le hm0 (hm (p 0) (hp 0))
    simpa [abs_of_pos (hF'pos (p 0) (hp 0))] using habs
  calc
    2 * (1 / F' (p 0)) ≤ 2 * (1 / m) := by gcongr
    _ = 2 / m := by ring

/-- Negative-slope finite-partition estimate for the exact reciprocal
weights in the first-derivative test. -/
theorem norm_sum_partition_exp_integral_div_slope_le_of_neg
    {F F' : Real → Real} {a b m : Real} (p : Nat → Real) (n : Nat)
    (hm0 : 0 < m) (hp : ∀ i, p i ∈ Set.uIcc a b)
    (hpmono : Monotone p) (hF'mono : MonotoneOn F' (Set.uIcc a b))
    (hF'neg : ∀ t ∈ Set.uIcc a b, F' t < 0)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∑ i ∈ Finset.range n, (1 / F' (p i)) •
        (∫ u in F (p i)..F (p (i + 1)),
          Complex.exp (Complex.I * u))‖ ≤ 2 / m := by
  have hrecipAnti : AntitoneOn (fun t => 1 / F' t) (Set.uIcc a b) := by
    intro x hx y hy hxy
    exact one_div_le_one_div_of_neg_of_le (hF'neg y hy)
      (hF'mono hx hy hxy)
  have hsum := norm_sum_partition_exp_integral_smul_le_of_antitone_nonpos
    (fun t => 1 / F' t) F p n
    (fun i hi => hrecipAnti (hp i) (hp (i + 1))
      (hpmono (Nat.le_succ i)))
    (fun i => one_div_nonpos.mpr (hF'neg (p i) (hp i)).le)
  refine hsum.trans ?_
  have hweightNonpos : 1 / F' (p (n - 1)) ≤ 0 :=
    one_div_nonpos.mpr (hF'neg (p (n - 1)) (hp (n - 1))).le
  have hrecipBound : |1 / F' (p (n - 1))| ≤ 1 / m := by
    simpa [abs_div] using one_div_le_one_div_of_le hm0
      (hm (p (n - 1)) (hp (n - 1)))
  calc
    -(1 / F' (p (n - 1))) * 2 =
        2 * |1 / F' (p (n - 1))| := by
      rw [abs_of_nonpos hweightNonpos]
      ring
    _ ≤ 2 * (1 / m) := by gcongr
    _ = 2 / m := by ring

/-- Without derivative information, a unit-modulus oscillatory integral is
bounded by the length of its interval.  H3 uses this only on the short central
region around a stationary point. -/
theorem norm_integral_exp_I_mul_phase_le_length
    (F : Real → Real) (a b : Real) :
    ‖∫ t in a..b, Complex.exp (Complex.I * F t)‖ ≤ |b - a| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := (1 : Real))
    (f := fun t : Real => Complex.exp (Complex.I * F t))
    (fun t ht => by simp [Complex.norm_exp])
  simpa using h

/-- The unit-modulus exponential associated to a real phase.  This definition
is local to the H3 source theorem and its two Hardy specializations. -/
def firstDerivativeOscillation (F : Real → Real) (t : Real) : Complex :=
  Complex.exp (Complex.I * F t)

/-- Reciprocal-slope primitive used by the source first-derivative test. -/
def firstDerivativeOscillationPrimitive
    (F F' : Real → Real) (t : Real) : Complex :=
  firstDerivativeOscillation F t / (Complex.I * (F' t : Complex))

/-- Curvature correction produced when the reciprocal-slope primitive is
differentiated. -/
def firstDerivativeOscillationCurvature
    (F F' F'' : Real → Real) (t : Real) : Complex :=
  firstDerivativeOscillation F t * (Complex.I * (F'' t : Complex)) /
    (Complex.I * (F' t : Complex)) ^ 2

/-- Exact derivative of the unit-modulus phase exponential. -/
theorem hasDerivAt_firstDerivativeOscillation
    {F F' : Real → Real} {t : Real} (hF : HasDerivAt F (F' t) t) :
    HasDerivAt (firstDerivativeOscillation F)
      (firstDerivativeOscillation F t *
        (Complex.I * (F' t : Complex))) t := by
  have hphase := hF.ofReal_comp.const_mul Complex.I
  have hexp := (Complex.hasDerivAt_exp
    (Complex.I * (F t : Complex))).comp t hphase
  exact hexp

/-- The phase exponential has norm one. -/
@[simp] theorem norm_firstDerivativeOscillation
    (F : Real → Real) (t : Real) :
    ‖firstDerivativeOscillation F t‖ = 1 := by
  simp [firstDerivativeOscillation, Complex.norm_exp]

/-- Phase change of variables under the exact `C¹` hypotheses. -/
theorem integral_slope_smul_firstDerivativeOscillation
    {F F' : Real → Real} {a b : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b)) :
    ∫ t in a..b, F' t • firstDerivativeOscillation F t =
      ∫ u in F a..F b, Complex.exp (Complex.I * u) := by
  have hchange := intervalIntegral.integral_deriv_smul_comp
    (f := F) (f' := F')
    (g := fun u : Real => Complex.exp (Complex.I * u))
    hF hF' (by fun_prop)
  simpa [firstDerivativeOscillation, Function.comp_apply] using hchange

/-- A reciprocal-slope weighted phase cell is the integral of the local
slope ratio times the original oscillation. -/
theorem one_div_slope_smul_integral_exp_eq_integral
    {F F' : Real → Real} {a b x : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b)) :
    (1 / F' x) • (∫ u in F a..F b, Complex.exp (Complex.I * u)) =
      ∫ t in a..b, (F' t / F' x) • firstDerivativeOscillation F t := by
  rw [← integral_slope_smul_firstDerivativeOscillation hF hF',
    ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t ht
  change (1 / F' x) • (F' t • firstDerivativeOscillation F t) =
    (F' t / F' x) • firstDerivativeOscillation F t
  rw [smul_smul]
  congr 1
  ring

/-- The cellwise approximation error is exactly the scalar slope-ratio
error because the oscillatory factor has norm one. -/
theorem norm_firstDerivativeOscillation_sub_slopeRatio
    (F F' : Real → Real) (x t : Real) :
    ‖firstDerivativeOscillation F t -
        (F' t / F' x) • firstDerivativeOscillation F t‖ =
      |1 - F' t / F' x| := by
  have heq : firstDerivativeOscillation F t -
      (F' t / F' x) • firstDerivativeOscillation F t =
      (1 - F' t / F' x) • firstDerivativeOscillation F t := by
    rw [sub_smul, one_smul]
  rw [heq, norm_smul, norm_firstDerivativeOscillation, mul_one,
    Real.norm_eq_abs]

/-- If the slope ratio is uniformly close to one on a cell, the original
oscillatory integral is close to the reciprocal-slope phase-space
estimator by the same error times the cell length. -/
theorem norm_integral_firstDerivativeOscillation_sub_cellEstimator_le
    {F F' : Real → Real} {a b x ε : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b))
    (hclose : ∀ t ∈ Set.uIcc a b, |1 - F' t / F' x| ≤ ε) :
    ‖(∫ t in a..b, firstDerivativeOscillation F t) -
        (1 / F' x) •
          (∫ u in F a..F b, Complex.exp (Complex.I * u))‖ ≤
      ε * |b - a| := by
  rw [one_div_slope_smul_integral_exp_eq_integral hF hF']
  have hoscCont : ContinuousOn (firstDerivativeOscillation F)
      (Set.uIcc a b) := by
    intro t ht
    exact (hasDerivAt_firstDerivativeOscillation (hF t ht)).continuousAt.continuousWithinAt
  have hratioCont : ContinuousOn
      (fun t => (F' t / F' x) • firstDerivativeOscillation F t)
      (Set.uIcc a b) :=
    (hF'.div_const (F' x)).smul hoscCont
  have hosc : IntervalIntegrable (firstDerivativeOscillation F) volume a b :=
    hoscCont.intervalIntegrable
  have hratio : IntervalIntegrable
      (fun t => (F' t / F' x) • firstDerivativeOscillation F t) volume a b :=
    hratioCont.intervalIntegrable
  rw [← intervalIntegral.integral_sub hosc hratio]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [norm_firstDerivativeOscillation_sub_slopeRatio]
  exact hclose t (Set.uIoc_subset_uIcc ht)

/-- Summing the cellwise comparison over an ordered finite partition gives
the same relative error times the total interval length. -/
theorem norm_integral_firstDerivativeOscillation_sub_partitionEstimator_le
    {F F' : Real → Real} {a b ε : Real} (p : Nat → Real) (n : Nat)
    (hp0 : p 0 = a) (hpn : p n = b) (hpmono : Monotone p)
    (hF : ∀ i < n, ∀ t ∈ Set.uIcc (p i) (p (i + 1)),
      HasDerivAt F (F' t) t)
    (hF' : ∀ i < n,
      ContinuousOn F' (Set.uIcc (p i) (p (i + 1))))
    (hclose : ∀ i < n, ∀ t ∈ Set.uIcc (p i) (p (i + 1)),
      |1 - F' t / F' (p i)| ≤ ε) :
    ‖(∫ t in a..b, firstDerivativeOscillation F t) -
        ∑ i ∈ Finset.range n, (1 / F' (p i)) •
          (∫ u in F (p i)..F (p (i + 1)),
            Complex.exp (Complex.I * u))‖ ≤
      ε * |b - a| := by
  have hint : ∀ i < n, IntervalIntegrable (firstDerivativeOscillation F)
      volume (p i) (p (i + 1)) := by
    intro i hi
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hasDerivAt_firstDerivativeOscillation
      (hF i hi t ht)).continuousAt.continuousWithinAt
  have hsumIntegral :
      ∑ i ∈ Finset.range n,
          (∫ t in p i..p (i + 1), firstDerivativeOscillation F t) =
        ∫ t in p 0..p n, firstDerivativeOscillation F t :=
    intervalIntegral.sum_integral_adjacent_intervals hint
  have hlength :
      ∑ i ∈ Finset.range n, |p (i + 1) - p i| = |p n - p 0| := by
    have hstep : ∀ i, |p (i + 1) - p i| = p (i + 1) - p i := by
      intro i
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr (hpmono (Nat.le_succ i))
    simp_rw [hstep]
    rw [Finset.sum_range_sub, abs_of_nonneg]
    exact sub_nonneg.mpr (hpmono (Nat.zero_le n))
  calc
    ‖(∫ t in a..b, firstDerivativeOscillation F t) -
        ∑ i ∈ Finset.range n, (1 / F' (p i)) •
          (∫ u in F (p i)..F (p (i + 1)),
            Complex.exp (Complex.I * u))‖ =
        ‖∑ i ∈ Finset.range n,
          ((∫ t in p i..p (i + 1), firstDerivativeOscillation F t) -
            (1 / F' (p i)) •
              (∫ u in F (p i)..F (p (i + 1)),
                Complex.exp (Complex.I * u)))‖ := by
      rw [Finset.sum_sub_distrib, hsumIntegral, hp0, hpn]
    _ ≤ ∑ i ∈ Finset.range n,
        ‖(∫ t in p i..p (i + 1), firstDerivativeOscillation F t) -
          (1 / F' (p i)) •
            (∫ u in F (p i)..F (p (i + 1)),
              Complex.exp (Complex.I * u))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n, ε * |p (i + 1) - p i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mem_range] at hi
      exact norm_integral_firstDerivativeOscillation_sub_cellEstimator_le
        (hF i hi) (hF' i hi) (hclose i hi)
    _ = ε * |b - a| := by rw [← Finset.mul_sum, hlength, hpn, hp0]

/-- Uniform continuity supplies a finite ordered partition on which every
left-endpoint slope ratio is uniformly close to one.  The partition is
clamped after its final point so its values stay in the source interval. -/
theorem exists_partition_slopeRatio_close
    {F' : Real → Real} {a b m ε : Real} (hab : a ≤ b)
    (hm0 : 0 < m) (hε : 0 < ε)
    (hF' : ContinuousOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ∃ (p : Nat → Real) (n : Nat),
      p 0 = a ∧ p n = b ∧ Monotone p ∧
      (∀ i, p i ∈ Set.uIcc a b) ∧
      (∀ i < n, ∀ t ∈ Set.uIcc (p i) (p (i + 1)),
        |1 - F' t / F' (p i)| ≤ ε) := by
  by_cases hdeg : a = b
  · subst b
    refine ⟨fun _ => a, 0, rfl, rfl, monotone_const, ?_, ?_⟩
    · intro i
      simp
    · intro i hi
      omega
  have hablt : a < b := lt_of_le_of_ne hab hdeg
  have hlength0 : 0 < b - a := sub_pos.mpr hablt
  have hunif : UniformContinuousOn F' (Set.uIcc a b) :=
    isCompact_uIcc.uniformContinuousOn_of_continuous hF'
  obtain ⟨δ, hδ0, hδ⟩ :=
    Metric.uniformContinuousOn_iff.mp hunif (m * ε) (mul_pos hm0 hε)
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  have hn0 : 0 < n := by
    have hquot0 : 0 < (b - a) / δ := div_pos hlength0 hδ0
    exact_mod_cast hquot0.trans hn
  have hnReal0 : 0 < (n : Real) := by exact_mod_cast hn0
  have hmesh : (b - a) / (n : Real) < δ := by
    apply (div_lt_iff₀ hnReal0).2
    simpa [mul_comm] using (div_lt_iff₀ hδ0).1 hn
  let p : Nat → Real := fun i =>
    a + (Nat.min i n : Real) * ((b - a) / (n : Real))
  have hp0 : p 0 = a := by simp [p]
  have hpn : p n = b := by
    dsimp only [p]
    simp only [min_self]
    field_simp
    ring
  have hpmono : Monotone p := by
    intro i j hij
    dsimp only [p]
    have hmin : Nat.min i n ≤ Nat.min j n :=
      min_le_min hij le_rfl
    have hcast : (Nat.min i n : Real) ≤ Nat.min j n := by
      exact_mod_cast hmin
    have hfactor := mul_le_mul_of_nonneg_right hcast
      (div_nonneg hlength0.le hnReal0.le)
    linarith
  have hp : ∀ i, p i ∈ Set.uIcc a b := by
    intro i
    rw [Set.uIcc_of_le hab]
    constructor
    · dsimp only [p]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity)
        (div_nonneg hlength0.le hnReal0.le))
    · have hmin : Nat.min i n ≤ n := Nat.min_le_right i n
      dsimp only [p]
      have hfactor : (Nat.min i n : Real) * ((b - a) / (n : Real)) ≤
          (n : Real) * ((b - a) / (n : Real)) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hmin
        · exact div_nonneg hlength0.le hnReal0.le
      calc
        a + (Nat.min i n : Real) * ((b - a) / (n : Real)) ≤
            a + (n : Real) * ((b - a) / (n : Real)) := by
              linarith
        _ = b := by
          field_simp
          ring
  refine ⟨p, n, hp0, hpn, hpmono, hp, ?_⟩
  intro i hi t ht
  have hip : p i ≤ p (i + 1) := hpmono (Nat.le_succ i)
  have htCell : t ∈ Set.Icc (p i) (p (i + 1)) := by
    simpa [Set.uIcc_of_le hip] using ht
  have htGlobal : t ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    have hpiIcc : p i ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hp i
    have hpisIcc : p (i + 1) ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hp (i + 1)
    exact ⟨hpiIcc.1.trans htCell.1,
      htCell.2.trans hpisIcc.2⟩
  have hpiGlobal := hp i
  have hdist : dist t (p i) < δ := by
    rw [Real.dist_eq]
    have hcellLength : p (i + 1) - p i =
        (b - a) / (n : Real) := by
      dsimp only [p]
      have hiLe : i ≤ n := hi.le
      have hisLe : i + 1 ≤ n := hi
      have hmini : Nat.min i n = i := Nat.min_eq_left hiLe
      have hminis : Nat.min (i + 1) n = i + 1 :=
        Nat.min_eq_left hisLe
      simp only [hmini, hminis]
      push_cast
      ring
    rw [abs_of_nonneg (sub_nonneg.mpr htCell.1)]
    exact (sub_le_sub_right htCell.2 (p i)).trans_lt
      (hcellLength.trans_lt hmesh)
  have hvar := hδ t htGlobal (p i) hpiGlobal hdist
  have hpiNe : F' (p i) ≠ 0 := by
    intro hzero
    have := hm (p i) hpiGlobal
    rw [hzero, abs_zero] at this
    linarith
  have hratio :
      1 - F' t / F' (p i) =
        (F' (p i) - F' t) / F' (p i) := by
    field_simp [hpiNe]
  rw [hratio, abs_div]
  apply (div_le_iff₀ (abs_pos.mpr hpiNe)).2
  calc
    |F' (p i) - F' t| = dist (F' t) (F' (p i)) := by
      rw [Real.dist_eq, abs_sub_comm]
    _ ≤ m * ε := hvar.le
    _ ≤ ε * |F' (p i)| := by
      nlinarith [hm (p i) hpiGlobal]

/-- Exact `C¹` first-derivative test on the positive slope component.  A
fine partition compares the original integral with Bonnet's reciprocal-slope
estimator, assigning `2 / m` to each of the two bounds. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_of_monotoneOn_of_pos
    {F F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hpos : ∀ t ∈ Set.uIcc a b, 0 < F' t)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  by_cases hdeg : a = b
  · subst b
    rw [intervalIntegral.integral_same, norm_zero]
    positivity
  have hablt : a < b := lt_of_le_of_ne hab hdeg
  have hlength0 : 0 < b - a := sub_pos.mpr hablt
  let ε : Real := 2 / (m * (b - a))
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  obtain ⟨p, n, hp0, hpn, hpmono, hp, hclose⟩ :=
    exists_partition_slopeRatio_close hab hm0 hε hF' hm
  have hcellSubset : ∀ i,
      Set.uIcc (p i) (p (i + 1)) ⊆ Set.uIcc a b := by
    intro i t ht
    have hip : p i ≤ p (i + 1) := hpmono (Nat.le_succ i)
    have htCell : t ∈ Set.Icc (p i) (p (i + 1)) := by
      simpa [Set.uIcc_of_le hip] using ht
    have hpiIcc : p i ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hp i
    have hpisIcc : p (i + 1) ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hp (i + 1)
    rw [Set.uIcc_of_le hab]
    exact ⟨hpiIcc.1.trans htCell.1,
      htCell.2.trans hpisIcc.2⟩
  let S : Complex :=
    ∑ i ∈ Finset.range n, (1 / F' (p i)) •
      (∫ u in F (p i)..F (p (i + 1)),
        Complex.exp (Complex.I * u))
  have happrox :
      ‖(∫ t in a..b, firstDerivativeOscillation F t) - S‖ ≤ 2 / m := by
    have hraw :=
      norm_integral_firstDerivativeOscillation_sub_partitionEstimator_le
        p n hp0 hpn hpmono
        (fun i hi t ht => hF t (hcellSubset i ht))
        (fun i hi => hF'.mono (hcellSubset i)) hclose
    dsimp only [S]
    calc
      ‖(∫ t in a..b, firstDerivativeOscillation F t) -
          ∑ i ∈ Finset.range n, (1 / F' (p i)) •
            (∫ u in F (p i)..F (p (i + 1)),
              Complex.exp (Complex.I * u))‖ ≤ ε * |b - a| := hraw
      _ = 2 / m := by
        rw [abs_of_pos hlength0]
        dsimp only [ε]
        field_simp
  have hest : ‖S‖ ≤ 2 / m := by
    dsimp only [S]
    exact norm_sum_partition_exp_integral_div_slope_le
      p n hm0 hp hpmono hmono hpos hm
  calc
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ =
        ‖((∫ t in a..b, firstDerivativeOscillation F t) - S) + S‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(∫ t in a..b, firstDerivativeOscillation F t) - S‖ + ‖S‖ :=
      norm_add_le _ _
    _ ≤ 2 / m + 2 / m := add_le_add happrox hest
    _ = 4 / m := by ring

/-- Exact `C¹` first-derivative test on the negative slope component.  The
same fine-partition comparison is paired with the right-endpoint form of
Bonnet's inequality. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_of_monotoneOn_of_neg
    {F F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hneg : ∀ t ∈ Set.uIcc a b, F' t < 0)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  by_cases hdeg : a = b
  · subst b
    rw [intervalIntegral.integral_same, norm_zero]
    positivity
  have hablt : a < b := lt_of_le_of_ne hab hdeg
  have hlength0 : 0 < b - a := sub_pos.mpr hablt
  let ε : Real := 2 / (m * (b - a))
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  obtain ⟨p, n, hp0, hpn, hpmono, hp, hclose⟩ :=
    exists_partition_slopeRatio_close hab hm0 hε hF' hm
  have hcellSubset : ∀ i,
      Set.uIcc (p i) (p (i + 1)) ⊆ Set.uIcc a b := by
    intro i t ht
    have hip : p i ≤ p (i + 1) := hpmono (Nat.le_succ i)
    have htCell : t ∈ Set.Icc (p i) (p (i + 1)) := by
      simpa [Set.uIcc_of_le hip] using ht
    have hpiIcc : p i ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hp i
    have hpisIcc : p (i + 1) ∈ Set.Icc a b := by
      simpa [Set.uIcc_of_le hab] using hp (i + 1)
    rw [Set.uIcc_of_le hab]
    exact ⟨hpiIcc.1.trans htCell.1,
      htCell.2.trans hpisIcc.2⟩
  let S : Complex :=
    ∑ i ∈ Finset.range n, (1 / F' (p i)) •
      (∫ u in F (p i)..F (p (i + 1)),
        Complex.exp (Complex.I * u))
  have happrox :
      ‖(∫ t in a..b, firstDerivativeOscillation F t) - S‖ ≤ 2 / m := by
    have hraw :=
      norm_integral_firstDerivativeOscillation_sub_partitionEstimator_le
        p n hp0 hpn hpmono
        (fun i hi t ht => hF t (hcellSubset i ht))
        (fun i hi => hF'.mono (hcellSubset i)) hclose
    dsimp only [S]
    calc
      ‖(∫ t in a..b, firstDerivativeOscillation F t) -
          ∑ i ∈ Finset.range n, (1 / F' (p i)) •
            (∫ u in F (p i)..F (p (i + 1)),
              Complex.exp (Complex.I * u))‖ ≤ ε * |b - a| := hraw
      _ = 2 / m := by
        rw [abs_of_pos hlength0]
        dsimp only [ε]
        field_simp
  have hest : ‖S‖ ≤ 2 / m := by
    dsimp only [S]
    exact norm_sum_partition_exp_integral_div_slope_le_of_neg
      p n hm0 hp hpmono hmono hneg hm
  calc
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ =
        ‖((∫ t in a..b, firstDerivativeOscillation F t) - S) + S‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖(∫ t in a..b, firstDerivativeOscillation F t) - S‖ + ‖S‖ :=
      norm_add_le _ _
    _ ≤ 2 / m + 2 / m := add_le_add happrox hest
    _ = 4 / m := by ring

/-- Differentiating the reciprocal-slope primitive gives the original
oscillation minus the explicit curvature correction. -/
theorem hasDerivAt_firstDerivativeOscillationPrimitive
    {F F' F'' : Real → Real} {t : Real}
    (hF : HasDerivAt F (F' t) t)
    (hF' : HasDerivAt F' (F'' t) t) (hF'ne : F' t ≠ 0) :
    HasDerivAt (firstDerivativeOscillationPrimitive F F')
      (firstDerivativeOscillation F t -
        firstDerivativeOscillationCurvature F F' F'' t) t := by
  have hnum := hasDerivAt_firstDerivativeOscillation hF
  have hden := hF'.ofReal_comp.const_mul Complex.I
  have hF'cne : (F' t : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hF'ne
  have hdenNe : Complex.I * (F' t : Complex) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hF'cne
  have hquot := hnum.div hden hdenNe
  change HasDerivAt
    (fun u : Real => firstDerivativeOscillation F u /
      (Complex.I * (F' u : Complex))) _ t
  change HasDerivAt _
    (firstDerivativeOscillation F t -
      firstDerivativeOscillation F t * (Complex.I * (F'' t : Complex)) /
        (Complex.I * (F' t : Complex)) ^ 2) t
  exact hquot.congr_deriv (by field_simp [hdenNe, hF'cne])

/-- The reciprocal-slope primitive has exactly inverse-slope norm. -/
theorem norm_firstDerivativeOscillationPrimitive
    (F F' : Real → Real) (t : Real) :
    ‖firstDerivativeOscillationPrimitive F F' t‖ = 1 / |F' t| := by
  simp [firstDerivativeOscillationPrimitive, Real.norm_eq_abs]

/-- The curvature correction has the scalar norm expected from integration
by parts. -/
theorem norm_firstDerivativeOscillationCurvature
    (F F' F'' : Real → Real) (t : Real) :
    ‖firstDerivativeOscillationCurvature F F' F'' t‖ =
      |F'' t| / |F' t| ^ 2 := by
  simp [firstDerivativeOscillationCurvature, norm_pow, Real.norm_eq_abs]

/-- The reciprocal slope differentiates to the negative scalar curvature
weight.  This turns the correction term into total variation. -/
theorem hasDerivAt_one_div_slope
    {F' F'' : Real → Real} {t : Real}
    (hF' : HasDerivAt F' (F'' t) t) (hF'ne : F' t ≠ 0) :
    HasDerivAt (fun u : Real => 1 / F' u)
      (-(F'' t / (F' t) ^ 2)) t := by
  apply ((hasDerivAt_const t (1 : Real)).div hF' hF'ne).congr_deriv
  ring

/-- A continuous nonvanishing slope has a continuous reciprocal. -/
theorem continuousOn_one_div_slope
    {F' : Real → Real} {s : Set Real} (hF' : ContinuousOn F' s)
    (hne : ∀ t ∈ s, F' t ≠ 0) :
    ContinuousOn (fun t => 1 / F' t) s :=
  continuousOn_const.div hF' hne

/-- On the positive component, reciprocation reverses a monotone slope. -/
theorem antitoneOn_one_div_slope_of_monotoneOn_of_pos
    {F' : Real → Real} {s : Set Real} (hmono : MonotoneOn F' s)
    (hpos : ∀ t ∈ s, 0 < F' t) :
    AntitoneOn (fun t => 1 / F' t) s := by
  intro x hx y hy hxy
  exact one_div_le_one_div_of_le (hpos x hx) (hmono hx hy hxy)

/-- On the negative component, reciprocation also reverses a monotone
slope. -/
theorem antitoneOn_one_div_slope_of_monotoneOn_of_neg
    {F' : Real → Real} {s : Set Real} (hmono : MonotoneOn F' s)
    (hneg : ∀ t ∈ s, F' t < 0) :
    AntitoneOn (fun t => 1 / F' t) s := by
  intro x hx y hy hxy
  exact one_div_le_one_div_of_neg_of_le (hneg y hy) (hmono hx hy hxy)

/-- The reciprocal slope inherits the uniform `1 / m` bound. -/
theorem abs_one_div_slope_le
    {F' : Real → Real} {s : Set Real} {m : Real} (hm0 : 0 < m)
    (hm : ∀ t ∈ s, m ≤ |F' t|) :
    ∀ t ∈ s, |1 / F' t| ≤ 1 / m := by
  intro t ht
  simpa [abs_div] using one_div_le_one_div_of_le hm0 (hm t ht)

/-- A continuous monotone slope bounded away from zero stays in one sign
component on the whole interval. -/
theorem monotoneOn_slope_sign
    {F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hcont : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    (∀ t ∈ Set.uIcc a b, 0 < F' t) ∨
      (∀ t ∈ Set.uIcc a b, F' t < 0) := by
  have hcontIcc : ContinuousOn F' (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using hcont
  have hmonoIcc : MonotoneOn F' (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using hmono
  have hne : ∀ t ∈ Set.Icc a b, F' t ≠ 0 := by
    intro t ht hzero
    have hbound := hm t (by simpa [Set.uIcc_of_le hab] using ht)
    rw [hzero, abs_zero] at hbound
    linarith
  by_cases ha : 0 < F' a
  · left
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ha.trans_le (hmonoIcc (Set.left_mem_Icc.mpr hab) ht ht.1)
  · have haNeg : F' a < 0 := lt_of_le_of_ne (le_of_not_gt ha) (hne a
      (Set.left_mem_Icc.mpr hab))
    by_cases hb : F' b < 0
    · right
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact (hmonoIcc ht (Set.right_mem_Icc.mpr hab) ht.2).trans_lt hb
    · have hbPos : 0 < F' b := lt_of_le_of_ne (le_of_not_gt hb)
        (hne b (Set.right_mem_Icc.mpr hab)).symm
      have hzeroMem : (0 : Real) ∈ Set.Icc (F' a) (F' b) :=
        ⟨haNeg.le, hbPos.le⟩
      obtain ⟨t, ht, htzero⟩ :=
        (intermediate_value_Icc hab hcontIcc) hzeroMem
      exact (hne t ht htzero).elim

/-- Source-shaped `C¹` first-derivative exponential-integral estimate.  A
continuous monotone slope bounded away from zero has a constant sign, and the
two Bonnet partition estimates give the same `4 / m` bound. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_c1
    {F F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  rcases monotoneOn_slope_sign hab hm0 hF' hmono hm with hpos | hneg
  · exact
      norm_integral_firstDerivativeOscillation_le_four_div_of_monotoneOn_of_pos
        hab hm0 hF hF' hmono hpos hm
  · exact
      norm_integral_firstDerivativeOscillation_le_four_div_of_monotoneOn_of_neg
        hab hm0 hF hF' hmono hneg hm

/-- Stationary-safe assembly once the interval where `|F'|` is small has
been isolated.  The two nonstationary sides cost `4 / sqrt r` each and the
central interval costs its length, at most `2 / sqrt r`. -/
theorem norm_integral_firstDerivativeOscillation_le_ten_div_sqrt_of_split
    {F F' : Real → Real} {a b c d r : Real}
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) (hr : 0 < r)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hleft : a = c ∨
      ∀ t ∈ Set.uIcc a c, Real.sqrt r ≤ |F' t|)
    (hright : d = b ∨
      ∀ t ∈ Set.uIcc d b, Real.sqrt r ≤ |F' t|)
    (hmiddle : d - c ≤ 2 / Real.sqrt r) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤
      10 / Real.sqrt r := by
  have hab : a ≤ b := hac.trans (hcd.trans hdb)
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsub : ∀ {x y : Real}, a ≤ x → x ≤ y → y ≤ b →
      Set.uIcc x y ⊆ Set.uIcc a b := by
    intro x y hax hxy hyb t ht
    rw [Set.uIcc_of_le hxy] at ht
    rw [Set.uIcc_of_le hab]
    exact ⟨hax.trans ht.1, ht.2.trans hyb⟩
  have hsubLeft : Set.uIcc a c ⊆ Set.uIcc a b :=
    hsub le_rfl hac (hcd.trans hdb)
  have hsubMiddle : Set.uIcc c d ⊆ Set.uIcc a b :=
    hsub hac hcd hdb
  have hsubRight : Set.uIcc d b ⊆ Set.uIcc a b :=
    hsub (hac.trans hcd) hdb le_rfl
  have hleftBound :
      ‖∫ t in a..c, firstDerivativeOscillation F t‖ ≤
        4 / Real.sqrt r := by
    rcases hleft with hleftDeg | hleft
    · subst c
      rw [intervalIntegral.integral_same, norm_zero]
      positivity
    · exact norm_integral_firstDerivativeOscillation_le_four_div_c1
        hac hsqrt
        (fun t ht => hF t (hsubLeft ht))
        (hF'.mono hsubLeft) (hmono.mono hsubLeft) hleft
  have hrightBound :
      ‖∫ t in d..b, firstDerivativeOscillation F t‖ ≤
        4 / Real.sqrt r := by
    rcases hright with hrightDeg | hright
    · subst d
      rw [intervalIntegral.integral_same, norm_zero]
      positivity
    · exact norm_integral_firstDerivativeOscillation_le_four_div_c1
        hdb hsqrt
        (fun t ht => hF t (hsubRight ht))
        (hF'.mono hsubRight) (hmono.mono hsubRight) hright
  have hmiddleBound :
      ‖∫ t in c..d, firstDerivativeOscillation F t‖ ≤
        2 / Real.sqrt r := by
    refine (norm_integral_exp_I_mul_phase_le_length F c d).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hcd)]
    exact hmiddle
  have hoscCont : ContinuousOn (firstDerivativeOscillation F)
      (Set.uIcc a b) := by
    intro t ht
    exact (hasDerivAt_firstDerivativeOscillation
      (hF t ht)).continuousAt.continuousWithinAt
  have hiLeft : IntervalIntegrable (firstDerivativeOscillation F) volume a c :=
    (hoscCont.mono hsubLeft).intervalIntegrable
  have hiMiddle : IntervalIntegrable (firstDerivativeOscillation F) volume c d :=
    (hoscCont.mono hsubMiddle).intervalIntegrable
  have hiRight : IntervalIntegrable (firstDerivativeOscillation F) volume d b :=
    (hoscCont.mono hsubRight).intervalIntegrable
  have hsplit :
      ∫ t in a..b, firstDerivativeOscillation F t =
        (∫ t in a..c, firstDerivativeOscillation F t) +
          ((∫ t in c..d, firstDerivativeOscillation F t) +
            ∫ t in d..b, firstDerivativeOscillation F t) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hiMiddle hiRight,
      intervalIntegral.integral_add_adjacent_intervals hiLeft
        (hiMiddle.trans hiRight)]
  rw [hsplit]
  calc
    ‖(∫ t in a..c, firstDerivativeOscillation F t) +
        ((∫ t in c..d, firstDerivativeOscillation F t) +
          ∫ t in d..b, firstDerivativeOscillation F t)‖ ≤
        ‖∫ t in a..c, firstDerivativeOscillation F t‖ +
          ‖(∫ t in c..d, firstDerivativeOscillation F t) +
            ∫ t in d..b, firstDerivativeOscillation F t‖ := norm_add_le _ _
    _ ≤ ‖∫ t in a..c, firstDerivativeOscillation F t‖ +
        (‖∫ t in c..d, firstDerivativeOscillation F t‖ +
          ‖∫ t in d..b, firstDerivativeOscillation F t‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 4 / Real.sqrt r +
        (2 / Real.sqrt r + 4 / Real.sqrt r) := by
      gcongr
    _ = 10 / Real.sqrt r := by ring

/-- A monotone differentiable slope whose derivative has magnitude at least
`r` separates values at least linearly.  Monotonicity fixes the sign of the
second derivative, so the absolute curvature hypothesis becomes `r ≤ F''`. -/
theorem mul_sub_le_slope_sub_of_monotoneOn
    {F' F'' : Real → Real} {a b r x y : Real}
    (hab : a ≤ b)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hcurv : ∀ t ∈ Set.uIcc a b, r ≤ |F'' t|)
    (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a b) (hxy : x ≤ y) :
    r * (y - x) ≤ F' y - F' x := by
  by_cases hdeg : a = b
  · subst b
    have hx' : x = a := by simpa using hx
    have hy' : y = a := by simpa using hy
    simp [hx', hy']
  have hablt : a < b := lt_of_le_of_ne hab hdeg
  have hcontIcc : ContinuousOn F' (Set.Icc a b) := by
    intro t ht
    exact (hF' t (by simpa [Set.uIcc_of_le hab] using ht)).continuousAt.continuousWithinAt
  have hmonoIcc : MonotoneOn F' (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using hmono
  have hdiff : DifferentiableOn Real F' (interior (Set.Icc a b)) := by
    rw [interior_Icc]
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    exact (hF' t (by simpa [Set.uIcc_of_le hab] using htIcc)).differentiableAt.differentiableWithinAt
  have hsecond : ∀ t ∈ interior (Set.Icc a b), r ≤ deriv F' t := by
    rw [interior_Icc]
    intro t ht
    have htIcc : t ∈ Set.Icc a b := ⟨ht.1.le, ht.2.le⟩
    have htUIcc : t ∈ Set.uIcc a b := by
      simpa [Set.uIcc_of_le hab] using htIcc
    have hderivNonneg : 0 ≤ deriv F' t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact hmonoIcc.derivWithin_nonneg
    have hderivEq : deriv F' t = F'' t := (hF' t htUIcc).deriv
    rw [hderivEq] at hderivNonneg ⊢
    simpa [abs_of_nonneg hderivNonneg] using hcurv t htUIcc
  have hxIcc : x ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hx
  have hyIcc : y ∈ Set.Icc a b := by
    simpa [Set.uIcc_of_le hab] using hy
  exact ((convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    hcontIcc hdiff hsecond) x hxIcc y hyIcc hxy

/-- Two points where the slope has magnitude at most `sqrt r` are separated
by at most `2 / sqrt r`.  This is the quantitative width bound for the
stationary region. -/
theorem sub_le_two_div_sqrt_of_slope_abs_le
    {F' F'' : Real → Real} {a b r x y : Real}
    (hab : a ≤ b) (hr : 0 < r)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hcurv : ∀ t ∈ Set.uIcc a b, r ≤ |F'' t|)
    (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a b) (hxy : x ≤ y)
    (hxsmall : |F' x| ≤ Real.sqrt r)
    (hysmall : |F' y| ≤ Real.sqrt r) :
    y - x ≤ 2 / Real.sqrt r := by
  have hsep := mul_sub_le_slope_sub_of_monotoneOn
    hab hF' hmono hcurv hx hy hxy
  have hdiffUpper : F' y - F' x ≤ 2 * Real.sqrt r := by
    calc
      F' y - F' x ≤ |F' y| + |F' x| := by
        linarith [le_abs_self (F' y), neg_le_abs (F' x)]
      _ ≤ Real.sqrt r + Real.sqrt r := add_le_add hysmall hxsmall
      _ = 2 * Real.sqrt r := by ring
  have hprod : r * (y - x) ≤ 2 * Real.sqrt r :=
    hsep.trans hdiffUpper
  have hsqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsquare : Real.sqrt r * Real.sqrt r = r :=
    Real.mul_self_sqrt hr.le
  apply (le_div_iff₀ hsqrt).2
  calc
    (y - x) * Real.sqrt r =
        (r * (y - x)) / Real.sqrt r := by
      field_simp [hsqrt.ne']
      rw [pow_two, hsquare]
    _ ≤ (2 * Real.sqrt r) / Real.sqrt r :=
      div_le_div_of_nonneg_right hprod hsqrt.le
    _ = 2 := by field_simp [hsqrt.ne']

/-- A continuous increasing slope with curvature bounded below in magnitude
admits a stationary-safe threshold split at `±sqrt r`.  Degenerate side
intervals cover the cases where the small-slope region reaches an endpoint. -/
theorem exists_stationarySafe_slope_split
    {F' F'' : Real → Real} {a b r : Real}
    (hab : a ≤ b) (hr : 0 < r)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hcurv : ∀ t ∈ Set.uIcc a b, r ≤ |F'' t|) :
    ∃ c d, a ≤ c ∧ c ≤ d ∧ d ≤ b ∧
      (a = c ∨ ∀ t ∈ Set.uIcc a c, Real.sqrt r ≤ |F' t|) ∧
      (d = b ∨ ∀ t ∈ Set.uIcc d b, Real.sqrt r ≤ |F' t|) ∧
      d - c ≤ 2 / Real.sqrt r := by
  let s := Real.sqrt r
  have hs : 0 < s := Real.sqrt_pos.2 hr
  have ha : a ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact Set.left_mem_Icc.mpr hab
  have hb : b ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    exact Set.right_mem_Icc.mpr hab
  have hmonoIcc : MonotoneOn F' (Set.Icc a b) := by
    simpa [Set.uIcc_of_le hab] using hmono
  have hcontIcc : ContinuousOn F' (Set.Icc a b) := by
    intro t ht
    exact (hF' t (by simpa [Set.uIcc_of_le hab] using ht)).continuousAt.continuousWithinAt
  have hleftOf : ∀ c ∈ Set.Icc a b, F' c ≤ -s →
      ∀ t ∈ Set.uIcc a c, s ≤ |F' t| := by
    intro c hc hcSlope t ht
    have htIcc : t ∈ Set.Icc a c := by
      simpa [Set.uIcc_of_le hc.1] using ht
    have htGlobal : t ∈ Set.Icc a b :=
      ⟨htIcc.1, htIcc.2.trans hc.2⟩
    have htle : F' t ≤ -s :=
      (hmonoIcc htGlobal hc htIcc.2).trans hcSlope
    rw [abs_of_nonpos (htle.trans (neg_nonpos.mpr hs.le))]
    linarith
  have hrightOf : ∀ d ∈ Set.Icc a b, s ≤ F' d →
      ∀ t ∈ Set.uIcc d b, s ≤ |F' t| := by
    intro d hd hdSlope t ht
    have htIcc : t ∈ Set.Icc d b := by
      simpa [Set.uIcc_of_le hd.2] using ht
    have htGlobal : t ∈ Set.Icc a b :=
      ⟨hd.1.trans htIcc.1, htIcc.2⟩
    have htle : s ≤ F' t :=
      hdSlope.trans (hmonoIcc hd htGlobal htIcc.1)
    rw [abs_of_nonneg (hs.le.trans htle)]
    exact htle
  have hwidth : ∀ c d, c ∈ Set.Icc a b → d ∈ Set.Icc a b → c ≤ d →
      |F' c| ≤ s → |F' d| ≤ s → d - c ≤ 2 / s := by
    intro c d hc hd hcd hcsmall hdsmall
    exact sub_le_two_div_sqrt_of_slope_abs_le hab hr hF' hmono hcurv
      (by simpa [Set.uIcc_of_le hab] using hc)
      (by simpa [Set.uIcc_of_le hab] using hd) hcd
      (by simpa only [s] using hcsmall) (by simpa only [s] using hdsmall)
  have hfa_le_hfb : F' a ≤ F' b :=
    hmono ha hb hab
  by_cases hfaLow : F' a ≤ -s
  · by_cases hfbLow : F' b ≤ -s
    · refine ⟨b, b, hab, le_rfl, le_rfl, Or.inr ?_, Or.inl rfl, ?_⟩
      · exact hleftOf b (Set.right_mem_Icc.mpr hab) hfbLow
      · rw [sub_self]
        exact div_nonneg (by norm_num) (Real.sqrt_nonneg r)
    · have hneg_lt_hfb : -s < F' b := lt_of_not_ge hfbLow
      have hnegMem : -s ∈ Set.Icc (F' a) (F' b) :=
        ⟨hfaLow, hneg_lt_hfb.le⟩
      obtain ⟨c, hc, hcSlope⟩ :=
        (intermediate_value_Icc hab hcontIcc) hnegMem
      by_cases hfbHigh : s ≤ F' b
      · have hposMem : s ∈ Set.Icc (F' a) (F' b) := by
          constructor
          · linarith
          · exact hfbHigh
        obtain ⟨d, hd, hdSlope⟩ :=
          (intermediate_value_Icc hab hcontIcc) hposMem
        have hcd : c ≤ d := by
          by_contra hdc
          have := hmonoIcc hd hc (le_of_not_ge hdc)
          rw [hcSlope, hdSlope] at this
          linarith
        refine ⟨c, d, hc.1, hcd, hd.2, Or.inr ?_, Or.inr ?_, ?_⟩
        · exact hleftOf c hc (by rw [hcSlope])
        · exact hrightOf d hd (by rw [hdSlope])
        · apply hwidth c d hc hd hcd
          · rw [hcSlope, abs_neg, abs_of_nonneg hs.le]
          · rw [hdSlope, abs_of_nonneg hs.le]
      · have hfbSmall : |F' b| ≤ s := by
          rw [abs_le]
          exact ⟨hneg_lt_hfb.le, le_of_not_ge hfbHigh⟩
        refine ⟨c, b, hc.1, hc.2, le_rfl, Or.inr ?_, Or.inl rfl, ?_⟩
        · exact hleftOf c hc (by rw [hcSlope])
        · apply hwidth c b hc (Set.right_mem_Icc.mpr hab) hc.2
          · rw [hcSlope, abs_neg, abs_of_nonneg hs.le]
          · exact hfbSmall
  · have hneg_lt_hfa : -s < F' a := lt_of_not_ge hfaLow
    by_cases hfaHigh : s ≤ F' a
    · refine ⟨a, a, le_rfl, le_rfl, hab, Or.inl rfl, Or.inr ?_, ?_⟩
      · exact hrightOf a (Set.left_mem_Icc.mpr hab) hfaHigh
      · rw [sub_self]
        exact div_nonneg (by norm_num) (Real.sqrt_nonneg r)
    · have hfaSmall : |F' a| ≤ s := by
        rw [abs_le]
        exact ⟨hneg_lt_hfa.le, le_of_not_ge hfaHigh⟩
      by_cases hfbHigh : s ≤ F' b
      · have hposMem : s ∈ Set.Icc (F' a) (F' b) :=
          ⟨(le_of_not_ge hfaHigh), hfbHigh⟩
        obtain ⟨d, hd, hdSlope⟩ :=
          (intermediate_value_Icc hab hcontIcc) hposMem
        refine ⟨a, d, le_rfl, hd.1, hd.2, Or.inl rfl, Or.inr ?_, ?_⟩
        · exact hrightOf d hd (by rw [hdSlope])
        · apply hwidth a d (Set.left_mem_Icc.mpr hab) hd hd.1 hfaSmall
          rw [hdSlope, abs_of_nonneg hs.le]
      · have hfbSmall : |F' b| ≤ s := by
          rw [abs_le]
          exact ⟨hneg_lt_hfa.le.trans hfa_le_hfb,
            le_of_not_ge hfbHigh⟩
        refine ⟨a, b, le_rfl, hab, le_rfl, Or.inl rfl, Or.inl rfl, ?_⟩
        exact hwidth a b (Set.left_mem_Icc.mpr hab)
          (Set.right_mem_Icc.mpr hab) hab hfaSmall hfbSmall

/-- Stationary-point-safe second-derivative estimate derived from the exact
`C¹` first-derivative theorem.  It remains valid when `F'` vanishes inside
the interval. -/
theorem norm_integral_firstDerivativeOscillation_le_ten_div_sqrt
    {F F' F'' : Real → Real} {a b r : Real}
    (hab : a ≤ b) (hr : 0 < r)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hcurv : ∀ t ∈ Set.uIcc a b, r ≤ |F'' t|) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤
      10 / Real.sqrt r := by
  obtain ⟨c, d, hac, hcd, hdb, hleft, hright, hmiddle⟩ :=
    exists_stationarySafe_slope_split hab hr hF' hmono hcurv
  have hF'cont : ContinuousOn F' (Set.uIcc a b) := by
    intro t ht
    exact (hF' t ht).continuousAt.continuousWithinAt
  exact norm_integral_firstDerivativeOscillation_le_ten_div_sqrt_of_split
    hac hcd hdb hr hF hF'cont hmono hleft hright hmiddle

/-- Exact `C¹` reciprocal-slope package: the reciprocal of a continuous
monotone slope bounded away from zero is continuous, antitone, and uniformly
bounded by `1 / m`. -/
theorem one_div_slope_c1_data
    {F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hcont : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ContinuousOn (fun t => 1 / F' t) (Set.uIcc a b) ∧
      AntitoneOn (fun t => 1 / F' t) (Set.uIcc a b) ∧
      (∀ t ∈ Set.uIcc a b, |1 / F' t| ≤ 1 / m) := by
  have hne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0 := by
    intro t ht hzero
    have hbound := hm t ht
    rw [hzero, abs_zero] at hbound
    linarith
  refine ⟨continuousOn_one_div_slope hcont hne, ?_,
    abs_one_div_slope_le hm0 hm⟩
  rcases monotoneOn_slope_sign hab hm0 hcont hmono hm with hpos | hneg
  · exact antitoneOn_one_div_slope_of_monotoneOn_of_pos hmono hpos
  · exact antitoneOn_one_div_slope_of_monotoneOn_of_neg hmono hneg

/-- The reciprocal slope in the exact `C¹` first-derivative test has
bounded variation. -/
theorem boundedVariationOn_one_div_slope
    {F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hcont : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    BoundedVariationOn (fun t => 1 / F' t) (Set.uIcc a b) := by
  obtain ⟨hrecipCont, hrecipAnti, hrecipBound⟩ :=
    one_div_slope_c1_data hab hm0 hcont hmono hm
  have hnegMono : MonotoneOn (fun t => -(1 / F' t)) (Set.uIcc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hrecipAnti hx hy hxy)
  have hnegBound :
      ∀ t ∈ Set.uIcc a b, |-(1 / F' t)| ≤ 1 / m := by
    intro t ht
    simpa only [abs_neg] using hrecipBound t ht
  have hnegVar := hnegMono.boundedVariationOn hnegBound
  unfold BoundedVariationOn at hnegVar ⊢
  have hvariation :
      eVariationOn (fun t => 1 / F' t) (Set.uIcc a b) =
        eVariationOn (fun t => -(1 / F' t)) (Set.uIcc a b) := by
    simp only [eVariationOn, edist_neg_neg]
  rwa [hvariation]

/-- Quantitative form of reciprocal-slope bounded variation. -/
theorem eVariationOn_one_div_slope_le
    {F' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hcont : ContinuousOn F' (Set.uIcc a b))
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    eVariationOn (fun t => 1 / F' t) (Set.uIcc a b) ≤
      ENNReal.ofReal (2 / m) := by
  obtain ⟨hrecipCont, hrecipAnti, hrecipBound⟩ :=
    one_div_slope_c1_data hab hm0 hcont hmono hm
  have hnegMono : MonotoneOn (fun t => -(1 / F' t)) (Set.uIcc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hrecipAnti hx hy hxy)
  have hvariation :
      eVariationOn (fun t => 1 / F' t) (Set.uIcc a b) =
        eVariationOn (fun t => -(1 / F' t)) (Set.uIcc a b) := by
    simp only [eVariationOn, edist_neg_neg]
  rw [hvariation, eVariationOn.eq_biSup_inter_Icc]
  simp only [Set.mem_setOf_eq, iSup_le_iff, and_imp, Prod.forall]
  intro x y hx hy hxy
  refine (hnegMono.eVariationOn_le hx hy).trans ?_
  apply ENNReal.ofReal_mono
  have hxBound := hrecipBound x hx
  have hyBound := hrecipBound y hy
  have hxUpper := le_abs_self (1 / F' x)
  have hyLower := neg_le_abs (1 / F' y)
  calc
    -(1 / F' y) - -(1 / F' x) ≤
        |1 / F' y| + |1 / F' x| := by linarith
    _ ≤ 1 / m + 1 / m := add_le_add hyBound hxBound
    _ = 2 / m := by ring

/-- Finite-interval integration by parts for the source first-derivative
test, solved for the original oscillatory integral. -/
theorem integral_firstDerivativeOscillation_eq_boundary_add_curvature
    {F F' F'' : Real → Real} {a b : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hF'ne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0)
    (hcurv : IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b) :
    ∫ t in a..b, firstDerivativeOscillation F t =
      firstDerivativeOscillationPrimitive F F' b -
        firstDerivativeOscillationPrimitive F F' a +
      ∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t := by
  have hosc : IntervalIntegrable (firstDerivativeOscillation F) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (hasDerivAt_firstDerivativeOscillation
      (hF t ht)).continuousAt.continuousWithinAt
  have hdiff : IntervalIntegrable
      (fun t : Real => firstDerivativeOscillation F t -
        firstDerivativeOscillationCurvature F F' F'' t) volume a b :=
    hosc.sub hcurv
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := firstDerivativeOscillationPrimitive F F')
    (f' := fun t : Real => firstDerivativeOscillation F t -
      firstDerivativeOscillationCurvature F F' F'' t)
    (fun t ht => hasDerivAt_firstDerivativeOscillationPrimitive
      (hF t ht) (hF' t ht) (hF'ne t ht)) hdiff
  rw [intervalIntegral.integral_sub hosc hcurv] at hFTC
  exact (sub_eq_iff_eq_add).mp hFTC

/-- For a differentiable monotone slope bounded away from zero, the
curvature correction is automatically interval integrable. -/
theorem intervalIntegrable_firstDerivativeOscillationCurvature_of_slopeDeriv
    {F F' F'' : Real → Real} {a b : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hF''int : IntervalIntegrable F'' volume a b)
    (hne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0) :
    IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b := by
  have hF''complex : IntervalIntegrable (fun t : Real => (F'' t : Complex)) volume a b :=
    ⟨Complex.ofRealCLM.integrable_comp hF''int.1,
      Complex.ofRealCLM.integrable_comp hF''int.2⟩
  let A : Real → Complex := fun t =>
    firstDerivativeOscillation F t * Complex.I /
      (Complex.I * (F' t : Complex)) ^ 2
  have hA : ContinuousOn A (Set.uIcc a b) := by
    intro t ht
    have hosc := (hasDerivAt_firstDerivativeOscillation
      (hF t ht)).continuousAt
    have hslope := Complex.continuous_ofReal.continuousAt.comp
      (hF' t ht).continuousAt
    have hden : Complex.I * (F' t : Complex) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hne t ht))
    exact ((hosc.mul continuousAt_const).div
      ((continuousAt_const.mul hslope).pow 2) (pow_ne_zero 2 hden)).continuousWithinAt
  have hprod := hF''complex.continuousOn_mul hA
  apply hprod.congr
  intro t ht
  have ht' := Set.uIoc_subset_uIcc ht
  have hden : Complex.I * (F' t : Complex) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (hne t ht'))
  change A t * (F'' t : Complex) =
    firstDerivativeOscillationCurvature F F' F'' t
  simp only [A, firstDerivativeOscillationCurvature]
  field_simp [hden]

/-- Monotonicity makes the slope derivative integrable, hence so is the
curvature correction. -/
theorem intervalIntegrable_firstDerivativeOscillationCurvature_of_monotoneOn
    {F F' F'' : Real → Real} {a b : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0) :
    IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b := by
  have hF''int : IntervalIntegrable F'' volume a b := by
    apply hmono.intervalIntegrable_deriv.congr
    intro t ht
    exact (hF' t (Set.uIoc_subset_uIcc ht)).deriv
  exact intervalIntegrable_firstDerivativeOscillationCurvature_of_slopeDeriv
    hF hF' hF''int hne

/-- The same automatic curvature integrability holds for an antitone slope. -/
theorem intervalIntegrable_firstDerivativeOscillationCurvature_of_antitoneOn
    {F F' F'' : Real → Real} {a b : Real}
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hanti : AntitoneOn F' (Set.uIcc a b))
    (hne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0) :
    IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b := by
  have hnegmono : MonotoneOn (fun t => -F' t) (Set.uIcc a b) := by
    intro x hx y hy hxy
    exact neg_le_neg (hanti hx hy hxy)
  have hnegint : IntervalIntegrable (fun t => -F'' t) volume a b := by
    apply hnegmono.intervalIntegrable_deriv.congr
    intro t ht
    exact ((hF' t (Set.uIoc_subset_uIcc ht)).neg.deriv)
  have hF''int : IntervalIntegrable F'' volume a b := by
    apply hnegint.neg.congr
    intro t ht
    simp
  exact intervalIntegrable_firstDerivativeOscillationCurvature_of_slopeDeriv
    hF hF' hF''int hne

/-- When the slope derivative is nonnegative, the curvature correction is
bounded by the endpoint variation of the reciprocal slope. -/
theorem norm_integral_firstDerivativeOscillationCurvature_le_two_div_of_nonneg
    {F F' F'' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hF'ne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0)
    (hF'' : ∀ t ∈ Set.uIoo a b, 0 ≤ F'' t)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|)
    (hcurv : IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b) :
    ‖∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t‖ ≤
      2 / m := by
  have hnormEq : Set.EqOn
      (fun t : Real => ‖firstDerivativeOscillationCurvature F F' F'' t‖)
      (fun t : Real => F'' t / (F' t) ^ 2) (Set.uIoo a b) := by
    intro t ht
    change ‖firstDerivativeOscillationCurvature F F' F'' t‖ =
      F'' t / (F' t) ^ 2
    rw [norm_firstDerivativeOscillationCurvature,
      abs_of_nonneg (hF'' t ht), sq_abs]
  have hscalar : IntervalIntegrable
      (fun t : Real => F'' t / (F' t) ^ 2) volume a b :=
    hcurv.norm.congr_uIoo hnormEq
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : Real => 1 / F' t)
    (f' := fun t : Real => -(F'' t / (F' t) ^ 2))
    (fun t ht => hasDerivAt_one_div_slope
      (hF' t ht) (hF'ne t ht)) hscalar.neg
  have hintegral :
      ∫ t in a..b, F'' t / (F' t) ^ 2 = 1 / F' a - 1 / F' b := by
    rw [intervalIntegral.integral_neg] at hFTC
    linarith
  have hmA : m ≤ |F' a| := hm a Set.left_mem_uIcc
  have hmB : m ≤ |F' b| := hm b Set.right_mem_uIcc
  have hA : |1 / F' a| ≤ 1 / m := by
    simpa [abs_div] using one_div_le_one_div_of_le hm0 hmA
  have hB : |1 / F' b| ≤ 1 / m := by
    simpa [abs_div] using one_div_le_one_div_of_le hm0 hmB
  calc
    ‖∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t‖ ≤
        ∫ t in a..b, ‖firstDerivativeOscillationCurvature F F' F'' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, F'' t / (F' t) ^ 2 :=
      intervalIntegral.integral_congr_uIoo hnormEq
    _ = 1 / F' a - 1 / F' b := hintegral
    _ ≤ |1 / F' a| + |1 / F' b| := by
      linarith [le_abs_self (1 / F' a), neg_le_abs (1 / F' b)]
    _ ≤ 1 / m + 1 / m := add_le_add hA hB
    _ = 2 / m := by ring

/-- Smooth increasing-slope form of the first-derivative test.  The two
reciprocal-slope boundary terms and the curvature variation give the exact
source constant `4 / m`. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_of_nonneg
    {F F' F'' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hF'ne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0)
    (hF'' : ∀ t ∈ Set.uIoo a b, 0 ≤ F'' t)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|)
    (hcurv : IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  have hboundaryA :
      ‖firstDerivativeOscillationPrimitive F F' a‖ ≤ 1 / m := by
    rw [norm_firstDerivativeOscillationPrimitive]
    exact one_div_le_one_div_of_le hm0 (hm a Set.left_mem_uIcc)
  have hboundaryB :
      ‖firstDerivativeOscillationPrimitive F F' b‖ ≤ 1 / m := by
    rw [norm_firstDerivativeOscillationPrimitive]
    exact one_div_le_one_div_of_le hm0 (hm b Set.right_mem_uIcc)
  have hcurvBound :=
    norm_integral_firstDerivativeOscillationCurvature_le_two_div_of_nonneg
      (F := F) hab hm0 hF' hF'ne hF'' hm hcurv
  rw [integral_firstDerivativeOscillation_eq_boundary_add_curvature
    hF hF' hF'ne hcurv]
  calc
    ‖firstDerivativeOscillationPrimitive F F' b -
          firstDerivativeOscillationPrimitive F F' a +
        ∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t‖ ≤
        ‖firstDerivativeOscillationPrimitive F F' b -
          firstDerivativeOscillationPrimitive F F' a‖ +
        ‖∫ t in a..b,
          firstDerivativeOscillationCurvature F F' F'' t‖ :=
      norm_add_le _ _
    _ ≤ (‖firstDerivativeOscillationPrimitive F F' b‖ +
          ‖firstDerivativeOscillationPrimitive F F' a‖) +
        ‖∫ t in a..b,
          firstDerivativeOscillationCurvature F F' F'' t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (1 / m + 1 / m) + 2 / m :=
      add_le_add (add_le_add hboundaryB hboundaryA) hcurvBound
    _ = 4 / m := by ring

/-- Decreasing-slope counterpart of the reciprocal-variation estimate. -/
theorem norm_integral_firstDerivativeOscillationCurvature_le_two_div_of_nonpos
    {F F' F'' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hF'ne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0)
    (hF'' : ∀ t ∈ Set.uIoo a b, F'' t ≤ 0)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|)
    (hcurv : IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b) :
    ‖∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t‖ ≤
      2 / m := by
  have hnormEq : Set.EqOn
      (fun t : Real => ‖firstDerivativeOscillationCurvature F F' F'' t‖)
      (fun t : Real => -(F'' t / (F' t) ^ 2)) (Set.uIoo a b) := by
    intro t ht
    change ‖firstDerivativeOscillationCurvature F F' F'' t‖ =
      -(F'' t / (F' t) ^ 2)
    rw [norm_firstDerivativeOscillationCurvature,
      abs_of_nonpos (hF'' t ht), sq_abs]
    ring
  have hscalar : IntervalIntegrable
      (fun t : Real => -(F'' t / (F' t) ^ 2)) volume a b :=
    hcurv.norm.congr_uIoo hnormEq
  have hintegral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : Real => 1 / F' t)
    (f' := fun t : Real => -(F'' t / (F' t) ^ 2))
    (fun t ht => hasDerivAt_one_div_slope
      (hF' t ht) (hF'ne t ht)) hscalar
  have hmA : m ≤ |F' a| := hm a Set.left_mem_uIcc
  have hmB : m ≤ |F' b| := hm b Set.right_mem_uIcc
  have hA : |1 / F' a| ≤ 1 / m := by
    simpa [abs_div] using one_div_le_one_div_of_le hm0 hmA
  have hB : |1 / F' b| ≤ 1 / m := by
    simpa [abs_div] using one_div_le_one_div_of_le hm0 hmB
  calc
    ‖∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t‖ ≤
        ∫ t in a..b, ‖firstDerivativeOscillationCurvature F F' F'' t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, -(F'' t / (F' t) ^ 2) :=
      intervalIntegral.integral_congr_uIoo hnormEq
    _ = 1 / F' b - 1 / F' a := hintegral
    _ ≤ |1 / F' b| + |1 / F' a| := by
      linarith [le_abs_self (1 / F' b), neg_le_abs (1 / F' a)]
    _ ≤ 1 / m + 1 / m := add_le_add hB hA
    _ = 2 / m := by ring

/-- Smooth decreasing-slope form of the first-derivative test. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_of_nonpos
    {F F' F'' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hF'ne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0)
    (hF'' : ∀ t ∈ Set.uIoo a b, F'' t ≤ 0)
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|)
    (hcurv : IntervalIntegrable
      (firstDerivativeOscillationCurvature F F' F'') volume a b) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  have hboundaryA :
      ‖firstDerivativeOscillationPrimitive F F' a‖ ≤ 1 / m := by
    rw [norm_firstDerivativeOscillationPrimitive]
    exact one_div_le_one_div_of_le hm0 (hm a Set.left_mem_uIcc)
  have hboundaryB :
      ‖firstDerivativeOscillationPrimitive F F' b‖ ≤ 1 / m := by
    rw [norm_firstDerivativeOscillationPrimitive]
    exact one_div_le_one_div_of_le hm0 (hm b Set.right_mem_uIcc)
  have hcurvBound :=
    norm_integral_firstDerivativeOscillationCurvature_le_two_div_of_nonpos
      (F := F) hab hm0 hF' hF'ne hF'' hm hcurv
  rw [integral_firstDerivativeOscillation_eq_boundary_add_curvature
    hF hF' hF'ne hcurv]
  calc
    ‖firstDerivativeOscillationPrimitive F F' b -
          firstDerivativeOscillationPrimitive F F' a +
        ∫ t in a..b, firstDerivativeOscillationCurvature F F' F'' t‖ ≤
        ‖firstDerivativeOscillationPrimitive F F' b -
          firstDerivativeOscillationPrimitive F F' a‖ +
        ‖∫ t in a..b,
          firstDerivativeOscillationCurvature F F' F'' t‖ :=
      norm_add_le _ _
    _ ≤ (‖firstDerivativeOscillationPrimitive F F' b‖ +
          ‖firstDerivativeOscillationPrimitive F F' a‖) +
        ‖∫ t in a..b,
          firstDerivativeOscillationCurvature F F' F'' t‖ :=
      add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (1 / m + 1 / m) + 2 / m :=
      add_le_add (add_le_add hboundaryB hboundaryA) hcurvBound
    _ = 4 / m := by ring

/-- Smooth monotone-slope first-derivative test.  Monotonicity supplies the
sign of the second derivative on the open interval. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_of_monotoneOn
    {F F' F'' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hmono : MonotoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  have hne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0 := by
    intro t ht hzero
    have := hm t ht
    rw [hzero, abs_zero] at this
    linarith
  have hsecond : ∀ t ∈ Set.uIoo a b, 0 ≤ F'' t := by
    intro t ht
    rw [Set.uIoo_of_le hab] at ht
    have htIcc : t ∈ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      exact ⟨ht.1.le, ht.2.le⟩
    have hmonoIcc : MonotoneOn F' (Set.Icc a b) := by
      simpa [Set.uIcc_of_le hab] using hmono
    have hderiv : 0 ≤ deriv F' t := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact hmonoIcc.derivWithin_nonneg
    simpa [(hF' t htIcc).deriv] using hderiv
  have hcurv :=
    intervalIntegrable_firstDerivativeOscillationCurvature_of_monotoneOn
      hF hF' hmono hne
  exact norm_integral_firstDerivativeOscillation_le_four_div_of_nonneg
    hab hm0 hF hF' hne hsecond hm hcurv

/-- Smooth antitone-slope first-derivative test. -/
theorem norm_integral_firstDerivativeOscillation_le_four_div_of_antitoneOn
    {F F' F'' : Real → Real} {a b m : Real} (hab : a ≤ b) (hm0 : 0 < m)
    (hF : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t)
    (hF' : ∀ t ∈ Set.uIcc a b, HasDerivAt F' (F'' t) t)
    (hanti : AntitoneOn F' (Set.uIcc a b))
    (hm : ∀ t ∈ Set.uIcc a b, m ≤ |F' t|) :
    ‖∫ t in a..b, firstDerivativeOscillation F t‖ ≤ 4 / m := by
  have hne : ∀ t ∈ Set.uIcc a b, F' t ≠ 0 := by
    intro t ht hzero
    have := hm t ht
    rw [hzero, abs_zero] at this
    linarith
  have hsecond : ∀ t ∈ Set.uIoo a b, F'' t ≤ 0 := by
    intro t ht
    rw [Set.uIoo_of_le hab] at ht
    have htIcc : t ∈ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      exact ⟨ht.1.le, ht.2.le⟩
    have hantiIcc : AntitoneOn F' (Set.Icc a b) := by
      simpa [Set.uIcc_of_le hab] using hanti
    have hderiv : deriv F' t ≤ 0 := by
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
      exact hantiIcc.derivWithin_nonpos
    simpa [(hF' t htIcc).deriv] using hderiv
  have hcurv :=
    intervalIntegrable_firstDerivativeOscillationCurvature_of_antitoneOn
      hF hF' hanti hne
  exact norm_integral_firstDerivativeOscillation_le_four_div_of_nonpos
    hab hm0 hF hF' hne hsecond hm hcurv

/-- The oscillatory phase appearing after combining the critical-line
Stirling phase with the `n`th Dirichlet monomial.  On positive inputs this is
`(t / 2) * log (t / (2 * pi * e * n^2))`. -/
def hardyOscillatoryPhase (n : Nat) (t : Real) : Real :=
  (t / 2) * Real.log (t / (2 * Real.pi * (n : Real) ^ 2)) - t / 2

/-- The logarithmic factor in the derivative of the Hardy phase. -/
def hardyOscillatoryPhaseDeriv (n : Nat) (t : Real) : Real :=
  (1 / 2) * Real.log (t / (2 * Real.pi * (n : Real) ^ 2))

/-- Positive-height form of the source phase, with Euler's number left in the
logarithmic denominator exactly as in the Hardy argument. -/
theorem hardyOscillatoryPhase_eq_sourceForm
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    hardyOscillatoryPhase n t =
      (t / 2) * Real.log
        (t / (2 * Real.pi * Real.exp 1 * (n : Real) ^ 2)) := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hbase : (2 * Real.pi * (n : Real) ^ 2) ≠ 0 := by positivity
  have hquot :
      t / (2 * Real.pi * Real.exp 1 * (n : Real) ^ 2) =
        (t / (2 * Real.pi * (n : Real) ^ 2)) / Real.exp 1 := by
    field_simp [hbase, Real.exp_ne_zero]
  rw [hquot, Real.log_div (div_ne_zero ht.ne' hbase) (Real.exp_ne_zero 1),
    Real.log_exp]
  unfold hardyOscillatoryPhase
  ring

/-- The source phase has the expected first derivative at positive height
for every positive integer mode. -/
theorem hasDerivAt_hardyOscillatoryPhase
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    HasDerivAt (hardyOscillatoryPhase n)
      (hardyOscillatoryPhaseDeriv n t) t := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hden : (2 * Real.pi * (n : Real) ^ 2) ≠ 0 := by positivity
  have harg : t / (2 * Real.pi * (n : Real) ^ 2) ≠ 0 :=
    div_ne_zero ht.ne' hden
  have hlogRaw :=
    ((hasDerivAt_id t).div_const
      (2 * Real.pi * (n : Real) ^ 2)).log harg
  have hquot :
      1 / (2 * Real.pi * (n : Real) ^ 2) /
          (t / (2 * Real.pi * (n : Real) ^ 2)) = 1 / t := by
    field_simp [ht.ne', hden]
  have hlog :
      HasDerivAt
        (fun u : Real => Real.log
          (u / (2 * Real.pi * (n : Real) ^ 2)))
        (1 / t) t := by
    simpa only [id_eq, hquot] using hlogRaw
  have hraw := ((hasDerivAt_id t).div_const 2).mul hlog
  have hlinear := (hasDerivAt_id t).div_const 2
  have hfun :
      hardyOscillatoryPhase n =
        ((fun u : Real => u / 2) *
          fun u : Real => Real.log
            (u / (2 * Real.pi * (n : Real) ^ 2))) -
          fun u : Real => u / 2 := by
    funext u
    rfl
  rw [hfun]
  apply (hraw.sub hlinear).congr_deriv
  unfold hardyOscillatoryPhaseDeriv
  simp only [id_eq]
  field_simp [ht.ne']
  ring

/-- Pointwise derivative identity for the source phase. -/
theorem deriv_hardyOscillatoryPhase
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    deriv (hardyOscillatoryPhase n) t =
      hardyOscillatoryPhaseDeriv n t :=
  (hasDerivAt_hardyOscillatoryPhase hn ht).deriv

/-- The first derivative of the Hardy source phase is strictly increasing on
the positive axis. -/
theorem strictMonoOn_hardyOscillatoryPhaseDeriv
    {n : Nat} (hn : 0 < n) :
    StrictMonoOn (hardyOscillatoryPhaseDeriv n) (Set.Ioi 0) := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hden : 0 < 2 * Real.pi * (n : Real) ^ 2 := by positivity
  intro x hx y hy hxy
  unfold hardyOscillatoryPhaseDeriv
  apply mul_lt_mul_of_pos_left _ (by norm_num)
  exact Real.log_lt_log (div_pos hx hden) (div_lt_div_of_pos_right hxy hden)

/-- Monotonicity form required by the source first-derivative test. -/
theorem monotoneOn_hardyOscillatoryPhaseDeriv
    {n : Nat} (hn : 0 < n) :
    MonotoneOn (hardyOscillatoryPhaseDeriv n) (Set.Ioi 0) :=
  (strictMonoOn_hardyOscillatoryPhaseDeriv hn).monotoneOn

/-- The derivative of the source phase has curvature `1 / (2 * t)` at
positive height. -/
theorem hasDerivAt_hardyOscillatoryPhaseDeriv
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    HasDerivAt (hardyOscillatoryPhaseDeriv n) (1 / (2 * t)) t := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hden : (2 * Real.pi * (n : Real) ^ 2) ≠ 0 := by positivity
  have harg : t / (2 * Real.pi * (n : Real) ^ 2) ≠ 0 :=
    div_ne_zero ht.ne' hden
  have hlogRaw :=
    ((hasDerivAt_id t).div_const
      (2 * Real.pi * (n : Real) ^ 2)).log harg
  have hquot :
      1 / (2 * Real.pi * (n : Real) ^ 2) /
          (t / (2 * Real.pi * (n : Real) ^ 2)) = 1 / t := by
    field_simp [ht.ne', hden]
  have hlog :
      HasDerivAt
        (fun u : Real => Real.log
          (u / (2 * Real.pi * (n : Real) ^ 2)))
        (1 / t) t := by
    simpa only [id_eq, hquot] using hlogRaw
  apply (hlog.const_mul (1 / 2)).congr_deriv
  field_simp [ht.ne']

/-- The displayed source derivative is continuous throughout the positive
axis. -/
theorem continuousOn_hardyOscillatoryPhaseDeriv
    {n : Nat} (hn : 0 < n) :
    ContinuousOn (hardyOscillatoryPhaseDeriv n) (Set.Ioi 0) := by
  intro t ht
  exact (hasDerivAt_hardyOscillatoryPhaseDeriv hn ht).continuousAt.continuousWithinAt

/-- The exact second derivative of the Hardy phase on the positive axis. -/
theorem secondDeriv_hardyOscillatoryPhase
    {n : Nat} (hn : 0 < n) {t : Real} (ht : 0 < t) :
    deriv (deriv (hardyOscillatoryPhase n)) t = 1 / (2 * t) := by
  have hlocal :
      Filter.EventuallyEq (nhds t) (deriv (hardyOscillatoryPhase n))
        (hardyOscillatoryPhaseDeriv n) := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact deriv_hardyOscillatoryPhase hn hu
  rw [Filter.EventuallyEq.deriv_eq hlocal]
  exact (hasDerivAt_hardyOscillatoryPhaseDeriv hn ht).deriv

/-- On the Hardy dyadic interval `[T, 2T]`, the source curvature is bounded
below by `1 / (4T)`. -/
theorem one_div_four_mul_le_secondDeriv_hardyOscillatoryPhase
    {n : Nat} (hn : 0 < n) {T t : Real} (hT : 0 < T)
    (ht : t ∈ Set.Icc T (2 * T)) :
    1 / (4 * T) ≤ deriv (deriv (hardyOscillatoryPhase n)) t := by
  have ht0 : 0 < t := hT.trans_le ht.1
  rw [secondDeriv_hardyOscillatoryPhase hn ht0]
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * T)
    (by positivity : 0 < 2 * t)).2
  nlinarith [ht.2]

/-- The stationary-safe second-derivative estimate specialized to the Hardy
source phase on `[T, 2T]`.  Its curvature floor `1 / (4T)` gives the declared
`20 * sqrt T` bound. -/
theorem norm_integral_hardyOscillatoryPhase_le_twenty_mul_sqrt
    {n : Nat} (hn : 0 < n) {T : Real} (hT : 0 < T) :
    ‖∫ t in T..2 * T,
        firstDerivativeOscillation (hardyOscillatoryPhase n) t‖ ≤
      20 * Real.sqrt T := by
  have hTle : T ≤ 2 * T := by linarith
  have hr : 0 < (1 / (4 * T) : Real) := by positivity
  have hraw := norm_integral_firstDerivativeOscillation_le_ten_div_sqrt
    hTle hr
    (F := hardyOscillatoryPhase n)
    (F' := hardyOscillatoryPhaseDeriv n)
    (F'' := fun t : Real => 1 / (2 * t))
    (fun t ht => by
      rw [Set.uIcc_of_le hTle] at ht
      exact hasDerivAt_hardyOscillatoryPhase hn (hT.trans_le ht.1))
    (fun t ht => by
      rw [Set.uIcc_of_le hTle] at ht
      exact hasDerivAt_hardyOscillatoryPhaseDeriv hn (hT.trans_le ht.1))
    ((monotoneOn_hardyOscillatoryPhaseDeriv hn).mono (by
      intro t ht
      rw [Set.uIcc_of_le hTle] at ht
      exact hT.trans_le ht.1))
    (fun t ht => by
      rw [Set.uIcc_of_le hTle] at ht
      have ht0 : 0 < t := hT.trans_le ht.1
      rw [abs_of_pos (by positivity : 0 < 1 / (2 * t))]
      apply (div_le_div_iff₀ (by positivity : 0 < 4 * T)
        (by positivity : 0 < 2 * t)).2
      nlinarith [ht.2])
  refine hraw.trans_eq ?_
  rw [Real.sqrt_div (by norm_num : (0 : Real) ≤ 1), Real.sqrt_one,
    Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
  have hsqrtFour : Real.sqrt (4 : Real) = 2 := by
    exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hsqrtFour]
  field_simp [Real.sqrt_pos.2 hT]
  norm_num

/-- Beyond the source split `3 * sqrt (T / pi)`, the Hardy phase derivative
is uniformly at most `-4/9` throughout `[T, 2T]`. -/
theorem hardyOscillatoryPhaseDeriv_le_neg_four_ninths
    {n : Nat} {T t : Real} (hT : 0 < T)
    (hnlarge : 3 * Real.sqrt (T / Real.pi) < (n : Real))
    (ht : t ∈ Set.Icc T (2 * T)) :
    hardyOscillatoryPhaseDeriv n t ≤ -(4 / 9 : Real) := by
  have hn0 : 0 < (n : Real) := by
    have hsqrt0 : 0 ≤ Real.sqrt (T / Real.pi) := Real.sqrt_nonneg _
    linarith
  have ht0 : 0 < t := hT.trans_le ht.1
  have hquot0 : 0 ≤ T / Real.pi := div_nonneg hT.le Real.pi_pos.le
  have hsqrtSq : (Real.sqrt (T / Real.pi)) ^ 2 = T / Real.pi :=
    Real.sq_sqrt hquot0
  have hnsq : 9 * (T / Real.pi) < (n : Real) ^ 2 := by
    have hdiff : 0 < (n : Real) - 3 * Real.sqrt (T / Real.pi) :=
      sub_pos.mpr hnlarge
    have hsum : 0 < (n : Real) + 3 * Real.sqrt (T / Real.pi) := by
      positivity
    have hprod := mul_pos hdiff hsum
    nlinarith [hsqrtSq, hprod]
  have hpiSq : 9 * T < Real.pi * (n : Real) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_left hnsq Real.pi_pos
    calc
      9 * T = Real.pi * (9 * (T / Real.pi)) := by
        field_simp [Real.pi_ne_zero]
      _ < Real.pi * (n : Real) ^ 2 := hmul
  have hratio :
      9 ≤ (2 * Real.pi * (n : Real) ^ 2) / t := by
    apply (le_div_iff₀ ht0).2
    nlinarith [ht.2, hpiSq]
  have hlogNine : (8 / 9 : Real) ≤ Real.log 9 := by
    have hlogThree := Real.log_three_gt_d9
    rw [show (9 : Real) = 3 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    norm_num at hlogThree ⊢
    linarith
  have hratio0 : 0 < (2 * Real.pi * (n : Real) ^ 2) / t := by positivity
  have hlogRatio : (8 / 9 : Real) ≤
      Real.log ((2 * Real.pi * (n : Real) ^ 2) / t) := by
    exact hlogNine.trans (Real.log_le_log (by norm_num) hratio)
  have hden0 : 0 < 2 * Real.pi * (n : Real) ^ 2 := by positivity
  have hlogNeg :
      Real.log (t / (2 * Real.pi * (n : Real) ^ 2)) =
        -Real.log ((2 * Real.pi * (n : Real) ^ 2) / t) := by
    rw [Real.log_div ht0.ne' hden0.ne',
      Real.log_div hden0.ne' ht0.ne']
    ring
  unfold hardyOscillatoryPhaseDeriv
  rw [hlogNeg]
  linarith

/-- The source first-derivative estimate gives the declared constant `9` for
every Hardy mode beyond `3 * sqrt (T / pi)`. -/
theorem norm_integral_hardyOscillatoryPhase_le_nine_of_large_mode
    {n : Nat} (hn : 0 < n) {T : Real} (hT : 0 < T)
    (hnlarge : 3 * Real.sqrt (T / Real.pi) < (n : Real)) :
    ‖∫ t in T..2 * T,
        firstDerivativeOscillation (hardyOscillatoryPhase n) t‖ ≤ 9 := by
  have hTle : T ≤ 2 * T := by linarith
  have hm0 : (0 : Real) < 4 / 9 := by norm_num
  have hbound := norm_integral_firstDerivativeOscillation_le_four_div_c1
    hTle hm0
    (F := hardyOscillatoryPhase n)
    (F' := hardyOscillatoryPhaseDeriv n)
    (fun t ht => by
      rw [Set.uIcc_of_le hTle] at ht
      exact hasDerivAt_hardyOscillatoryPhase hn (hT.trans_le ht.1))
    ((continuousOn_hardyOscillatoryPhaseDeriv hn).mono (by
      intro t ht
      rw [Set.uIcc_of_le hTle] at ht
      exact hT.trans_le ht.1))
    ((monotoneOn_hardyOscillatoryPhaseDeriv hn).mono (by
      intro t ht
      rw [Set.uIcc_of_le hTle] at ht
      exact hT.trans_le ht.1))
    (fun t ht => by
      rw [Set.uIcc_of_le hTle] at ht
      have hneg := hardyOscillatoryPhaseDeriv_le_neg_four_ninths
        hT hnlarge ht
      rw [abs_of_nonpos (hneg.trans (by norm_num))]
      linarith)
  norm_num at hbound ⊢
  exact hbound

end

end Hardy

end RiemannHypothesisProject
