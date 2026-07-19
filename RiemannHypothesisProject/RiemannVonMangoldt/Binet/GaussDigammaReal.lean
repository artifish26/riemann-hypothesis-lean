import Mathlib.NumberTheory.Harmonic.GammaDeriv
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.GaussDigammaSeries

/-!
# Gauss's digamma series on the positive real axis

This module identifies the reciprocal-series limit from
`GaussDigammaSeries` with the logarithmic derivative of `Gamma` on positive
real arguments.  The asymptotic input is the Bohr--Mollerup convexity theorem,
already available in mathlib.
-/

open Filter Set Topology

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- On the positive real axis, the complex digamma function is the real
derivative of `log Gamma`. -/
theorem digamma_ofReal_eq_deriv_logGamma {x : Real} (hx : 0 < x) :
    Complex.digamma (x : Complex) =
      ((deriv (Real.log ∘ Real.Gamma) x : Real) : Complex) := by
  have hGammaReal : DifferentiableAt Real Real.Gamma x :=
    Real.differentiableAt_Gamma (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
  have hGammaComplex : DifferentiableAt Complex Complex.Gamma (x : Complex) :=
    Complex.differentiableAt_Gamma (x : Complex) (fun m => by
      intro h
      have hre := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith)
  have hderivGamma :
      deriv Complex.Gamma (x : Complex) =
        ((deriv Real.Gamma x : Real) : Complex) := by
    have hc : HasDerivAt (fun y : Real => Complex.Gamma (y : Complex))
        (deriv Complex.Gamma (x : Complex)) x :=
      hGammaComplex.hasDerivAt.comp_ofReal
    have hr : HasDerivAt (fun y : Real => (Real.Gamma y : Complex))
        ((deriv Real.Gamma x : Real) : Complex) x :=
      hGammaReal.hasDerivAt.ofReal_comp
    have hc' : HasDerivAt (fun y : Real => (Real.Gamma y : Complex))
        (deriv Complex.Gamma (x : Complex)) x := by
      simpa only [Complex.Gamma_ofReal] using hc
    exact hc'.unique hr
  rw [Complex.digamma_def, logDeriv_apply, hderivGamma,
    Complex.Gamma_ofReal]
  rw [Function.comp_def, deriv.log hGammaReal
    (Real.Gamma_ne_zero (fun m => by
      have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
      linarith))]
  exact (Complex.ofReal_div _ _).symm

/-- The logarithmic derivative of the real Gamma function satisfies the
usual unit-shift recurrence on the positive half-line. -/
theorem deriv_logGamma_add_one {x : Real} (hx : 0 < x) :
    deriv (Real.log ∘ Real.Gamma) (x + 1) =
      deriv (Real.log ∘ Real.Gamma) x + 1 / x := by
  let f := Real.log ∘ Real.Gamma
  have hrec (y : Real) (hy : 0 < y) :
      f (y + 1) = f y + Real.log y := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hy.ne',
      Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]
  have hder {y : Real} (hy : 0 < y) : DifferentiableAt Real f y := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
      exact fun m => ne_of_gt (by
        have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
        linarith)
  change deriv f (x + 1) = deriv f x + 1 / x
  rw [← deriv_comp_add_const, one_div, ← Real.deriv_log,
    ← deriv_add (hder (by positivity)) (Real.differentiableAt_log hx.ne')]
  apply EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hx] using hrec

/-- Iterating the unit-shift recurrence expresses a translated logarithmic
Gamma derivative by a finite reciprocal sum. -/
theorem deriv_logGamma_add_nat {x : Real} (hx : 0 < x) (n : Nat) :
    deriv (Real.log ∘ Real.Gamma) (x + n) =
      deriv (Real.log ∘ Real.Gamma) x +
        ∑ k ∈ Finset.range n, 1 / (x + k) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [Nat.cast_succ, show x + ((n : Real) + 1) =
        (x + (n : Real)) + 1 by ring,
        deriv_logGamma_add_one (by
          have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
          linarith), hn, Finset.sum_range_succ]
      ring

/-- The convexity of `log Gamma` bounds its derivative below by the previous
unit secant. -/
theorem log_sub_one_le_deriv_logGamma {y : Real} (hy : 1 < y) :
    Real.log (y - 1) ≤ deriv (Real.log ∘ Real.Gamma) y := by
  let f := Real.log ∘ Real.Gamma
  have hc : ConvexOn Real (Set.Ioi 0) f := Real.convexOn_log_Gamma
  have hrec (u : Real) (hu : 0 < u) :
      f (u + 1) = f u + Real.log u := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hu.ne',
      Real.log_mul hu.ne' (Real.Gamma_pos_of_pos hu).ne', add_comm]
  have hder {u : Real} (hu : 0 < u) : DifferentiableAt Real f u := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
      exact fun m => ne_of_gt (by
        have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
        linarith)
  refine (le_of_eq ?_).trans <| hc.slope_le_deriv
    (Set.mem_Ioi.mpr (by linarith : 0 < y - 1))
    (Set.mem_Ioi.mpr (by linarith : 0 < y))
    (by linarith : y - 1 < y) (hder (by linarith))
  rw [slope_def_field, show y - (y - 1) = (1 : Real) by ring, div_one]
  calc
    Real.log (y - 1) =
        (f (y - 1) + Real.log (y - 1)) - f (y - 1) := by ring
    _ = f ((y - 1) + 1) - f (y - 1) := by
      rw [hrec (y - 1) (by linarith)]
    _ = f y - f (y - 1) := by ring

/-- The convexity of `log Gamma` bounds its derivative above by the next unit
secant. -/
theorem deriv_logGamma_le_log {y : Real} (hy : 0 < y) :
    deriv (Real.log ∘ Real.Gamma) y ≤ Real.log y := by
  let f := Real.log ∘ Real.Gamma
  have hc : ConvexOn Real (Set.Ioi 0) f := Real.convexOn_log_Gamma
  have hrec (u : Real) (hu : 0 < u) :
      f (u + 1) = f u + Real.log u := by
    simp only [f, Function.comp_apply, Real.Gamma_add_one hu.ne',
      Real.log_mul hu.ne' (Real.Gamma_pos_of_pos hu).ne', add_comm]
  have hder {u : Real} (hu : 0 < u) : DifferentiableAt Real f u := by
    refine ((Real.differentiableAt_Gamma ?_).log (Real.Gamma_ne_zero ?_)) <;>
      exact fun m => ne_of_gt (by
        have hm : (0 : Real) ≤ m := Nat.cast_nonneg m
        linarith)
  refine (hc.deriv_le_slope (by simpa using hy)
    (by linarith : 0 < y + 1) (by linarith) (hder hy)).trans (le_of_eq ?_)
  rw [slope_def_field, show y + 1 - y = (1 : Real) by ring, div_one,
    hrec y hy, add_sub_cancel_left]

/-- Along every positive real translate, the logarithmic Gamma derivative is
asymptotic to `log n`. -/
theorem tendsto_deriv_logGamma_add_nat_sub_log {x : Real} (hx : 0 < x) :
    Tendsto
      (fun n : Nat =>
        deriv (Real.log ∘ Real.Gamma) (x + n) - Real.log n)
      atTop (nhds 0) := by
  have hlBase :=
    (Real.tendsto_log_comp_add_sub_log (x - 1)).comp
      tendsto_natCast_atTop_atTop
  have huBase :=
    (Real.tendsto_log_comp_add_sub_log x).comp
      tendsto_natCast_atTop_atTop
  have hl :
      Tendsto
        (fun n : Nat => Real.log (x + n - 1) - Real.log n)
        atTop (nhds 0) := by
    have heq :
        (fun n : Nat => Real.log (x + n - 1) - Real.log n) =
          (fun n : Nat =>
            Real.log ((n : Real) + (x - 1)) - Real.log (n : Real)) := by
      funext n
      congr 2
      ring
    rw [heq]
    change Tendsto
      ((fun t : Real => Real.log (t + (x - 1)) - Real.log t) ∘
        (fun n : Nat => (n : Real))) atTop (nhds 0)
    exact hlBase
  have hu :
      Tendsto
        (fun n : Nat => Real.log (x + n) - Real.log n)
        atTop (nhds 0) := by
    have heq :
        (fun n : Nat => Real.log (x + n) - Real.log n) =
          (fun n : Nat =>
            Real.log ((n : Real) + x) - Real.log (n : Real)) := by
      funext n
      congr 2
      ring
    rw [heq]
    change Tendsto
      ((fun t : Real => Real.log (t + x) - Real.log t) ∘
        (fun n : Nat => (n : Real))) atTop (nhds 0)
    exact huBase
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnReal : (1 : Real) ≤ n := by exact_mod_cast hn
    exact sub_le_sub_right
      (log_sub_one_le_deriv_logGamma (by linarith : 1 < x + n)) _
  · filter_upwards with n
    exact sub_le_sub_right
      (deriv_logGamma_le_log (by
        have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
        linarith : 0 < x + n)) _

/-- Real form of a term in Gauss's reciprocal series. -/
def realGaussDigammaSeriesTerm (x : Real) (k : Nat) : Real :=
  1 / (k + 1 : Real) - 1 / (x + k)

/-- The first reciprocal sum in Gauss's series is the real cast of the
harmonic number. -/
theorem sum_one_div_natCast_eq_harmonic (n : Nat) :
    (∑ k ∈ Finset.range n, 1 / (k + 1 : Real)) =
      (harmonic n : Real) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_add, Nat.cast_one]

/-- The real Gauss partial sum is a harmonic number minus a translated
logarithmic-Gamma derivative increment. -/
theorem sum_realGaussDigammaSeriesTerm {x : Real} (hx : 0 < x) (n : Nat) :
    (∑ k ∈ Finset.range n, realGaussDigammaSeriesTerm x k) =
      (harmonic n : Real) -
        (deriv (Real.log ∘ Real.Gamma) (x + n) -
          deriv (Real.log ∘ Real.Gamma) x) := by
  simp only [realGaussDigammaSeriesTerm, Finset.sum_sub_distrib]
  rw [
    sum_one_div_natCast_eq_harmonic, deriv_logGamma_add_nat hx]
  ring

/-- Gauss's reciprocal partial sums converge to the positive-real digamma
value plus Euler's constant. -/
theorem tendsto_realGaussDigammaSeriesPartialSum {x : Real} (hx : 0 < x) :
    Tendsto
      (fun n : Nat =>
        ∑ k ∈ Finset.range n, realGaussDigammaSeriesTerm x k)
      atTop
      (nhds
        (deriv (Real.log ∘ Real.Gamma) x +
          Real.eulerMascheroniConstant)) := by
  have hmain :=
    (Real.tendsto_harmonic_sub_log.sub
      (tendsto_deriv_logGamma_add_nat_sub_log hx)).add
        (tendsto_const_nhds : Tendsto
          (fun _ : Nat => deriv (Real.log ∘ Real.Gamma) x)
          atTop (nhds (deriv (Real.log ∘ Real.Gamma) x)))
  convert hmain using 1
  · funext n
    rw [sum_realGaussDigammaSeriesTerm hx]
    ring
  · ring

/-- Positive real arguments identify the complex reciprocal-series limit
with `digamma x + γ`. -/
theorem tendsto_gaussDigammaSeriesPartialSum_ofReal {x : Real} (hx : 0 < x) :
    Tendsto
      (fun n : Nat =>
        ∑ k ∈ Finset.range n,
          gaussDigammaSeriesTerm (x : Complex) k)
      atTop
      (nhds
        (Complex.digamma (x : Complex) +
          Real.eulerMascheroniConstant)) := by
  have hreal := (tendsto_realGaussDigammaSeriesPartialSum hx).ofReal
  convert hreal using 1
  · funext n
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    simp only [gaussDigammaSeriesTerm, realGaussDigammaSeriesTerm,
      Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_add, Complex.ofReal_natCast]
  · rw [Complex.ofReal_add, ← digamma_ofReal_eq_deriv_logGamma hx]

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
