import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannHypothesisProject.LiCriterion.LiRationalBasis

/-!
# Cutoff covariance for Lagarias's Li rational tests

Lagarias's inverse Mellin kernel for the positive-index test `G_n` is the
Laguerre-type polynomial

`P_n(u) = sum_{j=1}^n choose(n,j) * u^(j-1) / (j-1)!`.

It is supported on the multiplicative interval `(0,1)` (with the usual
half-value convention at `1`).  These kernels are not ordinary Schwartz trace
tests.  The first kernel already makes the `s = 0` endpoint contribution grow
like `log T` under the source cutoff `[1/T,1]`; a covariance formula must keep
the cancelling finite-prime contribution in the same cutoff limit.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Filter intervalIntegral MeasureTheory
open scoped ArithmeticFunction

/-- The polynomial `P_n` in Lagarias's inverse Mellin kernel, indexed from
zero in Lean. -/
def liInverseMellinPolynomial (n : Nat) (u : Real) : Real :=
  ∑ j ∈ Finset.range n,
    (n.choose (j + 1) : Real) * u ^ j / j.factorial

@[simp]
theorem liInverseMellinPolynomial_zero (u : Real) :
    liInverseMellinPolynomial 0 u = 0 := by
  simp [liInverseMellinPolynomial]

@[simp]
theorem liInverseMellinPolynomial_one (u : Real) :
    liInverseMellinPolynomial 1 u = 1 := by
  simp [liInverseMellinPolynomial]

/-- Lagarias's multiplicative inverse Mellin kernel, including the source's
half-value convention at the jump point `x = 1`. -/
def liInverseMellinKernel (n : Nat) (x : Real) : Real :=
  if 0 < x ∧ x < 1 then
    liInverseMellinPolynomial n (Real.log x)
  else if x = 1 then
    n / 2
  else
    0

theorem liInverseMellinKernel_of_mem_Ioo
    (n : Nat) {x : Real} (hx : x ∈ Set.Ioo (0 : Real) 1) :
    liInverseMellinKernel n x =
      liInverseMellinPolynomial n (Real.log x) := by
  rw [liInverseMellinKernel, if_pos ⟨hx.1, hx.2⟩]

@[simp]
theorem liInverseMellinKernel_at_one (n : Nat) :
    liInverseMellinKernel n 1 = n / 2 := by
  simp [liInverseMellinKernel]

theorem liInverseMellinKernel_eq_zero_of_one_lt
    (n : Nat) {x : Real} (hx : 1 < x) :
    liInverseMellinKernel n x = 0 := by
  have hnot : ¬(0 < x ∧ x < 1) :=
    fun h => (not_lt_of_ge hx.le) h.2
  simp [liInverseMellinKernel, hnot, hx.ne']

/-- The cutoff version of the `s = 0` endpoint integral for `P_n`.  It is
kept separate from all finite-prime terms so cancellation cannot be hidden in
the definition. -/
def liZeroEndpointCutoff (n : Nat) (T : Real) : Real :=
  ∫ x in T⁻¹..1, liInverseMellinPolynomial n (Real.log x) / x

/-- Logarithmic monomials divided by `x` are integrable on every positive
multiplicative cutoff interval. -/
theorem intervalIntegrable_log_pow_div
    (j : Nat) {T : Real} (hT : 0 < T) :
    IntervalIntegrable (fun x => (Real.log x) ^ j / x) volume T⁻¹ 1 := by
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
  apply ContinuousOn.intervalIntegrable
  intro x hx
  have hxpos : 0 < x := (lt_min hTinv zero_lt_one).trans_le hx.1
  exact (((Real.continuousAt_log hxpos.ne').pow j).div
    continuousAt_id hxpos.ne').continuousWithinAt

/-- The logarithmic monomial integral that produces the endpoint
counterterms in the Bombieri--Lagarias cutoff. -/
theorem integral_log_pow_div
    (j : Nat) {T : Real} (hT : 0 < T) :
    (∫ x in T⁻¹..1, (Real.log x) ^ j / x) =
      (-1 : Real) ^ j * (Real.log T) ^ (j + 1) / (j + 1) := by
  let F : Real → Real := fun x => (Real.log x) ^ (j + 1) / (j + 1)
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
  have hpos : ∀ x ∈ Set.uIcc T⁻¹ 1, 0 < x := by
    intro x hx
    exact (lt_min hTinv zero_lt_one).trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc T⁻¹ 1,
      HasDerivAt F ((Real.log x) ^ j / x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hpos x hx)
    dsimp [F]
    have h := ((Real.hasDerivAt_log hx0).pow (j + 1)).div_const
      (j + 1 : Real)
    convert h using 1
    all_goals first
      | rfl
      | (simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel_right,
          div_eq_mul_inv]; field_simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_log_pow_div j hT)]
  simp [F, Real.log_inv, div_eq_mul_inv]
  ring

/-- The explicit logarithmic counterterm paired with the finite-prime side at
cutoff `T`. -/
def liEndpointCounterterm (n : Nat) (T : Real) : Real :=
  ∑ j ∈ Finset.range n,
    (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
      (Real.log T) ^ (j + 1) / (j + 1)

/-- The endpoint integral is exactly the finite logarithmic polynomial used
to renormalize the prime-power sum. -/
theorem liZeroEndpointCutoff_eq_counterterm
    (n : Nat) {T : Real} (hT : 0 < T) :
    liZeroEndpointCutoff n T = liEndpointCounterterm n T := by
  simp only [liZeroEndpointCutoff, liInverseMellinPolynomial,
    liEndpointCounterterm, Finset.sum_div]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    have hfun :
        (fun x : Real =>
          ((n.choose (j + 1) : Real) * Real.log x ^ j / j.factorial) / x) =
        fun x => ((n.choose (j + 1) : Real) / j.factorial) *
          (Real.log x ^ j / x) := by
      funext x
      ring
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_log_pow_div j hT]
    ring
  · intro j hj
    have hfun :
        (fun x : Real =>
          ((n.choose (j + 1) : Real) * Real.log x ^ j / j.factorial) / x) =
        fun x => ((n.choose (j + 1) : Real) / j.factorial) *
          (Real.log x ^ j / x) := by
      funext x
      ring
    rw [hfun]
    exact (intervalIntegrable_log_pow_div j hT).const_mul _

/-- The `j`th finite von Mangoldt moment at the natural cutoff `N`.  This is
the finite-prime term appearing in Bombieri--Lagarias Theorem 2. -/
def liPrimeMomentCutoff (j N : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt m * (Real.log (m : Real)) ^ j / m

/-- The prime moment after subtracting the logarithmic endpoint divergence
with the same cutoff. -/
def liPrimeMomentRemainder (j N : Nat) : Real :=
  liPrimeMomentCutoff j N -
    (Real.log (N : Real)) ^ (j + 1) / (j + 1)

/-- The truncated finite-prime contribution of the inverse Mellin polynomial.
The jump convention at `m = 1` is immaterial because `Λ(1) = 0`. -/
def liFinitePrimeCutoff (n N : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt m / m *
      liInverseMellinPolynomial n (-Real.log (m : Real))

/-- The same finite-prime term written with the source's piecewise inverse
Mellin kernel, including its half-value convention at the jump. -/
def liFinitePrimeKernelCutoff (n N : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 N,
    ArithmeticFunction.vonMangoldt m / m *
      liInverseMellinKernel n ((m : Real)⁻¹)

/-- The source kernel and polynomial finite-prime cutoffs agree exactly.  The
only possible discrepancy is at `m = 1`, where the von Mangoldt weight is
zero. -/
theorem liFinitePrimeKernelCutoff_eq (n N : Nat) :
    liFinitePrimeKernelCutoff n N = liFinitePrimeCutoff n N := by
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hm1 : m = 1
  · subst m
    simp [ArithmeticFunction.vonMangoldt_apply_one]
  · have hmBounds : 1 ≤ m ∧ m ≤ N := Finset.mem_Icc.mp hm
    have hmgt : 1 < m := lt_of_le_of_ne hmBounds.1 (Ne.symm hm1)
    have hmpos : 0 < (m : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hmgt)
    have hmgtReal : (1 : Real) < m := by exact_mod_cast hmgt
    have hinv : (m : Real)⁻¹ ∈ Set.Ioo (0 : Real) 1 := by
      exact ⟨inv_pos.mpr hmpos, (inv_lt_one₀ hmpos).2 hmgtReal⟩
    rw [liInverseMellinKernel_of_mem_Ioo n hinv, Real.log_inv]

/-- Expanding the inverse Mellin polynomial decomposes the finite-prime term
into the exact von Mangoldt moments used by the source theorem. -/
theorem liFinitePrimeCutoff_eq_momentSum (n N : Nat) :
    liFinitePrimeCutoff n N =
      ∑ j ∈ Finset.range n,
        (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
          liPrimeMomentCutoff j N := by
  simp only [liFinitePrimeCutoff, liInverseMellinPolynomial,
    liPrimeMomentCutoff]
  calc
    (∑ m ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt m / (m : Real) *
          ∑ j ∈ Finset.range n,
            (n.choose (j + 1) : Real) * (-Real.log (m : Real)) ^ j /
              j.factorial) =
        ∑ m ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range n,
          ArithmeticFunction.vonMangoldt m / (m : Real) *
            ((n.choose (j + 1) : Real) * (-Real.log (m : Real)) ^ j /
              j.factorial) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range n, ∑ m ∈ Finset.Icc 1 N,
          ArithmeticFunction.vonMangoldt m / (m : Real) *
            ((n.choose (j + 1) : Real) * (-Real.log (m : Real)) ^ j /
              j.factorial) := by
          rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range n,
          (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
            ∑ m ∈ Finset.Icc 1 N,
              ArithmeticFunction.vonMangoldt m *
                Real.log (m : Real) ^ j / (m : Real) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          rw [neg_pow]
          ring

/-- The source regularization keeps the endpoint and finite-prime terms under
one common natural cutoff. -/
def liCutoffCovariance (n N : Nat) : Real :=
  liZeroEndpointCutoff n N - liFinitePrimeKernelCutoff n N

/-- Exact finite-cutoff covariance identity.  Neither divergent side is sent
to a limit separately: their difference is the weighted sum of renormalized
prime moments. -/
theorem liCutoffCovariance_eq_primeMomentRemainderSum
    (n N : Nat) (hN : 0 < N) :
    liCutoffCovariance n N =
      -(∑ j ∈ Finset.range n,
        (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
          liPrimeMomentRemainder j N) := by
  rw [liCutoffCovariance,
    liZeroEndpointCutoff_eq_counterterm n (Nat.cast_pos.mpr hN),
    liFinitePrimeKernelCutoff_eq,
    liFinitePrimeCutoff_eq_momentSum]
  simp only [liEndpointCounterterm, liPrimeMomentRemainder]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The precise published analytic input for one renormalized prime moment.
Bombieri--Lagarias obtain these limits from the prime number theorem.  Keeping
the index and limiting constant in this proposition prevents that source
theorem from being hidden inside an endpoint package. -/
def BombieriLagariasPrimeMomentAsymptotic (j : Nat) (limit : Real) : Prop :=
  Tendsto (liPrimeMomentRemainder j) atTop (nhds limit)

/-- Once the individual published moment asymptotics are supplied, the exact
finite covariance identity gives the regularized Li cutoff limit. -/
theorem tendsto_liCutoffCovariance_of_primeMomentAsymptotics
    (n : Nat) (limit : Nat → Real)
    (hsource : ∀ j ∈ Finset.range n,
      BombieriLagariasPrimeMomentAsymptotic j (limit j)) :
    Tendsto (liCutoffCovariance n) atTop
      (nhds (-(∑ j ∈ Finset.range n,
        (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
          limit j))) := by
  have hsum : Tendsto
      (fun N => ∑ j ∈ Finset.range n,
        (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
          liPrimeMomentRemainder j N)
      atTop
      (nhds (∑ j ∈ Finset.range n,
        (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
          limit j)) := by
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.mul (hsource j hj)
  apply hsum.neg.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (liCutoffCovariance_eq_primeMomentRemainderSum n N hN).symm

/-- At the first Li index the covariance is exactly the negative of the
classical Mertens--von Mangoldt remainder. -/
theorem liCutoffCovariance_one
    (N : Nat) (hN : 0 < N) :
    liCutoffCovariance 1 N = -liPrimeMomentRemainder 0 N := by
  rw [liCutoffCovariance_eq_primeMomentRemainderSum 1 N hN]
  norm_num

/-- For `G_1`, the cutoff endpoint contribution is exactly `log T`. -/
theorem liZeroEndpointCutoff_one
    {T : Real} (hT : 0 < T) :
    liZeroEndpointCutoff 1 T = Real.log T := by
  rw [liZeroEndpointCutoff]
  simp only [liInverseMellinPolynomial_one, one_div]
  rw [integral_inv_of_pos (inv_pos.mpr hT) zero_lt_one]
  congr 1
  field_simp [hT.ne']

/-- The individual `s = 0` endpoint term for the first Li test diverges under
the source cutoff.  This is the concrete no-go theorem behind the covariance
regularization requirement. -/
theorem tendsto_liZeroEndpointCutoff_one_atTop :
    Tendsto (liZeroEndpointCutoff 1) atTop atTop := by
  apply Real.tendsto_log_atTop.congr'
  filter_upwards [eventually_gt_atTop (0 : Real)] with T hT
  exact (liZeroEndpointCutoff_one hT).symm

/-- Consequently the first endpoint cutoff cannot converge to a finite real
value on its own. -/
theorem not_tendsto_liZeroEndpointCutoff_one_nhds (L : Real) :
    ¬ Tendsto (liZeroEndpointCutoff 1) atTop (nhds L) :=
  not_tendsto_nhds_of_tendsto_atTop tendsto_liZeroEndpointCutoff_one_atTop L

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
