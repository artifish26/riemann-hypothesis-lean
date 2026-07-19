import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CanonicalDecomposition
import RiemannHypothesisProject.GuinandWeilConcrete.LocalLogDerivativeBound

/-!
# Finite Blaschke zero removal

This module constructs the finite canonical product used in the local
logarithmic-derivative argument.  Meromorphic normal form supplies the
removable values at the selected zeros; the outer-circle norm remains exactly
the norm of the original analytic function.
-/

namespace RiemannHypothesisProject

open Complex Filter Metric Set
open scoped Topology

noncomputable section

/-- The raw finite canonical product before filling its removable values. -/
noncomputable def finiteBlaschkeRaw
    (f : Complex -> Complex) (R : Real) (zeros : Finset Complex)
    (multiplicity : Complex -> Nat) (z : Complex) : Complex :=
  f z *
    ∏ u ∈ zeros, (Complex.canonicalFactor R u z) ^ multiplicity u

/-- The finite canonical product with all removable values filled by
meromorphic normal form. -/
noncomputable def finiteBlaschkeRemoval
    (f : Complex -> Complex) (R : Real) (zeros : Finset Complex)
    (multiplicity : Complex -> Nat) : Complex -> Complex :=
  toMeromorphicNFOn (finiteBlaschkeRaw f R zeros multiplicity) Set.univ

theorem finiteBlaschkeRaw_meromorphicOn
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ) :
    MeromorphicOn (finiteBlaschkeRaw f R zeros multiplicity) Set.univ := by
  intro z _hz
  apply (hf z (Set.mem_univ z)).meromorphicAt.mul
  apply MeromorphicAt.fun_prod
  intro u hu
  exact
    (Complex.meromorphic_canonicalFactor R u z).pow
      (multiplicity u)

theorem finiteBlaschkeRemoval_meromorphicNFOn
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat} :
    MeromorphicNFOn (finiteBlaschkeRemoval f R zeros multiplicity) Set.univ := by
  unfold finiteBlaschkeRemoval
  exact meromorphicNFOn_toMeromorphicNFOn
    (finiteBlaschkeRaw f R zeros multiplicity) Set.univ

/-- The raw product is analytic away from its finite set of possible poles. -/
theorem finiteBlaschkeRaw_analyticAt_of_not_mem
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    {z : Complex} (hz : z ∉ zeros) :
    AnalyticAt Complex (finiteBlaschkeRaw f R zeros multiplicity) z := by
  apply (hf z (Set.mem_univ z)).mul
  classical
  let U : Set Complex := (zeros : Set Complex)ᶜ
  have hU_open : IsOpen U := zeros.isClosed.isOpen_compl
  have hprod_diff : DifferentiableOn Complex
      (fun w => ∏ u ∈ zeros,
        (Complex.canonicalFactor R u w) ^ multiplicity u) U := by
    intro w hw
    apply DifferentiableWithinAt.fun_finsetProd
    intro u hu
    have hwu : w ≠ u := by
      intro h
      have : w ∈ (zeros : Set Complex) := by simpa [h] using hu
      exact hw this
    exact
      ((Complex.analyticOnNhd_canonicalFactor R u w hwu).pow
        (multiplicity u)).differentiableAt.differentiableWithinAt
  exact (hprod_diff.analyticOnNhd hU_open) z (by simpa [U] using hz)

/-- Away from the selected zero set, no normal-form correction is needed. -/
theorem finiteBlaschkeRemoval_eq_raw_of_not_mem
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    {z : Complex} (hz : z ∉ zeros) :
    finiteBlaschkeRemoval f R zeros multiplicity z =
      finiteBlaschkeRaw f R zeros multiplicity z := by
  have hraw_analytic := finiteBlaschkeRaw_analyticAt_of_not_mem
    (R := R) (multiplicity := multiplicity) hf hz
  rw [finiteBlaschkeRemoval,
    toMeromorphicNFOn_eq_toMeromorphicNFAt
      (finiteBlaschkeRaw_meromorphicOn hf) (Set.mem_univ z),
    toMeromorphicNFAt_eq_self.2 hraw_analytic.meromorphicNFAt]

/-- Canonical factors preserve norm on their defining outer circle, so the
filled finite product has exactly the original boundary norm. -/
theorem norm_finiteBlaschkeRemoval_eq_on_sphere
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    {z : Complex} (hz : z ∈ sphere (0 : Complex) R) :
    norm (finiteBlaschkeRemoval f R zeros multiplicity z) = norm (f z) := by
  have hz_not_mem : z ∉ zeros := by
    intro hzin
    have hz_ball := hzeros z hzin
    have hz_norm_lt : norm z < R := by
      simpa [mem_ball, dist_zero_right] using hz_ball
    have hz_norm_eq : norm z = R := by
      simpa [mem_sphere, dist_zero_right] using hz
    linarith
  rw [finiteBlaschkeRemoval_eq_raw_of_not_mem hf hz_not_mem]
  rw [finiteBlaschkeRaw, norm_mul]
  have hprod :
      norm
          (∏ u ∈ zeros,
            (Complex.canonicalFactor R u z) ^ multiplicity u) = 1 := by
    rw [norm_prod]
    apply Finset.prod_eq_one
    intro u hu
    rw [norm_pow, Complex.norm_canonicalFactor_eval_circle_eq_one
      (hzeros u hu) hz, one_pow]
  rw [hprod, mul_one]

/-- At a selected zero, analytic multiplicity exactly cancels the poles of
the corresponding canonical factor. -/
theorem meromorphicOrderAt_finiteBlaschkeRaw_eq_zero_of_mem
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    {u : Complex} (hu : u ∈ zeros) :
    meromorphicOrderAt (finiteBlaschkeRaw f R zeros multiplicity) u = 0 := by
  have hf_u := hf u (Set.mem_univ u)
  have hprod_mer : MeromorphicAt
      (fun z => ∏ v ∈ zeros,
        (Complex.canonicalFactor R v z) ^ multiplicity v) u := by
    apply MeromorphicAt.fun_prod
    intro v hv
    exact
      (Complex.meromorphic_canonicalFactor R v u).pow
        (multiplicity v)
  change meromorphicOrderAt
    (f * fun z => ∏ v ∈ zeros,
      (Complex.canonicalFactor R v z) ^ multiplicity v) u = 0
  rw [meromorphicOrderAt_mul hf_u.meromorphicAt hprod_mer,
    hf_u.meromorphicOrderAt_eq, horder u hu,
    meromorphicOrderAt_fun_prod]
  · have hoff : ∀ v ∈ zeros, v ≠ u ->
        meromorphicOrderAt
          (fun z => (Complex.canonicalFactor R v z) ^ multiplicity v) u = 0 := by
      intro v hv hvi
      have hv_ball := hzeros v hv
      have hu_closed : u ∈ closedBall (0 : Complex) R :=
        ball_subset_closedBall (hzeros u hu)
      have huv : u ≠ v := Ne.symm hvi
      have hfactor_analytic :=
        Complex.analyticOnNhd_canonicalFactor R v u huv
      have hfactor_ne :=
        Complex.canonicalFactor_ne_zero hv_ball hu_closed huv
      change meromorphicOrderAt
        ((Complex.canonicalFactor R v) ^ multiplicity v) u = 0
      rw [meromorphicOrderAt_pow hfactor_analytic.meromorphicAt,
        hfactor_analytic.meromorphicOrderAt_eq,
        hfactor_analytic.analyticOrderAt_eq_zero.mpr hfactor_ne]
      simp
    rw [Finset.sum_eq_single u hoff (fun hnot => (hnot hu).elim),
      show meromorphicOrderAt
          (fun z => (Complex.canonicalFactor R u z) ^ multiplicity u) u =
        meromorphicOrderAt
          ((Complex.canonicalFactor R u) ^ multiplicity u) u by rfl,
      meromorphicOrderAt_pow
        (Complex.meromorphic_canonicalFactor R u u),
      Complex.meromorphicOrderAt_canonicalFactor (hzeros u hu)]
    change ((multiplicity u : Int) : WithTop Int) +
      ((multiplicity u : Int) : WithTop Int) * ((-1 : Int) : WithTop Int) =
        ((0 : Int) : WithTop Int)
    rw [← WithTop.coe_mul, ← WithTop.coe_add, WithTop.coe_eq_coe]
    ring
  · intro v hv
    exact
      (Complex.meromorphic_canonicalFactor R v u).pow
        (multiplicity v)

/-- Filling the removable values turns the finite canonical product into an
entire function. -/
theorem finiteBlaschkeRemoval_analyticOnNhd
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat)) :
    AnalyticOnNhd Complex
      (finiteBlaschkeRemoval f R zeros multiplicity) Set.univ := by
  intro z _hz
  have hnf := finiteBlaschkeRemoval_meromorphicNFOn
    (f := f) (R := R) (zeros := zeros) (multiplicity := multiplicity)
      (Set.mem_univ z)
  rw [← hnf.meromorphicOrderAt_nonneg_iff_analyticAt]
  rw [finiteBlaschkeRemoval,
    meromorphicOrderAt_toMeromorphicNFOn
      (finiteBlaschkeRaw_meromorphicOn hf) (Set.mem_univ z)]
  by_cases hz : z ∈ zeros
  · rw [meromorphicOrderAt_finiteBlaschkeRaw_eq_zero_of_mem
      hf hzeros horder hz]
  · exact
      (finiteBlaschkeRaw_analyticAt_of_not_mem
        (R := R) (multiplicity := multiplicity) hf hz).meromorphicOrderAt_nonneg

/-- If the selected set is exactly the zero set on an inner disk, then the
filled canonical product has no zeros there. -/
theorem finiteBlaschkeRemoval_ne_zero_on_closedBall
    {f : Complex -> Complex} {r R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hrR : r ≤ R)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzeroSet : ∀ z ∈ closedBall (0 : Complex) r,
      f z = 0 ↔ z ∈ zeros)
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r) :
    finiteBlaschkeRemoval f R zeros multiplicity z ≠ 0 := by
  by_cases hzmem : z ∈ zeros
  · have hnf := finiteBlaschkeRemoval_meromorphicNFOn
      (f := f) (R := R) (zeros := zeros) (multiplicity := multiplicity)
        (Set.mem_univ z)
    rw [← hnf.meromorphicOrderAt_eq_zero_iff]
    rw [finiteBlaschkeRemoval,
      meromorphicOrderAt_toMeromorphicNFOn
        (finiteBlaschkeRaw_meromorphicOn hf) (Set.mem_univ z),
      meromorphicOrderAt_finiteBlaschkeRaw_eq_zero_of_mem
        hf hzeros horder hzmem]
  · rw [finiteBlaschkeRemoval_eq_raw_of_not_mem hf hzmem,
      finiteBlaschkeRaw]
    apply mul_ne_zero
    · intro hfz
      exact hzmem ((hzeroSet z hz).mp hfz)
    · apply Finset.prod_ne_zero_iff.mpr
      intro u hu
      apply pow_ne_zero
      apply Complex.canonicalFactor_ne_zero (hzeros u hu)
      · exact closedBall_subset_closedBall hrR hz
      · intro hzu
        exact hzmem (by simpa [hzu] using hu)

/-- If the selected set is exactly the zero set on an open disk, then the
filled canonical product has no zeros on that disk.  This version allows the
outer circle itself to contain zeros of the original function. -/
theorem finiteBlaschkeRemoval_ne_zero_on_ball
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzeroSet : ∀ z ∈ ball (0 : Complex) R,
      f z = 0 ↔ z ∈ zeros)
    {z : Complex} (hz : z ∈ ball (0 : Complex) R) :
    finiteBlaschkeRemoval f R zeros multiplicity z ≠ 0 := by
  by_cases hzmem : z ∈ zeros
  · have hnf := finiteBlaschkeRemoval_meromorphicNFOn
      (f := f) (R := R) (zeros := zeros) (multiplicity := multiplicity)
        (Set.mem_univ z)
    rw [← hnf.meromorphicOrderAt_eq_zero_iff]
    rw [finiteBlaschkeRemoval,
      meromorphicOrderAt_toMeromorphicNFOn
        (finiteBlaschkeRaw_meromorphicOn hf) (Set.mem_univ z),
      meromorphicOrderAt_finiteBlaschkeRaw_eq_zero_of_mem
        hf hzeros horder hzmem]
  · rw [finiteBlaschkeRemoval_eq_raw_of_not_mem hf hzmem,
      finiteBlaschkeRaw]
    apply mul_ne_zero
    · intro hfz
      exact hzmem ((hzeroSet z hz).mp hfz)
    · apply Finset.prod_ne_zero_iff.mpr
      intro u hu
      apply pow_ne_zero
      apply Complex.canonicalFactor_ne_zero (hzeros u hu)
      · exact ball_subset_closedBall hz
      · intro hzu
        exact hzmem (by simpa [hzu] using hu)

/-- A boundary bound for the original function controls the filled canonical
product throughout the closed disk. -/
theorem norm_finiteBlaschkeRemoval_le_on_closedBall
    {f : Complex -> Complex} {R M : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hR : 0 < R)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hboundary : ∀ z ∈ sphere (0 : Complex) R, norm (f z) ≤ M)
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) R) :
    norm (finiteBlaschkeRemoval f R zeros multiplicity z) ≤ M := by
  have hdiff : DiffContOnCl Complex
      (finiteBlaschkeRemoval f R zeros multiplicity)
      (ball (0 : Complex) R) :=
    (finiteBlaschkeRemoval_analyticOnNhd hf hzeros horder).differentiableOn
      |>.diffContOnCl_ball (by simp)
  apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    hdiff
  · intro w hw
    rw [norm_finiteBlaschkeRemoval_eq_on_sphere hf hzeros
      (frontier_ball_subset_sphere hw)]
    exact hboundary w (frontier_ball_subset_sphere hw)
  · simpa [closure_ball (0 : Complex) hR.ne'] using hz

/-- A canonical factor associated to a nonzero point inside the disk has norm
at least one at the center. -/
theorem one_le_norm_canonicalFactor_zero
    {R : Real} {u : Complex}
    (hR : 0 < R) (hu : u ∈ ball (0 : Complex) R) (hu0 : u ≠ 0) :
    1 ≤ norm (Complex.canonicalFactor R u 0) := by
  have hu_norm : norm u < R := by
    simpa [mem_ball, dist_zero_right] using hu
  have hu_norm_pos : 0 < norm u := norm_pos_iff.mpr hu0
  rw [Complex.canonicalFactor_apply]
  simp only [mul_zero, sub_zero, zero_sub, norm_div, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_neg]
  rw [le_div_iff₀ (mul_pos hR hu_norm_pos)]
  nlinarith

/-- The logarithmic derivative of a canonical factor is its negative
principal pole plus a holomorphic numerator correction. -/
theorem logDeriv_canonicalFactor
    {R : Real} {u z : Complex}
    (hR : 0 < R) (hu : u ∈ ball (0 : Complex) R)
    (hz : z ∈ closedBall (0 : Complex) R) (hzu : z ≠ u) :
    logDeriv (Complex.canonicalFactor R u) z =
      -(starRingEnd Complex u) /
          ((R : Complex) ^ 2 - (starRingEnd Complex u) * z) -
        1 / (z - u) := by
  let A : Complex -> Complex := fun w =>
    (R : Complex) ^ 2 - (starRingEnd Complex u) * w
  let D : Complex -> Complex := fun w => (R : Complex) * (w - u)
  have hcf_ne := Complex.canonicalFactor_ne_zero hu hz hzu
  have hA_ne : A z ≠ 0 := by
    intro hA
    apply hcf_ne
    change (R : Complex) ^ 2 - (starRingEnd Complex u) * z = 0 at hA
    rw [Complex.canonicalFactor_apply, hA]
    simp
  have hD_ne : D z ≠ 0 := by
    exact mul_ne_zero (ofReal_ne_zero.mpr hR.ne') (sub_ne_zero.mpr hzu)
  have hR_ne : (R : Complex) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  have hsub_ne : z - u ≠ 0 := sub_ne_zero.mpr hzu
  change logDeriv (fun w => A w / D w) z = _
  rw [logDeriv_div z hA_ne hD_ne (by fun_prop) (by fun_prop)]
  simp [logDeriv_apply, A, D]
  field_simp [hR_ne, hsub_ne]

/-- Away from the selected zeros, the principal-part residual of the
original function is the logarithmic derivative of the zero-free removal
plus the holomorphic canonical-factor correction. -/
theorem logDeriv_sub_principalPart_eq_finiteBlaschkeRemoval_add
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat} {z : Complex}
    (hR : 0 < R)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (hz : z ∈ closedBall (0 : Complex) R)
    (hzmem : z ∉ zeros) (hfz : f z ≠ 0) :
    logDeriv f z -
        ∑ u ∈ zeros, (multiplicity u : Complex) / (z - u) =
      logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z +
        ∑ u ∈ zeros,
          (multiplicity u : Complex) * (starRingEnd Complex u) /
            ((R : Complex) ^ 2 - (starRingEnd Complex u) * z) := by
  let P : Complex -> Complex := fun w =>
    ∏ u ∈ zeros, (Complex.canonicalFactor R u w) ^ multiplicity u
  have hzu : ∀ u ∈ zeros, z ≠ u := by
    intro u hu h
    subst u
    exact hzmem hu
  have heq : finiteBlaschkeRemoval f R zeros multiplicity =ᶠ[𝓝 z]
      finiteBlaschkeRaw f R zeros multiplicity := by
    filter_upwards [zeros.isClosed.isOpen_compl.mem_nhds (by simpa using hzmem)]
      with w hw
    exact finiteBlaschkeRemoval_eq_raw_of_not_mem
      (R := R) (multiplicity := multiplicity) hf (by simpa using hw)
  have hlog_eq :
      logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z =
        logDeriv (finiteBlaschkeRaw f R zeros multiplicity) z := by
    simp only [logDeriv_apply]
    rw [heq.deriv_eq, heq.eq_of_nhds]
  have hP_ne : P z ≠ 0 := by
    dsimp [P]
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu
    apply pow_ne_zero
    exact Complex.canonicalFactor_ne_zero (hzeros u hu) hz (hzu u hu)
  have hP_diff : DifferentiableAt Complex P z := by
    dsimp [P]
    apply DifferentiableAt.fun_finsetProd
    intro u hu
    apply DifferentiableAt.pow
    apply AnalyticAt.differentiableAt
    exact Complex.analyticOnNhd_canonicalFactor R u z (hzu u hu)
  have hraw_log :
      logDeriv (finiteBlaschkeRaw f R zeros multiplicity) z =
        logDeriv f z + logDeriv P z := by
    change logDeriv (fun w => f w * P w) z = _
    exact logDeriv_mul z hfz hP_ne
      (hf z (Set.mem_univ z)).differentiableAt hP_diff
  have hP_log :
      logDeriv P z =
        ∑ u ∈ zeros, (multiplicity u : Complex) *
          (-(starRingEnd Complex u) /
              ((R : Complex) ^ 2 - (starRingEnd Complex u) * z) -
            1 / (z - u)) := by
    dsimp [P]
    rw [logDeriv_prod]
    · apply Finset.sum_congr rfl
      intro u hu
      rw [logDeriv_fun_pow
        (Complex.analyticOnNhd_canonicalFactor R u z (hzu u hu)).differentiableAt,
        logDeriv_canonicalFactor hR (hzeros u hu) hz (hzu u hu)]
    · intro u hu
      exact pow_ne_zero _ (Complex.canonicalFactor_ne_zero
        (hzeros u hu) hz (hzu u hu))
    · intro u hu
      exact (Complex.analyticOnNhd_canonicalFactor R u z
        (hzu u hu)).differentiableAt.pow
        (multiplicity u)
  rw [hlog_eq, hraw_log, hP_log]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv]
  simp only [one_mul, mul_neg, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring_nf

/-- On nested disks, the holomorphic canonical-factor correction is bounded
linearly by the total selected multiplicity. -/
theorem norm_finiteBlaschkeCorrection_le
    {R q r : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat} {z : Complex}
    (hR : 0 < R) (hq : 0 ≤ q)
    (hgap : 0 < R ^ 2 - q * r)
    (hzeros : ∀ u ∈ zeros, norm u ≤ q)
    (hz : norm z ≤ r) :
    norm
        (∑ u ∈ zeros,
          (multiplicity u : Complex) * (starRingEnd Complex u) /
            ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) ≤
      (∑ u ∈ zeros, (multiplicity u : Real)) * q /
        (R ^ 2 - q * r) := by
  have hterm : ∀ u ∈ zeros,
      norm
          ((multiplicity u : Complex) * (starRingEnd Complex u) /
            ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) ≤
        (multiplicity u : Real) * q / (R ^ 2 - q * r) := by
    intro u hu
    have huq := hzeros u hu
    have hprod : norm ((starRingEnd Complex u) * z) ≤ q * r := by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul huq hz (norm_nonneg z) hq
    have hden : R ^ 2 - q * r ≤
        norm ((R : Complex) ^ 2 - (starRingEnd Complex u) * z) := by
      calc
        R ^ 2 - q * r ≤
            R ^ 2 - norm ((starRingEnd Complex u) * z) := by linarith
        _ = norm ((R : Complex) ^ 2) -
            norm ((starRingEnd Complex u) * z) := by
              simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
        _ ≤ norm ((R : Complex) ^ 2 -
            (starRingEnd Complex u) * z) := norm_sub_norm_le _ _
    have hden_pos : 0 <
        norm ((R : Complex) ^ 2 - (starRingEnd Complex u) * z) :=
      hgap.trans_le hden
    rw [norm_div, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
    exact div_le_div₀
      (mul_nonneg (Nat.cast_nonneg _) hq)
      (mul_le_mul_of_nonneg_left huq (Nat.cast_nonneg _))
      hgap hden
  calc
    norm
        (∑ u ∈ zeros,
          (multiplicity u : Complex) * (starRingEnd Complex u) /
            ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) ≤
        ∑ u ∈ zeros,
          norm
            ((multiplicity u : Complex) * (starRingEnd Complex u) /
              ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) :=
      norm_sum_le _ _
    _ ≤ ∑ u ∈ zeros,
        (multiplicity u : Real) * q / (R ^ 2 - q * r) := by
      exact Finset.sum_le_sum fun u hu => hterm u hu
    _ = (∑ u ∈ zeros, (multiplicity u : Real)) * q /
        (R ^ 2 - q * r) := by
      simp_rw [mul_div_assoc]
      rw [Finset.sum_mul]

/-- The finite Blaschke removal does not decrease the center norm. -/
theorem norm_f_le_norm_finiteBlaschkeRemoval_zero
    {f : Complex -> Complex} {R : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hR : 0 < R)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (hzero : (0 : Complex) ∉ zeros) :
    norm (f 0) ≤ norm (finiteBlaschkeRemoval f R zeros multiplicity 0) := by
  rw [finiteBlaschkeRemoval_eq_raw_of_not_mem hf hzero,
    finiteBlaschkeRaw, norm_mul]
  have hprod : 1 ≤
      norm (∏ u ∈ zeros,
        (Complex.canonicalFactor R u 0) ^ multiplicity u) := by
    rw [norm_prod]
    apply Finset.one_le_prod
    intro u hu
    rw [norm_pow]
    exact one_le_pow₀ (one_le_norm_canonicalFactor_zero hR (hzeros u hu)
      (fun hu0 => hzero (by simpa [hu0] using hu)))
  nlinarith [norm_nonneg (f 0)]

/-- An absolute outer-circle bound and a center normalization give the
relative growth bound required by the local logarithmic-derivative theorem. -/
theorem norm_finiteBlaschkeRemoval_le_mul_center_on_ball
    {f : Complex -> Complex} {R M B : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hR : 0 < R) (hB : 0 ≤ B)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzero : (0 : Complex) ∉ zeros)
    (hboundary : ∀ z ∈ sphere (0 : Complex) R, norm (f z) ≤ M)
    (hM : M ≤ B * norm (f 0))
    {z : Complex} (hz : z ∈ ball (0 : Complex) R) :
    norm (finiteBlaschkeRemoval f R zeros multiplicity z) ≤
      B * norm (finiteBlaschkeRemoval f R zeros multiplicity 0) := by
  calc
    norm (finiteBlaschkeRemoval f R zeros multiplicity z) ≤ M :=
      norm_finiteBlaschkeRemoval_le_on_closedBall hR hf hzeros horder
        hboundary (ball_subset_closedBall hz)
    _ ≤ B * norm (f 0) := hM
    _ ≤ B * norm (finiteBlaschkeRemoval f R zeros multiplicity 0) :=
      mul_le_mul_of_nonneg_left
        (norm_f_le_norm_finiteBlaschkeRemoval_zero hR hf hzeros hzero) hB

/-- Boundary growth and an exact finite zero set give a quantitative
logarithmic-derivative bound for the filled zero-free removal. -/
theorem norm_logDeriv_finiteBlaschkeRemoval_le
    {f : Complex -> Complex} {R r M B : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzeroSet : ∀ z ∈ closedBall (0 : Complex) R,
      f z = 0 ↔ z ∈ zeros)
    (hzero : (0 : Complex) ∉ zeros)
    (hboundary : ∀ z ∈ sphere (0 : Complex) R, norm (f z) ≤ M)
    (hM : M ≤ B * norm (f 0))
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r) :
    norm (logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z) ≤
      8 * Real.log B * R / (R - r) ^ 2 := by
  apply norm_logDeriv_le_of_norm_le_mul_center_on_ball hR hrR hB
  · exact (finiteBlaschkeRemoval_analyticOnNhd hf hzeros horder).mono
      (Set.subset_univ _)
  · intro w hw
    exact finiteBlaschkeRemoval_ne_zero_on_closedBall hf (le_refl R)
      hzeros horder hzeroSet (ball_subset_closedBall hw)
  · intro w hw
    exact norm_finiteBlaschkeRemoval_le_mul_center_on_ball hR
      (zero_le_one.trans hB.le) hf
      hzeros horder hzero hboundary hM hw
  · exact hz

/-- Open-disk zero-set version of the finite Blaschke logarithmic-derivative
bound.  No nonvanishing assumption is imposed on the outer circle. -/
theorem norm_logDeriv_finiteBlaschkeRemoval_le_of_zeroSet_on_ball
    {f : Complex -> Complex} {R r M B : Real} {zeros : Finset Complex}
    {multiplicity : Complex -> Nat}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzeroSet : ∀ z ∈ ball (0 : Complex) R,
      f z = 0 ↔ z ∈ zeros)
    (hzero : (0 : Complex) ∉ zeros)
    (hboundary : ∀ z ∈ sphere (0 : Complex) R, norm (f z) ≤ M)
    (hM : M ≤ B * norm (f 0))
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r) :
    norm (logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z) ≤
      8 * Real.log B * R / (R - r) ^ 2 := by
  apply norm_logDeriv_le_of_norm_le_mul_center_on_ball hR hrR hB
  · exact (finiteBlaschkeRemoval_analyticOnNhd hf hzeros horder).mono
      (Set.subset_univ _)
  · intro w hw
    exact finiteBlaschkeRemoval_ne_zero_on_ball hf hzeros horder hzeroSet hw
  · intro w hw
    exact norm_finiteBlaschkeRemoval_le_mul_center_on_ball hR
      (zero_le_one.trans hB.le) hf hzeros horder hzero hboundary hM hw
  · exact hz

/-- The original function's multiplicity-weighted principal-part residual is
bounded by the zero-free logarithmic derivative plus the explicit canonical
correction. -/
theorem norm_logDeriv_sub_principalPart_le_of_finiteBlaschkeRemoval
    {f : Complex -> Complex} {R r q M B : Real}
    {zeros : Finset Complex} {multiplicity : Complex -> Nat}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hq : 0 ≤ q) (hgap : 0 < R ^ 2 - q * r)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (hzerosNorm : ∀ u ∈ zeros, norm u ≤ q)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzeroSet : ∀ z ∈ closedBall (0 : Complex) R,
      f z = 0 ↔ z ∈ zeros)
    (hzero : (0 : Complex) ∉ zeros)
    (hboundary : ∀ z ∈ sphere (0 : Complex) R, norm (f z) ≤ M)
    (hM : M ≤ B * norm (f 0))
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r)
    (hzmem : z ∉ zeros) :
    norm
        (logDeriv f z -
          ∑ u ∈ zeros, (multiplicity u : Complex) / (z - u)) ≤
      8 * Real.log B * R / (R - r) ^ 2 +
        (∑ u ∈ zeros, (multiplicity u : Real)) * q /
          (R ^ 2 - q * r) := by
  have hzR : z ∈ closedBall (0 : Complex) R :=
    closedBall_subset_closedBall hrR.le hz
  have hfz : f z ≠ 0 := by
    intro hfz
    exact hzmem ((hzeroSet z hzR).mp hfz)
  rw [logDeriv_sub_principalPart_eq_finiteBlaschkeRemoval_add
    hR hf hzeros hzR hzmem hfz]
  calc
    norm
        (logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z +
          ∑ u ∈ zeros,
            (multiplicity u : Complex) * (starRingEnd Complex u) /
              ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) ≤
        norm (logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z) +
          norm
            (∑ u ∈ zeros,
              (multiplicity u : Complex) * (starRingEnd Complex u) /
                ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) :=
      norm_add_le _ _
    _ ≤ 8 * Real.log B * R / (R - r) ^ 2 +
        (∑ u ∈ zeros, (multiplicity u : Real)) * q /
          (R ^ 2 - q * r) := by
      apply add_le_add
      · exact norm_logDeriv_finiteBlaschkeRemoval_le hR hrR hB hf
          hzeros horder hzeroSet hzero hboundary hM hz
      · apply norm_finiteBlaschkeCorrection_le hR hq hgap hzerosNorm
        simpa [mem_closedBall, dist_zero_right] using hz

/-- Open-disk zero-set version of the complete principal-part residual bound. -/
theorem norm_logDeriv_sub_principalPart_le_of_finiteBlaschkeRemoval_open
    {f : Complex -> Complex} {R r q M B : Real}
    {zeros : Finset Complex} {multiplicity : Complex -> Nat}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hq : 0 ≤ q) (hgap : 0 < R ^ 2 - q * r)
    (hf : AnalyticOnNhd Complex f Set.univ)
    (hzeros : ∀ u ∈ zeros, u ∈ ball (0 : Complex) R)
    (hzerosNorm : ∀ u ∈ zeros, norm u ≤ q)
    (horder : ∀ u ∈ zeros,
      analyticOrderAt f u = (multiplicity u : ENat))
    (hzeroSet : ∀ z ∈ ball (0 : Complex) R,
      f z = 0 ↔ z ∈ zeros)
    (hzero : (0 : Complex) ∉ zeros)
    (hboundary : ∀ z ∈ sphere (0 : Complex) R, norm (f z) ≤ M)
    (hM : M ≤ B * norm (f 0))
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r)
    (hzmem : z ∉ zeros) :
    norm
        (logDeriv f z -
          ∑ u ∈ zeros, (multiplicity u : Complex) / (z - u)) ≤
      8 * Real.log B * R / (R - r) ^ 2 +
        (∑ u ∈ zeros, (multiplicity u : Real)) * q /
          (R ^ 2 - q * r) := by
  have hzNorm : norm z ≤ r := by
    simpa [mem_closedBall, dist_zero_right] using hz
  have hzBall : z ∈ ball (0 : Complex) R := by
    simpa [mem_ball, dist_zero_right] using hzNorm.trans_lt hrR
  have hzR : z ∈ closedBall (0 : Complex) R := ball_subset_closedBall hzBall
  have hfz : f z ≠ 0 := by
    intro hfz
    exact hzmem ((hzeroSet z hzBall).mp hfz)
  rw [logDeriv_sub_principalPart_eq_finiteBlaschkeRemoval_add
    hR hf hzeros hzR hzmem hfz]
  calc
    norm
        (logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z +
          ∑ u ∈ zeros,
            (multiplicity u : Complex) * (starRingEnd Complex u) /
              ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) ≤
        norm (logDeriv (finiteBlaschkeRemoval f R zeros multiplicity) z) +
          norm
            (∑ u ∈ zeros,
              (multiplicity u : Complex) * (starRingEnd Complex u) /
                ((R : Complex) ^ 2 - (starRingEnd Complex u) * z)) :=
      norm_add_le _ _
    _ ≤ 8 * Real.log B * R / (R - r) ^ 2 +
        (∑ u ∈ zeros, (multiplicity u : Real)) * q /
          (R ^ 2 - q * r) := by
      apply add_le_add
      · exact norm_logDeriv_finiteBlaschkeRemoval_le_of_zeroSet_on_ball
          hR hrR hB hf hzeros horder hzeroSet hzero hboundary hM hz
      · apply norm_finiteBlaschkeCorrection_le hR hq hgap hzerosNorm
        exact hzNorm

end

end RiemannHypothesisProject
