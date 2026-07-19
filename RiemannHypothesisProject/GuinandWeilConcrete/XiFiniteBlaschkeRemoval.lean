import RiemannHypothesisProject.GuinandWeilConcrete.FiniteBlaschkeRemoval
import RiemannHypothesisProject.GuinandWeilConcrete.XiDivisor
import RiemannHypothesisProject.GuinandWeilConcrete.XiRightHalfPlaneLower
import RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiGrowth

/-!
# Finite Blaschke removal for translated xi

This module constructs the exact finite zero set of a translate of Riemann's
xi function inside an open disk.  The set is obtained from compact divisor
support on the closed disk and then filtered to the open disk, so zeros on the
outer circle do not enter the canonical product.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Complex Metric Set
open scoped Topology

noncomputable section

/-- Riemann's xi function in local coordinates centered at `c`. -/
def shiftedRiemannXi (c z : Complex) : Complex :=
  riemannXi (c + z)

theorem analyticOnNhd_shiftedRiemannXi (c : Complex) :
    AnalyticOnNhd Complex (shiftedRiemannXi c) Set.univ := by
  intro z _hz
  change AnalyticAt Complex (riemannXi ∘ fun w => c + w) z
  exact (differentiable_riemannXi.analyticAt (c + z)).comp (by fun_prop)

theorem shiftedRiemannXi_two_sub_center_ne_zero (c : Complex) :
    shiftedRiemannXi c (2 - c) ≠ 0 := by
  simpa [shiftedRiemannXi] using riemannXi_two_ne_zero

/-- A translated xi function has finite analytic order at every point. -/
theorem analyticOrderAt_shiftedRiemannXi_ne_top (c z : Complex) :
    analyticOrderAt (shiftedRiemannXi c) z ≠ ⊤ := by
  have hknown := (analyticOnNhd_shiftedRiemannXi c) (2 - c) trivial
  apply (analyticOnNhd_shiftedRiemannXi c).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (x := (2 : Complex) - c) (y := z) trivial trivial
  rw [hknown.analyticOrderAt_eq_zero.mpr
    (shiftedRiemannXi_two_sub_center_ne_zero c)]
  simp

/-- Xi's translated divisor has finite support on every closed disk. -/
theorem shiftedRiemannXiClosedBallDivisorSupport_finite
    (c : Complex) (R : Real) :
    (MeromorphicOn.divisor (shiftedRiemannXi c)
      (closedBall (0 : Complex) R)).support.Finite := by
  exact
    (MeromorphicOn.divisor (shiftedRiemannXi c)
      (closedBall (0 : Complex) R)).finiteSupport
        (isCompact_closedBall (0 : Complex) R)

/-- The finite divisor support of translated xi on the closed disk. -/
def shiftedRiemannXiClosedBallDivisorSupport
    (c : Complex) (R : Real) : Finset Complex :=
  (shiftedRiemannXiClosedBallDivisorSupport_finite c R).toFinset

@[simp]
theorem mem_shiftedRiemannXiClosedBallDivisorSupport
    {c s : Complex} {R : Real} :
    s ∈ shiftedRiemannXiClosedBallDivisorSupport c R ↔
      s ∈ (MeromorphicOn.divisor (shiftedRiemannXi c)
        (closedBall (0 : Complex) R)).support := by
  simp [shiftedRiemannXiClosedBallDivisorSupport]

theorem shiftedRiemannXi_eq_zero_of_mem_closedBallDivisorSupport
    {c s : Complex} {R : Real}
    (hs : s ∈ shiftedRiemannXiClosedBallDivisorSupport c R) :
    shiftedRiemannXi c s = 0 := by
  have hsSupport :
      s ∈ (MeromorphicOn.divisor (shiftedRiemannXi c)
        (closedBall (0 : Complex) R)).support :=
    mem_shiftedRiemannXiClosedBallDivisorSupport.mp hs
  have hsBall : s ∈ closedBall (0 : Complex) R :=
    (MeromorphicOn.divisor (shiftedRiemannXi c)
      (closedBall (0 : Complex) R)).supportWithinDomain hsSupport
  have hdivisor_ne :
      MeromorphicOn.divisor (shiftedRiemannXi c)
        (closedBall (0 : Complex) R) s ≠ 0 := by
    simpa [Function.mem_support] using hsSupport
  have horder_ne : analyticOrderAt (shiftedRiemannXi c) s ≠ 0 := by
    intro horder
    apply hdivisor_ne
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      ((analyticOnNhd_shiftedRiemannXi c).mono (Set.subset_univ _)) hsBall,
      horder]
    simp
  exact apply_eq_zero_of_analyticOrderAt_ne_zero horder_ne

theorem mem_shiftedRiemannXiClosedBallDivisorSupport_iff
    {c s : Complex} {R : Real} :
    s ∈ shiftedRiemannXiClosedBallDivisorSupport c R ↔
      s ∈ closedBall (0 : Complex) R ∧ shiftedRiemannXi c s = 0 := by
  constructor
  · intro hs
    exact ⟨
      (MeromorphicOn.divisor (shiftedRiemannXi c)
        (closedBall (0 : Complex) R)).supportWithinDomain
          (mem_shiftedRiemannXiClosedBallDivisorSupport.mp hs),
      shiftedRiemannXi_eq_zero_of_mem_closedBallDivisorSupport hs⟩
  · rintro ⟨hsBall, hxi⟩
    rw [mem_shiftedRiemannXiClosedBallDivisorSupport, Function.mem_support]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
      ((analyticOnNhd_shiftedRiemannXi c).mono (Set.subset_univ _)) hsBall]
    have hsAnalytic := (analyticOnNhd_shiftedRiemannXi c) s trivial
    have horder_ne_zero : analyticOrderAt (shiftedRiemannXi c) s ≠ 0 :=
      hsAnalytic.analyticOrderAt_ne_zero.mpr hxi
    have horder_ne_top : analyticOrderAt (shiftedRiemannXi c) s ≠ ⊤ :=
      analyticOrderAt_shiftedRiemannXi_ne_top c s
    rw [← ENat.coe_toNat horder_ne_top] at horder_ne_zero ⊢
    simpa using horder_ne_zero

/-- The exact finite zero set of translated xi in the open disk. -/
def shiftedRiemannXiOpenBallZeroFinset
    (c : Complex) (R : Real) : Finset Complex := by
  classical
  exact (shiftedRiemannXiClosedBallDivisorSupport c R).filter
    (fun z => z ∈ ball (0 : Complex) R)

@[simp]
theorem mem_shiftedRiemannXiOpenBallZeroFinset_iff
    {c s : Complex} {R : Real} :
    s ∈ shiftedRiemannXiOpenBallZeroFinset c R ↔
      s ∈ ball (0 : Complex) R ∧ shiftedRiemannXi c s = 0 := by
  classical
  rw [shiftedRiemannXiOpenBallZeroFinset, Finset.mem_filter]
  constructor
  · intro h
    have hclosed :=
      (mem_shiftedRiemannXiClosedBallDivisorSupport_iff.mp h.1)
    exact ⟨h.2, hclosed.2⟩
  · intro h
    exact ⟨mem_shiftedRiemannXiClosedBallDivisorSupport_iff.mpr
      ⟨ball_subset_closedBall h.1, h.2⟩, h.1⟩

/-- Analytic multiplicity of a translated xi zero. -/
def shiftedRiemannXiMultiplicity (c z : Complex) : Nat :=
  (analyticOrderAt (shiftedRiemannXi c) z).toNat

theorem analyticOrderAt_shiftedRiemannXi_eq_multiplicity
    (c z : Complex) :
    analyticOrderAt (shiftedRiemannXi c) z =
      (shiftedRiemannXiMultiplicity c z : ENat) := by
  exact (ENat.coe_toNat (analyticOrderAt_shiftedRiemannXi_ne_top c z)).symm

/-- Translation of the input does not change xi's analytic order. -/
theorem analyticOrderAt_shiftedRiemannXi_eq_riemannXi
    (c z : Complex) :
    analyticOrderAt (shiftedRiemannXi c) z =
      analyticOrderAt riemannXi (c + z) := by
  let g : Complex → Complex := fun w => c + w
  have hg : AnalyticAt Complex g z := by fun_prop
  have hg' : deriv g z ≠ 0 := by
    dsimp only [g]
    simp
  change analyticOrderAt (riemannXi ∘ g) z =
    analyticOrderAt riemannXi (g z)
  exact analyticOrderAt_comp_of_deriv_ne_zero hg hg'

/-- At a translated xi zero, the local multiplicity is exactly the project's
analytic zeta-zero multiplicity. -/
theorem shiftedRiemannXiMultiplicity_eq_zetaZeroMultiplicity
    (c z : Complex) (hz : shiftedRiemannXi c z = 0) :
    shiftedRiemannXiMultiplicity c z =
      zetaZeroMultiplicity
        (zetaZeroSubtypeOfRiemannXiZero (c + z) (by
          simpa only [shiftedRiemannXi] using hz)) := by
  let rho : ZetaZeroSubtype :=
    zetaZeroSubtypeOfRiemannXiZero (c + z) (by
      simpa only [shiftedRiemannXi] using hz)
  have hnotTrivial : Not (IsTrivialZetaZero (rho : Complex)) := by
    dsimp only [rho, zetaZeroSubtypeOfRiemannXiZero]
    exact not_isTrivialZetaZero_of_riemannXi_eq_zero
      (by simpa only [shiftedRiemannXi] using hz)
  have horder :=
    analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
      rho hnotTrivial
  unfold shiftedRiemannXiMultiplicity
  rw [analyticOrderAt_shiftedRiemannXi_eq_riemannXi c z]
  change (analyticOrderAt riemannXi (rho : Complex)).toNat = _
  rw [horder]
  simp
  apply congrArg zetaZeroMultiplicity
  apply Subtype.ext
  rfl

theorem shiftedRiemannXiOpenBallZeroFinset_center_not_mem
    {c : Complex} {R : Real} (hc : riemannXi c ≠ 0) :
    (0 : Complex) ∉ shiftedRiemannXiOpenBallZeroFinset c R := by
  intro hmem
  have hzero := (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hmem).2
  exact hc (by simpa [shiftedRiemannXi] using hzero)

/-- The finite Blaschke removal of all translated xi zeros in the open disk. -/
def shiftedRiemannXiBlaschkeRemoval
    (c : Complex) (R : Real) : Complex -> Complex :=
  finiteBlaschkeRemoval (shiftedRiemannXi c) R
    (shiftedRiemannXiOpenBallZeroFinset c R)
    (shiftedRiemannXiMultiplicity c)

theorem shiftedRiemannXiBlaschkeRemoval_analyticOnNhd
    (c : Complex) (R : Real) :
    AnalyticOnNhd Complex (shiftedRiemannXiBlaschkeRemoval c R) Set.univ := by
  apply finiteBlaschkeRemoval_analyticOnNhd
  · exact analyticOnNhd_shiftedRiemannXi c
  · intro u hu
    exact (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hu).1
  · intro u _hu
    exact analyticOrderAt_shiftedRiemannXi_eq_multiplicity c u

theorem shiftedRiemannXiBlaschkeRemoval_ne_zero_on_ball
    (c : Complex) (R : Real) {z : Complex}
    (hz : z ∈ ball (0 : Complex) R) :
    shiftedRiemannXiBlaschkeRemoval c R z ≠ 0 := by
  apply finiteBlaschkeRemoval_ne_zero_on_ball
  · exact analyticOnNhd_shiftedRiemannXi c
  · intro u hu
    exact (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hu).1
  · intro u _hu
    exact analyticOrderAt_shiftedRiemannXi_eq_multiplicity c u
  · intro w hw
    constructor
    · intro hzero
      exact mem_shiftedRiemannXiOpenBallZeroFinset_iff.mpr ⟨hw, hzero⟩
    · intro hmem
      exact (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hmem).2
  · exact hz

theorem norm_shiftedRiemannXiBlaschkeRemoval_eq_on_sphere
    {c z : Complex} {R : Real} (hz : z ∈ sphere (0 : Complex) R) :
    norm (shiftedRiemannXiBlaschkeRemoval c R z) =
      norm (shiftedRiemannXi c z) := by
  apply norm_finiteBlaschkeRemoval_eq_on_sphere
  · exact analyticOnNhd_shiftedRiemannXi c
  · intro u hu
    exact (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hu).1
  · exact hz

theorem norm_shiftedRiemannXi_le_norm_BlaschkeRemoval_zero
    {c : Complex} {R : Real} (hR : 0 < R) (hc : riemannXi c ≠ 0) :
    norm (riemannXi c) ≤ norm (shiftedRiemannXiBlaschkeRemoval c R 0) := by
  simpa [shiftedRiemannXi, shiftedRiemannXiBlaschkeRemoval] using
    norm_f_le_norm_finiteBlaschkeRemoval_zero hR
      (analyticOnNhd_shiftedRiemannXi c)
      (fun u hu => (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hu).1)
      (shiftedRiemannXiOpenBallZeroFinset_center_not_mem hc)

/-- Quantitative principal-part residual bound for translated xi on nested
disks.  The finite sum is over exactly the xi zeros in the outer open disk. -/
theorem norm_logDeriv_shiftedRiemannXi_sub_principalPart_le
    {c : Complex} {R r M B : Real}
    (hR : 0 < R) (hrR : r < R) (hB : 1 < B)
    (hc : riemannXi c ≠ 0)
    (hboundary : ∀ z ∈ sphere (0 : Complex) R,
      norm (shiftedRiemannXi c z) ≤ M)
    (hM : M ≤ B * norm (riemannXi c))
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r)
    (hzmem : z ∉ shiftedRiemannXiOpenBallZeroFinset c R) :
    norm
        (logDeriv (shiftedRiemannXi c) z -
          ∑ u ∈ shiftedRiemannXiOpenBallZeroFinset c R,
            (shiftedRiemannXiMultiplicity c u : Complex) / (z - u)) ≤
      8 * Real.log B * R / (R - r) ^ 2 +
        (∑ u ∈ shiftedRiemannXiOpenBallZeroFinset c R,
          (shiftedRiemannXiMultiplicity c u : Real)) * R /
            (R ^ 2 - R * r) := by
  have hgap : 0 < R ^ 2 - R * r := by
    nlinarith
  apply norm_logDeriv_sub_principalPart_le_of_finiteBlaschkeRemoval_open
    hR hrR hB hR.le hgap
  · exact analyticOnNhd_shiftedRiemannXi c
  · intro u hu
    exact (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hu).1
  · intro u hu
    have huBall := (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hu).1
    exact (by simpa [mem_ball, dist_zero_right] using huBall : norm u < R).le
  · intro u _hu
    exact analyticOrderAt_shiftedRiemannXi_eq_multiplicity c u
  · intro w hw
    constructor
    · intro hzero
      exact mem_shiftedRiemannXiOpenBallZeroFinset_iff.mpr ⟨hw, hzero⟩
    · intro hmem
      exact (mem_shiftedRiemannXiOpenBallZeroFinset_iff.mp hmem).2
  · exact shiftedRiemannXiOpenBallZeroFinset_center_not_mem hc
  · exact hboundary
  · simpa [shiftedRiemannXi] using hM
  · exact hz
  · exact hzmem

/-- The explicit translated-disk majorant inherited from the global
order-`3 / 2` xi growth bound. -/
def shiftedRiemannXiBoundaryMajorant
    (K k : Real) (c : Complex) (R : Real) : Real :=
  ((norm c + R) * (norm c + R + 1) * K *
      Real.exp (k * (norm c + R + 2) ^ (3 / 2 : Real)) + 1) / 2

/-- Unconditional order-`3 / 2` growth on every translated xi sphere. -/
theorem exists_shiftedRiemannXiBoundaryMajorant :
    ∃ K k : Real, 0 < K ∧ 0 < k ∧
      ∀ c : Complex, ∀ R : Real, 0 ≤ R →
        ∀ z ∈ sphere (0 : Complex) R,
          norm (shiftedRiemannXi c z) ≤
            shiftedRiemannXiBoundaryMajorant K k c R := by
  obtain ⟨K, k, hK, hk, hxi⟩ :=
    exists_riemannXi_polynomial_rpowThreeHalvesExp_bound
  refine ⟨K, k, hK, hk, fun c R hR z hz => ?_⟩
  have hzNorm : norm z = R := by
    simpa [mem_sphere, dist_zero_right] using hz
  have hnorm : norm (c + z) ≤ norm c + R := by
    calc
      norm (c + z) ≤ norm c + norm z := norm_add_le _ _
      _ = norm c + R := by rw [hzNorm]
  have hnorm1 : norm (c + z) + 1 ≤ norm c + R + 1 := by linarith
  have hnorm2 : norm (c + z) + 2 ≤ norm c + R + 2 := by linarith
  have hrpow : (norm (c + z) + 2) ^ (3 / 2 : Real) ≤
      (norm c + R + 2) ^ (3 / 2 : Real) := by
    exact Real.rpow_le_rpow (by positivity) hnorm2 (by norm_num)
  have hexp :
      Real.exp (k * (norm (c + z) + 2) ^ (3 / 2 : Real)) ≤
        Real.exp (k * (norm c + R + 2) ^ (3 / 2 : Real)) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrpow hk.le)
  unfold shiftedRiemannXi
  calc
    norm (riemannXi (c + z)) ≤
        (norm (c + z) * (norm (c + z) + 1) * K *
          Real.exp (k * (norm (c + z) + 2) ^ (3 / 2 : Real)) + 1) / 2 :=
      hxi (c + z)
    _ ≤ shiftedRiemannXiBoundaryMajorant K k c R := by
      unfold shiftedRiemannXiBoundaryMajorant
      gcongr

/-- A canonical relative-growth factor obtained from the translated boundary
majorant and the nonzero xi value at the disk center. -/
def shiftedRiemannXiRelativeGrowthFactor
    (K k : Real) (c : Complex) (R : Real) : Real :=
  shiftedRiemannXiBoundaryMajorant K k c R / norm (riemannXi c) + 1

theorem one_lt_shiftedRiemannXiRelativeGrowthFactor
    {K k R : Real} {c : Complex}
    (hK : 0 < K) (_hk : 0 < k) (hR : 0 ≤ R) (hc : riemannXi c ≠ 0) :
    1 < shiftedRiemannXiRelativeGrowthFactor K k c R := by
  have hmajorant : 0 < shiftedRiemannXiBoundaryMajorant K k c R := by
    unfold shiftedRiemannXiBoundaryMajorant
    have hbase : 0 ≤ norm c + R := add_nonneg (norm_nonneg c) hR
    have hproduct : 0 ≤
        (norm c + R) * (norm c + R + 1) * K *
          Real.exp (k * (norm c + R + 2) ^ (3 / 2 : Real)) := by
      positivity
    linarith
  unfold shiftedRiemannXiRelativeGrowthFactor
  have hcenter : 0 < norm (riemannXi c) := norm_pos_iff.mpr hc
  have : 0 < shiftedRiemannXiBoundaryMajorant K k c R /
      norm (riemannXi c) := div_pos hmajorant hcenter
  linarith

theorem shiftedRiemannXiBoundaryMajorant_le_relative_mul_center
    {K k R : Real} {c : Complex} (hc : riemannXi c ≠ 0) :
    shiftedRiemannXiBoundaryMajorant K k c R ≤
      shiftedRiemannXiRelativeGrowthFactor K k c R * norm (riemannXi c) := by
  have hcenter : norm (riemannXi c) ≠ 0 := norm_ne_zero_iff.mpr hc
  unfold shiftedRiemannXiRelativeGrowthFactor
  rw [add_mul, div_mul_cancel₀ _ hcenter, one_mul]
  exact le_add_of_nonneg_right (norm_nonneg _)

/-- The translated-xi principal-part residual bound with the global xi growth
theorem supplying the boundary estimate unconditionally. -/
theorem exists_norm_logDeriv_shiftedRiemannXi_sub_principalPart_le
    {c : Complex} {R r : Real}
    (hR : 0 < R) (hrR : r < R) (hc : riemannXi c ≠ 0)
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r)
    (hzmem : z ∉ shiftedRiemannXiOpenBallZeroFinset c R) :
    ∃ K k : Real, 0 < K ∧ 0 < k ∧
      norm
          (logDeriv (shiftedRiemannXi c) z -
            ∑ u ∈ shiftedRiemannXiOpenBallZeroFinset c R,
              (shiftedRiemannXiMultiplicity c u : Complex) / (z - u)) ≤
        8 * Real.log (shiftedRiemannXiRelativeGrowthFactor K k c R) * R /
            (R - r) ^ 2 +
          (∑ u ∈ shiftedRiemannXiOpenBallZeroFinset c R,
            (shiftedRiemannXiMultiplicity c u : Real)) * R /
              (R ^ 2 - R * r) := by
  obtain ⟨K, k, hK, hk, hboundary⟩ :=
    exists_shiftedRiemannXiBoundaryMajorant
  refine ⟨K, k, hK, hk, ?_⟩
  apply norm_logDeriv_shiftedRiemannXi_sub_principalPart_le
    hR hrR
    (one_lt_shiftedRiemannXiRelativeGrowthFactor hK hk hR.le hc) hc
  · exact hboundary c R hR.le
  · exact shiftedRiemannXiBoundaryMajorant_le_relative_mul_center hc
  · exact hz
  · exact hzmem

/-- The fixed right-half-plane center used for local xi disks at height `T`. -/
def xiLocalDiskCenter (T : Real) : Complex :=
  3 + Complex.I * T

theorem riemannXi_xiLocalDiskCenter_ne_zero (T : Real) :
    riemannXi (xiLocalDiskCenter T) ≠ 0 := by
  apply riemannXi_ne_zero_of_one_lt_re
  simp [xiLocalDiskCenter]

/-- A denominator-free local boundary-growth factor.  The final exponential
factor is the reciprocal xi majorant on the center line `3 + iT`. -/
def xiLocalDiskGrowthFactor
    (K k A T R : Real) : Real :=
  shiftedRiemannXiBoundaryMajorant K k (xiLocalDiskCenter T) R *
      (A * Real.exp (Real.pi * (abs T + 1))) + 1

theorem one_lt_xiLocalDiskGrowthFactor
    {K k A T R : Real}
    (hK : 0 < K) (_hk : 0 < k) (hA : 0 < A) (hR : 0 ≤ R) :
    1 < xiLocalDiskGrowthFactor K k A T R := by
  have hmajorant :
      0 < shiftedRiemannXiBoundaryMajorant K k (xiLocalDiskCenter T) R := by
    unfold shiftedRiemannXiBoundaryMajorant
    have hbase : 0 ≤ norm (xiLocalDiskCenter T) + R :=
      add_nonneg (norm_nonneg _) hR
    have hproduct : 0 ≤
        (norm (xiLocalDiskCenter T) + R) *
          (norm (xiLocalDiskCenter T) + R + 1) * K *
            Real.exp
              (k * (norm (xiLocalDiskCenter T) + R + 2) ^
                (3 / 2 : Real)) := by
      positivity
    linarith
  unfold xiLocalDiskGrowthFactor
  have hexponential : 0 < A * Real.exp (Real.pi * (abs T + 1)) := by
    positivity
  nlinarith

theorem shiftedRiemannXiBoundaryMajorant_le_localGrowthFactor_mul_center
    {K k A T R : Real}
    (hK : 0 < K)
    (hR : 0 ≤ R)
    (hxiInv : norm (riemannXi (xiLocalDiskCenter T))⁻¹ ≤
      A * Real.exp (Real.pi * (abs T + 1))) :
    shiftedRiemannXiBoundaryMajorant K k (xiLocalDiskCenter T) R ≤
      xiLocalDiskGrowthFactor K k A T R *
        norm (riemannXi (xiLocalDiskCenter T)) := by
  let M := shiftedRiemannXiBoundaryMajorant K k (xiLocalDiskCenter T) R
  let E := A * Real.exp (Real.pi * (abs T + 1))
  have hcenter : 0 < norm (riemannXi (xiLocalDiskCenter T)) :=
    norm_pos_iff.mpr (riemannXi_xiLocalDiskCenter_ne_zero T)
  have hInvReal : (norm (riemannXi (xiLocalDiskCenter T)))⁻¹ ≤ E := by
    simpa only [E, norm_inv] using hxiInv
  have hM : 0 ≤ M := by
    dsimp only [M, shiftedRiemannXiBoundaryMajorant]
    have hbase : 0 ≤ norm (xiLocalDiskCenter T) + R :=
      add_nonneg (norm_nonneg _) hR
    have hproduct : 0 ≤
        (norm (xiLocalDiskCenter T) + R) *
          (norm (xiLocalDiskCenter T) + R + 1) * K *
            Real.exp
              (k * (norm (xiLocalDiskCenter T) + R + 2) ^
                (3 / 2 : Real)) := by
      positivity
    positivity
  change M ≤ (M * E + 1) * norm (riemannXi (xiLocalDiskCenter T))
  calc
    M = M * (norm (riemannXi (xiLocalDiskCenter T)))⁻¹ *
        norm (riemannXi (xiLocalDiskCenter T)) := by
      field_simp
    _ ≤ M * E * norm (riemannXi (xiLocalDiskCenter T)) := by
      gcongr
    _ ≤ (M * E + 1) * norm (riemannXi (xiLocalDiskCenter T)) := by
      exact mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) hcenter.le

/-- Unconditional local residual estimate at the moving right-half-plane
center `3 + iT`, with all center-value dependence replaced by an explicit
height majorant. -/
theorem exists_norm_logDeriv_xiLocalDisk_sub_principalPart_le
    {T R r : Real} (hR : 0 < R) (hrR : r < R)
    {z : Complex} (hz : z ∈ closedBall (0 : Complex) r)
    (hzmem : z ∉ shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) R) :
    ∃ K k A : Real, 0 < K ∧ 0 < k ∧ 0 < A ∧
      norm
          (logDeriv (shiftedRiemannXi (xiLocalDiskCenter T)) z -
            ∑ u ∈ shiftedRiemannXiOpenBallZeroFinset (xiLocalDiskCenter T) R,
              (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Complex) /
                (z - u)) ≤
        8 * Real.log
              (xiLocalDiskGrowthFactor K k A T R) * R / (R - r) ^ 2 +
          (∑ u ∈ shiftedRiemannXiOpenBallZeroFinset
              (xiLocalDiskCenter T) R,
            (shiftedRiemannXiMultiplicity (xiLocalDiskCenter T) u : Real)) * R /
              (R ^ 2 - R * r) := by
  obtain ⟨K, k, hK, hk, hboundary⟩ :=
    exists_shiftedRiemannXiBoundaryMajorant
  obtain ⟨A, hA, hxiInv⟩ :=
    exists_pos_const_norm_riemannXi_threeLine_inv_le_exp
  refine ⟨K, k, A, hK, hk, hA, ?_⟩
  apply norm_logDeriv_shiftedRiemannXi_sub_principalPart_le
    hR hrR (one_lt_xiLocalDiskGrowthFactor hK hk hA hR.le)
      (riemannXi_xiLocalDiskCenter_ne_zero T)
  · exact hboundary (xiLocalDiskCenter T) R hR.le
  · exact shiftedRiemannXiBoundaryMajorant_le_localGrowthFactor_mul_center
      hK hR.le (hxiInv T)
  · exact hz
  · exact hzmem

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
