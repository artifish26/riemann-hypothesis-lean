import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import RiemannHypothesisProject.GuinandWeilDensityFormulaBridge
import RiemannHypothesisProject.RiemannWeilShiftedRadius.RealSchwartzSeminorms

/-!
# Cutoff approximation for shifted-radius source density

This module contains the compact smooth line source, cutoff approximation
families, scaled cutoff derivative bounds, and compact-source density proof
used by the shifted-radius p-series route.
-/

namespace RiemannHypothesisProject

open scoped Topology

/-- Smooth compactly supported functions on the real line, embedded as project
Schwartz test functions by Mathlib's compact-support-to-Schwartz constructor. -/
noncomputable def compactlySupportedSmoothLineToSchwartz
    (g : TestFunction (⊤ : TopologicalSpace.Opens Real) Complex (⊤ : ℕ∞)) :
    SchwartzLineTestFunction :=
  g.hasCompactSupport.toSchwartzMap g.contDiff

/--
Concrete compactly supported smooth real-line source class.

This is the first actual source-image candidate for the 70% p-series gate.  Its
admissible image is the Mathlib `TestFunction` image inside the project
Schwartz space; the remaining hard analytic field is its density in the
Schwartz topology.
-/
noncomputable def compactlySupportedSmoothLineSource :
    GuinandWeilSourceTestFunctionClass where
  SourceTestFunction :=
    TestFunction (⊤ : TopologicalSpace.Opens Real) Complex (⊤ : ℕ∞)
  toSchwartz := compactlySupportedSmoothLineToSchwartz
  sourceFourier := fun g =>
    SchwartzLineTestFunction.fourier
      (compactlySupportedSmoothLineToSchwartz g)
  stripAnalytic := fun _ => True
  rapidDecay := fun _ => True
  admissible := fun _ => True
  admissible_stripAnalytic := by
    intro _ _
    trivial
  admissible_rapidDecay := by
    intro _ _
    trivial
  sourceFourier_eq_projectFourier := by
    intro _ _
    rfl

/-- Compactly supported project Schwartz tests, viewed as the compact smooth
source tests used by `compactlySupportedSmoothLineSource`. -/
noncomputable def compactlySupportedSchwartzLineToSource
    (f : SchwartzLineTestFunction) (hf : HasCompactSupport f) :
    compactlySupportedSmoothLineSource.SourceTestFunction where
  toFun := f
  contDiff' := f.smooth ⊤
  hasCompactSupport' := hf
  tsupport_subset' := by
    intro x _hx
    simp

@[simp]
theorem compactlySupportedSchwartzLineToSource_toSchwartz
    (f : SchwartzLineTestFunction) (hf : HasCompactSupport f) :
    compactlySupportedSmoothLineSource.toSchwartz
        (compactlySupportedSchwartzLineToSource f hf) =
      f := by
  ext x
  rfl

/-- Every compactly supported project Schwartz test belongs to the admissible
image of the compact smooth source class. -/
theorem compactlySupportedSchwartzLine_mem_compactlySupportedSmoothLineSource_image
    (f : SchwartzLineTestFunction) (hf : HasCompactSupport f) :
    f ∈
      guinandWeilAdmissibleSchwartzImage
        compactlySupportedSmoothLineSource := by
  refine ⟨compactlySupportedSchwartzLineToSource f hf, by trivial, ?_⟩
  exact compactlySupportedSchwartzLineToSource_toSchwartz f hf

/-- The compact-support Schwartz core inside the project Schwartz line space. -/
def compactlySupportedSchwartzLineCore : Set SchwartzLineTestFunction :=
  {f : SchwartzLineTestFunction | HasCompactSupport f}

/-- The compact-support Schwartz core is contained in the concrete compact
smooth source image. -/
theorem compactlySupportedSchwartzLineCore_subset_compactlySupportedSmoothLineSource_image :
    compactlySupportedSchwartzLineCore ⊆
      guinandWeilAdmissibleSchwartzImage
        compactlySupportedSmoothLineSource := by
  intro f hf
  exact
    compactlySupportedSchwartzLine_mem_compactlySupportedSmoothLineSource_image
      f hf

/-- Density of compactly supported Schwartz tests implies density of the actual
compact smooth source image. -/
theorem compactlySupportedSmoothLineSource_dense_of_compactlySupportedSchwartzLineCore_dense
    (hdense : closure compactlySupportedSchwartzLineCore = Set.univ) :
    closure
        (guinandWeilAdmissibleSchwartzImage
          compactlySupportedSmoothLineSource) =
      Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro f
  have hf_core : f ∈ closure compactlySupportedSchwartzLineCore := by
    rw [hdense]
    exact Set.mem_univ f
  exact
    (closure_mono
      compactlySupportedSchwartzLineCore_subset_compactlySupportedSmoothLineSource_image)
      hf_core

/-- A compactly supported Schwartz approximation sequence is enough to close
the actual compact smooth source-image density field. -/
theorem compactlySupportedSmoothLineSource_dense_of_compactlySupportedSchwartz_approx
    (approx : SchwartzLineTestFunction -> Nat -> SchwartzLineTestFunction)
    (hcompact :
      forall (f : SchwartzLineTestFunction) (N : Nat),
        HasCompactSupport (approx f N))
    (happrox :
      forall f : SchwartzLineTestFunction,
        Filter.Tendsto (fun N : Nat => approx f N)
          Filter.atTop (nhds f)) :
    closure
        (guinandWeilAdmissibleSchwartzImage
          compactlySupportedSmoothLineSource) =
      Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro f
  refine mem_closure_of_tendsto (happrox f) ?_
  exact Filter.Eventually.of_forall fun N =>
    compactlySupportedSchwartzLine_mem_compactlySupportedSmoothLineSource_image
      (approx f N) (hcompact f N)

/-- Radius-`N` smooth cutoff bump, equal to one on `‖x‖ <= N + 1`
and supported in `‖x‖ < N + 2`. -/
noncomputable def schwartzLineCutoffBump (N : Nat) :
    ContDiffBump (0 : Real) where
  rIn := (N : Real) + 1
  rOut := (N : Real) + 2
  rIn_pos := by positivity
  rIn_lt_rOut := by norm_num

/-- The complex-valued scalar cutoff used to truncate Schwartz line tests. -/
noncomputable def schwartzLineCutoffScalar (N : Nat) (x : Real) :
    Complex :=
  schwartzLineCutoffBump N x

theorem schwartzLineCutoffScalar_contDiff (N : Nat) :
    ContDiff ℝ (⊤ : ℕ∞) (schwartzLineCutoffScalar N) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (Complex.ofReal ∘ (schwartzLineCutoffBump N : Real -> Real))
  exact Complex.ofRealCLM.contDiff.comp (schwartzLineCutoffBump N).contDiff

theorem schwartzLineCutoffScalar_hasCompactSupport (N : Nat) :
    HasCompactSupport (schwartzLineCutoffScalar N) := by
  change HasCompactSupport
    (Complex.ofReal ∘ (schwartzLineCutoffBump N : Real -> Real))
  exact
    (schwartzLineCutoffBump N).hasCompactSupport.comp_left
      (g := Complex.ofReal) (by simp)

theorem schwartzLineCutoffScalar_hasTemperateGrowth (N : Nat) :
    Function.HasTemperateGrowth (schwartzLineCutoffScalar N) :=
  (schwartzLineCutoffScalar_hasCompactSupport N).hasTemperateGrowth
    (schwartzLineCutoffScalar_contDiff N)

@[simp]
theorem schwartzLineCutoffScalar_eq_one_of_norm_le
    (N : Nat) {x : Real} (hx : ‖x‖ <= (N : Real) + 1) :
    schwartzLineCutoffScalar N x = 1 := by
  have hxmem :
      x ∈ Metric.closedBall (0 : Real) (schwartzLineCutoffBump N).rIn := by
    simpa [schwartzLineCutoffBump, Real.dist_eq] using hx
  have hone : schwartzLineCutoffBump N x = 1 :=
    (schwartzLineCutoffBump N).one_of_mem_closedBall hxmem
  simp [schwartzLineCutoffScalar, hone]

@[simp]
theorem schwartzLineCutoffScalar_eq_zero_of_radius_le_norm
    (N : Nat) {x : Real} (hx : (N : Real) + 2 <= ‖x‖) :
    schwartzLineCutoffScalar N x = 0 := by
  have hdist :
      (schwartzLineCutoffBump N).rOut <= dist x (0 : Real) := by
    simpa [schwartzLineCutoffBump, Real.dist_eq] using hx
  have hzero : schwartzLineCutoffBump N x = 0 :=
    (schwartzLineCutoffBump N).zero_of_le_dist hdist
  simp [schwartzLineCutoffScalar, hzero]

/-- The concrete cutoff approximation `χ_N · f` in the project Schwartz line
space. -/
noncomputable def schwartzLineCutoffApprox
    (N : Nat) (f : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  SchwartzMap.smulLeftCLM Complex (schwartzLineCutoffScalar N) f

@[simp]
theorem schwartzLineCutoffApprox_apply
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    schwartzLineCutoffApprox N f x =
      schwartzLineCutoffScalar N x * f x := by
  simp [schwartzLineCutoffApprox,
    SchwartzMap.smulLeftCLM_apply_apply
      (schwartzLineCutoffScalar_hasTemperateGrowth N), smul_eq_mul]

@[simp]
theorem schwartzLineCutoffApprox_apply_eq_self_of_norm_le
    (N : Nat) (f : SchwartzLineTestFunction) {x : Real}
    (hx : ‖x‖ <= (N : Real) + 1) :
    schwartzLineCutoffApprox N f x = f x := by
  simp [schwartzLineCutoffScalar_eq_one_of_norm_le N hx]

@[simp]
theorem schwartzLineCutoffApprox_apply_eq_zero_of_radius_le_norm
    (N : Nat) (f : SchwartzLineTestFunction) {x : Real}
    (hx : (N : Real) + 2 <= ‖x‖) :
    schwartzLineCutoffApprox N f x = 0 := by
  simp [schwartzLineCutoffScalar_eq_zero_of_radius_le_norm N hx]

/-- The cutoff approximant agrees with the target on its inner closed ball. -/
theorem schwartzLineCutoffApprox_eqOn_closedBall
    (N : Nat) (f : SchwartzLineTestFunction) :
    Set.EqOn (schwartzLineCutoffApprox N f) f
      (Metric.closedBall (0 : Real) ((N : Real) + 1)) := by
  intro x hx
  apply schwartzLineCutoffApprox_apply_eq_self_of_norm_le
  simpa [Real.dist_eq] using hx

/-- At each fixed point, the cutoff approximants are eventually equal to the
original Schwartz test function. -/
theorem schwartzLineCutoffApprox_eventually_apply_eq_self
    (f : SchwartzLineTestFunction) (x : Real) :
    ∀ᶠ N : Nat in Filter.atTop, schwartzLineCutoffApprox N f x = f x := by
  rw [Filter.eventually_atTop]
  obtain ⟨N0, hN0⟩ := exists_nat_ge ‖x‖
  refine ⟨N0, ?_⟩
  intro N hN
  apply schwartzLineCutoffApprox_apply_eq_self_of_norm_le
  have hN0' : ‖x‖ <= (N0 : Real) := hN0
  have hN' : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  linarith

/-- At each fixed point, every fixed real derivative of the cutoff approximants
is eventually equal to the corresponding derivative of the target. -/
theorem schwartzLineCutoffApprox_eventually_iteratedDeriv_eq_self
    (f : SchwartzLineTestFunction) (n : Nat) (x : Real) :
    ∀ᶠ N : Nat in Filter.atTop,
      iteratedDeriv n (schwartzLineCutoffApprox N f : Real -> Complex) x =
        iteratedDeriv n (f : Real -> Complex) x := by
  rw [Filter.eventually_atTop]
  obtain ⟨N0, hN0⟩ := exists_nat_gt ‖x‖
  refine ⟨N0, ?_⟩
  intro N hN
  have hxball :
      x ∈ Metric.ball (0 : Real) ((N : Real) + 1) := by
    have hN' : (N0 : Real) <= (N : Real) := by
      exact_mod_cast hN
    have hxlt : ‖x‖ < (N : Real) + 1 := by
      linarith
    simpa [Metric.mem_ball, Real.dist_eq] using hxlt
  have hnear :
      (schwartzLineCutoffApprox N f : Real -> Complex) =ᶠ[𝓝 x]
        (f : Real -> Complex) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
    apply schwartzLineCutoffApprox_apply_eq_self_of_norm_le
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)
  exact Filter.EventuallyEq.iteratedDeriv_eq n hnear

/-- On each compact real set, the cutoff approximants are eventually equal to
the target Schwartz test function. -/
theorem schwartzLineCutoffApprox_eventually_eqOn_compact
    (f : SchwartzLineTestFunction) {K : Set Real} (hK : IsCompact K) :
    ∀ᶠ N : Nat in Filter.atTop,
      Set.EqOn (schwartzLineCutoffApprox N f) f K := by
  rw [Filter.eventually_atTop]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Real)
  obtain ⟨N0, hN0⟩ := exists_nat_ge R
  refine ⟨N0, ?_⟩
  intro N hN x hx
  apply schwartzLineCutoffApprox_apply_eq_self_of_norm_le
  have hxR : ‖x‖ <= R := by
    simpa [Metric.mem_closedBall, Real.dist_eq] using hR hx
  have hN0' : R <= (N0 : Real) := hN0
  have hN' : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  linarith

/-- On each compact real set, every fixed derivative of the cutoff
approximants is eventually equal to the corresponding derivative of the target. -/
theorem schwartzLineCutoffApprox_eventually_iteratedDeriv_eqOn_compact
    (f : SchwartzLineTestFunction) (n : Nat) {K : Set Real}
    (hK : IsCompact K) :
    ∀ᶠ N : Nat in Filter.atTop,
      Set.EqOn
        (fun x : Real =>
          iteratedDeriv n (schwartzLineCutoffApprox N f : Real -> Complex) x)
        (fun x : Real => iteratedDeriv n (f : Real -> Complex) x) K := by
  rw [Filter.eventually_atTop]
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Real)
  obtain ⟨N0, hN0⟩ := exists_nat_ge R
  refine ⟨N0, ?_⟩
  intro N hN x hx
  have hxball :
      x ∈ Metric.ball (0 : Real) ((N : Real) + 1) := by
    have hxR : ‖x‖ <= R := by
      simpa [Metric.mem_closedBall, Real.dist_eq] using hR hx
    have hN0' : R <= (N0 : Real) := hN0
    have hN' : (N0 : Real) <= (N : Real) := by
      exact_mod_cast hN
    have hxlt : ‖x‖ < (N : Real) + 1 := by
      linarith
    simpa [Metric.mem_ball, Real.dist_eq] using hxlt
  have hnear :
      (schwartzLineCutoffApprox N f : Real -> Complex) =ᶠ[𝓝 x]
        (f : Real -> Complex) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
    apply schwartzLineCutoffApprox_apply_eq_self_of_norm_le
    exact le_of_lt (by simpa [Metric.mem_ball, Real.dist_eq] using hy)
  exact Filter.EventuallyEq.iteratedDeriv_eq n hnear

/-- The scalar cutoff differs from `1` by norm at most `1`. -/
theorem schwartzLineCutoffScalar_norm_sub_one_le (N : Nat) (x : Real) :
    ‖schwartzLineCutoffScalar N x - 1‖ <= 1 := by
  have h0 : 0 <= schwartzLineCutoffBump N x :=
    (schwartzLineCutoffBump N).nonneg
  have h1 : schwartzLineCutoffBump N x <= 1 :=
    (schwartzLineCutoffBump N).le_one
  have habs : |schwartzLineCutoffBump N x - 1| <= 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr h1)]
    linarith
  let a : Real := schwartzLineCutoffBump N x - 1
  have habs' : |a| <= 1 := by
    simpa [a] using habs
  have hnorm : ‖(a : Complex)‖ <= 1 := by
    simpa [Complex.norm_real] using habs'
  convert hnorm using 1
  simp [a, schwartzLineCutoffScalar]

/-- Pointwise value-error of the cutoff approximation is bounded by the target
value. -/
theorem schwartzLineCutoffApprox_sub_apply_norm_le
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    ‖(schwartzLineCutoffApprox N f - f) x‖ <= ‖f x‖ := by
  have hmul :
      schwartzLineCutoffApprox N f x - f x =
        (schwartzLineCutoffScalar N x - 1) * f x := by
    rw [schwartzLineCutoffApprox_apply]
    ring
  change ‖schwartzLineCutoffApprox N f x - f x‖ <= ‖f x‖
  rw [hmul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) <|
    schwartzLineCutoffScalar_norm_sub_one_le N x

/-- The value seminorm of the cutoff error is controlled by the next Schwartz
tail seminorm of the target. -/
theorem schwartzLineCutoffApprox_zeroDeriv_seminorm_le
    (N k : Nat) (f : SchwartzLineTestFunction) :
    SchwartzMap.seminorm ℝ k 0 (schwartzLineCutoffApprox N f - f) <=
      SchwartzMap.seminorm ℝ (k + 1) 0 f / ((N : Real) + 1) := by
  have hden_pos : 0 < (N : Real) + 1 := by positivity
  refine SchwartzMap.seminorm_le_bound' ℝ k 0
    (schwartzLineCutoffApprox N f - f)
    (div_nonneg (apply_nonneg _ _) hden_pos.le) ?_
  intro x
  simp only [iteratedDeriv_zero]
  by_cases hx : ‖x‖ <= (N : Real) + 1
  · have hzero : (schwartzLineCutoffApprox N f - f) x = 0 := by
      change schwartzLineCutoffApprox N f x - f x = 0
      rw [schwartzLineCutoffApprox_apply_eq_self_of_norm_le N f hx]
      simp
    simpa [hzero] using
      (div_nonneg (apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) 0) f)
        hden_pos.le)
  · have hxge_norm : (N : Real) + 1 <= ‖x‖ := le_of_not_ge hx
    have hxge_abs : (N : Real) + 1 <= |x| := by
      simpa [Real.norm_eq_abs] using hxge_norm
    have hfactor : 1 <= |x| / ((N : Real) + 1) := by
      rw [le_div_iff₀ hden_pos]
      simpa using hxge_abs
    have hpoint := schwartzLineCutoffApprox_sub_apply_norm_le N f x
    have habs_nonneg : 0 <= |x| := abs_nonneg x
    have hpow_nonneg : 0 <= |x| ^ k := pow_nonneg habs_nonneg k
    have hmul_nonneg : 0 <= |x| ^ k * ‖f x‖ :=
      mul_nonneg hpow_nonneg (norm_nonneg _)
    have htail0 :
        |x| ^ k * ‖(schwartzLineCutoffApprox N f - f) x‖ <=
          |x| ^ k * ‖f x‖ :=
      mul_le_mul_of_nonneg_left hpoint hpow_nonneg
    have htail1 :
        |x| ^ k * ‖f x‖ <=
          |x| ^ (k + 1) * ‖f x‖ / ((N : Real) + 1) := by
      calc
        |x| ^ k * ‖f x‖
            <= (|x| ^ k * ‖f x‖) * (|x| / ((N : Real) + 1)) :=
          le_mul_of_one_le_right hmul_nonneg hfactor
        _ = |x| ^ (k + 1) * ‖f x‖ / ((N : Real) + 1) := by
          rw [pow_succ]
          ring
    have hseminorm := SchwartzMap.le_seminorm' ℝ (k + 1) 0 f x
    simp only [iteratedDeriv_zero] at hseminorm
    have htail2 :
        |x| ^ (k + 1) * ‖f x‖ / ((N : Real) + 1) <=
          SchwartzMap.seminorm ℝ (k + 1) 0 f / ((N : Real) + 1) :=
      div_le_div_of_nonneg_right hseminorm hden_pos.le
    exact htail0.trans (htail1.trans htail2)

/-- The concrete cutoff approximants converge in every value-only Schwartz
seminorm. -/
theorem schwartzLineCutoffApprox_zeroDeriv_schwartzSeminorm_eventually_lt
    (f : SchwartzLineTestFunction) (k : Nat) {ε : Real} (hε : 0 < ε) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      schwartzSeminormFamily ℝ Real Complex (k, 0)
        (schwartzLineCutoffApprox N f - f) < ε := by
  let S : Real := SchwartzMap.seminorm ℝ (k + 1) 0 f
  obtain ⟨N0, hN0⟩ := exists_nat_gt (S / ε)
  refine ⟨N0, ?_⟩
  intro N hN
  have hden_pos : 0 < (N : Real) + 1 := by positivity
  have hN0_le_N : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  have hden_gt : S / ε < (N : Real) + 1 := by
    linarith
  have hS_lt : S < ((N : Real) + 1) * ε :=
    (div_lt_iff₀ hε).1 hden_gt
  have htail_lt : S / ((N : Real) + 1) < ε := by
    rw [div_lt_iff₀ hden_pos]
    linarith
  have hle := schwartzLineCutoffApprox_zeroDeriv_seminorm_le N k f
  have hmain :
      SchwartzMap.seminorm ℝ k 0 (schwartzLineCutoffApprox N f - f) < ε := by
    exact lt_of_le_of_lt hle (by simpa [S] using htail_lt)
  simpa [schwartzSeminormFamily] using hmain

/-- Fixed-shape cutoff base for scaled truncations.  Unlike
`schwartzLineCutoffBump`, this bump is rescaled by radius, so differentiating
the rescaled cutoff contributes explicit inverse powers of the radius. -/
noncomputable def schwartzLineScaledCutoffBaseBump :
    ContDiffBump (0 : Real) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- Complex-valued fixed-shape cutoff base. -/
noncomputable def schwartzLineScaledCutoffBaseScalar (x : Real) :
    Complex :=
  schwartzLineScaledCutoffBaseBump x

theorem schwartzLineScaledCutoffBaseScalar_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) schwartzLineScaledCutoffBaseScalar := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (Complex.ofReal ∘ (schwartzLineScaledCutoffBaseBump : Real -> Real))
  exact Complex.ofRealCLM.contDiff.comp
    schwartzLineScaledCutoffBaseBump.contDiff

theorem schwartzLineScaledCutoffBaseScalar_hasCompactSupport :
    HasCompactSupport schwartzLineScaledCutoffBaseScalar := by
  change HasCompactSupport
    (Complex.ofReal ∘ (schwartzLineScaledCutoffBaseBump : Real -> Real))
  exact
    schwartzLineScaledCutoffBaseBump.hasCompactSupport.comp_left
      (g := Complex.ofReal) (by simp)

/-- The fixed cutoff base has a finite global first-derivative bound. -/
theorem schwartzLineScaledCutoffBaseScalar_deriv_norm_bounded :
    ∃ C : Real, 0 <= C ∧ ∀ x : Real,
      ‖deriv schwartzLineScaledCutoffBaseScalar x‖ <= C := by
  let g := fun x : Real =>
    ‖deriv schwartzLineScaledCutoffBaseScalar x‖
  have hg_cont : Continuous g := by
    dsimp [g]
    exact
      (schwartzLineScaledCutoffBaseScalar_contDiff.continuous_deriv
        (by simp)).norm
  have hg_compact : HasCompactSupport g := by
    dsimp [g]
    exact schwartzLineScaledCutoffBaseScalar_hasCompactSupport.deriv.norm
  obtain ⟨x0, hx0⟩ :=
    hg_cont.exists_forall_ge_of_hasCompactSupport hg_compact
  refine ⟨g x0, norm_nonneg _, ?_⟩
  intro x
  exact hx0 x

/-- A chosen global first-derivative bound for the fixed cutoff base. -/
noncomputable def schwartzLineScaledCutoffBaseDerivBound : Real :=
  Classical.choose schwartzLineScaledCutoffBaseScalar_deriv_norm_bounded

theorem schwartzLineScaledCutoffBaseDerivBound_nonneg :
    0 <= schwartzLineScaledCutoffBaseDerivBound :=
  (Classical.choose_spec
    schwartzLineScaledCutoffBaseScalar_deriv_norm_bounded).1

theorem schwartzLineScaledCutoffBaseScalar_deriv_norm_le (x : Real) :
    ‖deriv schwartzLineScaledCutoffBaseScalar x‖ <=
      schwartzLineScaledCutoffBaseDerivBound :=
  (Classical.choose_spec
    schwartzLineScaledCutoffBaseScalar_deriv_norm_bounded).2 x

/-- The fixed cutoff base has a finite global second-derivative bound. -/
theorem schwartzLineScaledCutoffBaseScalar_secondDeriv_norm_bounded :
    ∃ C : Real, 0 <= C ∧ ∀ x : Real,
      ‖iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar x‖ <= C := by
  let g := fun x : Real =>
    ‖iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar x‖
  have hg_cont : Continuous g := by
    have htwo_le_infty :
        (2 : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) <= ⊤)
    dsimp [g]
    exact
      (schwartzLineScaledCutoffBaseScalar_contDiff.of_le
        htwo_le_infty).continuous_iteratedDeriv' 2
        |>.norm
  have hiter :
      iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar =
        deriv (deriv schwartzLineScaledCutoffBaseScalar) := by
    rw [show (2 : Nat) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  have hg_compact : HasCompactSupport g := by
    dsimp [g]
    rw [hiter]
    exact schwartzLineScaledCutoffBaseScalar_hasCompactSupport.deriv.deriv.norm
  obtain ⟨x0, hx0⟩ :=
    hg_cont.exists_forall_ge_of_hasCompactSupport hg_compact
  refine ⟨g x0, norm_nonneg _, ?_⟩
  intro x
  exact hx0 x

/-- A chosen global second-derivative bound for the fixed cutoff base. -/
noncomputable def schwartzLineScaledCutoffBaseSecondDerivBound : Real :=
  Classical.choose schwartzLineScaledCutoffBaseScalar_secondDeriv_norm_bounded

theorem schwartzLineScaledCutoffBaseSecondDerivBound_nonneg :
    0 <= schwartzLineScaledCutoffBaseSecondDerivBound :=
  (Classical.choose_spec
    schwartzLineScaledCutoffBaseScalar_secondDeriv_norm_bounded).1

theorem schwartzLineScaledCutoffBaseScalar_secondDeriv_norm_le (x : Real) :
    ‖iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar x‖ <=
      schwartzLineScaledCutoffBaseSecondDerivBound :=
  (Classical.choose_spec
    schwartzLineScaledCutoffBaseScalar_secondDeriv_norm_bounded).2 x

/-- The fixed cutoff base has a finite global third-derivative bound. -/
theorem schwartzLineScaledCutoffBaseScalar_thirdDeriv_norm_bounded :
    ∃ C : Real, 0 <= C ∧ ∀ x : Real,
      ‖iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar x‖ <= C := by
  let g := fun x : Real =>
    ‖iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar x‖
  have hg_cont : Continuous g := by
    have hthree_le_infty :
        (3 : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) <= ⊤)
    dsimp [g]
    exact
      (schwartzLineScaledCutoffBaseScalar_contDiff.of_le
        hthree_le_infty).continuous_iteratedDeriv' 3
        |>.norm
  have hiter :
      iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar =
        deriv (deriv (deriv schwartzLineScaledCutoffBaseScalar)) := by
    rw [show (3 : Nat) = 2 + 1 by norm_num, iteratedDeriv_succ,
      show (2 : Nat) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
  have hg_compact : HasCompactSupport g := by
    dsimp [g]
    rw [hiter]
    exact
      schwartzLineScaledCutoffBaseScalar_hasCompactSupport.deriv.deriv.deriv.norm
  obtain ⟨x0, hx0⟩ :=
    hg_cont.exists_forall_ge_of_hasCompactSupport hg_compact
  refine ⟨g x0, norm_nonneg _, ?_⟩
  intro x
  exact hx0 x

/-- A chosen global third-derivative bound for the fixed cutoff base. -/
noncomputable def schwartzLineScaledCutoffBaseThirdDerivBound : Real :=
  Classical.choose schwartzLineScaledCutoffBaseScalar_thirdDeriv_norm_bounded

theorem schwartzLineScaledCutoffBaseThirdDerivBound_nonneg :
    0 <= schwartzLineScaledCutoffBaseThirdDerivBound :=
  (Classical.choose_spec
    schwartzLineScaledCutoffBaseScalar_thirdDeriv_norm_bounded).1

theorem schwartzLineScaledCutoffBaseScalar_thirdDeriv_norm_le (x : Real) :
    ‖iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar x‖ <=
      schwartzLineScaledCutoffBaseThirdDerivBound :=
  (Classical.choose_spec
    schwartzLineScaledCutoffBaseScalar_thirdDeriv_norm_bounded).2 x

/-- Every finite derivative of the fixed cutoff base has a finite global norm
bound.  This is the uniform replacement for climbing cutoff derivatives one
order at a time. -/
theorem schwartzLineScaledCutoffBaseScalar_iteratedDeriv_norm_bounded
    (m : Nat) :
    ∃ C : Real, 0 <= C ∧ ∀ x : Real,
      ‖iteratedDeriv m schwartzLineScaledCutoffBaseScalar x‖ <= C := by
  have h_compact_iter :
      HasCompactSupport
        (((fun f : Real -> Complex => deriv f)^[m])
          schwartzLineScaledCutoffBaseScalar) := by
    induction m with
    | zero =>
        simpa using schwartzLineScaledCutoffBaseScalar_hasCompactSupport
    | succ m ih =>
        rw [Function.iterate_succ']
        exact ih.deriv
  let g := fun x : Real =>
    ‖iteratedDeriv m schwartzLineScaledCutoffBaseScalar x‖
  have hg_cont : Continuous g := by
    have hm_le_infty :
        (m : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact WithTop.coe_le_coe.2 (le_top : (m : ℕ∞) <= ⊤)
    dsimp [g]
    exact
      (schwartzLineScaledCutoffBaseScalar_contDiff.of_le
        hm_le_infty).continuous_iteratedDeriv' m
        |>.norm
  have hg_compact : HasCompactSupport g := by
    dsimp [g]
    rw [iteratedDeriv_eq_iterate]
    exact h_compact_iter.norm
  obtain ⟨x0, hx0⟩ :=
    hg_cont.exists_forall_ge_of_hasCompactSupport hg_compact
  refine ⟨g x0, norm_nonneg _, ?_⟩
  intro x
  exact hx0 x

/-- A chosen global norm bound for the `m`-th derivative of the fixed cutoff
base. -/
noncomputable def schwartzLineScaledCutoffBaseIteratedDerivBound
    (m : Nat) : Real :=
  Classical.choose
    (schwartzLineScaledCutoffBaseScalar_iteratedDeriv_norm_bounded m)

theorem schwartzLineScaledCutoffBaseIteratedDerivBound_nonneg
    (m : Nat) :
    0 <= schwartzLineScaledCutoffBaseIteratedDerivBound m :=
  (Classical.choose_spec
    (schwartzLineScaledCutoffBaseScalar_iteratedDeriv_norm_bounded m)).1

theorem schwartzLineScaledCutoffBaseScalar_iteratedDeriv_norm_le
    (m : Nat) (x : Real) :
    ‖iteratedDeriv m schwartzLineScaledCutoffBaseScalar x‖ <=
      schwartzLineScaledCutoffBaseIteratedDerivBound m :=
  (Classical.choose_spec
    (schwartzLineScaledCutoffBaseScalar_iteratedDeriv_norm_bounded m)).2 x

/-- Radius used by the scaled fixed-shape cutoff. -/
def schwartzLineScaledCutoffRadius (N : Nat) : Real :=
  (N : Real) + 1

theorem schwartzLineScaledCutoffRadius_pos (N : Nat) :
    0 < schwartzLineScaledCutoffRadius N := by
  dsimp [schwartzLineScaledCutoffRadius]
  positivity

/-- Radius-scaled cutoff.  Its transition annulus has fixed ratio, not fixed
width, which is what gives derivative decay. -/
noncomputable def schwartzLineScaledCutoffScalar (N : Nat) (x : Real) :
    Complex :=
  schwartzLineScaledCutoffBaseScalar
    ((schwartzLineScaledCutoffRadius N)⁻¹ * x)

theorem schwartzLineScaledCutoffScalar_contDiff (N : Nat) :
    ContDiff ℝ (⊤ : ℕ∞) (schwartzLineScaledCutoffScalar N) := by
  unfold schwartzLineScaledCutoffScalar
  exact schwartzLineScaledCutoffBaseScalar_contDiff.comp (by fun_prop)

@[simp]
theorem schwartzLineScaledCutoffScalar_eq_one_of_norm_le
    (N : Nat) {x : Real}
    (hx : ‖x‖ <= schwartzLineScaledCutoffRadius N) :
    schwartzLineScaledCutoffScalar N x = 1 := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hinv_nonneg :
      0 <= (schwartzLineScaledCutoffRadius N)⁻¹ :=
    inv_nonneg.mpr hR_pos.le
  have hnorm_scale :
      ‖(schwartzLineScaledCutoffRadius N)⁻¹ * x‖ <= 1 := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    rw [inv_mul_eq_div, div_le_iff₀ hR_pos]
    simpa using hx
  have hxmem :
      (schwartzLineScaledCutoffRadius N)⁻¹ * x ∈
        Metric.closedBall (0 : Real)
          schwartzLineScaledCutoffBaseBump.rIn := by
    simpa [schwartzLineScaledCutoffBaseBump, Real.dist_eq]
      using hnorm_scale
  have hone :
      schwartzLineScaledCutoffBaseBump
        ((schwartzLineScaledCutoffRadius N)⁻¹ * x) = 1 :=
    schwartzLineScaledCutoffBaseBump.one_of_mem_closedBall hxmem
  simp [schwartzLineScaledCutoffScalar,
    schwartzLineScaledCutoffBaseScalar, hone]

@[simp]
theorem schwartzLineScaledCutoffScalar_eq_zero_of_radius_le_norm
    (N : Nat) {x : Real}
    (hx : 2 * schwartzLineScaledCutoffRadius N <= ‖x‖) :
    schwartzLineScaledCutoffScalar N x = 0 := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hinv_nonneg :
      0 <= (schwartzLineScaledCutoffRadius N)⁻¹ :=
    inv_nonneg.mpr hR_pos.le
  have hnorm_scale :
      2 <= ‖(schwartzLineScaledCutoffRadius N)⁻¹ * x‖ := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hinv_nonneg]
    rw [inv_mul_eq_div, le_div_iff₀ hR_pos]
    simpa using hx
  have hdist :
      schwartzLineScaledCutoffBaseBump.rOut <=
        dist ((schwartzLineScaledCutoffRadius N)⁻¹ * x) (0 : Real) := by
    simpa [schwartzLineScaledCutoffBaseBump, Real.dist_eq]
      using hnorm_scale
  have hzero :
      schwartzLineScaledCutoffBaseBump
        ((schwartzLineScaledCutoffRadius N)⁻¹ * x) = 0 :=
    schwartzLineScaledCutoffBaseBump.zero_of_le_dist hdist
  simp [schwartzLineScaledCutoffScalar,
    schwartzLineScaledCutoffBaseScalar, hzero]

/-- The scaled cutoff is supported inside the closed ball of radius `2R`. -/
theorem schwartzLineScaledCutoffScalar_tsupport_subset_closedBall
    (N : Nat) :
    tsupport (schwartzLineScaledCutoffScalar N) ⊆
      Metric.closedBall (0 : Real)
        (2 * schwartzLineScaledCutoffRadius N) := by
  rw [tsupport]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  by_contra hxball
  have hxnorm :
      2 * schwartzLineScaledCutoffRadius N <= ‖x‖ := by
    have hlt :
        2 * schwartzLineScaledCutoffRadius N < dist x (0 : Real) := by
      simpa [Metric.mem_closedBall] using hxball
    have hdist : dist x (0 : Real) = ‖x‖ := by
      simp
    linarith
  exact hx
    (schwartzLineScaledCutoffScalar_eq_zero_of_radius_le_norm N hxnorm)

theorem schwartzLineScaledCutoffScalar_hasCompactSupport (N : Nat) :
    HasCompactSupport (schwartzLineScaledCutoffScalar N) := by
  exact
    IsCompact.of_isClosed_subset
      (isCompact_closedBall (0 : Real)
        (2 * schwartzLineScaledCutoffRadius N))
      isClosed_closure
      (schwartzLineScaledCutoffScalar_tsupport_subset_closedBall N)

theorem schwartzLineScaledCutoffScalar_hasTemperateGrowth (N : Nat) :
    Function.HasTemperateGrowth (schwartzLineScaledCutoffScalar N) :=
  (schwartzLineScaledCutoffScalar_hasCompactSupport N).hasTemperateGrowth
    (schwartzLineScaledCutoffScalar_contDiff N)

/-- The scaled scalar cutoff differs from `1` by norm at most `1`. -/
theorem schwartzLineScaledCutoffScalar_norm_sub_one_le
    (N : Nat) (x : Real) :
    ‖schwartzLineScaledCutoffScalar N x - 1‖ <= 1 := by
  have h0 :
      0 <= schwartzLineScaledCutoffBaseBump
        ((schwartzLineScaledCutoffRadius N)⁻¹ * x) :=
    schwartzLineScaledCutoffBaseBump.nonneg
  have h1 :
      schwartzLineScaledCutoffBaseBump
        ((schwartzLineScaledCutoffRadius N)⁻¹ * x) <= 1 :=
    schwartzLineScaledCutoffBaseBump.le_one
  have habs :
      |schwartzLineScaledCutoffBaseBump
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x) - 1| <= 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr h1)]
    linarith
  let a : Real :=
    schwartzLineScaledCutoffBaseBump
      ((schwartzLineScaledCutoffRadius N)⁻¹ * x) - 1
  have hnorm : ‖(a : Complex)‖ <= 1 := by
    simpa [Complex.norm_real] using habs
  convert hnorm using 1
  simp [a, schwartzLineScaledCutoffScalar,
    schwartzLineScaledCutoffBaseScalar]

theorem schwartzLineScaledCutoffScalar_deriv (N : Nat) :
    deriv (schwartzLineScaledCutoffScalar N) =
      fun x : Real =>
        (schwartzLineScaledCutoffRadius N)⁻¹ •
          deriv schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * x) := by
  have hbase :
      ContDiff ℝ 1 schwartzLineScaledCutoffBaseScalar :=
    schwartzLineScaledCutoffBaseScalar_contDiff.of_le (by simp)
  have hchain :=
    iteratedDeriv_comp_const_smul
      (n := 1) (f := schwartzLineScaledCutoffBaseScalar)
      hbase ((schwartzLineScaledCutoffRadius N)⁻¹)
  funext x
  have hx := congrFun hchain x
  change
    deriv
        (fun y : Real =>
          schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * y)) x =
      (schwartzLineScaledCutoffRadius N)⁻¹ •
        deriv schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  simpa [iteratedDeriv_one] using hx

/-- First derivative of the scaled cutoff is controlled by the base derivative
bound divided by the radius. -/
theorem schwartzLineScaledCutoffScalar_deriv_norm_le
    (N : Nat) (x : Real) :
    ‖deriv (schwartzLineScaledCutoffScalar N) x‖ <=
      schwartzLineScaledCutoffBaseDerivBound /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hderiv := congrFun (schwartzLineScaledCutoffScalar_deriv N) x
  rw [hderiv, norm_smul]
  have hinv_norm :
      ‖(schwartzLineScaledCutoffRadius N)⁻¹‖ =
        (schwartzLineScaledCutoffRadius N)⁻¹ := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (inv_nonneg.mpr hR_pos.le)
  rw [hinv_norm]
  calc
    (schwartzLineScaledCutoffRadius N)⁻¹ *
        ‖deriv schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)‖
        <=
          (schwartzLineScaledCutoffRadius N)⁻¹ *
            schwartzLineScaledCutoffBaseDerivBound :=
      mul_le_mul_of_nonneg_left
        (schwartzLineScaledCutoffBaseScalar_deriv_norm_le
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x))
        (inv_nonneg.mpr hR_pos.le)
    _ =
        schwartzLineScaledCutoffBaseDerivBound /
          schwartzLineScaledCutoffRadius N := by
      rw [div_eq_inv_mul, mul_comm]

theorem schwartzLineScaledCutoffScalar_iteratedDeriv_two (N : Nat) :
    iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) =
      fun x : Real =>
        ((schwartzLineScaledCutoffRadius N)⁻¹ ^ 2) •
          iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * x) := by
  have htwo_le_infty :
      (2 : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) <= ⊤)
  have hbase :
      ContDiff ℝ 2 schwartzLineScaledCutoffBaseScalar :=
    schwartzLineScaledCutoffBaseScalar_contDiff.of_le htwo_le_infty
  have hchain :=
    iteratedDeriv_comp_const_smul
      (n := 2) (f := schwartzLineScaledCutoffBaseScalar)
      hbase ((schwartzLineScaledCutoffRadius N)⁻¹)
  funext x
  have hx := congrFun hchain x
  change
    iteratedDeriv 2
        (fun y : Real =>
          schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * y)) x =
      ((schwartzLineScaledCutoffRadius N)⁻¹ ^ 2) •
        iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  simpa [schwartzLineScaledCutoffScalar] using hx

/-- Second derivative of the scaled cutoff has inverse-radius control.  The
chain rule gives `1 / R^2`; this lemma weakens it to `1 / R`, the scale needed
for seminorm convergence. -/
theorem schwartzLineScaledCutoffScalar_iteratedDeriv_two_norm_le
    (N : Nat) (x : Real) :
    ‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ <=
      schwartzLineScaledCutoffBaseSecondDerivBound /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hR_one : 1 <= schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hinv_nonneg :
      0 <= (schwartzLineScaledCutoffRadius N)⁻¹ :=
    inv_nonneg.mpr hR_pos.le
  have hinv_le_one :
      (schwartzLineScaledCutoffRadius N)⁻¹ <= 1 :=
    inv_le_one_of_one_le₀ hR_one
  have hderiv := congrFun
    (schwartzLineScaledCutoffScalar_iteratedDeriv_two N) x
  rw [hderiv, norm_smul]
  have hpow_norm :
      ‖(schwartzLineScaledCutoffRadius N)⁻¹ ^ 2‖ =
        (schwartzLineScaledCutoffRadius N)⁻¹ ^ 2 := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (pow_nonneg hinv_nonneg 2)
  rw [hpow_norm]
  have hbase :=
    schwartzLineScaledCutoffBaseScalar_secondDeriv_norm_le
      ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  calc
    (schwartzLineScaledCutoffRadius N)⁻¹ ^ 2 *
        ‖iteratedDeriv 2 schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)‖
        <=
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ 2 *
            schwartzLineScaledCutoffBaseSecondDerivBound :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hinv_nonneg 2)
    _ <=
        (schwartzLineScaledCutoffRadius N)⁻¹ *
          schwartzLineScaledCutoffBaseSecondDerivBound := by
      have hpow_le :
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ 2 <=
            (schwartzLineScaledCutoffRadius N)⁻¹ := by
        simpa [pow_succ] using
          mul_le_of_le_one_right hinv_nonneg hinv_le_one
      exact mul_le_mul_of_nonneg_right hpow_le
        schwartzLineScaledCutoffBaseSecondDerivBound_nonneg
    _ =
        schwartzLineScaledCutoffBaseSecondDerivBound /
          schwartzLineScaledCutoffRadius N := by
      rw [div_eq_inv_mul, mul_comm]

theorem schwartzLineScaledCutoffScalar_iteratedDeriv_three (N : Nat) :
    iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) =
      fun x : Real =>
        ((schwartzLineScaledCutoffRadius N)⁻¹ ^ 3) •
          iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * x) := by
  have hthree_le_infty :
      (3 : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) <= ⊤)
  have hbase :
      ContDiff ℝ 3 schwartzLineScaledCutoffBaseScalar :=
    schwartzLineScaledCutoffBaseScalar_contDiff.of_le hthree_le_infty
  have hchain :=
    iteratedDeriv_comp_const_smul
      (n := 3) (f := schwartzLineScaledCutoffBaseScalar)
      hbase ((schwartzLineScaledCutoffRadius N)⁻¹)
  funext x
  have hx := congrFun hchain x
  change
    iteratedDeriv 3
        (fun y : Real =>
          schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * y)) x =
      ((schwartzLineScaledCutoffRadius N)⁻¹ ^ 3) •
        iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  simpa [schwartzLineScaledCutoffScalar] using hx

/-- Third derivative of the scaled cutoff has inverse-radius control.  The
chain rule gives `1 / R^3`; this lemma weakens it to `1 / R`, the scale needed
for seminorm convergence. -/
theorem schwartzLineScaledCutoffScalar_iteratedDeriv_three_norm_le
    (N : Nat) (x : Real) :
    ‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ <=
      schwartzLineScaledCutoffBaseThirdDerivBound /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hR_one : 1 <= schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hinv_nonneg :
      0 <= (schwartzLineScaledCutoffRadius N)⁻¹ :=
    inv_nonneg.mpr hR_pos.le
  have hinv_le_one :
      (schwartzLineScaledCutoffRadius N)⁻¹ <= 1 :=
    inv_le_one_of_one_le₀ hR_one
  have hderiv := congrFun
    (schwartzLineScaledCutoffScalar_iteratedDeriv_three N) x
  rw [hderiv, norm_smul]
  have hpow_norm :
      ‖(schwartzLineScaledCutoffRadius N)⁻¹ ^ 3‖ =
        (schwartzLineScaledCutoffRadius N)⁻¹ ^ 3 := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (pow_nonneg hinv_nonneg 3)
  rw [hpow_norm]
  have hbase :=
    schwartzLineScaledCutoffBaseScalar_thirdDeriv_norm_le
      ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  calc
    (schwartzLineScaledCutoffRadius N)⁻¹ ^ 3 *
        ‖iteratedDeriv 3 schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)‖
        <=
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ 3 *
            schwartzLineScaledCutoffBaseThirdDerivBound :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hinv_nonneg 3)
    _ <=
        (schwartzLineScaledCutoffRadius N)⁻¹ *
          schwartzLineScaledCutoffBaseThirdDerivBound := by
      have hpow_le :
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ 3 <=
            (schwartzLineScaledCutoffRadius N)⁻¹ := by
        calc
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ 3 =
              (schwartzLineScaledCutoffRadius N)⁻¹ ^ 2 *
                (schwartzLineScaledCutoffRadius N)⁻¹ := by
            rw [show (3 : Nat) = 2 + 1 by norm_num, pow_succ]
          _ <= 1 * (schwartzLineScaledCutoffRadius N)⁻¹ :=
            mul_le_mul_of_nonneg_right
              (pow_le_one₀ hinv_nonneg hinv_le_one) hinv_nonneg
          _ = (schwartzLineScaledCutoffRadius N)⁻¹ := by
            ring
      exact mul_le_mul_of_nonneg_right hpow_le
        schwartzLineScaledCutoffBaseThirdDerivBound_nonneg
    _ =
        schwartzLineScaledCutoffBaseThirdDerivBound /
          schwartzLineScaledCutoffRadius N := by
      rw [div_eq_inv_mul, mul_comm]

/-- Chain-rule formula for every finite derivative of the scaled cutoff. -/
theorem schwartzLineScaledCutoffScalar_iteratedDeriv_eq
    (N m : Nat) :
    iteratedDeriv m (schwartzLineScaledCutoffScalar N) =
      fun x : Real =>
        ((schwartzLineScaledCutoffRadius N)⁻¹ ^ m) •
          iteratedDeriv m schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * x) := by
  have hm_le_infty :
      (m : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (le_top : (m : ℕ∞) <= ⊤)
  have hbase :
      ContDiff ℝ m schwartzLineScaledCutoffBaseScalar :=
    schwartzLineScaledCutoffBaseScalar_contDiff.of_le hm_le_infty
  have hchain :=
    iteratedDeriv_comp_const_smul
      (n := m) (f := schwartzLineScaledCutoffBaseScalar)
      hbase ((schwartzLineScaledCutoffRadius N)⁻¹)
  funext x
  have hx := congrFun hchain x
  change
    iteratedDeriv m
        (fun y : Real =>
          schwartzLineScaledCutoffBaseScalar
            ((schwartzLineScaledCutoffRadius N)⁻¹ * y)) x =
      ((schwartzLineScaledCutoffRadius N)⁻¹ ^ m) •
        iteratedDeriv m schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  simpa [schwartzLineScaledCutoffScalar] using hx

/-- Every positive finite derivative of the scaled cutoff is controlled by a
chosen fixed-base derivative bound divided by the scaling radius. -/
theorem schwartzLineScaledCutoffScalar_iteratedDeriv_norm_le
    (N m : Nat) (hm : 1 <= m) (x : Real) :
    ‖iteratedDeriv m (schwartzLineScaledCutoffScalar N) x‖ <=
      schwartzLineScaledCutoffBaseIteratedDerivBound m /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hR_one : 1 <= schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  have hinv_nonneg :
      0 <= (schwartzLineScaledCutoffRadius N)⁻¹ :=
    inv_nonneg.mpr hR_pos.le
  have hderiv := congrFun
    (schwartzLineScaledCutoffScalar_iteratedDeriv_eq N m) x
  rw [hderiv, norm_smul]
  have hpow_norm :
      ‖(schwartzLineScaledCutoffRadius N)⁻¹ ^ m‖ =
        (schwartzLineScaledCutoffRadius N)⁻¹ ^ m := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (pow_nonneg hinv_nonneg m)
  rw [hpow_norm]
  have hbase :=
    schwartzLineScaledCutoffBaseScalar_iteratedDeriv_norm_le m
      ((schwartzLineScaledCutoffRadius N)⁻¹ * x)
  calc
    (schwartzLineScaledCutoffRadius N)⁻¹ ^ m *
        ‖iteratedDeriv m schwartzLineScaledCutoffBaseScalar
          ((schwartzLineScaledCutoffRadius N)⁻¹ * x)‖
        <=
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ m *
            schwartzLineScaledCutoffBaseIteratedDerivBound m :=
      mul_le_mul_of_nonneg_left hbase (pow_nonneg hinv_nonneg m)
    _ <=
        (schwartzLineScaledCutoffRadius N)⁻¹ *
          schwartzLineScaledCutoffBaseIteratedDerivBound m := by
      have hpow_le :
          (schwartzLineScaledCutoffRadius N)⁻¹ ^ m <=
            (schwartzLineScaledCutoffRadius N)⁻¹ := by
        have h :=
          inv_pow_le_inv_pow_of_le
            (a := schwartzLineScaledCutoffRadius N) hR_one
            (m := 1) (n := m) hm
        simpa [inv_pow, pow_one] using h
      exact mul_le_mul_of_nonneg_right hpow_le
        (schwartzLineScaledCutoffBaseIteratedDerivBound_nonneg m)
    _ =
        schwartzLineScaledCutoffBaseIteratedDerivBound m /
          schwartzLineScaledCutoffRadius N := by
      rw [div_eq_inv_mul, mul_comm]

/-- The concrete fixed-ratio scaled cutoff approximation `χ(x/R) · f`. -/
noncomputable def schwartzLineScaledCutoffApprox
    (N : Nat) (f : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  SchwartzMap.smulLeftCLM Complex (schwartzLineScaledCutoffScalar N) f

@[simp]
theorem schwartzLineScaledCutoffApprox_apply
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    schwartzLineScaledCutoffApprox N f x =
      schwartzLineScaledCutoffScalar N x * f x := by
  simp [schwartzLineScaledCutoffApprox,
    SchwartzMap.smulLeftCLM_apply_apply
      (schwartzLineScaledCutoffScalar_hasTemperateGrowth N),
    smul_eq_mul]

@[simp]
theorem schwartzLineScaledCutoffApprox_apply_eq_self_of_norm_le
    (N : Nat) (f : SchwartzLineTestFunction) {x : Real}
    (hx : ‖x‖ <= schwartzLineScaledCutoffRadius N) :
    schwartzLineScaledCutoffApprox N f x = f x := by
  simp [schwartzLineScaledCutoffScalar_eq_one_of_norm_le N hx]

@[simp]
theorem schwartzLineScaledCutoffApprox_apply_eq_zero_of_radius_le_norm
    (N : Nat) (f : SchwartzLineTestFunction) {x : Real}
    (hx : 2 * schwartzLineScaledCutoffRadius N <= ‖x‖) :
    schwartzLineScaledCutoffApprox N f x = 0 := by
  simp [schwartzLineScaledCutoffScalar_eq_zero_of_radius_le_norm N hx]

/-- First derivative of the scaled cutoff error, split into the tail derivative
piece and the cutoff-derivative transition piece. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_one_eq
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    iteratedDeriv 1
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x =
      deriv (schwartzLineScaledCutoffScalar N) x * f x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 1 (f : Real -> Complex) x := by
  have hχdiff :
      DifferentiableAt ℝ (schwartzLineScaledCutoffScalar N) x :=
    (schwartzLineScaledCutoffScalar_contDiff N).differentiable
      (by simp) x
  have hfdiff : DifferentiableAt ℝ (f : Real -> Complex) x :=
    (f.smooth ⊤).differentiable (by simp) x
  have hproddiff :
      DifferentiableAt ℝ
        (fun y : Real => schwartzLineScaledCutoffScalar N y * f y) x :=
    hχdiff.mul hfdiff
  rw [iteratedDeriv_one]
  change
    deriv
        ((schwartzLineScaledCutoffApprox N f : Real -> Complex) -
          (f : Real -> Complex)) x =
      deriv (schwartzLineScaledCutoffScalar N) x * f x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 1 (f : Real -> Complex) x
  have hfun :
      ((schwartzLineScaledCutoffApprox N f : Real -> Complex) -
          (f : Real -> Complex)) =
        fun y : Real =>
          schwartzLineScaledCutoffScalar N y * f y - f y := by
    funext y
    simp [schwartzLineScaledCutoffApprox_apply]
  have hiter :
      iteratedDeriv 1 (f : Real -> Complex) x =
        deriv (f : Real -> Complex) x := by
    simp [iteratedDeriv_one]
  rw [hfun]
  rw [deriv_fun_sub hproddiff hfdiff]
  rw [deriv_fun_mul hχdiff hfdiff]
  rw [hiter]
  ring

/-- Pointwise first-derivative error bound for the scaled cutoff
approximants. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_one_norm_le
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    ‖iteratedDeriv 1
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
      ‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
        ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv 1 (f : Real -> Complex) x‖ := by
  rw [schwartzLineScaledCutoffApprox_sub_iteratedDeriv_one_eq]
  calc
    ‖deriv (schwartzLineScaledCutoffScalar N) x * f x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 1 (f : Real -> Complex) x‖
        <=
          ‖deriv (schwartzLineScaledCutoffScalar N) x * f x‖ +
            ‖(schwartzLineScaledCutoffScalar N x - 1) *
              iteratedDeriv 1 (f : Real -> Complex) x‖ :=
      norm_add_le _ _
    _ =
        ‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ := by
      rw [norm_mul, norm_mul]

/-- Second derivative of the scaled cutoff error, split into the two cutoff
transition terms and the tail second-derivative term. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_two_eq
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    iteratedDeriv 2
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x =
      iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x * f x +
        (2 : Complex) *
          iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x *
            iteratedDeriv 1 (f : Real -> Complex) x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 2 (f : Real -> Complex) x := by
  have htwo_le_infty :
      (2 : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) <= ⊤)
  have hχ :
      ContDiffAt ℝ 2 (schwartzLineScaledCutoffScalar N) x :=
    (schwartzLineScaledCutoffScalar_contDiff N).contDiffAt.of_le
      htwo_le_infty
  have hf : ContDiffAt ℝ 2 (f : Real -> Complex) x :=
    (f.smooth (⊤ : ℕ∞)).contDiffAt.of_le htwo_le_infty
  have hprod :
      ContDiffAt ℝ 2
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex)) x :=
    hχ.mul hf
  have hfun :
      ((schwartzLineScaledCutoffApprox N f : Real -> Complex) -
          (f : Real -> Complex)) =
        fun y : Real =>
          schwartzLineScaledCutoffScalar N y * f y - f y := by
    funext y
    simp [schwartzLineScaledCutoffApprox_apply]
  rw [hfun]
  change
    iteratedDeriv 2
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex) -
          (f : Real -> Complex)) x =
      iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x * f x +
        (2 : Complex) *
          iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x *
            iteratedDeriv 1 (f : Real -> Complex) x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 2 (f : Real -> Complex) x
  rw [iteratedDeriv_sub hprod hf]
  rw [iteratedDeriv_mul hχ hf]
  simp [Finset.sum_range_succ]
  ring

/-- Pointwise second-derivative error bound for the scaled cutoff
approximants. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_two_norm_le
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    ‖iteratedDeriv 2
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
      ‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
        2 *
          (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
        ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv 2 (f : Real -> Complex) x‖ := by
  rw [schwartzLineScaledCutoffApprox_sub_iteratedDeriv_two_eq]
  let A :=
    iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x * f x
  let B :=
    (2 : Complex) *
      iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x *
        iteratedDeriv 1 (f : Real -> Complex) x
  let C :=
    (schwartzLineScaledCutoffScalar N x - 1) *
      iteratedDeriv 2 (f : Real -> Complex) x
  calc
    ‖A + B + C‖ <= ‖A + B‖ + ‖C‖ :=
      norm_add_le _ _
    _ <= (‖A‖ + ‖B‖) + ‖C‖ := by
      have hAB := norm_add_le A B
      linarith
    _ =
      ‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
        2 *
          (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
        ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv 2 (f : Real -> Complex) x‖ := by
      dsimp [A, B, C]
      simp
      ring

/-- Third derivative of the scaled cutoff error, split into cutoff transition
terms and the tail third-derivative term. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_three_eq
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    iteratedDeriv 3
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x =
      iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x * f x +
        (3 : Complex) *
          iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x *
            iteratedDeriv 1 (f : Real -> Complex) x +
        (3 : Complex) *
          iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x *
            iteratedDeriv 2 (f : Real -> Complex) x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 3 (f : Real -> Complex) x := by
  have hthree_le_infty :
      (3 : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (le_top : (3 : ℕ∞) <= ⊤)
  have hχ :
      ContDiffAt ℝ 3 (schwartzLineScaledCutoffScalar N) x :=
    (schwartzLineScaledCutoffScalar_contDiff N).contDiffAt.of_le
      hthree_le_infty
  have hf : ContDiffAt ℝ 3 (f : Real -> Complex) x :=
    (f.smooth (⊤ : ℕ∞)).contDiffAt.of_le hthree_le_infty
  have hprod :
      ContDiffAt ℝ 3
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex)) x :=
    hχ.mul hf
  have hfun :
      ((schwartzLineScaledCutoffApprox N f : Real -> Complex) -
          (f : Real -> Complex)) =
        fun y : Real =>
          schwartzLineScaledCutoffScalar N y * f y - f y := by
    funext y
    simp [schwartzLineScaledCutoffApprox_apply]
  rw [hfun]
  change
    iteratedDeriv 3
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex) -
          (f : Real -> Complex)) x =
      iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x * f x +
        (3 : Complex) *
          iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x *
            iteratedDeriv 1 (f : Real -> Complex) x +
        (3 : Complex) *
          iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x *
            iteratedDeriv 2 (f : Real -> Complex) x +
        (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv 3 (f : Real -> Complex) x
  rw [iteratedDeriv_sub hprod hf]
  rw [iteratedDeriv_mul hχ hf]
  simp [Finset.sum_range_succ]
  ring

/-- Pointwise third-derivative error bound for the scaled cutoff
approximants. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_three_norm_le
    (N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    ‖iteratedDeriv 3
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
      ‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
        3 *
          (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
        3 *
          (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖) +
        ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv 3 (f : Real -> Complex) x‖ := by
  rw [schwartzLineScaledCutoffApprox_sub_iteratedDeriv_three_eq]
  let A :=
    iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x * f x
  let B :=
    (3 : Complex) *
      iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x *
        iteratedDeriv 1 (f : Real -> Complex) x
  let C :=
    (3 : Complex) *
      iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x *
        iteratedDeriv 2 (f : Real -> Complex) x
  let D :=
    (schwartzLineScaledCutoffScalar N x - 1) *
      iteratedDeriv 3 (f : Real -> Complex) x
  calc
    ‖A + B + C + D‖ <= ‖A + B + C‖ + ‖D‖ :=
      norm_add_le _ _
    _ <= (‖A + B‖ + ‖C‖) + ‖D‖ := by
      have hABC := norm_add_le (A + B) C
      linarith
    _ <= ((‖A‖ + ‖B‖) + ‖C‖) + ‖D‖ := by
      have hAB := norm_add_le A B
      linarith
    _ =
      ‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
        3 *
          (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
        3 *
          (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖) +
        ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv 3 (f : Real -> Complex) x‖ := by
      dsimp [A, B, C, D]
      simp
      ring

/-- Exact finite-order Leibniz split for the scaled cutoff error.  The `i = 0`
product term has been combined with the subtraction into `(χ - 1) f⁽ⁿ⁾`; the
remaining finite sum contains only positive cutoff derivatives. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_eq_sum
    (N n : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    iteratedDeriv n
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x =
      (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv n (f : Real -> Complex) x +
        ∑ i ∈ Finset.range n,
          (n.choose (i + 1) : Complex) *
            iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x *
              iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x := by
  have hn_le_infty :
      (n : WithTop ℕ∞) <= ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    exact WithTop.coe_le_coe.2 (le_top : (n : ℕ∞) <= ⊤)
  have hχ :
      ContDiffAt ℝ n (schwartzLineScaledCutoffScalar N) x :=
    (schwartzLineScaledCutoffScalar_contDiff N).contDiffAt.of_le
      hn_le_infty
  have hf : ContDiffAt ℝ n (f : Real -> Complex) x :=
    (f.smooth (⊤ : ℕ∞)).contDiffAt.of_le hn_le_infty
  have hprod :
      ContDiffAt ℝ n
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex)) x :=
    hχ.mul hf
  have hfun :
      ((schwartzLineScaledCutoffApprox N f : Real -> Complex) -
          (f : Real -> Complex)) =
        fun y : Real =>
          schwartzLineScaledCutoffScalar N y * f y - f y := by
    funext y
    simp [schwartzLineScaledCutoffApprox_apply]
  rw [hfun]
  change
    iteratedDeriv n
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex) -
          (f : Real -> Complex)) x =
      (schwartzLineScaledCutoffScalar N x - 1) *
          iteratedDeriv n (f : Real -> Complex) x +
        ∑ i ∈ Finset.range n,
          (n.choose (i + 1) : Complex) *
            iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x *
              iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x
  rw [iteratedDeriv_sub hprod hf]
  rw [iteratedDeriv_mul hχ hf]
  rw [Finset.sum_range_succ']
  simp [Nat.choose_zero_right]
  ring

/-- Pointwise arbitrary-order norm bound for the scaled cutoff error.  The
finite sum contains only positive cutoff derivatives. -/
theorem schwartzLineScaledCutoffApprox_sub_iteratedDeriv_norm_le_sum
    (N n : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    ‖iteratedDeriv n
        (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
      ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv n (f : Real -> Complex) x‖ +
        ∑ i ∈ Finset.range n,
          (n.choose (i + 1) : Real) *
            (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖) := by
  rw [schwartzLineScaledCutoffApprox_sub_iteratedDeriv_eq_sum]
  let Tail :=
    (schwartzLineScaledCutoffScalar N x - 1) *
      iteratedDeriv n (f : Real -> Complex) x
  let Term := fun i : Nat =>
    (n.choose (i + 1) : Complex) *
      iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x *
        iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x
  calc
    ‖Tail + ∑ i ∈ Finset.range n, Term i‖ <=
        ‖Tail‖ + ‖∑ i ∈ Finset.range n, Term i‖ :=
      norm_add_le _ _
    _ <=
        ‖Tail‖ + ∑ i ∈ Finset.range n, ‖Term i‖ := by
      have hsum := norm_sum_le (Finset.range n) Term
      linarith
    _ =
      ‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv n (f : Real -> Complex) x‖ +
        ∑ i ∈ Finset.range n,
          (n.choose (i + 1) : Real) *
            (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖) := by
      dsimp [Tail, Term]
      simp [mul_assoc]

/-- Weighted tail contribution for an arbitrary derivative order: away from the
inner cutoff ball the missing cutoff factor is paid for by one extra Schwartz
weight. -/
theorem schwartzLineScaledCutoffApprox_tail_iteratedDeriv_weighted_le
    (N k n : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    |x| ^ k *
        (‖schwartzLineScaledCutoffScalar N x - 1‖ *
          ‖iteratedDeriv n (f : Real -> Complex) x‖) <=
      SchwartzMap.seminorm ℝ (k + 1) n f /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hS_nonneg :
      0 <= SchwartzMap.seminorm ℝ (k + 1) n f :=
    apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) n) f
  have habs_nonneg : 0 <= |x| := abs_nonneg x
  have hpow_nonneg : 0 <= |x| ^ k :=
    pow_nonneg habs_nonneg k
  by_cases hx : ‖x‖ <= schwartzLineScaledCutoffRadius N
  · have hχ :
        schwartzLineScaledCutoffScalar N x = 1 :=
      schwartzLineScaledCutoffScalar_eq_one_of_norm_le N hx
    have hzero :
        ‖schwartzLineScaledCutoffScalar N x - 1‖ = 0 := by
      simp [hχ]
    rw [hzero, zero_mul, mul_zero]
    exact div_nonneg hS_nonneg hR_pos.le
  · have hxge_norm :
        schwartzLineScaledCutoffRadius N <= ‖x‖ :=
      le_of_not_ge hx
    have hxge_abs :
        schwartzLineScaledCutoffRadius N <= |x| := by
      simpa [Real.norm_eq_abs] using hxge_norm
    have hfactor :
        1 <= |x| / schwartzLineScaledCutoffRadius N := by
      rw [le_div_iff₀ hR_pos]
      simpa using hxge_abs
    have hχ :=
      schwartzLineScaledCutoffScalar_norm_sub_one_le N x
    have hχ_mul :
        ‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv n (f : Real -> Complex) x‖ <=
          ‖iteratedDeriv n (f : Real -> Complex) x‖ := by
      simpa using
        mul_le_mul_of_nonneg_right hχ
          (norm_nonneg
            (iteratedDeriv n (f : Real -> Complex) x))
    have htail0 :
        |x| ^ k *
            (‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv n (f : Real -> Complex) x‖) <=
          |x| ^ k *
            ‖iteratedDeriv n (f : Real -> Complex) x‖ :=
      mul_le_mul_of_nonneg_left hχ_mul hpow_nonneg
    have hbase_nonneg :
        0 <= |x| ^ k *
          ‖iteratedDeriv n (f : Real -> Complex) x‖ :=
      mul_nonneg hpow_nonneg (norm_nonneg _)
    have htail1 :
        |x| ^ k *
            ‖iteratedDeriv n (f : Real -> Complex) x‖ <=
          |x| ^ (k + 1) *
            ‖iteratedDeriv n (f : Real -> Complex) x‖ /
            schwartzLineScaledCutoffRadius N := by
      calc
        |x| ^ k *
            ‖iteratedDeriv n (f : Real -> Complex) x‖
            <=
          (|x| ^ k *
            ‖iteratedDeriv n (f : Real -> Complex) x‖) *
            (|x| / schwartzLineScaledCutoffRadius N) :=
          le_mul_of_one_le_right hbase_nonneg hfactor
        _ =
          |x| ^ (k + 1) *
            ‖iteratedDeriv n (f : Real -> Complex) x‖ /
            schwartzLineScaledCutoffRadius N := by
          rw [pow_succ]
          ring
    have hseminorm := SchwartzMap.le_seminorm' ℝ (k + 1) n f x
    have htail2 :
        |x| ^ (k + 1) *
            ‖iteratedDeriv n (f : Real -> Complex) x‖ /
            schwartzLineScaledCutoffRadius N <=
          SchwartzMap.seminorm ℝ (k + 1) n f /
            schwartzLineScaledCutoffRadius N :=
      div_le_div_of_nonneg_right hseminorm hR_pos.le
    exact htail0.trans (htail1.trans htail2)

/-- Weighted contribution of one positive derivative of the scaled cutoff in
the arbitrary Leibniz sum. -/
theorem schwartzLineScaledCutoffApprox_transition_iteratedDeriv_weighted_le
    (N k n i : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    |x| ^ k *
        ((n.choose (i + 1) : Real) *
          (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖)) <=
      (n.choose (i + 1) : Real) *
        schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) *
          SchwartzMap.seminorm ℝ k (n - (i + 1)) f /
          schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hchoose_nonneg : 0 <= (n.choose (i + 1) : Real) := by
    exact_mod_cast (Nat.zero_le (n.choose (i + 1)))
  have hi_pos : 1 <= i + 1 := by
    exact Nat.succ_le_succ (Nat.zero_le i)
  have hB_nonneg :
      0 <= schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) :=
    schwartzLineScaledCutoffBaseIteratedDerivBound_nonneg (i + 1)
  have hBdiv_nonneg :
      0 <= schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) /
        schwartzLineScaledCutoffRadius N :=
    div_nonneg hB_nonneg hR_pos.le
  have habs_nonneg : 0 <= |x| := abs_nonneg x
  have hpow_nonneg : 0 <= |x| ^ k :=
    pow_nonneg habs_nonneg k
  have hderiv_bound :=
    schwartzLineScaledCutoffScalar_iteratedDeriv_norm_le
      N (i + 1) hi_pos x
  have hmul :
      ‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
          ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖ <=
        (schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) /
          schwartzLineScaledCutoffRadius N) *
          ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖ :=
    mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
  have hweighted_mul :
      |x| ^ k *
          (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖) <=
        |x| ^ k *
          ((schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) /
            schwartzLineScaledCutoffRadius N) *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖) :=
    mul_le_mul_of_nonneg_left hmul hpow_nonneg
  have hseminorm :=
    SchwartzMap.le_seminorm' ℝ k (n - (i + 1)) f x
  calc
    |x| ^ k *
        ((n.choose (i + 1) : Real) *
          (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖))
        =
      (n.choose (i + 1) : Real) *
        (|x| ^ k *
          (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖)) := by
      ring
    _ <=
      (n.choose (i + 1) : Real) *
        (|x| ^ k *
          ((schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) /
            schwartzLineScaledCutoffRadius N) *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖)) :=
      mul_le_mul_of_nonneg_left hweighted_mul hchoose_nonneg
    _ =
      (n.choose (i + 1) : Real) *
        ((schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) /
          schwartzLineScaledCutoffRadius N) *
          (|x| ^ k *
            ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖)) := by
      ring
    _ <=
      (n.choose (i + 1) : Real) *
        ((schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) /
          schwartzLineScaledCutoffRadius N) *
          SchwartzMap.seminorm ℝ k (n - (i + 1)) f) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm hBdiv_nonneg)
        hchoose_nonneg
    _ =
      (n.choose (i + 1) : Real) *
        schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) *
          SchwartzMap.seminorm ℝ k (n - (i + 1)) f /
          schwartzLineScaledCutoffRadius N := by
      ring

/-- Finite numerator controlling the arbitrary-order scaled cutoff error
Schwartz seminorm. -/
noncomputable def schwartzLineScaledCutoffApproxSeminormBoundNumerator
    (k n : Nat) (f : SchwartzLineTestFunction) : Real :=
  (∑ i ∈ Finset.range n,
      (n.choose (i + 1) : Real) *
        schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) *
          SchwartzMap.seminorm ℝ k (n - (i + 1)) f) +
    SchwartzMap.seminorm ℝ (k + 1) n f

theorem schwartzLineScaledCutoffApproxSeminormBoundNumerator_nonneg
    (k n : Nat) (f : SchwartzLineTestFunction) :
    0 <= schwartzLineScaledCutoffApproxSeminormBoundNumerator k n f := by
  dsimp [schwartzLineScaledCutoffApproxSeminormBoundNumerator]
  refine add_nonneg ?_ ?_
  · refine Finset.sum_nonneg ?_
    intro i hi
    have hchoose_nonneg : 0 <= (n.choose (i + 1) : Real) := by
      exact_mod_cast (Nat.zero_le (n.choose (i + 1)))
    have hB_nonneg :
        0 <= schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) :=
      schwartzLineScaledCutoffBaseIteratedDerivBound_nonneg (i + 1)
    have hS_nonneg :
        0 <= SchwartzMap.seminorm ℝ k (n - (i + 1)) f :=
      apply_nonneg (SchwartzMap.seminorm ℝ k (n - (i + 1))) f
    exact mul_nonneg (mul_nonneg hchoose_nonneg hB_nonneg) hS_nonneg
  · exact apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) n) f

/-- Arbitrary-order Schwartz seminorm control for the scaled cutoff error.
This replaces the derivative-by-derivative chain with one finite Leibniz sum. -/
theorem schwartzLineScaledCutoffApprox_iteratedDeriv_seminorm_le
    (N k n : Nat) (f : SchwartzLineTestFunction) :
    SchwartzMap.seminorm ℝ k n
        (schwartzLineScaledCutoffApprox N f - f) <=
      schwartzLineScaledCutoffApproxSeminormBoundNumerator k n f /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hnum_nonneg :=
    schwartzLineScaledCutoffApproxSeminormBoundNumerator_nonneg k n f
  refine SchwartzMap.seminorm_le_bound' ℝ k n
    (schwartzLineScaledCutoffApprox N f - f)
    (div_nonneg hnum_nonneg hR_pos.le) ?_
  intro x
  let Tail : Real :=
    ‖schwartzLineScaledCutoffScalar N x - 1‖ *
      ‖iteratedDeriv n (f : Real -> Complex) x‖
  let Term : Nat -> Real := fun i =>
    (n.choose (i + 1) : Real) *
      (‖iteratedDeriv (i + 1) (schwartzLineScaledCutoffScalar N) x‖ *
        ‖iteratedDeriv (n - (i + 1)) (f : Real -> Complex) x‖)
  have hpoint :
      ‖iteratedDeriv n
          (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
        Tail + ∑ i ∈ Finset.range n, Term i := by
    simpa [Tail, Term] using
      schwartzLineScaledCutoffApprox_sub_iteratedDeriv_norm_le_sum N n f x
  have habs_nonneg : 0 <= |x| := abs_nonneg x
  have hpow_nonneg : 0 <= |x| ^ k :=
    pow_nonneg habs_nonneg k
  have hweighted :
      |x| ^ k *
          ‖iteratedDeriv n
            (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
        |x| ^ k * (Tail + ∑ i ∈ Finset.range n, Term i) :=
    mul_le_mul_of_nonneg_left hpoint hpow_nonneg
  have htail_piece :
      |x| ^ k * Tail <=
        SchwartzMap.seminorm ℝ (k + 1) n f /
          schwartzLineScaledCutoffRadius N := by
    dsimp [Tail]
    exact
      schwartzLineScaledCutoffApprox_tail_iteratedDeriv_weighted_le
        N k n f x
  have htransition_piece :
      |x| ^ k * (∑ i ∈ Finset.range n, Term i) <=
        ∑ i ∈ Finset.range n,
          (n.choose (i + 1) : Real) *
            schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) *
              SchwartzMap.seminorm ℝ k (n - (i + 1)) f /
              schwartzLineScaledCutoffRadius N := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro i hi
    dsimp [Term]
    exact
      schwartzLineScaledCutoffApprox_transition_iteratedDeriv_weighted_le
        N k n i f x
  calc
    |x| ^ k *
        ‖iteratedDeriv n
          (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖
        <=
      |x| ^ k * (Tail + ∑ i ∈ Finset.range n, Term i) :=
      hweighted
    _ =
      |x| ^ k * Tail +
        |x| ^ k * (∑ i ∈ Finset.range n, Term i) := by
      ring
    _ <=
      SchwartzMap.seminorm ℝ (k + 1) n f /
          schwartzLineScaledCutoffRadius N +
        ∑ i ∈ Finset.range n,
          (n.choose (i + 1) : Real) *
            schwartzLineScaledCutoffBaseIteratedDerivBound (i + 1) *
              SchwartzMap.seminorm ℝ k (n - (i + 1)) f /
              schwartzLineScaledCutoffRadius N :=
      add_le_add htail_piece htransition_piece
    _ =
      schwartzLineScaledCutoffApproxSeminormBoundNumerator k n f /
        schwartzLineScaledCutoffRadius N := by
      dsimp [schwartzLineScaledCutoffApproxSeminormBoundNumerator]
      rw [← Finset.sum_div]
      ring

/-- The scaled cutoff approximants converge in every fixed Schwartz seminorm.
This is the finite-order endpoint: no derivative order is handled separately. -/
theorem schwartzLineScaledCutoffApprox_iteratedDeriv_schwartzSeminorm_eventually_lt
    (f : SchwartzLineTestFunction) (k n : Nat) {ε : Real} (hε : 0 < ε) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      schwartzSeminormFamily ℝ Real Complex (k, n)
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
  let S : Real := schwartzLineScaledCutoffApproxSeminormBoundNumerator k n f
  obtain ⟨N0, hN0⟩ := exists_nat_gt (S / ε)
  refine ⟨N0, ?_⟩
  intro N hN
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hN0_le_N : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  have hden_gt :
      S / ε < schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    linarith
  have hS_lt :
      S < schwartzLineScaledCutoffRadius N * ε :=
    (div_lt_iff₀ hε).1 hden_gt
  have htail_lt :
      S / schwartzLineScaledCutoffRadius N < ε := by
    rw [div_lt_iff₀ hR_pos]
    linarith
  have hle :=
    schwartzLineScaledCutoffApprox_iteratedDeriv_seminorm_le N k n f
  have hmain :
      SchwartzMap.seminorm ℝ k n
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
    exact lt_of_le_of_lt hle (by simpa [S] using htail_lt)
  simpa [schwartzSeminormFamily] using hmain

/-- The first-derivative Schwartz seminorm of the scaled cutoff error has an
explicit `1 / R` bound.  This is the first positive-derivative seminorm slice
needed for the compact-source density argument. -/
theorem schwartzLineScaledCutoffApprox_oneDeriv_seminorm_le
    (N k : Nat) (f : SchwartzLineTestFunction) :
    SchwartzMap.seminorm ℝ k 1
        (schwartzLineScaledCutoffApprox N f - f) <=
      (schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        SchwartzMap.seminorm ℝ (k + 1) 1 f) /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hC_nonneg := schwartzLineScaledCutoffBaseDerivBound_nonneg
  have hS0_nonneg :
      0 <= SchwartzMap.seminorm ℝ k 0 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ k 0) f
  have hS1_nonneg :
      0 <= SchwartzMap.seminorm ℝ (k + 1) 1 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) 1) f
  have hnum_nonneg :
      0 <= schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        SchwartzMap.seminorm ℝ (k + 1) 1 f :=
    add_nonneg (mul_nonneg hC_nonneg hS0_nonneg) hS1_nonneg
  refine SchwartzMap.seminorm_le_bound' ℝ k 1
    (schwartzLineScaledCutoffApprox N f - f)
    (div_nonneg hnum_nonneg hR_pos.le) ?_
  intro x
  have hpoint :=
    schwartzLineScaledCutoffApprox_sub_iteratedDeriv_one_norm_le N f x
  have habs_nonneg : 0 <= |x| := abs_nonneg x
  have hpow_nonneg : 0 <= |x| ^ k :=
    pow_nonneg habs_nonneg k
  have hweighted :
      |x| ^ k *
          ‖iteratedDeriv 1
            (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
        |x| ^ k *
          (‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
            ‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) :=
    mul_le_mul_of_nonneg_left hpoint hpow_nonneg
  have hseminorm0 := SchwartzMap.le_seminorm' ℝ k 0 f x
  simp only [iteratedDeriv_zero] at hseminorm0
  have hderiv_piece :
      |x| ^ k *
          (‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖) <=
        schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N := by
    have hderiv_bound :=
      schwartzLineScaledCutoffScalar_deriv_norm_le N x
    have hmul :
        ‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ <=
          (schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
    calc
      |x| ^ k *
          (‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖)
          <=
        |x| ^ k *
          ((schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N) * ‖f x‖) :=
        mul_le_mul_of_nonneg_left hmul hpow_nonneg
      _ =
        (schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N) *
          (|x| ^ k * ‖f x‖) := by
        ring
      _ <=
        (schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N) *
          SchwartzMap.seminorm ℝ k 0 f :=
        mul_le_mul_of_nonneg_left hseminorm0
          (div_nonneg hC_nonneg hR_pos.le)
      _ =
        schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N := by
        ring
  have htail_piece :
      |x| ^ k *
          (‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) <=
        SchwartzMap.seminorm ℝ (k + 1) 1 f /
          schwartzLineScaledCutoffRadius N := by
    by_cases hx : ‖x‖ <= schwartzLineScaledCutoffRadius N
    · have hχ :
          schwartzLineScaledCutoffScalar N x = 1 :=
        schwartzLineScaledCutoffScalar_eq_one_of_norm_le N hx
      have hzero :
          ‖schwartzLineScaledCutoffScalar N x - 1‖ = 0 := by
        simp [hχ]
      rw [hzero, zero_mul, mul_zero]
      exact div_nonneg hS1_nonneg hR_pos.le
    · have hxge_norm :
          schwartzLineScaledCutoffRadius N <= ‖x‖ :=
        le_of_not_ge hx
      have hxge_abs :
          schwartzLineScaledCutoffRadius N <= |x| := by
        simpa [Real.norm_eq_abs] using hxge_norm
      have hfactor :
          1 <= |x| / schwartzLineScaledCutoffRadius N := by
        rw [le_div_iff₀ hR_pos]
        simpa using hxge_abs
      have hχ :=
        schwartzLineScaledCutoffScalar_norm_sub_one_le N x
      have hχ_mul :
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖ <=
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ := by
        simpa using
          mul_le_mul_of_nonneg_right hχ
            (norm_nonneg
              (iteratedDeriv 1 (f : Real -> Complex) x))
      have htail0 :
          |x| ^ k *
              (‖schwartzLineScaledCutoffScalar N x - 1‖ *
                ‖iteratedDeriv 1 (f : Real -> Complex) x‖) <=
            |x| ^ k *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖ :=
        mul_le_mul_of_nonneg_left hχ_mul hpow_nonneg
      have hbase_nonneg :
          0 <= |x| ^ k *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ :=
        mul_nonneg hpow_nonneg (norm_nonneg _)
      have htail1 :
          |x| ^ k *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖ <=
            |x| ^ (k + 1) *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N := by
        calc
          |x| ^ k *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖
              <=
            (|x| ^ k *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) *
              (|x| / schwartzLineScaledCutoffRadius N) :=
            le_mul_of_one_le_right hbase_nonneg hfactor
          _ =
            |x| ^ (k + 1) *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N := by
            rw [pow_succ]
            ring
      have hseminorm1 := SchwartzMap.le_seminorm' ℝ (k + 1) 1 f x
      have htail2 :
          |x| ^ (k + 1) *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N <=
            SchwartzMap.seminorm ℝ (k + 1) 1 f /
              schwartzLineScaledCutoffRadius N :=
        div_le_div_of_nonneg_right hseminorm1 hR_pos.le
      exact htail0.trans (htail1.trans htail2)
  calc
    |x| ^ k *
        ‖iteratedDeriv 1
          (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖
        <=
      |x| ^ k *
        (‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖ +
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) :=
      hweighted
    _ =
      |x| ^ k *
          (‖deriv (schwartzLineScaledCutoffScalar N) x‖ * ‖f x‖) +
        |x| ^ k *
          (‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖) := by
      ring
    _ <=
      schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N +
        SchwartzMap.seminorm ℝ (k + 1) 1 f /
          schwartzLineScaledCutoffRadius N :=
      add_le_add hderiv_piece htail_piece
    _ =
      (schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        SchwartzMap.seminorm ℝ (k + 1) 1 f) /
        schwartzLineScaledCutoffRadius N := by
      ring

/-- The scaled cutoff approximants converge in every first-derivative
Schwartz seminorm. -/
theorem schwartzLineScaledCutoffApprox_oneDeriv_schwartzSeminorm_eventually_lt
    (f : SchwartzLineTestFunction) (k : Nat) {ε : Real} (hε : 0 < ε) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      schwartzSeminormFamily ℝ Real Complex (k, 1)
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
  let S : Real :=
    schwartzLineScaledCutoffBaseDerivBound *
        SchwartzMap.seminorm ℝ k 0 f +
      SchwartzMap.seminorm ℝ (k + 1) 1 f
  obtain ⟨N0, hN0⟩ := exists_nat_gt (S / ε)
  refine ⟨N0, ?_⟩
  intro N hN
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hN0_le_N : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  have hden_gt :
      S / ε < schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    linarith
  have hS_lt :
      S < schwartzLineScaledCutoffRadius N * ε :=
    (div_lt_iff₀ hε).1 hden_gt
  have htail_lt :
      S / schwartzLineScaledCutoffRadius N < ε := by
    rw [div_lt_iff₀ hR_pos]
    linarith
  have hle :=
    schwartzLineScaledCutoffApprox_oneDeriv_seminorm_le N k f
  have hmain :
      SchwartzMap.seminorm ℝ k 1
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
    exact lt_of_le_of_lt hle (by simpa [S] using htail_lt)
  simpa [schwartzSeminormFamily] using hmain

/-- The second-derivative Schwartz seminorm of the scaled cutoff error has an
explicit `1 / R` bound. -/
theorem schwartzLineScaledCutoffApprox_twoDeriv_seminorm_le
    (N k : Nat) (f : SchwartzLineTestFunction) :
    SchwartzMap.seminorm ℝ k 2
        (schwartzLineScaledCutoffApprox N f - f) <=
      (schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 1 f +
        SchwartzMap.seminorm ℝ (k + 1) 2 f) /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hC2_nonneg :=
    schwartzLineScaledCutoffBaseSecondDerivBound_nonneg
  have hC1_nonneg := schwartzLineScaledCutoffBaseDerivBound_nonneg
  have hS0_nonneg :
      0 <= SchwartzMap.seminorm ℝ k 0 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ k 0) f
  have hS1_nonneg :
      0 <= SchwartzMap.seminorm ℝ k 1 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ k 1) f
  have hS2_nonneg :
      0 <= SchwartzMap.seminorm ℝ (k + 1) 2 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) 2) f
  have hfirst_nonneg :
      0 <= (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
        SchwartzMap.seminorm ℝ k 1 f :=
    mul_nonneg (mul_nonneg (by norm_num) hC1_nonneg) hS1_nonneg
  have hnum_nonneg :
      0 <= schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 1 f +
        SchwartzMap.seminorm ℝ (k + 1) 2 f :=
    add_nonneg
      (add_nonneg (mul_nonneg hC2_nonneg hS0_nonneg) hfirst_nonneg)
      hS2_nonneg
  refine SchwartzMap.seminorm_le_bound' ℝ k 2
    (schwartzLineScaledCutoffApprox N f - f)
    (div_nonneg hnum_nonneg hR_pos.le) ?_
  intro x
  have hpoint :=
    schwartzLineScaledCutoffApprox_sub_iteratedDeriv_two_norm_le N f x
  have habs_nonneg : 0 <= |x| := abs_nonneg x
  have hpow_nonneg : 0 <= |x| ^ k :=
    pow_nonneg habs_nonneg k
  have hweighted :
      |x| ^ k *
          ‖iteratedDeriv 2
            (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
        |x| ^ k *
          (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖f x‖ +
            2 *
              (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
                ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
            ‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖) :=
    mul_le_mul_of_nonneg_left hpoint hpow_nonneg
  have hseminorm0 := SchwartzMap.le_seminorm' ℝ k 0 f x
  simp only [iteratedDeriv_zero] at hseminorm0
  have hseminorm1 := SchwartzMap.le_seminorm' ℝ k 1 f x
  have hsecond_piece :
      |x| ^ k *
          (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖) <=
        schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N := by
    have hderiv_bound :=
      schwartzLineScaledCutoffScalar_iteratedDeriv_two_norm_le N x
    have hmul :
        ‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖ <=
          (schwartzLineScaledCutoffBaseSecondDerivBound /
            schwartzLineScaledCutoffRadius N) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
    calc
      |x| ^ k *
          (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖)
          <=
        |x| ^ k *
          ((schwartzLineScaledCutoffBaseSecondDerivBound /
            schwartzLineScaledCutoffRadius N) * ‖f x‖) :=
        mul_le_mul_of_nonneg_left hmul hpow_nonneg
      _ =
        (schwartzLineScaledCutoffBaseSecondDerivBound /
            schwartzLineScaledCutoffRadius N) *
          (|x| ^ k * ‖f x‖) := by
        ring
      _ <=
        (schwartzLineScaledCutoffBaseSecondDerivBound /
            schwartzLineScaledCutoffRadius N) *
          SchwartzMap.seminorm ℝ k 0 f :=
        mul_le_mul_of_nonneg_left hseminorm0
          (div_nonneg hC2_nonneg hR_pos.le)
      _ =
        schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N := by
        ring
  have hfirst_piece :
      |x| ^ k *
          (2 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)) <=
        (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 1 f /
          schwartzLineScaledCutoffRadius N := by
    have hderiv_bound :
        ‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ <=
          schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N := by
      simpa [iteratedDeriv_one] using
        schwartzLineScaledCutoffScalar_deriv_norm_le N x
    have hmul :
        ‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ <=
          (schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N) *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ :=
      mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
    have hbase :
        |x| ^ k *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) <=
          schwartzLineScaledCutoffBaseDerivBound *
            SchwartzMap.seminorm ℝ k 1 f /
            schwartzLineScaledCutoffRadius N := by
      calc
        |x| ^ k *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)
            <=
          |x| ^ k *
            ((schwartzLineScaledCutoffBaseDerivBound /
              schwartzLineScaledCutoffRadius N) *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) :=
          mul_le_mul_of_nonneg_left hmul hpow_nonneg
        _ =
          (schwartzLineScaledCutoffBaseDerivBound /
              schwartzLineScaledCutoffRadius N) *
            (|x| ^ k *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) := by
          ring
        _ <=
          (schwartzLineScaledCutoffBaseDerivBound /
              schwartzLineScaledCutoffRadius N) *
            SchwartzMap.seminorm ℝ k 1 f :=
          mul_le_mul_of_nonneg_left hseminorm1
            (div_nonneg hC1_nonneg hR_pos.le)
        _ =
          schwartzLineScaledCutoffBaseDerivBound *
            SchwartzMap.seminorm ℝ k 1 f /
            schwartzLineScaledCutoffRadius N := by
          ring
    calc
      |x| ^ k *
          (2 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖))
          =
        (2 : Real) *
          (|x| ^ k *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)) := by
        ring
      _ <=
        (2 : Real) *
          (schwartzLineScaledCutoffBaseDerivBound *
            SchwartzMap.seminorm ℝ k 1 f /
            schwartzLineScaledCutoffRadius N) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ =
        (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 1 f /
          schwartzLineScaledCutoffRadius N := by
        ring
  have htail_piece :
      |x| ^ k *
          (‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖) <=
        SchwartzMap.seminorm ℝ (k + 1) 2 f /
          schwartzLineScaledCutoffRadius N := by
    by_cases hx : ‖x‖ <= schwartzLineScaledCutoffRadius N
    · have hχ :
          schwartzLineScaledCutoffScalar N x = 1 :=
        schwartzLineScaledCutoffScalar_eq_one_of_norm_le N hx
      have hzero :
          ‖schwartzLineScaledCutoffScalar N x - 1‖ = 0 := by
        simp [hχ]
      rw [hzero, zero_mul, mul_zero]
      exact div_nonneg hS2_nonneg hR_pos.le
    · have hxge_norm :
          schwartzLineScaledCutoffRadius N <= ‖x‖ :=
        le_of_not_ge hx
      have hxge_abs :
          schwartzLineScaledCutoffRadius N <= |x| := by
        simpa [Real.norm_eq_abs] using hxge_norm
      have hfactor :
          1 <= |x| / schwartzLineScaledCutoffRadius N := by
        rw [le_div_iff₀ hR_pos]
        simpa using hxge_abs
      have hχ :=
        schwartzLineScaledCutoffScalar_norm_sub_one_le N x
      have hχ_mul :
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖ <=
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖ := by
        simpa using
          mul_le_mul_of_nonneg_right hχ
            (norm_nonneg
              (iteratedDeriv 2 (f : Real -> Complex) x))
      have htail0 :
          |x| ^ k *
              (‖schwartzLineScaledCutoffScalar N x - 1‖ *
                ‖iteratedDeriv 2 (f : Real -> Complex) x‖) <=
            |x| ^ k *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖ :=
        mul_le_mul_of_nonneg_left hχ_mul hpow_nonneg
      have hbase_nonneg :
          0 <= |x| ^ k *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖ :=
        mul_nonneg hpow_nonneg (norm_nonneg _)
      have htail1 :
          |x| ^ k *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖ <=
            |x| ^ (k + 1) *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N := by
        calc
          |x| ^ k *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖
              <=
            (|x| ^ k *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖) *
              (|x| / schwartzLineScaledCutoffRadius N) :=
            le_mul_of_one_le_right hbase_nonneg hfactor
          _ =
            |x| ^ (k + 1) *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N := by
            rw [pow_succ]
            ring
      have hseminorm2 := SchwartzMap.le_seminorm' ℝ (k + 1) 2 f x
      have htail2 :
          |x| ^ (k + 1) *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N <=
            SchwartzMap.seminorm ℝ (k + 1) 2 f /
              schwartzLineScaledCutoffRadius N :=
        div_le_div_of_nonneg_right hseminorm2 hR_pos.le
      exact htail0.trans (htail1.trans htail2)
  calc
    |x| ^ k *
        ‖iteratedDeriv 2
          (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖
        <=
      |x| ^ k *
        (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖ +
          2 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖) :=
      hweighted
    _ =
      |x| ^ k *
          (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖) +
        |x| ^ k *
          (2 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)) +
        |x| ^ k *
          (‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖) := by
      ring
    _ <=
      schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N +
        (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 1 f /
          schwartzLineScaledCutoffRadius N +
        SchwartzMap.seminorm ℝ (k + 1) 2 f /
          schwartzLineScaledCutoffRadius N :=
      add_le_add (add_le_add hsecond_piece hfirst_piece) htail_piece
    _ =
      (schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 1 f +
        SchwartzMap.seminorm ℝ (k + 1) 2 f) /
        schwartzLineScaledCutoffRadius N := by
      ring

/-- The scaled cutoff approximants converge in every second-derivative
Schwartz seminorm. -/
theorem schwartzLineScaledCutoffApprox_twoDeriv_schwartzSeminorm_eventually_lt
    (f : SchwartzLineTestFunction) (k : Nat) {ε : Real} (hε : 0 < ε) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      schwartzSeminormFamily ℝ Real Complex (k, 2)
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
  let S : Real :=
    schwartzLineScaledCutoffBaseSecondDerivBound *
        SchwartzMap.seminorm ℝ k 0 f +
      (2 : Real) * schwartzLineScaledCutoffBaseDerivBound *
        SchwartzMap.seminorm ℝ k 1 f +
      SchwartzMap.seminorm ℝ (k + 1) 2 f
  obtain ⟨N0, hN0⟩ := exists_nat_gt (S / ε)
  refine ⟨N0, ?_⟩
  intro N hN
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hN0_le_N : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  have hden_gt :
      S / ε < schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    linarith
  have hS_lt :
      S < schwartzLineScaledCutoffRadius N * ε :=
    (div_lt_iff₀ hε).1 hden_gt
  have htail_lt :
      S / schwartzLineScaledCutoffRadius N < ε := by
    rw [div_lt_iff₀ hR_pos]
    linarith
  have hle :=
    schwartzLineScaledCutoffApprox_twoDeriv_seminorm_le N k f
  have hmain :
      SchwartzMap.seminorm ℝ k 2
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
    exact lt_of_le_of_lt hle (by simpa [S] using htail_lt)
  simpa [schwartzSeminormFamily] using hmain

/-- The third-derivative Schwartz seminorm of the scaled cutoff error has an
explicit `1 / R` bound. -/
theorem schwartzLineScaledCutoffApprox_threeDeriv_seminorm_le
    (N k : Nat) (f : SchwartzLineTestFunction) :
    SchwartzMap.seminorm ℝ k 3
        (schwartzLineScaledCutoffApprox N f - f) <=
      (schwartzLineScaledCutoffBaseThirdDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 1 f +
        (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 2 f +
        SchwartzMap.seminorm ℝ (k + 1) 3 f) /
        schwartzLineScaledCutoffRadius N := by
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hC3_nonneg :=
    schwartzLineScaledCutoffBaseThirdDerivBound_nonneg
  have hC2_nonneg :=
    schwartzLineScaledCutoffBaseSecondDerivBound_nonneg
  have hC1_nonneg := schwartzLineScaledCutoffBaseDerivBound_nonneg
  have hS0_nonneg :
      0 <= SchwartzMap.seminorm ℝ k 0 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ k 0) f
  have hS1_nonneg :
      0 <= SchwartzMap.seminorm ℝ k 1 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ k 1) f
  have hS2_nonneg :
      0 <= SchwartzMap.seminorm ℝ k 2 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ k 2) f
  have hS3_nonneg :
      0 <= SchwartzMap.seminorm ℝ (k + 1) 3 f :=
    apply_nonneg (SchwartzMap.seminorm ℝ (k + 1) 3) f
  have hsecond_nonneg :
      0 <= (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
        SchwartzMap.seminorm ℝ k 1 f :=
    mul_nonneg (mul_nonneg (by norm_num) hC2_nonneg) hS1_nonneg
  have hfirst_nonneg :
      0 <= (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
        SchwartzMap.seminorm ℝ k 2 f :=
    mul_nonneg (mul_nonneg (by norm_num) hC1_nonneg) hS2_nonneg
  have hnum_nonneg :
      0 <= schwartzLineScaledCutoffBaseThirdDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 1 f +
        (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 2 f +
        SchwartzMap.seminorm ℝ (k + 1) 3 f :=
    add_nonneg
      (add_nonneg
        (add_nonneg (mul_nonneg hC3_nonneg hS0_nonneg) hsecond_nonneg)
        hfirst_nonneg)
      hS3_nonneg
  refine SchwartzMap.seminorm_le_bound' ℝ k 3
    (schwartzLineScaledCutoffApprox N f - f)
    (div_nonneg hnum_nonneg hR_pos.le) ?_
  intro x
  have hpoint :=
    schwartzLineScaledCutoffApprox_sub_iteratedDeriv_three_norm_le N f x
  have habs_nonneg : 0 <= |x| := abs_nonneg x
  have hpow_nonneg : 0 <= |x| ^ k :=
    pow_nonneg habs_nonneg k
  have hweighted :
      |x| ^ k *
          ‖iteratedDeriv 3
            (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖ <=
        |x| ^ k *
          (‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖f x‖ +
            3 *
              (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
                ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
            3 *
              (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
                ‖iteratedDeriv 2 (f : Real -> Complex) x‖) +
            ‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖) :=
    mul_le_mul_of_nonneg_left hpoint hpow_nonneg
  have hseminorm0 := SchwartzMap.le_seminorm' ℝ k 0 f x
  simp only [iteratedDeriv_zero] at hseminorm0
  have hseminorm1 := SchwartzMap.le_seminorm' ℝ k 1 f x
  have hseminorm2 := SchwartzMap.le_seminorm' ℝ k 2 f x
  have hthird_piece :
      |x| ^ k *
          (‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖) <=
        schwartzLineScaledCutoffBaseThirdDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N := by
    have hderiv_bound :=
      schwartzLineScaledCutoffScalar_iteratedDeriv_three_norm_le N x
    have hmul :
        ‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖ <=
          (schwartzLineScaledCutoffBaseThirdDerivBound /
            schwartzLineScaledCutoffRadius N) * ‖f x‖ :=
      mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
    calc
      |x| ^ k *
          (‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖)
          <=
        |x| ^ k *
          ((schwartzLineScaledCutoffBaseThirdDerivBound /
            schwartzLineScaledCutoffRadius N) * ‖f x‖) :=
        mul_le_mul_of_nonneg_left hmul hpow_nonneg
      _ =
        (schwartzLineScaledCutoffBaseThirdDerivBound /
            schwartzLineScaledCutoffRadius N) *
          (|x| ^ k * ‖f x‖) := by
        ring
      _ <=
        (schwartzLineScaledCutoffBaseThirdDerivBound /
            schwartzLineScaledCutoffRadius N) *
          SchwartzMap.seminorm ℝ k 0 f :=
        mul_le_mul_of_nonneg_left hseminorm0
          (div_nonneg hC3_nonneg hR_pos.le)
      _ =
        schwartzLineScaledCutoffBaseThirdDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N := by
        ring
  have hsecond_piece :
      |x| ^ k *
          (3 *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)) <=
        (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 1 f /
          schwartzLineScaledCutoffRadius N := by
    have hderiv_bound :=
      schwartzLineScaledCutoffScalar_iteratedDeriv_two_norm_le N x
    have hmul :
        ‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ <=
          (schwartzLineScaledCutoffBaseSecondDerivBound /
            schwartzLineScaledCutoffRadius N) *
            ‖iteratedDeriv 1 (f : Real -> Complex) x‖ :=
      mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
    have hbase :
        |x| ^ k *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) <=
          schwartzLineScaledCutoffBaseSecondDerivBound *
            SchwartzMap.seminorm ℝ k 1 f /
            schwartzLineScaledCutoffRadius N := by
      calc
        |x| ^ k *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)
            <=
          |x| ^ k *
            ((schwartzLineScaledCutoffBaseSecondDerivBound /
              schwartzLineScaledCutoffRadius N) *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) :=
          mul_le_mul_of_nonneg_left hmul hpow_nonneg
        _ =
          (schwartzLineScaledCutoffBaseSecondDerivBound /
              schwartzLineScaledCutoffRadius N) *
            (|x| ^ k *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) := by
          ring
        _ <=
          (schwartzLineScaledCutoffBaseSecondDerivBound /
              schwartzLineScaledCutoffRadius N) *
            SchwartzMap.seminorm ℝ k 1 f :=
          mul_le_mul_of_nonneg_left hseminorm1
            (div_nonneg hC2_nonneg hR_pos.le)
        _ =
          schwartzLineScaledCutoffBaseSecondDerivBound *
            SchwartzMap.seminorm ℝ k 1 f /
            schwartzLineScaledCutoffRadius N := by
          ring
    calc
      |x| ^ k *
          (3 *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖))
          =
        (3 : Real) *
          (|x| ^ k *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)) := by
        ring
      _ <=
        (3 : Real) *
          (schwartzLineScaledCutoffBaseSecondDerivBound *
            SchwartzMap.seminorm ℝ k 1 f /
            schwartzLineScaledCutoffRadius N) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ =
        (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 1 f /
          schwartzLineScaledCutoffRadius N := by
        ring
  have hfirst_piece :
      |x| ^ k *
          (3 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖)) <=
        (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 2 f /
          schwartzLineScaledCutoffRadius N := by
    have hderiv_bound :
        ‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ <=
          schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N := by
      simpa [iteratedDeriv_one] using
        schwartzLineScaledCutoffScalar_deriv_norm_le N x
    have hmul :
        ‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖ <=
          (schwartzLineScaledCutoffBaseDerivBound /
            schwartzLineScaledCutoffRadius N) *
            ‖iteratedDeriv 2 (f : Real -> Complex) x‖ :=
      mul_le_mul_of_nonneg_right hderiv_bound (norm_nonneg _)
    have hbase :
        |x| ^ k *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖) <=
          schwartzLineScaledCutoffBaseDerivBound *
            SchwartzMap.seminorm ℝ k 2 f /
            schwartzLineScaledCutoffRadius N := by
      calc
        |x| ^ k *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖)
            <=
          |x| ^ k *
            ((schwartzLineScaledCutoffBaseDerivBound /
              schwartzLineScaledCutoffRadius N) *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖) :=
          mul_le_mul_of_nonneg_left hmul hpow_nonneg
        _ =
          (schwartzLineScaledCutoffBaseDerivBound /
              schwartzLineScaledCutoffRadius N) *
            (|x| ^ k *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖) := by
          ring
        _ <=
          (schwartzLineScaledCutoffBaseDerivBound /
              schwartzLineScaledCutoffRadius N) *
            SchwartzMap.seminorm ℝ k 2 f :=
          mul_le_mul_of_nonneg_left hseminorm2
            (div_nonneg hC1_nonneg hR_pos.le)
        _ =
          schwartzLineScaledCutoffBaseDerivBound *
            SchwartzMap.seminorm ℝ k 2 f /
            schwartzLineScaledCutoffRadius N := by
          ring
    calc
      |x| ^ k *
          (3 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖))
          =
        (3 : Real) *
          (|x| ^ k *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖)) := by
        ring
      _ <=
        (3 : Real) *
          (schwartzLineScaledCutoffBaseDerivBound *
            SchwartzMap.seminorm ℝ k 2 f /
            schwartzLineScaledCutoffRadius N) :=
        mul_le_mul_of_nonneg_left hbase (by norm_num)
      _ =
        (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 2 f /
          schwartzLineScaledCutoffRadius N := by
        ring
  have htail_piece :
      |x| ^ k *
          (‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 3 (f : Real -> Complex) x‖) <=
        SchwartzMap.seminorm ℝ (k + 1) 3 f /
          schwartzLineScaledCutoffRadius N := by
    by_cases hx : ‖x‖ <= schwartzLineScaledCutoffRadius N
    · have hχ :
          schwartzLineScaledCutoffScalar N x = 1 :=
        schwartzLineScaledCutoffScalar_eq_one_of_norm_le N hx
      have hzero :
          ‖schwartzLineScaledCutoffScalar N x - 1‖ = 0 := by
        simp [hχ]
      rw [hzero, zero_mul, mul_zero]
      exact div_nonneg hS3_nonneg hR_pos.le
    · have hxge_norm :
          schwartzLineScaledCutoffRadius N <= ‖x‖ :=
        le_of_not_ge hx
      have hxge_abs :
          schwartzLineScaledCutoffRadius N <= |x| := by
        simpa [Real.norm_eq_abs] using hxge_norm
      have hfactor :
          1 <= |x| / schwartzLineScaledCutoffRadius N := by
        rw [le_div_iff₀ hR_pos]
        simpa using hxge_abs
      have hχ :=
        schwartzLineScaledCutoffScalar_norm_sub_one_le N x
      have hχ_mul :
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖ <=
            ‖iteratedDeriv 3 (f : Real -> Complex) x‖ := by
        simpa using
          mul_le_mul_of_nonneg_right hχ
            (norm_nonneg
              (iteratedDeriv 3 (f : Real -> Complex) x))
      have htail0 :
          |x| ^ k *
              (‖schwartzLineScaledCutoffScalar N x - 1‖ *
                ‖iteratedDeriv 3 (f : Real -> Complex) x‖) <=
            |x| ^ k *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖ :=
        mul_le_mul_of_nonneg_left hχ_mul hpow_nonneg
      have hbase_nonneg :
          0 <= |x| ^ k *
            ‖iteratedDeriv 3 (f : Real -> Complex) x‖ :=
        mul_nonneg hpow_nonneg (norm_nonneg _)
      have htail1 :
          |x| ^ k *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖ <=
            |x| ^ (k + 1) *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N := by
        calc
          |x| ^ k *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖
              <=
            (|x| ^ k *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖) *
              (|x| / schwartzLineScaledCutoffRadius N) :=
            le_mul_of_one_le_right hbase_nonneg hfactor
          _ =
            |x| ^ (k + 1) *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N := by
            rw [pow_succ]
            ring
      have hseminorm3 := SchwartzMap.le_seminorm' ℝ (k + 1) 3 f x
      have htail2 :
          |x| ^ (k + 1) *
              ‖iteratedDeriv 3 (f : Real -> Complex) x‖ /
              schwartzLineScaledCutoffRadius N <=
            SchwartzMap.seminorm ℝ (k + 1) 3 f /
              schwartzLineScaledCutoffRadius N :=
        div_le_div_of_nonneg_right hseminorm3 hR_pos.le
      exact htail0.trans (htail1.trans htail2)
  calc
    |x| ^ k *
        ‖iteratedDeriv 3
          (schwartzLineScaledCutoffApprox N f - f : Real -> Complex) x‖
        <=
      |x| ^ k *
        (‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖ +
          3 *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖) +
          3 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖) +
          ‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 3 (f : Real -> Complex) x‖) :=
      hweighted
    _ =
      |x| ^ k *
          (‖iteratedDeriv 3 (schwartzLineScaledCutoffScalar N) x‖ *
            ‖f x‖) +
        |x| ^ k *
          (3 *
            (‖iteratedDeriv 2 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 1 (f : Real -> Complex) x‖)) +
        |x| ^ k *
          (3 *
            (‖iteratedDeriv 1 (schwartzLineScaledCutoffScalar N) x‖ *
              ‖iteratedDeriv 2 (f : Real -> Complex) x‖)) +
        |x| ^ k *
          (‖schwartzLineScaledCutoffScalar N x - 1‖ *
            ‖iteratedDeriv 3 (f : Real -> Complex) x‖) := by
      ring
    _ <=
      schwartzLineScaledCutoffBaseThirdDerivBound *
          SchwartzMap.seminorm ℝ k 0 f /
          schwartzLineScaledCutoffRadius N +
        (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 1 f /
          schwartzLineScaledCutoffRadius N +
        (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 2 f /
          schwartzLineScaledCutoffRadius N +
        SchwartzMap.seminorm ℝ (k + 1) 3 f /
          schwartzLineScaledCutoffRadius N :=
      add_le_add
        (add_le_add (add_le_add hthird_piece hsecond_piece) hfirst_piece)
        htail_piece
    _ =
      (schwartzLineScaledCutoffBaseThirdDerivBound *
          SchwartzMap.seminorm ℝ k 0 f +
        (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
          SchwartzMap.seminorm ℝ k 1 f +
        (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
          SchwartzMap.seminorm ℝ k 2 f +
        SchwartzMap.seminorm ℝ (k + 1) 3 f) /
        schwartzLineScaledCutoffRadius N := by
      ring

/-- The scaled cutoff approximants converge in every third-derivative
Schwartz seminorm. -/
theorem schwartzLineScaledCutoffApprox_threeDeriv_schwartzSeminorm_eventually_lt
    (f : SchwartzLineTestFunction) (k : Nat) {ε : Real} (hε : 0 < ε) :
    exists N0 : Nat, forall N : Nat, N0 <= N ->
      schwartzSeminormFamily ℝ Real Complex (k, 3)
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
  let S : Real :=
    schwartzLineScaledCutoffBaseThirdDerivBound *
        SchwartzMap.seminorm ℝ k 0 f +
      (3 : Real) * schwartzLineScaledCutoffBaseSecondDerivBound *
        SchwartzMap.seminorm ℝ k 1 f +
      (3 : Real) * schwartzLineScaledCutoffBaseDerivBound *
        SchwartzMap.seminorm ℝ k 2 f +
      SchwartzMap.seminorm ℝ (k + 1) 3 f
  obtain ⟨N0, hN0⟩ := exists_nat_gt (S / ε)
  refine ⟨N0, ?_⟩
  intro N hN
  have hR_pos := schwartzLineScaledCutoffRadius_pos N
  have hN0_le_N : (N0 : Real) <= (N : Real) := by
    exact_mod_cast hN
  have hden_gt :
      S / ε < schwartzLineScaledCutoffRadius N := by
    dsimp [schwartzLineScaledCutoffRadius]
    linarith
  have hS_lt :
      S < schwartzLineScaledCutoffRadius N * ε :=
    (div_lt_iff₀ hε).1 hden_gt
  have htail_lt :
      S / schwartzLineScaledCutoffRadius N < ε := by
    rw [div_lt_iff₀ hR_pos]
    linarith
  have hle :=
    schwartzLineScaledCutoffApprox_threeDeriv_seminorm_le N k f
  have hmain :
      SchwartzMap.seminorm ℝ k 3
        (schwartzLineScaledCutoffApprox N f - f) < ε := by
    exact lt_of_le_of_lt hle (by simpa [S] using htail_lt)
  simpa [schwartzSeminormFamily] using hmain

/-- The cutoff approximant is supported inside its outer closed ball. -/
theorem schwartzLineCutoffApprox_tsupport_subset_closedBall
    (N : Nat) (f : SchwartzLineTestFunction) :
    tsupport (schwartzLineCutoffApprox N f) ⊆
      Metric.closedBall (0 : Real) ((N : Real) + 2) := by
  rw [tsupport]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  by_contra hxball
  have hxnorm : (N : Real) + 2 <= ‖x‖ := by
    have hlt : (N : Real) + 2 < dist x (0 : Real) := by
      simpa [Metric.mem_closedBall] using hxball
    have hdist : dist x (0 : Real) = ‖x‖ := by
      simp
    linarith
  exact hx (schwartzLineCutoffApprox_apply_eq_zero_of_radius_le_norm N f hxnorm)

/-- Each concrete cutoff approximant is compactly supported. -/
theorem schwartzLineCutoffApprox_hasCompactSupport
    (N : Nat) (f : SchwartzLineTestFunction) :
    HasCompactSupport (schwartzLineCutoffApprox N f) := by
  have hprod :
      HasCompactSupport
        (schwartzLineCutoffScalar N * (f : Real -> Complex)) :=
    (schwartzLineCutoffScalar_hasCompactSupport N).mul_right
  convert hprod using 1
  funext x
  simp [Pi.mul_apply]

/-- The concrete cutoff approximant as an actual compact smooth source test. -/
noncomputable def schwartzLineCutoffSourceApprox
    (N : Nat) (f : SchwartzLineTestFunction) :
    compactlySupportedSmoothLineSource.SourceTestFunction :=
  compactlySupportedSchwartzLineToSource (schwartzLineCutoffApprox N f)
    (schwartzLineCutoffApprox_hasCompactSupport N f)

@[simp]
theorem schwartzLineCutoffSourceApprox_toSchwartz
    (N : Nat) (f : SchwartzLineTestFunction) :
    compactlySupportedSmoothLineSource.toSchwartz
        (schwartzLineCutoffSourceApprox N f) =
      schwartzLineCutoffApprox N f := by
  simp [schwartzLineCutoffSourceApprox]

/-- Every concrete cutoff approximant lies in the admissible image of the
compact smooth source class. -/
theorem schwartzLineCutoffApprox_mem_compactlySupportedSmoothLineSource_image
    (N : Nat) (f : SchwartzLineTestFunction) :
    schwartzLineCutoffApprox N f ∈
      guinandWeilAdmissibleSchwartzImage
        compactlySupportedSmoothLineSource :=
  compactlySupportedSchwartzLine_mem_compactlySupportedSmoothLineSource_image
    (schwartzLineCutoffApprox N f)
    (schwartzLineCutoffApprox_hasCompactSupport N f)

/-- Each scaled cutoff approximant is compactly supported. -/
theorem schwartzLineScaledCutoffApprox_hasCompactSupport
    (N : Nat) (f : SchwartzLineTestFunction) :
    HasCompactSupport (schwartzLineScaledCutoffApprox N f) := by
  have hprod :
      HasCompactSupport
        (schwartzLineScaledCutoffScalar N * (f : Real -> Complex)) :=
    (schwartzLineScaledCutoffScalar_hasCompactSupport N).mul_right
  convert hprod using 1
  funext x
  simp [Pi.mul_apply]

/-- The scaled cutoff approximant as an actual compact smooth source test. -/
noncomputable def schwartzLineScaledCutoffSourceApprox
    (N : Nat) (f : SchwartzLineTestFunction) :
    compactlySupportedSmoothLineSource.SourceTestFunction :=
  compactlySupportedSchwartzLineToSource (schwartzLineScaledCutoffApprox N f)
    (schwartzLineScaledCutoffApprox_hasCompactSupport N f)

@[simp]
theorem schwartzLineScaledCutoffSourceApprox_toSchwartz
    (N : Nat) (f : SchwartzLineTestFunction) :
    compactlySupportedSmoothLineSource.toSchwartz
        (schwartzLineScaledCutoffSourceApprox N f) =
      schwartzLineScaledCutoffApprox N f := by
  simp [schwartzLineScaledCutoffSourceApprox]

/-- Every scaled cutoff approximant lies in the admissible image of the compact
smooth source class. -/
theorem schwartzLineScaledCutoffApprox_mem_compactlySupportedSmoothLineSource_image
    (N : Nat) (f : SchwartzLineTestFunction) :
    schwartzLineScaledCutoffApprox N f ∈
      guinandWeilAdmissibleSchwartzImage
        compactlySupportedSmoothLineSource :=
  compactlySupportedSchwartzLine_mem_compactlySupportedSmoothLineSource_image
    (schwartzLineScaledCutoffApprox N f)
    (schwartzLineScaledCutoffApprox_hasCompactSupport N f)

/--
Schwartz-seminorm approximation criterion for the concrete compactly supported
smooth source.

The remaining analytic density proof can now be stated in the native seminorms
of the project Schwartz topology: for every target Schwartz test and every
Schwartz seminorm, produce compactly supported smooth source tests whose image
eventually lies within any requested seminorm error.  This theorem then closes
the actual source-image density field.
-/
theorem compactlySupportedSmoothLineSource_dense_of_schwartzSeminorm_approx
    (approx :
      SchwartzLineTestFunction ->
        Nat -> compactlySupportedSmoothLineSource.SourceTestFunction)
    (happrox :
      forall (f : SchwartzLineTestFunction) (m : Nat × Nat) (ε : Real),
        0 < ε ->
          exists N0 : Nat, forall N : Nat, N0 <= N ->
            schwartzSeminormFamily ℝ Real Complex m
              (compactlySupportedSmoothLineSource.toSchwartz
                (approx f N) - f) < ε) :
    closure
        (guinandWeilAdmissibleSchwartzImage
          compactlySupportedSmoothLineSource) =
      Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro f
  have htendsto :
      Filter.Tendsto
        (fun N : Nat =>
          compactlySupportedSmoothLineSource.toSchwartz
            (approx f N))
        Filter.atTop (nhds f) := by
    rw [(schwartz_withSeminorms ℝ Real Complex).tendsto_nhds_atTop
      (fun N : Nat =>
        compactlySupportedSmoothLineSource.toSchwartz
          (approx f N)) f]
    intro m ε hε
    exact happrox f m ε hε
  refine mem_closure_of_tendsto htendsto ?_
  exact Filter.Eventually.of_forall fun N =>
    ⟨approx f N, by trivial, rfl⟩

/-- The concrete compact smooth source image is dense in the project Schwartz
line space. -/
theorem compactlySupportedSmoothLineSource_dense :
    closure
        (guinandWeilAdmissibleSchwartzImage
          compactlySupportedSmoothLineSource) =
      Set.univ := by
  refine
    compactlySupportedSmoothLineSource_dense_of_schwartzSeminorm_approx
      (fun f N => schwartzLineScaledCutoffSourceApprox N f) ?_
  intro f m ε hε
  rcases m with ⟨k, n⟩
  simpa using
    schwartzLineScaledCutoffApprox_iteratedDeriv_schwartzSeminorm_eventually_lt
      f k n hε

end RiemannHypothesisProject
