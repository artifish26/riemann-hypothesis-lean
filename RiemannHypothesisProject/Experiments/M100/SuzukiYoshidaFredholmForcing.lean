import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceNormConsumer

/-!
# M100-DF6F projected Fredholm forcing

This module isolates the source-dual estimates needed for the two projected
Fredholm right-hand sides in the Suzuki--Yoshida route.  The first bridge
reduces a full closed-source estimate to an integration-by-parts estimate on
compactly supported smooth primitives.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiFredholmForcingCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- On a smooth differential, the inverse-Neumann source seminorm is exactly
the ambient `L2` norm of its compactly supported primitive. -/
theorem suzukiSourceKSeminorm_smoothCoreDifferential_eq_norm
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    suzukiSourceKSeminorm a
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) =
      ‖suzukiSmoothCoreToL2 v‖ := by
  rw [suzukiSourceKSeminorm]
  unfold suzukiSmoothCoreDifferentialZeroMeanL2
  rw [inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq ha v]
  simp only [Complex.ofReal_re]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- A source-dual estimate verified on compactly supported smooth
differentials extends to the entire closed zero-mean source space.  This is
the density bridge used for the concrete Fredholm forcings. -/
theorem suzukiSourceKDualBoundAt_of_smoothCore
    {a C : Real} (ha : 0 < a)
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hcore : ∀ v : SuzukiSmoothCore a,
      ‖inner Complex f (suzukiSmoothCoreDifferentialZeroMeanL2 ha v)‖ ≤
        C * ‖suzukiSmoothCoreToL2 v‖) :
    SuzukiSourceKDualBoundAt a f C := by
  intro u
  let p : SuzukiFiniteIntervalZeroMeanL2 a → Prop := fun w =>
    ‖inner Complex f w‖ ≤ C * suzukiSourceKSeminorm a w
  apply DenseRange.induction_on (p := p)
    (suzukiSmoothDifferentialCoreDenseAt a ha) u
  · apply isClosed_le
    · fun_prop
    · unfold suzukiSourceKSeminorm
      fun_prop
  · intro v
    dsimp only [p]
    rw [suzukiSourceKSeminorm_smoothCoreDifferential_eq_norm ha v]
    exact hcore v

/-- The real exponential `exp (c x)` as a continuous function on Suzuki's
finite interval. -/
def suzukiFredholmExponentialContinuous
    (a c : Real) : C(SuzukiFiniteInterval a, Complex) :=
  ⟨fun x => (Real.exp (c * x.1) : Complex), by fun_prop⟩

@[simp]
theorem suzukiFredholmExponentialContinuous_apply
    (a c : Real) (x : SuzukiFiniteInterval a) :
    suzukiFredholmExponentialContinuous a c x =
      (Real.exp (c * x.1) : Complex) :=
  rfl

/-- Orthogonal projection of the exponential forcing onto the closed
zero-mean source space. -/
def suzukiFredholmExponentialForcing
    (a c : Real) : SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalContinuousToZeroMeanL2 a
    (suzukiFredholmExponentialContinuous a c)

/-- The same exponential, truncated to the source interval and extended by
zero on the real line. -/
def suzukiFredholmExponentialFunction
    (a c x : Real) : Complex :=
  Set.indicator (Set.Icc (-a) a)
    (fun y => (Real.exp (c * y) : Complex)) x

theorem suzukiFredholmExponentialFunction_memLp
    {a : Real} (_ha : 0 < a) (c : Real) :
    MemLp (suzukiFredholmExponentialFunction a c)
      (2 : ENNReal) (volume : Measure Real) := by
  unfold suzukiFredholmExponentialFunction
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  haveI : IsFiniteMeasure
      ((volume : Measure Real).restrict (Set.Icc (-a) a)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_Icc_lt_top : volume (Set.Icc (-a) a) < ⊤)⟩
  refine MemLp.of_bound (C := Real.exp (|c| * a)) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    c * x ≤ |c * x| := le_abs_self _
    _ = |c| * |x| := abs_mul c x
    _ ≤ |c| * a := by
      exact mul_le_mul_of_nonneg_left ((abs_le).2 hx) (abs_nonneg c)

/-- Global `L2` representative of the truncated exponential. -/
def suzukiFredholmExponentialL2
    {a : Real} (ha : 0 < a) (c : Real) : SuzukiL2 :=
  (suzukiFredholmExponentialFunction_memLp ha c).toLp
    (suzukiFredholmExponentialFunction a c)

theorem suzukiFredholmExponentialL2_coeFn
    {a : Real} (ha : 0 < a) (c : Real) :
    (suzukiFredholmExponentialL2 ha c : Real → Complex) =ᵐ[volume]
      suzukiFredholmExponentialFunction a c :=
  (suzukiFredholmExponentialFunction_memLp ha c).coeFn_toLp

/-- Projecting the continuous exponential does not alter its pairing against
a zero-mean source vector. -/
theorem inner_suzukiFredholmExponentialForcing
    (a c : Real) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    inner Complex (suzukiFredholmExponentialForcing a c) u =
      inner Complex
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmExponentialContinuous a c))
        (u : SuzukiFiniteIntervalL2 a) := by
  change inner Complex
      ((SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiFredholmExponentialContinuous a c))) u = _
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right u _

/-- The global pairing with a smooth primitive is the finite-interval
exponential integral. -/
theorem inner_suzukiFredholmExponentialL2_smoothCoreToL2
    {a : Real} (ha : 0 < a) (c : Real) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiFredholmExponentialL2 ha c)
        (suzukiSmoothCoreToL2 v) =
      ∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) * v.1 x := by
  rw [MeasureTheory.L2.inner_def]
  have hExp := suzukiFredholmExponentialL2_coeFn ha c
  have hV : (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume]
      fun x => v.1 x := by
    simpa only [suzukiSmoothCoreToL2] using
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  have hpair :
      (fun x : Real => inner Complex
        ((suzukiFredholmExponentialL2 ha c : SuzukiL2) x)
        ((suzukiSmoothCoreToL2 v : SuzukiL2) x)) =ᵐ[volume]
      fun x => inner Complex (suzukiFredholmExponentialFunction a c x)
        (v.1 x) := by
    filter_upwards [hExp, hV] with x hxExp hxV
    rw [hxExp, hxV]
  rw [integral_congr_ae hpair]
  rw [show (fun x : Real =>
      inner Complex (suzukiFredholmExponentialFunction a c x) (v.1 x)) =
      (Set.Icc (-a) a).indicator
        (fun x => (Real.exp (c * x) : Complex) * v.1 x) by
    funext x
    by_cases hx : x ∈ Set.Icc (-a) a
    · unfold suzukiFredholmExponentialFunction
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp only [RCLike.inner_apply, starRingEnd_apply]
      change v.1 x * conj (Real.exp (c * x) : Complex) =
        (Real.exp (c * x) : Complex) * v.1 x
      rw [Complex.conj_ofReal]
      ring
    · simp [suzukiFredholmExponentialFunction, hx]]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]

/-- Exact integration-by-parts identity for the projected exponential
forcing on a smooth source differential. -/
theorem inner_suzukiFredholmExponentialForcing_smoothCoreDifferential
    {a : Real} (ha : 0 < a) (c : Real) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiFredholmExponentialForcing a c)
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) =
      -(Complex.I * (c : Complex)) *
        inner Complex (suzukiFredholmExponentialL2 ha c)
          (suzukiSmoothCoreToL2 v) := by
  rw [inner_suzukiFredholmExponentialForcing]
  unfold suzukiSmoothCoreDifferentialZeroMeanL2
  change inner Complex
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmExponentialContinuous a c))
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)) = _
  unfold suzukiFiniteIntervalContinuousToL2
  rw [ContinuousMap.inner_toLp]
  rw [show (∫ x : SuzukiFiniteInterval a,
      (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v x) *
        (starRingEnd Complex)
          (suzukiFredholmExponentialContinuous a c x) ∂volume) =
      ∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) *
          (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x) by
    rw [← MeasureTheory.integral_subtype measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    change (Complex.I *
        SchwartzMap.derivCLM Complex Complex v.1 x.1) *
      conj (Real.exp (c * x.1) : Complex) =
        (Real.exp (c * x.1) : Complex) *
          (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x.1)
    rw [Complex.conj_ofReal]
    ring]
  rw [show (∫ x in Set.Icc (-a) a,
      (Real.exp (c * x) : Complex) *
        (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x)) =
      Complex.I * ∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) *
          SchwartzMap.derivCLM Complex Complex v.1 x by
    have hfun : (fun x : Real =>
        (Real.exp (c * x) : Complex) *
          (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x)) =
        fun x => Complex.I *
          ((Real.exp (c * x) : Complex) *
            SchwartzMap.derivCLM Complex Complex v.1 x) := by
      funext x
      ring
    rw [hfun, integral_const_mul]]
  rw [setIntegral_exp_mul_deriv_eq ha
    (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩) c]
  rw [inner_suzukiFredholmExponentialL2_smoothCoreToL2 ha c v]
  ring

/-- Every projected real exponential has a concrete source-dual bound.  The
constant is the `L2` norm of its truncated derivative. -/
theorem suzukiSourceKDualBoundAt_fredholmExponential
    {a : Real} (ha : 0 < a) (c : Real) :
    SuzukiSourceKDualBoundAt a
      (suzukiFredholmExponentialForcing a c)
      (|c| * ‖suzukiFredholmExponentialL2 ha c‖) := by
  apply suzukiSourceKDualBoundAt_of_smoothCore ha
  intro v
  rw [inner_suzukiFredholmExponentialForcing_smoothCoreDifferential ha c v]
  calc
    ‖-(Complex.I * (c : Complex)) *
        inner Complex (suzukiFredholmExponentialL2 ha c)
          (suzukiSmoothCoreToL2 v)‖ =
        |c| * ‖inner Complex (suzukiFredholmExponentialL2 ha c)
          (suzukiSmoothCoreToL2 v)‖ := by simp
    _ ≤ |c| *
        (‖suzukiFredholmExponentialL2 ha c‖ *
          ‖suzukiSmoothCoreToL2 v‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = (|c| * ‖suzukiFredholmExponentialL2 ha c‖) *
        ‖suzukiSmoothCoreToL2 v‖ := by ring

/-- Constant interval functions are orthogonal to the zero-mean source
space, so their orthogonal projection vanishes. -/
def suzukiFiniteIntervalConstantContinuous
    (a : Real) (z : Complex) : C(SuzukiFiniteInterval a, Complex) :=
  ⟨fun _ => z, continuous_const⟩

@[simp]
theorem suzukiFiniteIntervalConstantContinuous_apply
    (a : Real) (z : Complex) (x : SuzukiFiniteInterval a) :
    suzukiFiniteIntervalConstantContinuous a z x = z :=
  rfl

theorem suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero
    (a : Real) (z : Complex) :
    suzukiFiniteIntervalContinuousToZeroMeanL2 a
        (suzukiFiniteIntervalConstantContinuous a z) = 0 := by
  unfold suzukiFiniteIntervalContinuousToZeroMeanL2
  change (SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFiniteIntervalConstantContinuous a z)) = 0
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  rw [Submodule.mem_orthogonal']
  intro u hu
  have huZero : suzukiFiniteIntervalMeanCLM a u = 0 := hu
  have hconst :
      suzukiFiniteIntervalContinuousToL2 a
          (suzukiFiniteIntervalConstantContinuous a z) =
        z • suzukiFiniteIntervalOneComplexL2 a := by
    rw [suzukiFiniteIntervalOneComplexL2, ← map_smul]
    congr 1
    ext x
    simp [suzukiFiniteIntervalConstantContinuous]
  rw [hconst, inner_smul_left]
  rw [suzukiFiniteIntervalMeanCLM_apply] at huZero
  rw [huZero, mul_zero]

/-- Suzuki's literal `exp x + i` Fredholm right-hand side before source
projection. -/
def suzukiFredholmPlusContinuous
    (a : Real) : C(SuzukiFiniteInterval a, Complex) :=
  suzukiFredholmExponentialContinuous a 1 +
    suzukiFiniteIntervalConstantContinuous a Complex.I

/-- Suzuki's literal `exp (-x) - i` Fredholm right-hand side before source
projection. -/
def suzukiFredholmMinusContinuous
    (a : Real) : C(SuzukiFiniteInterval a, Complex) :=
  suzukiFredholmExponentialContinuous a (-1) -
    suzukiFiniteIntervalConstantContinuous a Complex.I

/-- Projected `exp x + i` source forcing. -/
def suzukiFredholmPlusForcing
    (a : Real) : SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalContinuousToZeroMeanL2 a
    (suzukiFredholmPlusContinuous a)

/-- Projected `exp (-x) - i` source forcing. -/
def suzukiFredholmMinusForcing
    (a : Real) : SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalContinuousToZeroMeanL2 a
    (suzukiFredholmMinusContinuous a)

/-- Projection removes the constant `+i` term from the plus forcing. -/
theorem suzukiFredholmPlusForcing_eq_exponential (a : Real) :
    suzukiFredholmPlusForcing a =
      suzukiFredholmExponentialForcing a 1 := by
  unfold suzukiFredholmPlusForcing suzukiFredholmPlusContinuous
  unfold suzukiFredholmExponentialForcing
  rw [map_add,
    suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero, add_zero]

/-- Projection removes the constant `-i` term from the minus forcing. -/
theorem suzukiFredholmMinusForcing_eq_exponential (a : Real) :
    suzukiFredholmMinusForcing a =
      suzukiFredholmExponentialForcing a (-1) := by
  unfold suzukiFredholmMinusForcing suzukiFredholmMinusContinuous
  unfold suzukiFredholmExponentialForcing
  rw [map_sub,
    suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero, sub_zero]

/-- Concrete source-dual bound for Suzuki's projected plus forcing. -/
theorem suzukiSourceKDualBoundAt_fredholmPlus
    {a : Real} (ha : 0 < a) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmPlusForcing a)
      ‖suzukiFredholmExponentialL2 ha 1‖ := by
  rw [suzukiFredholmPlusForcing_eq_exponential]
  simpa using suzukiSourceKDualBoundAt_fredholmExponential ha 1

/-- Concrete source-dual bound for Suzuki's projected minus forcing. -/
theorem suzukiSourceKDualBoundAt_fredholmMinus
    {a : Real} (ha : 0 < a) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmMinusForcing a)
      ‖suzukiFredholmExponentialL2 ha (-1)‖ := by
  rw [suzukiFredholmMinusForcing_eq_exponential]
  simpa using suzukiSourceKDualBoundAt_fredholmExponential ha (-1)

/-- DF6F source-seminorm estimate for any solution with Suzuki's projected
plus forcing. -/
theorem suzukiDF6F_fredholmPlus_solution_sourceKSeminorm_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmPlusForcing a) :
    suzukiSourceKSeminorm a u ≤
      ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) 1‖ /
        ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda (norm_nonneg _)
    (suzukiSourceKDualBoundAt_fredholmPlus
      (suzukiDF6E_radius_pos ha)) hsolve

/-- DF6F source-seminorm estimate for any solution with Suzuki's projected
minus forcing. -/
theorem suzukiDF6F_fredholmMinus_solution_sourceKSeminorm_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceShiftedOperator a lambda u =
      suzukiFredholmMinusForcing a) :
    suzukiSourceKSeminorm a u ≤
      ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) (-1)‖ /
        ((1 / 400000 : Real) - lambda) := by
  exact suzukiDF6F_sourceKSeminorm_solution_le
    hsource hequation25 ha hlambda (norm_nonneg _)
    (suzukiSourceKDualBoundAt_fredholmMinus
      (suzukiDF6E_radius_pos ha)) hsolve

/-- Zero-shift plus-forcing specialization on the checked radius window. -/
theorem suzukiDF6F_sourceG_fredholmPlus_solution_sourceKSeminorm_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceGOperator a u =
      suzukiFredholmPlusForcing a) :
    suzukiSourceKSeminorm a u ≤
      400000 *
        ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) 1‖ := by
  exact suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha (norm_nonneg _)
    (suzukiSourceKDualBoundAt_fredholmPlus
      (suzukiDF6E_radius_pos ha)) hsolve

/-- Zero-shift minus-forcing specialization on the checked radius window. -/
theorem suzukiDF6F_sourceG_fredholmMinus_solution_sourceKSeminorm_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {u : SuzukiFiniteIntervalZeroMeanL2 a}
    (hsolve : suzukiSourceGOperator a u =
      suzukiFredholmMinusForcing a) :
    suzukiSourceKSeminorm a u ≤
      400000 *
        ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) (-1)‖ := by
  exact suzukiDF6F_sourceG_solution_sourceKSeminorm_le
    hsource hequation25 ha (norm_nonneg _)
    (suzukiSourceKDualBoundAt_fredholmMinus
      (suzukiDF6E_radius_pos ha)) hsolve

end

end RiemannHypothesisProject.Experiments.M100
