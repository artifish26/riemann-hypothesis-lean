import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDifferentialCoreDensity

/-!
# M100-DF6F primitive-core density

This module realizes compactly supported smooth primitives as a dense linear
subspace of finite-interval `L2`.  It complements the already checked density
of their differentials in the zero-mean source space and supplies the dense
domain needed for the later unbounded differential/adjoint construction.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace ComplexConjugate Topology

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiPrimitiveCoreDensityFiniteMeasure (a : Real) :
    IsFiniteMeasure (volume : Measure (SuzukiFiniteInterval a)) :=
  { measure_univ_lt_top := by
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
      exact measure_Icc_lt_top }

/-- Literal zero extension from the finite interval preserves the `L2` norm.
This turns the already defined zero-extension function into the isometric
bridge needed by unbounded-domain arguments. -/
theorem norm_suzukiFiniteIntervalL2ZeroExtension
    (a : Real) (u : SuzukiFiniteIntervalL2 a) :
    ‖suzukiFiniteIntervalL2ZeroExtension a u‖ = ‖u‖ := by
  let F : Real → Complex := suzukiFiniteIntervalL2ZeroExtensionFunction a u
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hindicator : (Icc (-a) a).indicator F = F := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · simp [hx]
    · simp only [Set.indicator, hx, ↓reduceIte]
      unfold F suzukiFiniteIntervalL2ZeroExtensionFunction
      rw [Function.extend_apply']
      simp only [Pi.zero_apply]
      rintro ⟨y, hy⟩
      exact hx (hy ▸ y.2)
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (suzukiFiniteIntervalL2ZeroExtension_coeFn a u)]
  apply congrArg ENNReal.toReal
  change eLpNorm F (2 : ENNReal) volume = eLpNorm (u :
    SuzukiFiniteInterval a → Complex) (2 : ENNReal) volume
  rw [← hindicator,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc,
    ← hmap, he.eLpNorm_map_measure]
  apply eLpNorm_congr_ae
  filter_upwards with x
  exact suzukiFiniteIntervalL2ZeroExtensionFunction_apply a u x

theorem suzukiFiniteIntervalL2ZeroExtension_add
    (a : Real) (u v : SuzukiFiniteIntervalL2 a) :
    suzukiFiniteIntervalL2ZeroExtension a (u + v) =
      suzukiFiniteIntervalL2ZeroExtension a u +
        suzukiFiniteIntervalL2ZeroExtension a v := by
  apply Lp.ext
  let Fuv := suzukiFiniteIntervalL2ZeroExtensionFunction a (u + v)
  let Fu := suzukiFiniteIntervalL2ZeroExtensionFunction a u
  let Fv := suzukiFiniteIntervalL2ZeroExtensionFunction a v
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hrestrict : Fuv =ᵐ[(volume : Measure Real).restrict (Icc (-a) a)]
      Fu + Fv := by
    rw [← hmap]
    apply (he.ae_map_iff).2
    filter_upwards [Lp.coeFn_add u v] with x hx
    simp only [Pi.add_apply]
    change suzukiFiniteIntervalL2ZeroExtensionFunction a (u + v) x.1 = _
    dsimp only [Fu, Fv, e]
    rw [suzukiFiniteIntervalL2ZeroExtensionFunction_apply,
      suzukiFiniteIntervalL2ZeroExtensionFunction_apply,
      suzukiFiniteIntervalL2ZeroExtensionFunction_apply, hx]
    simp only [Pi.add_apply]
  have hfun : Fuv =ᵐ[volume] Fu + Fv := by
    have hin : ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc (-a) a → Fuv x = (Fu + Fv) x :=
      ae_imp_of_ae_restrict hrestrict
    filter_upwards [hin] with x hx
    by_cases hxi : x ∈ Icc (-a) a
    · exact hx hxi
    · have hz : ∀ w : SuzukiFiniteIntervalL2 a,
          suzukiFiniteIntervalL2ZeroExtensionFunction a w x = 0 := by
        intro w
        unfold suzukiFiniteIntervalL2ZeroExtensionFunction
        rw [Function.extend_apply']
        simp only [Pi.zero_apply]
        rintro ⟨y, hy⟩
        exact hxi (hy ▸ y.2)
      change suzukiFiniteIntervalL2ZeroExtensionFunction a (u + v) x =
        suzukiFiniteIntervalL2ZeroExtensionFunction a u x +
          suzukiFiniteIntervalL2ZeroExtensionFunction a v x
      simp [hz]
  filter_upwards [suzukiFiniteIntervalL2ZeroExtension_coeFn a (u + v),
    suzukiFiniteIntervalL2ZeroExtension_coeFn a u,
    suzukiFiniteIntervalL2ZeroExtension_coeFn a v,
    Lp.coeFn_add (suzukiFiniteIntervalL2ZeroExtension a u)
      (suzukiFiniteIntervalL2ZeroExtension a v), hfun] with
      x huv hu hv hadd hfunx
  simp only [Pi.add_apply] at hadd hfunx
  dsimp only [Fuv, Fu, Fv] at hfunx
  rw [huv, hadd, hu, hv, hfunx]

theorem suzukiFiniteIntervalL2ZeroExtension_smul
    (a : Real) (c : Complex) (u : SuzukiFiniteIntervalL2 a) :
    suzukiFiniteIntervalL2ZeroExtension a (c • u) =
      c • suzukiFiniteIntervalL2ZeroExtension a u := by
  apply Lp.ext
  let Fcu := suzukiFiniteIntervalL2ZeroExtensionFunction a (c • u)
  let Fu := suzukiFiniteIntervalL2ZeroExtensionFunction a u
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hrestrict : Fcu =ᵐ[(volume : Measure Real).restrict (Icc (-a) a)]
      c • Fu := by
    rw [← hmap]
    apply (he.ae_map_iff).2
    filter_upwards [Lp.coeFn_smul c u] with x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    change suzukiFiniteIntervalL2ZeroExtensionFunction a (c • u) x.1 = _
    dsimp only [Fu, e]
    rw [suzukiFiniteIntervalL2ZeroExtensionFunction_apply,
      suzukiFiniteIntervalL2ZeroExtensionFunction_apply, hx]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hfun : Fcu =ᵐ[volume] c • Fu := by
    have hin : ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc (-a) a → Fcu x = (c • Fu) x :=
      ae_imp_of_ae_restrict hrestrict
    filter_upwards [hin] with x hx
    by_cases hxi : x ∈ Icc (-a) a
    · exact hx hxi
    · have hz : ∀ w : SuzukiFiniteIntervalL2 a,
          suzukiFiniteIntervalL2ZeroExtensionFunction a w x = 0 := by
        intro w
        unfold suzukiFiniteIntervalL2ZeroExtensionFunction
        rw [Function.extend_apply']
        simp only [Pi.zero_apply]
        rintro ⟨y, hy⟩
        exact hxi (hy ▸ y.2)
      change suzukiFiniteIntervalL2ZeroExtensionFunction a (c • u) x =
        c * suzukiFiniteIntervalL2ZeroExtensionFunction a u x
      simp [hz]
  filter_upwards [suzukiFiniteIntervalL2ZeroExtension_coeFn a (c • u),
    suzukiFiniteIntervalL2ZeroExtension_coeFn a u,
    Lp.coeFn_smul c (suzukiFiniteIntervalL2ZeroExtension a u), hfun] with
      x hcu hu hsmul hfunx
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul hfunx
  dsimp only [Fcu, Fu] at hfunx
  rw [hcu, hsmul, hu, hfunx]

/-- Literal zero extension as a complex linear isometry from interval `L2`
to global `L2`. -/
def suzukiFiniteIntervalL2ZeroExtensionLinearIsometry (a : Real) :
    SuzukiFiniteIntervalL2 a →ₗᵢ[Complex] SuzukiL2 where
  toFun := suzukiFiniteIntervalL2ZeroExtension a
  map_add' := suzukiFiniteIntervalL2ZeroExtension_add a
  map_smul' := suzukiFiniteIntervalL2ZeroExtension_smul a
  norm_map' := norm_suzukiFiniteIntervalL2ZeroExtension a

/-- The smooth primitive core embedded linearly in finite-interval `L2`. -/
def suzukiSmoothCoreFiniteIntervalL2LinearMap (a : Real) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiFiniteIntervalL2 a where
  toFun v := suzukiFiniteIntervalContinuousToL2 a
    (suzukiSmoothCoreFiniteIntervalContinuous
      (suzukiSmoothCoreLinearSubmoduleAsCore v))
  map_add' u v := by
    rw [← map_add]
    congr 1
  map_smul' c v := by
    rw [← map_smul]
    congr 1

/-- Zero-extending the interval restriction of a supported smooth primitive
recovers its existing global `L2` realization. -/
theorem suzukiFiniteIntervalL2ZeroExtension_smoothCore
    {a : Real} (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiFiniteIntervalL2ZeroExtension a
        (suzukiSmoothCoreFiniteIntervalL2LinearMap a v) =
      suzukiSmoothCoreToL2 (suzukiSmoothCoreLinearSubmoduleAsCore v) := by
  apply Lp.ext
  let U := suzukiSmoothCoreFiniteIntervalL2LinearMap a v
  let F := suzukiFiniteIntervalL2ZeroExtensionFunction a U
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hsub : (fun x : SuzukiFiniteInterval a => U x) =ᵐ[volume]
      fun x => v.1 x.1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreFiniteIntervalContinuous
        (suzukiSmoothCoreLinearSubmoduleAsCore v))
  have hrestrict : F =ᵐ[(volume : Measure Real).restrict (Icc (-a) a)]
      fun x => v.1 x := by
    rw [← hmap]
    apply (he.ae_map_iff).2
    filter_upwards [hsub] with x hx
    change suzukiFiniteIntervalL2ZeroExtensionFunction a U x.1 = v.1 x.1
    rw [suzukiFiniteIntervalL2ZeroExtensionFunction_apply, hx]
  have hfun : F =ᵐ[volume] fun x => v.1 x := by
    have hin : ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc (-a) a → F x = v.1 x :=
      ae_imp_of_ae_restrict hrestrict
    filter_upwards [hin] with x hx
    by_cases hxi : x ∈ Icc (-a) a
    · exact hx hxi
    · have hF : F x = 0 := by
        unfold F suzukiFiniteIntervalL2ZeroExtensionFunction
        rw [Function.extend_apply']
        simp only [Pi.zero_apply]
        rintro ⟨y, hy⟩
        exact hxi (hy ▸ y.2)
      have hv : v.1 x = 0 := by
        by_contra hne
        exact hxi ⟨(v.2 hne).1.le, (v.2 hne).2.le⟩
      rw [hF, hv]
  filter_upwards [suzukiFiniteIntervalL2ZeroExtension_coeFn a U,
    ((suzukiSmoothCoreLinearSubmoduleAsCore v).1.memLp
      (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
    hfun] with x hzero hsmooth hpoint
  change (suzukiFiniteIntervalL2ZeroExtension a U : Real → Complex) x =
    (suzukiSmoothCoreToL2
      (suzukiSmoothCoreLinearSubmoduleAsCore v) : Real → Complex) x
  rw [hzero]
  rw [show (suzukiSmoothCoreToL2
      (suzukiSmoothCoreLinearSubmoduleAsCore v) : Real → Complex) x =
      v.1 x by
    simpa only [suzukiSmoothCoreToL2,
      suzukiSmoothCoreLinearSubmoduleAsCore] using hsmooth]
  exact hpoint

/-- The shrinking cutoff times an arbitrary normalized interval Fourier mode,
promoted to the exact smooth primitive core. -/
def suzukiQuantitativeModeSmoothCore
    {a : Real} (ha : 0 < a) (m : Int) (n : Nat) : SuzukiSmoothCore a := by
  let f : Real → Complex := fun x =>
    (suzukiIntervalCutoff a n x : Complex) *
      suzukiIntervalExponentialCore a m x
  have hsupport : Function.support f ⊆ Ioo (-a) a := by
    intro x hx
    apply (suzukiIntervalCutoffSmoothCore ha n).2
    change (suzukiIntervalCutoff a n x : Complex) ≠ 0
    intro hzero
    exact hx (by simp [f, hzero])
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hopen := hsupport hne
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  have hcutoff : ContDiff Real (⊤ : ℕ∞)
      (fun x : Real =>
        (suzukiIntervalCutoff a n x : Complex)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_suzukiIntervalCutoff a n)
  refine ⟨hfCompact.toSchwartzMap
      (hcutoff.mul (contDiff_suzukiIntervalExponentialCore a m)), ?_⟩
  exact hsupport

@[simp]
theorem suzukiQuantitativeModeSmoothCore_apply
    {a : Real} (ha : 0 < a) (m : Int) (n : Nat) (x : Real) :
    (suzukiQuantitativeModeSmoothCore ha m n).1 x =
      (suzukiIntervalCutoff a n x : Complex) *
        suzukiIntervalExponentialCore a m x := by
  rfl

/-- On interval `L2`, the localized smooth mode is exactly multiplication of
the limiting Fourier mode by the canonical cutoff. -/
theorem suzukiSmoothCoreFiniteIntervalL2_quantitativeMode_eq_cutoffMul
    {a : Real} (ha : 0 < a) (m : Int) (n : Nat) :
    suzukiSmoothCoreFiniteIntervalL2LinearMap a
        ⟨(suzukiQuantitativeModeSmoothCore ha m n).1,
          (suzukiQuantitativeModeSmoothCore ha m n).2⟩ =
      suzukiIntervalCutoffMulL2 a n
        (suzukiIntervalExponentialL2 a m) := by
  apply Lp.ext
  have hleft :
      ((suzukiSmoothCoreFiniteIntervalL2LinearMap a
          ⟨(suzukiQuantitativeModeSmoothCore ha m n).1,
            (suzukiQuantitativeModeSmoothCore ha m n).2⟩ :
          SuzukiFiniteIntervalL2 a) : SuzukiFiniteInterval a → Complex)
        =ᵐ[volume] fun x =>
          (suzukiIntervalCutoff a n x.1 : Complex) *
            suzukiIntervalExponentialCore a m x.1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreFiniteIntervalContinuous
        (suzukiQuantitativeModeSmoothCore ha m n))
  filter_upwards [hleft,
    suzukiIntervalCutoffMulL2_coeFn a n
      (suzukiIntervalExponentialL2 a m),
    suzukiIntervalExponentialL2_coeFn a m] with x hleft hcutoff hmode
  rw [hleft, hcutoff]
  unfold suzukiIntervalCutoffMulFunction
  rw [hmode]

/-- Every normalized interval Fourier mode is an `L2` limit of exact smooth
compactly supported primitives. -/
theorem tendsto_suzukiQuantitativeModeSmoothCore_finiteIntervalL2
    {a : Real} (ha : 0 < a) (m : Int) :
    Tendsto
      (fun n : Nat => suzukiSmoothCoreFiniteIntervalL2LinearMap a
        ⟨(suzukiQuantitativeModeSmoothCore ha m n).1,
          (suzukiQuantitativeModeSmoothCore ha m n).2⟩)
      atTop (𝓝 (suzukiIntervalExponentialL2 a m)) := by
  simpa only [
    suzukiSmoothCoreFiniteIntervalL2_quantitativeMode_eq_cutoffMul ha m]
    using tendsto_suzukiIntervalCutoffMulL2 ha
      (suzukiIntervalExponentialL2 a m)

/-- Fourier uniqueness on the full interval space: all integer modes are
total. -/
theorem eq_zero_of_forall_inner_suzukiIntervalExponentialL2_eq_zero
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalL2 a)
    (horth : ∀ m : Int,
      inner Complex (suzukiIntervalExponentialL2 a m) u = 0) :
    u = 0 := by
  have hzeroMode := horth 0
  rw [suzukiIntervalExponentialL2_zero a, inner_smul_left] at hzeroMode
  have hroot : Real.sqrt (2 * a) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hscalar :
      star (((Real.sqrt (2 * a))⁻¹ : Real) : Complex) ≠ 0 := by
    exact star_ne_zero.mpr
      (Complex.ofReal_ne_zero.mpr (inv_ne_zero hroot))
  have hmean :
      inner Complex (suzukiFiniteIntervalOneComplexL2 a) u = 0 :=
    (mul_eq_zero.mp hzeroMode).resolve_left hscalar
  let u0 : SuzukiFiniteIntervalZeroMeanL2 a := ⟨u, hmean⟩
  have hdiff : ∀ (m : Int) (hm : m ≠ 0),
      inner Complex
        (suzukiIntervalDifferentialModeZeroMeanL2 ha hm) u0 = 0 := by
    intro m hm
    change inner Complex
      (suzukiIntervalDifferentialModeZeroMeanL2 ha hm :
        SuzukiFiniteIntervalL2 a) u = 0
    rw [suzukiIntervalDifferentialModeZeroMeanL2_coe_eq_smul_exponential
      ha hm, inner_smul_left, horth m, mul_zero]
  have hu0 : u0 = 0 :=
    eq_zero_of_forall_inner_suzukiIntervalDifferentialMode_eq_zero
      ha u0 hdiff
  exact congrArg Subtype.val hu0

/-- The span of all normalized interval Fourier modes is dense in the full
finite-interval `L2` space. -/
theorem topologicalClosure_span_suzukiIntervalExponentialL2_eq_top
    {a : Real} (ha : 0 < a) :
    (Submodule.span Complex
      (Set.range (suzukiIntervalExponentialL2 a))).topologicalClosure = ⊤ := by
  let S : Submodule Complex (SuzukiFiniteIntervalL2 a) :=
    Submodule.span Complex (Set.range (suzukiIntervalExponentialL2 a))
  apply le_antisymm le_top
  intro u _hu
  let w : SuzukiFiniteIntervalL2 a :=
    u - S.topologicalClosure.starProjection u
  have hwOrth : w ∈ S.topologicalClosureᗮ :=
    S.topologicalClosure.sub_starProjection_mem_orthogonal u
  have hwInner : ∀ m : Int,
      inner Complex (suzukiIntervalExponentialL2 a m) w = 0 := by
    intro m
    exact Submodule.inner_right_of_mem_orthogonal
      (S.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self m))) hwOrth
  have hwZero : w = 0 :=
    eq_zero_of_forall_inner_suzukiIntervalExponentialL2_eq_zero
      ha w hwInner
  have huProjection : u = S.topologicalClosure.starProjection u :=
    sub_eq_zero.mp hwZero
  rw [huProjection]
  exact S.topologicalClosure.starProjection_apply_mem u

/-- The smooth primitive range is dense because its closure contains every
integer Fourier mode. -/
theorem topologicalClosure_range_suzukiSmoothCoreFiniteIntervalL2_eq_top
    {a : Real} (ha : 0 < a) :
    (LinearMap.range
      (suzukiSmoothCoreFiniteIntervalL2LinearMap a)).topologicalClosure = ⊤ := by
  let R : Submodule Complex (SuzukiFiniteIntervalL2 a) :=
    LinearMap.range (suzukiSmoothCoreFiniteIntervalL2LinearMap a)
  let S : Submodule Complex (SuzukiFiniteIntervalL2 a) :=
    Submodule.span Complex (Set.range (suzukiIntervalExponentialL2 a))
  have hmode : ∀ m : Int,
      suzukiIntervalExponentialL2 a m ∈ R.topologicalClosure := by
    intro m
    apply mem_closure_of_tendsto
      (tendsto_suzukiQuantitativeModeSmoothCore_finiteIntervalL2 ha m)
    filter_upwards with n
    exact ⟨⟨(suzukiQuantitativeModeSmoothCore ha m n).1,
      (suzukiQuantitativeModeSmoothCore ha m n).2⟩, rfl⟩
  have hspan : S ≤ R.topologicalClosure := by
    dsimp only [S]
    rw [Submodule.span_le]
    rintro _ ⟨m, rfl⟩
    exact hmode m
  have hspanClosure : S.topologicalClosure ≤ R.topologicalClosure :=
    S.topologicalClosure_minimal hspan R.isClosed_topologicalClosure
  have htotal : S.topologicalClosure = ⊤ :=
    topologicalClosure_span_suzukiIntervalExponentialL2_eq_top ha
  apply top_unique
  rw [← htotal]
  exact hspanClosure

/-- Compactly supported smooth primitives have dense range in finite-interval
`L2`. -/
theorem denseRange_suzukiSmoothCoreFiniteIntervalL2LinearMap
    {a : Real} (ha : 0 < a) :
    DenseRange (suzukiSmoothCoreFiniteIntervalL2LinearMap a) := by
  rw [DenseRange, dense_iff_closure_eq]
  change closure
      ((LinearMap.range (suzukiSmoothCoreFiniteIntervalL2LinearMap a) :
        Submodule Complex (SuzukiFiniteIntervalL2 a)) :
        Set (SuzukiFiniteIntervalL2 a)) = Set.univ
  rw [← Submodule.topologicalClosure_coe,
    topologicalClosure_range_suzukiSmoothCoreFiniteIntervalL2_eq_top ha]
  rfl

/-- The smooth primitive embedding loses no pointwise information. -/
theorem injective_suzukiSmoothCoreFiniteIntervalL2LinearMap
    (a : Real) :
    Function.Injective (suzukiSmoothCoreFiniteIntervalL2LinearMap a) := by
  intro u v huv
  have hsub :
      (fun x : SuzukiFiniteInterval a => u.1 x.1) =ᵐ[volume]
        fun x : SuzukiFiniteInterval a => v.1 x.1 := by
    have huCoe := ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreFiniteIntervalContinuous
        (suzukiSmoothCoreLinearSubmoduleAsCore u))
    have hvCoe := ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreFiniteIntervalContinuous
        (suzukiSmoothCoreLinearSubmoduleAsCore v))
    filter_upwards [huCoe, hvCoe] with x huPoint hvPoint
    calc
      u.1 x.1 =
          (suzukiSmoothCoreFiniteIntervalL2LinearMap a u :
            SuzukiFiniteInterval a → Complex) x := huPoint.symm
      _ = (suzukiSmoothCoreFiniteIntervalL2LinearMap a v :
            SuzukiFiniteInterval a → Complex) x := by rw [huv]
      _ = v.1 x.1 := hvPoint
  let e : SuzukiFiniteInterval a → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval a)) =
      (volume : Measure Real).restrict (Icc (-a) a) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hrestrict :
      (fun x : Real => u.1 x) =ᵐ[(volume : Measure Real).restrict (Icc (-a) a)]
        fun x : Real => v.1 x := by
    rw [← hmap]
    apply (he.ae_map_iff).2
    exact hsub
  have hin : ∀ᵐ x ∂(volume : Measure Real),
      x ∈ Icc (-a) a → u.1 x = v.1 x :=
    ae_imp_of_ae_restrict hrestrict
  have hglobalAE : (fun x : Real => u.1 x) =ᵐ[volume]
      fun x : Real => v.1 x := by
    filter_upwards [hin] with x hx
    by_cases hxi : x ∈ Icc (-a) a
    · exact hx hxi
    · have hu : u.1 x = 0 := by
        by_contra hne
        exact hxi ⟨(u.2 hne).1.le, (u.2 hne).2.le⟩
      have hv : v.1 x = 0 := by
        by_contra hne
        exact hxi ⟨(v.2 hne).1.le, (v.2 hne).2.le⟩
      rw [hu, hv]
  apply Subtype.ext
  have hLp :
      u.1.toLp (2 : ENNReal) (volume : Measure Real) =
        v.1.toLp (2 : ENNReal) (volume : Measure Real) :=
    (MemLp.toLp_eq_toLp_iff
      (u.1.memLp (2 : ENNReal) (volume : Measure Real))
      (v.1.memLp (2 : ENNReal) (volume : Measure Real))).2 hglobalAE
  exact SchwartzMap.injective_toLp (2 : ENNReal)
    (volume : Measure Real) hLp

end

end RiemannHypothesisProject.Experiments.M100
