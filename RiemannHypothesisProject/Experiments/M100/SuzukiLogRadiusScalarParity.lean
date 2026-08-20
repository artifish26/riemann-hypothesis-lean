import RiemannHypothesisProject.Experiments.M100.SuzukiLogRadiusLinearCompletion
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# M100-DF6D5B1 scalar and reflection-parity reduction

This module records the exact reflection-parity subresult of the attempted
reduction from the complex logarithmic radius completion to the real even and
odd sectors consumed by the endpoint matrix inequalities.  It constructs the
orthogonal reflection decomposition in both the ambient global `L²` space and
the closed endpoint completion, including radius support, zero mean, exact
norm splitting, and a conditional complete-form splitting theorem.

The endpoint antiunitary conjugation and the concrete complete-form
reflection-invariance law are not introduced here; without them the
real/imaginary and unconditional complete-form reductions remain open.  No
Yoshida mode, finite projection, endpoint matrix identification, or coercivity
conclusion is introduced.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace

/-- The even projector `(I + R) / 2` for reflection through the origin. -/
def suzukiL2EvenProjector : SuzukiL2 →L[Complex] SuzukiL2 :=
  (2 : Complex)⁻¹ •
    (ContinuousLinearMap.id Complex SuzukiL2 +
      suzukiL2Reflection.toContinuousLinearMap)

/-- The odd projector `(I - R) / 2` for reflection through the origin. -/
def suzukiL2OddProjector : SuzukiL2 →L[Complex] SuzukiL2 :=
  (2 : Complex)⁻¹ •
    (ContinuousLinearMap.id Complex SuzukiL2 -
      suzukiL2Reflection.toContinuousLinearMap)

theorem suzukiL2EvenProjector_apply (v : SuzukiL2) :
    suzukiL2EvenProjector v =
      (2 : Complex)⁻¹ • (v + suzukiL2Reflection v) := by
  rfl

theorem suzukiL2OddProjector_apply (v : SuzukiL2) :
    suzukiL2OddProjector v =
      (2 : Complex)⁻¹ • (v - suzukiL2Reflection v) := by
  rfl

theorem suzukiL2EvenProjector_reflection (v : SuzukiL2) :
    suzukiL2Reflection (suzukiL2EvenProjector v) =
      suzukiL2EvenProjector v := by
  rw [suzukiL2EvenProjector_apply, map_smul, map_add,
    suzukiL2Reflection_involution]
  module

theorem suzukiL2OddProjector_reflection (v : SuzukiL2) :
    suzukiL2Reflection (suzukiL2OddProjector v) =
      -suzukiL2OddProjector v := by
  rw [suzukiL2OddProjector_apply, map_smul, map_sub,
    suzukiL2Reflection_involution]
  module

theorem suzukiL2EvenProjector_even (v : SuzukiL2) :
    SuzukiL2Even (suzukiL2EvenProjector v) :=
  suzukiL2EvenProjector_reflection v

theorem suzukiL2OddProjector_odd (v : SuzukiL2) :
    SuzukiL2Odd (suzukiL2OddProjector v) :=
  suzukiL2OddProjector_reflection v

theorem suzukiL2EvenProjector_add_oddProjector (v : SuzukiL2) :
    suzukiL2EvenProjector v + suzukiL2OddProjector v = v := by
  rw [suzukiL2EvenProjector_apply, suzukiL2OddProjector_apply]
  module

theorem inner_suzukiL2EvenProjector_oddProjector
    (v : SuzukiL2) :
    inner Complex (suzukiL2EvenProjector v)
        (suzukiL2OddProjector v) = 0 := by
  have hreflect :=
    suzukiL2Reflection.inner_map_map
      (suzukiL2EvenProjector v) (suzukiL2OddProjector v)
  rw [suzukiL2EvenProjector_reflection,
    suzukiL2OddProjector_reflection, inner_neg_right] at hreflect
  exact CharZero.neg_eq_self_iff.mp hreflect

/-- Exact Pythagorean splitting of the ambient global `L²` norm into its
even and odd reflection sectors. -/
theorem suzukiL2_norm_sq_even_odd_split (v : SuzukiL2) :
    ‖v‖ ^ 2 =
      ‖suzukiL2EvenProjector v‖ ^ 2 +
        ‖suzukiL2OddProjector v‖ ^ 2 := by
  calc
    ‖v‖ ^ 2 =
        ‖suzukiL2EvenProjector v + suzukiL2OddProjector v‖ ^ 2 := by
      rw [suzukiL2EvenProjector_add_oddProjector]
    _ = ‖suzukiL2EvenProjector v‖ ^ 2 +
          ‖suzukiL2OddProjector v‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          _ _ (inner_suzukiL2EvenProjector_oddProjector v)

theorem suzukiL2Reflection_supportedAt
    {r : Real} {v : SuzukiL2}
    (hv : suzukiL2SupportedAt r v) :
    suzukiL2SupportedAt r (suzukiL2Reflection v) := by
  have hvneg :
      ∀ᵐ x ∂(volume : Measure Real),
        -x ∉ Set.Icc (-r) r → v (-x) = 0 :=
    (Measure.measurePreserving_neg
      (volume : Measure Real)).quasiMeasurePreserving.ae hv
  filter_upwards [hvneg, suzukiL2Reflection_coeFn v] with x hx hreflect
  intro hxOutside
  rw [hreflect]
  apply hx
  intro hneg
  apply hxOutside
  exact ⟨by linarith [hneg.2], by linarith [hneg.1]⟩

theorem suzukiL2EvenProjector_supportedAt
    {r : Real} {v : SuzukiL2}
    (hv : suzukiL2SupportedAt r v) :
    suzukiL2SupportedAt r (suzukiL2EvenProjector v) := by
  filter_upwards [hv, suzukiL2Reflection_supportedAt hv,
    Lp.coeFn_add v (suzukiL2Reflection v),
    Lp.coeFn_smul (2 : Complex)⁻¹
      (v + suzukiL2Reflection v)] with x hx hreflect hadd hsmul
  intro hxOutside
  rw [suzukiL2EvenProjector_apply, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd, Pi.add_apply, hx hxOutside, hreflect hxOutside]
  simp

theorem suzukiL2OddProjector_supportedAt
    {r : Real} {v : SuzukiL2}
    (hv : suzukiL2SupportedAt r v) :
    suzukiL2SupportedAt r (suzukiL2OddProjector v) := by
  filter_upwards [hv, suzukiL2Reflection_supportedAt hv,
    Lp.coeFn_sub v (suzukiL2Reflection v),
    Lp.coeFn_smul (2 : Complex)⁻¹
      (v - suzukiL2Reflection v)] with x hx hreflect hsub hsmul
  intro hxOutside
  rw [suzukiL2OddProjector_apply, hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsub, Pi.sub_apply, hx hxOutside, hreflect hxOutside]
  simp

theorem suzukiL2IntervalMean_reflection
    (r : Real) (v : SuzukiL2) :
    suzukiL2IntervalMean r (suzukiL2Reflection v) =
      suzukiL2IntervalMean r v := by
  rw [suzukiL2IntervalMean_eq_setIntegral,
    suzukiL2IntervalMean_eq_setIntegral]
  have hreflection := suzukiL2Reflection_coeFn v
  rw [← MeasureTheory.integral_indicator measurableSet_Icc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ x, Set.indicator (Set.Icc (-r) r)
          (suzukiL2Reflection v : Real → Complex) x
        ∂(volume : Measure Real)) =
        ∫ x, Set.indicator (Set.Icc (-r) r)
          (fun y : Real => v (-y)) x
        ∂(volume : Measure Real) := by
      apply integral_congr_ae
      filter_upwards [hreflection] with x hx
      by_cases hmem : x ∈ Set.Icc (-r) r <;>
        simp [Set.indicator, hmem, hx]
    _ = ∫ x, (Set.indicator (Set.Icc (-r) r)
          (v : Real → Complex)) (-x)
        ∂(volume : Measure Real) := by
      apply integral_congr_ae
      filter_upwards with x
      have hmem :
          -x ∈ Set.Icc (-r) r ↔ x ∈ Set.Icc (-r) r := by
        simp only [Set.mem_Icc]
        constructor <;> intro h <;> constructor <;> linarith
      by_cases hx : x ∈ Set.Icc (-r) r
      · simp [Set.indicator, hx, hmem.mpr hx]
      · have hneg : -x ∉ Set.Icc (-r) r :=
          fun h => hx (hmem.mp h)
        simp [Set.indicator, hx, hneg]
    _ = ∫ x, Set.indicator (Set.Icc (-r) r)
          (v : Real → Complex) x
        ∂(volume : Measure Real) := by
      exact (Measure.measurePreserving_neg
        (volume : Measure Real)).integral_comp
          (Homeomorph.neg Real).measurableEmbedding _

/-- The odd reflection sector satisfies the interval zero-mean convention
automatically. -/
theorem suzukiL2IntervalMean_oddProjector_zero
    (r : Real) (v : SuzukiL2) :
    suzukiL2IntervalMean r (suzukiL2OddProjector v) = 0 := by
  rw [suzukiL2OddProjector_apply]
  change inner Complex (suzukiL2IntervalIndicator r)
      ((2 : Complex)⁻¹ • (v - suzukiL2Reflection v)) = 0
  rw [inner_smul_right, inner_sub_right]
  change (2 : Complex)⁻¹ *
      (suzukiL2IntervalMean r v -
        suzukiL2IntervalMean r (suzukiL2Reflection v)) = 0
  rw [suzukiL2IntervalMean_reflection]
  simp

/-- The even projector carries the full interval mean. -/
theorem suzukiL2IntervalMean_evenProjector
    (r : Real) (v : SuzukiL2) :
    suzukiL2IntervalMean r (suzukiL2EvenProjector v) =
      suzukiL2IntervalMean r v := by
  rw [suzukiL2EvenProjector_apply]
  change inner Complex (suzukiL2IntervalIndicator r)
      ((2 : Complex)⁻¹ • (v + suzukiL2Reflection v)) =
        suzukiL2IntervalMean r v
  rw [inner_smul_right, inner_add_right]
  change (2 : Complex)⁻¹ *
      (suzukiL2IntervalMean r v +
        suzukiL2IntervalMean r (suzukiL2Reflection v)) =
      suzukiL2IntervalMean r v
  rw [suzukiL2IntervalMean_reflection]
  ring

/-- Reflection through the origin on Schwartz functions. -/
def suzukiSchwartzReflection :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Complex
    (LinearIsometryEquiv.neg Real).toContinuousLinearEquiv

@[simp]
theorem suzukiSchwartzReflection_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    suzukiSchwartzReflection f x = f (-x) :=
  rfl

/-- The Schwartz and global-`L²` reflection operations agree. -/
theorem suzukiL2Reflection_schwartzToL2
    (f : SchwartzLineTestFunction) :
    suzukiL2Reflection
        (f.toLp (2 : ENNReal) (volume : Measure Real)) =
      (suzukiSchwartzReflection f).toLp
        (2 : ENNReal) (volume : Measure Real) := by
  apply Lp.ext
  have hfneg :=
    (Measure.measurePreserving_neg
      (volume : Measure Real)).quasiMeasurePreserving.ae
        (SchwartzMap.coeFn_toLp f (2 : ENNReal)
          (volume : Measure Real))
  filter_upwards [
    suzukiL2Reflection_coeFn
      (f.toLp (2 : ENNReal) (volume : Measure Real)),
    hfneg,
    SchwartzMap.coeFn_toLp (suzukiSchwartzReflection f)
      (2 : ENNReal) (volume : Measure Real)] with x hreflect hf hrf
  rw [hreflect, hf, hrf]
  rfl

/-- Reflection commutes with the Schwartz Fourier transform because negation
is an orthogonal linear equivalence. -/
theorem fourier_suzukiSchwartzReflection
    (f : SchwartzLineTestFunction) :
    FourierTransform.fourier (suzukiSchwartzReflection f) =
      suzukiSchwartzReflection (FourierTransform.fourier f) := by
  ext xi
  exact Real.fourier_comp_linearIsometry
    (LinearIsometryEquiv.neg Real) f xi

/-- Reflection commutes with Plancherel's Fourier transform on global
`L²(Real, Complex)`. -/
theorem fourier_suzukiL2Reflection (v : SuzukiL2) :
    FourierTransform.fourier (suzukiL2Reflection v) =
      suzukiL2Reflection (FourierTransform.fourier v) := by
  let p : SuzukiL2 → Prop := fun w =>
    FourierTransform.fourier (suzukiL2Reflection w) =
      suzukiL2Reflection (FourierTransform.fourier w)
  have hdense :
      DenseRange
        (SchwartzMap.toLpCLM Complex Complex
          (2 : ENNReal) (volume : Measure Real)) := by
    simpa using!
      (SchwartzMap.denseRange_toLpCLM
        (F := Complex) (p := (2 : ENNReal)) ENNReal.ofNat_ne_top)
  apply DenseRange.induction_on
    (p := p)
    hdense v
  · exact isClosed_eq
      ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.comp
        suzukiL2Reflection.continuous)
      (suzukiL2Reflection.continuous.comp
        (MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous)
  intro f
  dsimp only [p]
  change
    FourierTransform.fourier
        (suzukiL2Reflection
          (f.toLp (2 : ENNReal) (volume : Measure Real))) =
      suzukiL2Reflection
        (FourierTransform.fourier
          (f.toLp (2 : ENNReal) (volume : Measure Real)))
  rw [suzukiL2Reflection_schwartzToL2,
    SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq,
    suzukiL2Reflection_schwartzToL2,
    fourier_suzukiSchwartzReflection]

theorem suzukiLogFourierInvMultiplier_neg (xi : Real) :
    suzukiLogFourierInvMultiplier (-xi) =
      suzukiLogFourierInvMultiplier xi := by
  simp [suzukiLogFourierInvMultiplier, suzukiLogFourierWeight]

/-- The reciprocal logarithmic multiplier commutes with reflection. -/
theorem suzukiLogFourierInvMultiplierCLM_reflection (v : SuzukiL2) :
    suzukiLogFourierInvMultiplierCLM (suzukiL2Reflection v) =
      suzukiL2Reflection (suzukiLogFourierInvMultiplierCLM v) := by
  apply Lp.ext
  have hleft := suzukiLogFourierInvMultiplierCLM_coe_ae
    (suzukiL2Reflection v)
  have hrightReflection := suzukiL2Reflection_coeFn
    (suzukiLogFourierInvMultiplierCLM v)
  have hrightMultiplier :=
    (Measure.measurePreserving_neg
      (volume : Measure Real)).quasiMeasurePreserving.ae
        (suzukiLogFourierInvMultiplierCLM_coe_ae v)
  have hvReflection := suzukiL2Reflection_coeFn v
  filter_upwards [hleft, hrightReflection, hrightMultiplier,
    hvReflection] with xi hleft hright hmult hv
  rw [hleft, hright, hmult, hv,
    suzukiLogFourierInvMultiplier_neg]

/-- Reflection preserves the exact radius-`r` Schwartz core. -/
def suzukiSmoothCoreLinearReflection (r : Real) :
    SuzukiSmoothCoreLinearSubmodule r ≃ₗ[Complex]
      SuzukiSmoothCoreLinearSubmodule r where
  toFun v := ⟨suzukiSchwartzReflection v.1, by
    intro x hx
    change v.1 (-x) ≠ 0 at hx
    have hsupport := v.2 hx
    exact ⟨by linarith [hsupport.2], by linarith [hsupport.1]⟩⟩
  invFun v := ⟨suzukiSchwartzReflection v.1, by
    intro x hx
    change v.1 (-x) ≠ 0 at hx
    have hsupport := v.2 hx
    exact ⟨by linarith [hsupport.2], by linarith [hsupport.1]⟩⟩
  left_inv v := by
    apply Subtype.ext
    ext x
    simp [suzukiSchwartzReflection_apply]
  right_inv v := by
    apply Subtype.ext
    ext x
    simp [suzukiSchwartzReflection_apply]
  map_add' u v := by
    apply Subtype.ext
    ext x
    rfl
  map_smul' c v := by
    apply Subtype.ext
    ext x
    rfl

@[simp]
theorem suzukiSmoothCoreLinearReflection_apply
    (r : Real) (v : SuzukiSmoothCoreLinearSubmodule r) (x : Real) :
    (suzukiSmoothCoreLinearReflection r v).1 x = v.1 (-x) :=
  rfl

/-- Coordinatewise reflection on the Hilbert logarithmic graph. -/
def suzukiLogHilbertGraphReflection :
    SuzukiLogHilbertGraphSpace →ₗᵢ[Complex]
      SuzukiLogHilbertGraphSpace where
  toFun x := ⟨WithLp.toLp 2
      (suzukiL2Reflection (WithLp.ofLp x.1).1,
        suzukiL2Reflection (WithLp.ofLp x.1).2), by
    change
      (suzukiL2Reflection (WithLp.ofLp x.1).1,
          suzukiL2Reflection (WithLp.ofLp x.1).2) ∈
        suzukiLogFourierPMap.graph
    rw [suzukiLogFourierPMap_mem_graph_iff,
      fourier_suzukiL2Reflection,
      suzukiLogFourierInvMultiplierCLM_reflection]
    have hx := x.2
    change WithLp.ofLp x.1 ∈ suzukiLogFourierPMap.graph at hx
    exact congrArg suzukiL2Reflection
      ((suzukiLogFourierPMap_mem_graph_iff _).mp hx)⟩
  map_add' x y := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    apply Prod.ext
    · exact map_add _ _ _
    · exact map_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    apply Prod.ext
    · exact map_smul _ _ _
    · exact map_smul _ _ _
  norm_map' x := by
    change
      ‖WithLp.toLp 2
          (suzukiL2Reflection (WithLp.ofLp x.1).1,
            suzukiL2Reflection (WithLp.ofLp x.1).2)‖ =
        ‖x.1‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2]
    simp

@[simp]
theorem suzukiLogHilbertGraphReflection_fst
    (x : SuzukiLogHilbertGraphSpace) :
    (WithLp.ofLp (suzukiLogHilbertGraphReflection x).1).1 =
      suzukiL2Reflection (WithLp.ofLp x.1).1 :=
  rfl

@[simp]
theorem suzukiLogHilbertGraphReflection_snd
    (x : SuzukiLogHilbertGraphSpace) :
    (WithLp.ofLp (suzukiLogHilbertGraphReflection x).1).2 =
      suzukiL2Reflection (WithLp.ofLp x.1).2 :=
  rfl

@[simp]
theorem suzukiLogHilbertGraphReflection_involution
    (x : SuzukiLogHilbertGraphSpace) :
    suzukiLogHilbertGraphReflection
        (suzukiLogHilbertGraphReflection x) = x := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  apply Prod.ext
  · rw [suzukiLogHilbertGraphReflection_fst,
      suzukiLogHilbertGraphReflection_fst,
      suzukiL2Reflection_involution]
  · rw [suzukiLogHilbertGraphReflection_snd,
      suzukiLogHilbertGraphReflection_snd,
      suzukiL2Reflection_involution]

/-- The graph reflection restricts to the literal reflection of every
radius-`r` smooth-core element. -/
theorem suzukiLogHilbertGraphReflection_smoothCore
    (r : Real) (v : SuzukiSmoothCoreLinearSubmodule r) :
    suzukiLogHilbertGraphReflection
        (suzukiSmoothCoreToHilbertGraphLinearMap r v) =
      suzukiSmoothCoreToHilbertGraphLinearMap r
        (suzukiSmoothCoreLinearReflection r v) := by
  apply Subtype.ext
  apply WithLp.ofLp_injective
  apply Prod.ext
  · exact suzukiL2Reflection_schwartzToL2 v.1
  · have hleft :=
      (suzukiLogHilbertGraphReflection
        (suzukiSmoothCoreToHilbertGraphLinearMap r v)).2
    have hright :=
      (suzukiSmoothCoreToHilbertGraphLinearMap r
        (suzukiSmoothCoreLinearReflection r v)).2
    change WithLp.ofLp
      (suzukiLogHilbertGraphReflection
        (suzukiSmoothCoreToHilbertGraphLinearMap r v)).1 ∈
          suzukiLogFourierPMap.graph at hleft
    change WithLp.ofLp
      (suzukiSmoothCoreToHilbertGraphLinearMap r
        (suzukiSmoothCoreLinearReflection r v)).1 ∈
          suzukiLogFourierPMap.graph at hright
    exact suzukiLogFourierPMap.mem_graph_snd_inj
      hleft hright (suzukiL2Reflection_schwartzToL2 v.1)

/-- Reflection preserves the closed radius-`r` logarithmic completion. -/
theorem suzukiLogHilbertGraphReflection_mem_radius
    {r : Real} (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogHilbertGraphReflection v.1 ∈
      SuzukiLogRadiusLinearSubmodule r := by
  have hclosed : IsClosed
      {x : SuzukiLogHilbertGraphSpace |
        suzukiLogHilbertGraphReflection x ∈
          SuzukiLogRadiusLinearSubmodule r} :=
    (Submodule.isClosed_topologicalClosure
      (LinearMap.range
        (suzukiSmoothCoreToHilbertGraphLinearMap r))).preimage
          suzukiLogHilbertGraphReflection.continuous
  have hrange :
      (LinearMap.range
          (suzukiSmoothCoreToHilbertGraphLinearMap r) :
        Set SuzukiLogHilbertGraphSpace) ⊆
        {x : SuzukiLogHilbertGraphSpace |
          suzukiLogHilbertGraphReflection x ∈
            SuzukiLogRadiusLinearSubmodule r} := by
    rintro _ ⟨w, rfl⟩
    change suzukiLogHilbertGraphReflection
        (suzukiSmoothCoreToHilbertGraphLinearMap r w) ∈
      SuzukiLogRadiusLinearSubmodule r
    rw [suzukiLogHilbertGraphReflection_smoothCore]
    exact subset_closure
      (LinearMap.mem_range_self
        (suzukiSmoothCoreToHilbertGraphLinearMap r)
        (suzukiSmoothCoreLinearReflection r w))
  exact closure_minimal hrange hclosed v.2

/-- Reflection through the origin as a complex-linear isometry of the
endpoint radius completion. -/
def suzukiLogRadiusLinearReflection (r : Real) :
    SuzukiLogRadiusLinearCompletion r →ₗᵢ[Complex]
      SuzukiLogRadiusLinearCompletion r where
  toFun v := ⟨suzukiLogHilbertGraphReflection v.1,
    suzukiLogHilbertGraphReflection_mem_radius v⟩
  map_add' u v := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c v := by
    apply Subtype.ext
    exact map_smul _ _ _
  norm_map' v := suzukiLogHilbertGraphReflection.norm_map v.1

@[simp]
theorem suzukiLogRadiusLinearReflection_involution
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearReflection r
        (suzukiLogRadiusLinearReflection r v) = v := by
  apply Subtype.ext
  exact suzukiLogHilbertGraphReflection_involution v.1

/-- Endpoint reflection is literal ambient `L²` reflection under the
canonical first-coordinate embedding. -/
theorem suzukiLogRadiusLinearCompletionToL2_reflection
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearReflection r v) =
      suzukiL2Reflection
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rfl

/-- Reflection preserves the endpoint Hilbert inner product exactly. -/
theorem suzukiLogRadiusLinearReflection_inner_map_map
    (r : Real) (u v : SuzukiLogRadiusLinearCompletion r) :
    inner Complex (suzukiLogRadiusLinearReflection r u)
        (suzukiLogRadiusLinearReflection r v) =
      inner Complex u v := by
  change inner Complex
      (suzukiLogHilbertGraphReflection u.1).1
      (suzukiLogHilbertGraphReflection v.1).1 =
    inner Complex u.1.1 v.1.1
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    suzukiLogHilbertGraphReflection_fst,
    suzukiLogHilbertGraphReflection_fst,
    suzukiLogHilbertGraphReflection_snd,
    suzukiLogHilbertGraphReflection_snd,
    suzukiL2Reflection.inner_map_map,
    suzukiL2Reflection.inner_map_map]

/-- The even reflection projector on the endpoint completion. -/
def suzukiLogRadiusLinearEvenProjector (r : Real) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  (2 : Complex)⁻¹ •
    (ContinuousLinearMap.id Complex
        (SuzukiLogRadiusLinearCompletion r) +
      (suzukiLogRadiusLinearReflection r).toContinuousLinearMap)

/-- The odd reflection projector on the endpoint completion. -/
def suzukiLogRadiusLinearOddProjector (r : Real) :
    SuzukiLogRadiusLinearCompletion r →L[Complex]
      SuzukiLogRadiusLinearCompletion r :=
  (2 : Complex)⁻¹ •
    (ContinuousLinearMap.id Complex
        (SuzukiLogRadiusLinearCompletion r) -
      (suzukiLogRadiusLinearReflection r).toContinuousLinearMap)

theorem suzukiLogRadiusLinearEvenProjector_apply
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearEvenProjector r v =
      (2 : Complex)⁻¹ •
        (v + suzukiLogRadiusLinearReflection r v) := by
  rfl

theorem suzukiLogRadiusLinearOddProjector_apply
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearOddProjector r v =
      (2 : Complex)⁻¹ •
        (v - suzukiLogRadiusLinearReflection r v) := by
  rfl

theorem suzukiLogRadiusLinearEvenProjector_reflection
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearReflection r
        (suzukiLogRadiusLinearEvenProjector r v) =
      suzukiLogRadiusLinearEvenProjector r v := by
  rw [suzukiLogRadiusLinearEvenProjector_apply,
    map_smul, map_add,
    suzukiLogRadiusLinearReflection_involution]
  module

theorem suzukiLogRadiusLinearOddProjector_reflection
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearReflection r
        (suzukiLogRadiusLinearOddProjector r v) =
      -suzukiLogRadiusLinearOddProjector r v := by
  rw [suzukiLogRadiusLinearOddProjector_apply,
    (suzukiLogRadiusLinearReflection r).map_smul,
    (suzukiLogRadiusLinearReflection r).map_sub,
    suzukiLogRadiusLinearReflection_involution]
  module

theorem suzukiLogRadiusLinearEvenProjector_add_oddProjector
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearEvenProjector r v +
        suzukiLogRadiusLinearOddProjector r v = v := by
  rw [suzukiLogRadiusLinearEvenProjector_apply,
    suzukiLogRadiusLinearOddProjector_apply]
  module

theorem inner_suzukiLogRadiusLinearEvenProjector_oddProjector
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    inner Complex (suzukiLogRadiusLinearEvenProjector r v)
        (suzukiLogRadiusLinearOddProjector r v) = 0 := by
  have hreflect :
      inner Complex
          (suzukiLogRadiusLinearReflection r
            (suzukiLogRadiusLinearEvenProjector r v))
          (suzukiLogRadiusLinearReflection r
            (suzukiLogRadiusLinearOddProjector r v)) =
        inner Complex
          (suzukiLogRadiusLinearEvenProjector r v)
          (suzukiLogRadiusLinearOddProjector r v) :=
    suzukiLogRadiusLinearReflection_inner_map_map r
      (suzukiLogRadiusLinearEvenProjector r v)
      (suzukiLogRadiusLinearOddProjector r v)
  rw [suzukiLogRadiusLinearEvenProjector_reflection,
    suzukiLogRadiusLinearOddProjector_reflection] at hreflect
  change inner Complex
      (suzukiLogRadiusLinearEvenProjector r v).1.1
      (-(suzukiLogRadiusLinearOddProjector r v).1.1) =
    inner Complex
      (suzukiLogRadiusLinearEvenProjector r v).1.1
      (suzukiLogRadiusLinearOddProjector r v).1.1 at hreflect
  rw [inner_neg_right] at hreflect
  change inner Complex
      (suzukiLogRadiusLinearEvenProjector r v).1.1
      (suzukiLogRadiusLinearOddProjector r v).1.1 = 0
  exact CharZero.neg_eq_self_iff.mp hreflect

/-- Exact Pythagorean splitting of the endpoint Hilbert norm. -/
theorem suzukiLogRadiusLinear_norm_sq_even_odd_split
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    ‖v‖ ^ 2 =
      ‖suzukiLogRadiusLinearEvenProjector r v‖ ^ 2 +
        ‖suzukiLogRadiusLinearOddProjector r v‖ ^ 2 := by
  calc
    ‖v‖ ^ 2 =
        ‖suzukiLogRadiusLinearEvenProjector r v +
          suzukiLogRadiusLinearOddProjector r v‖ ^ 2 := by
      rw [suzukiLogRadiusLinearEvenProjector_add_oddProjector]
    _ = ‖suzukiLogRadiusLinearEvenProjector r v‖ ^ 2 +
          ‖suzukiLogRadiusLinearOddProjector r v‖ ^ 2 := by
      simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
          _ _
          (inner_suzukiLogRadiusLinearEvenProjector_oddProjector r v)

/-- The endpoint even projector agrees with the ambient `L²` even
projector. -/
theorem suzukiLogRadiusLinearCompletionToL2_evenProjector
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearEvenProjector r v) =
      suzukiL2EvenProjector
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rw [suzukiLogRadiusLinearEvenProjector_apply,
    suzukiL2EvenProjector_apply, map_smul, map_add,
    suzukiLogRadiusLinearCompletionToL2_reflection]

/-- The endpoint odd projector agrees with the ambient `L²` odd
projector. -/
theorem suzukiLogRadiusLinearCompletionToL2_oddProjector
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiLogRadiusLinearOddProjector r v) =
      suzukiL2OddProjector
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rw [suzukiLogRadiusLinearOddProjector_apply,
    suzukiL2OddProjector_apply, map_smul, map_sub,
    suzukiLogRadiusLinearCompletionToL2_reflection]

/-- Exact ambient `L²` norm splitting for every endpoint element. -/
theorem suzukiLogRadiusLinear_l2_norm_sq_even_odd_split
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    ‖suzukiLogRadiusLinearCompletionToL2 v‖ ^ 2 =
      ‖suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearEvenProjector r v)‖ ^ 2 +
        ‖suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearOddProjector r v)‖ ^ 2 := by
  rw [suzukiLogRadiusLinearCompletionToL2_evenProjector,
    suzukiLogRadiusLinearCompletionToL2_oddProjector]
  exact suzukiL2_norm_sq_even_odd_split
    (suzukiLogRadiusLinearCompletionToL2 v)

/-- The endpoint odd sector automatically lies in the interval zero-mean
subspace required by the receiving source domain. -/
theorem suzukiLogRadiusLinear_oddProjector_intervalMean_zero
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiL2IntervalMean r
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearOddProjector r v)) = 0 := by
  rw [suzukiLogRadiusLinearCompletionToL2_oddProjector]
  exact suzukiL2IntervalMean_oddProjector_zero r
    (suzukiLogRadiusLinearCompletionToL2 v)

/-- The endpoint even sector carries the full interval mean. -/
theorem suzukiLogRadiusLinear_evenProjector_intervalMean
    (r : Real) (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiL2IntervalMean r
        (suzukiLogRadiusLinearCompletionToL2
          (suzukiLogRadiusLinearEvenProjector r v)) =
      suzukiL2IntervalMean r
        (suzukiLogRadiusLinearCompletionToL2 v) := by
  rw [suzukiLogRadiusLinearCompletionToL2_evenProjector]
  exact suzukiL2IntervalMean_evenProjector r
    (suzukiLogRadiusLinearCompletionToL2 v)

/-- The finite symmetric-translation form is additive in its first input. -/
theorem suzukiL2FiniteTranslationEnergy_add_left
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u w v : SuzukiL2) :
    suzukiL2FiniteTranslationEnergy s coefficient shift (u + w) v =
      suzukiL2FiniteTranslationEnergy s coefficient shift u v +
        suzukiL2FiniteTranslationEnergy s coefficient shift w v := by
  unfold suzukiL2FiniteTranslationEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [suzukiL2SymmetricTranslationEnergy, map_add,
    inner_add_left]
  ring

/-- The finite symmetric-translation form is additive in its second input. -/
theorem suzukiL2FiniteTranslationEnergy_add_right
    {I : Type*} [DecidableEq I] (s : Finset I)
    (coefficient shift : I → Real) (u v w : SuzukiL2) :
    suzukiL2FiniteTranslationEnergy s coefficient shift u (v + w) =
      suzukiL2FiniteTranslationEnergy s coefficient shift u v +
        suzukiL2FiniteTranslationEnergy s coefficient shift u w := by
  unfold suzukiL2FiniteTranslationEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp [suzukiL2SymmetricTranslationEnergy, map_add,
    inner_add_right]
  ring

/-- The complete endpoint form is additive in its first input. -/
theorem suzukiLogRadiusLinearCompleteEnergy_add_left
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u w v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K (u + w) v =
      suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K u v +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K w v := by
  simp [suzukiLogRadiusLinearCompleteEnergy,
    suzukiL2FiniteRadiusRemainderEnergy,
    suzukiL2BoundedOperatorEnergy,
    suzukiL2FiniteTranslationEnergy_add_left,
    map_add, inner_add_left]
  ring

/-- The complete endpoint form is additive in its second input. -/
theorem suzukiLogRadiusLinearCompleteEnergy_add_right
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v w : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K u (v + w) =
      suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K u v +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K u w := by
  simp [suzukiLogRadiusLinearCompleteEnergy,
    suzukiL2FiniteRadiusRemainderEnergy,
    suzukiL2BoundedOperatorEnergy,
    suzukiL2FiniteTranslationEnergy_add_right,
    map_add, inner_add_right]
  ring

/-- The complete endpoint form changes sign under negation of its first
input. -/
theorem suzukiLogRadiusLinearCompleteEnergy_neg_left
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K (-u) v =
      -suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K u v := by
  have hadd :=
    suzukiLogRadiusLinearCompleteEnergy_add_left
      r s scalar coefficient shift K (-u) u v
  rw [neg_add_cancel] at hadd
  have hzero :
      suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K
            (0 : SuzukiLogRadiusLinearCompletion r) v = 0 := by
    have hzeroAdd :=
      suzukiLogRadiusLinearCompleteEnergy_add_left
        r s scalar coefficient shift K
          (0 : SuzukiLogRadiusLinearCompletion r) 0 v
    simp only [zero_add] at hzeroAdd
    linear_combination -hzeroAdd
  rw [hzero] at hadd
  exact eq_neg_of_add_eq_zero_left hadd.symm

/-- The complete endpoint form changes sign under negation of its second
input. -/
theorem suzukiLogRadiusLinearCompleteEnergy_neg_right
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (u v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K u (-v) =
      -suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K u v := by
  have hadd :=
    suzukiLogRadiusLinearCompleteEnergy_add_right
      r s scalar coefficient shift K u (-v) v
  rw [neg_add_cancel] at hadd
  have hzero :
      suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K u
            (0 : SuzukiLogRadiusLinearCompletion r) = 0 := by
    have hzeroAdd :=
      suzukiLogRadiusLinearCompleteEnergy_add_right
        r s scalar coefficient shift K u
          (0 : SuzukiLogRadiusLinearCompletion r) 0
    simp only [zero_add] at hzeroAdd
    linear_combination -hzeroAdd
  rw [hzero] at hadd
  exact eq_neg_of_add_eq_zero_left hadd.symm

/-- Exact complete-form parity splitting, conditional only on the missing
reflection-invariance law for the chosen remainder operator.  This isolates
the precise theorem required from the concrete Suzuki operator API. -/
theorem suzukiLogRadiusLinearCompleteEnergy_even_odd_split_of_reflectionInvariant
    {I : Type*} [DecidableEq I] (r : Real) (s : Finset I)
    (scalar : Real) (coefficient shift : I → Real)
    (K : SuzukiL2 →L[Complex] SuzukiL2)
    (hreflection : ∀ u v : SuzukiLogRadiusLinearCompletion r,
      suzukiLogRadiusLinearCompleteEnergy s scalar coefficient shift K
          (suzukiLogRadiusLinearReflection r u)
          (suzukiLogRadiusLinearReflection r v) =
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K u v)
    (v : SuzukiLogRadiusLinearCompletion r) :
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K v v =
      suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K
          (suzukiLogRadiusLinearEvenProjector r v)
          (suzukiLogRadiusLinearEvenProjector r v) +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K
          (suzukiLogRadiusLinearOddProjector r v)
          (suzukiLogRadiusLinearOddProjector r v) := by
  let e := suzukiLogRadiusLinearEvenProjector r v
  let o := suzukiLogRadiusLinearOddProjector r v
  have he : suzukiLogRadiusLinearReflection r e = e := by
    exact suzukiLogRadiusLinearEvenProjector_reflection r v
  have ho : suzukiLogRadiusLinearReflection r o = -o := by
    exact suzukiLogRadiusLinearOddProjector_reflection r v
  have hcrossEO := hreflection e o
  rw [he, ho,
    suzukiLogRadiusLinearCompleteEnergy_neg_right] at hcrossEO
  have hcrossEOzero :
      suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K e o = 0 :=
    CharZero.neg_eq_self_iff.mp hcrossEO
  have hcrossOE := hreflection o e
  rw [he, ho,
    suzukiLogRadiusLinearCompleteEnergy_neg_left] at hcrossOE
  have hcrossOEzero :
      suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K o e = 0 :=
    CharZero.neg_eq_self_iff.mp hcrossOE
  have hv : e + o = v := by
    exact suzukiLogRadiusLinearEvenProjector_add_oddProjector r v
  calc
    suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K v v =
      suzukiLogRadiusLinearCompleteEnergy
        s scalar coefficient shift K (e + o) (e + o) := by
          rw [hv]
    _ = (suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K e e +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K e o) +
      (suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K o e +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K o o) := by
          rw [suzukiLogRadiusLinearCompleteEnergy_add_left,
            suzukiLogRadiusLinearCompleteEnergy_add_right,
            suzukiLogRadiusLinearCompleteEnergy_add_right]
    _ = suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K e e +
        suzukiLogRadiusLinearCompleteEnergy
          s scalar coefficient shift K o o := by
          rw [hcrossEOzero, hcrossOEzero]
          ring

end

end M100
end Experiments
end RiemannHypothesisProject
