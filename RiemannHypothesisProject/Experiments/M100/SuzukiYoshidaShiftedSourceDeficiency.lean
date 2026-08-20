import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceEnergyVectors
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaUnboundedDifferential

/-!
# M100-DF6F deficiency vectors in the shifted source-energy completion

This module keeps Suzuki's deficiency vectors in the Hilbert completion
`H(S_(a,lambda))`.  It transfers the compactly supported smooth differential
to a densely defined operator on that completion and proves that the canonical
plus/minus Riesz vectors lie in its maximal adjoint domain with eigenvalues
`+i` and `-i`, respectively.  No interval-`L2` realization of either
deficiency vector is asserted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace ComplexConjugate LinearPMap

/-- The smooth differential as a complex-linear endomorphism of the compact
smooth core. -/
def suzukiSmoothCoreDifferentialLinearMap
    {a : Real} (ha : 0 < a) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiSmoothCoreLinearSubmodule a where
  toFun v :=
    ⟨(suzukiSmoothCoreDifferential ha
      (suzukiSmoothCoreLinearSubmoduleAsCore v)).1,
      (suzukiSmoothCoreDifferential ha
        (suzukiSmoothCoreLinearSubmoduleAsCore v)).2⟩
  map_add' u v := by
    apply Subtype.ext
    ext x
    change Complex.I * SchwartzMap.derivCLM Complex Complex (u.1 + v.1) x =
      Complex.I * SchwartzMap.derivCLM Complex Complex u.1 x +
        Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x
    rw [map_add]
    change Complex.I *
        (SchwartzMap.derivCLM Complex Complex u.1 x +
          SchwartzMap.derivCLM Complex Complex v.1 x) = _
    ring
  map_smul' c v := by
    apply Subtype.ext
    ext x
    change Complex.I * SchwartzMap.derivCLM Complex Complex (c • v.1) x =
      c * (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x)
    rw [map_smul]
    change Complex.I *
        (c * SchwartzMap.derivCLM Complex Complex v.1 x) = _
    ring

@[simp]
theorem suzukiSmoothCoreDifferentialLinearMap_asCore
    {a : Real} (ha : 0 < a)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiSmoothCoreDifferentialLinearMap ha v) =
      suzukiSmoothCoreDifferential ha
        (suzukiSmoothCoreLinearSubmoduleAsCore v) := by
  rfl

@[simp]
theorem suzukiSmoothCoreDifferentialZeroMeanLinearMap_apply_asCore
    {a : Real} (ha : 0 < a)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiSmoothCoreDifferentialZeroMeanLinearMap ha v =
      suzukiSmoothCoreDifferentialZeroMeanL2 ha
        (suzukiSmoothCoreLinearSubmoduleAsCore v) := by
  rfl

/-- Applying the smooth differential and then taking the global `L2`
pairing with a truncated exponential multiplies that pairing by `-i c`.
-/
theorem inner_suzukiFredholmExponentialL2_smoothCoreDifferential
    {a : Real} (ha : 0 < a) (c : Real) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiFredholmExponentialL2 ha c)
        (suzukiSmoothCoreToL2 (suzukiSmoothCoreDifferential ha v)) =
      -(Complex.I * (c : Complex)) *
        inner Complex (suzukiFredholmExponentialL2 ha c)
          (suzukiSmoothCoreToL2 v) := by
  rw [inner_suzukiFredholmExponentialL2_smoothCoreToL2,
    inner_suzukiFredholmExponentialL2_smoothCoreToL2]
  rw [show (∫ x in Set.Icc (-a) a,
      (Real.exp (c * x) : Complex) *
        (suzukiSmoothCoreDifferential ha v).1 x) =
      Complex.I * ∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) *
          SchwartzMap.derivCLM Complex Complex v.1 x by
    rw [show (fun x : Real =>
        (Real.exp (c * x) : Complex) *
          (suzukiSmoothCoreDifferential ha v).1 x) =
        fun x => Complex.I *
          ((Real.exp (c * x) : Complex) *
            SchwartzMap.derivCLM Complex Complex v.1 x) by
      funext x
      rw [suzukiSmoothCoreDifferential_apply]
      ring,
      MeasureTheory.integral_const_mul]]
  rw [setIntegral_exp_mul_deriv_eq ha
    (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩) c]
  ring

/-- The projected exponential forcing satisfies the deficiency recurrence
on the smooth differential graph. -/
theorem inner_suzukiFredholmExponentialForcing_secondDifferential
    {a : Real} (ha : 0 < a) (c : Real) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiFredholmExponentialForcing a c)
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha
          (suzukiSmoothCoreDifferential ha v)) =
      -(Complex.I * (c : Complex)) *
        inner Complex (suzukiFredholmExponentialForcing a c)
          (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) := by
  rw [inner_suzukiFredholmExponentialForcing_smoothCoreDifferential,
    inner_suzukiFredholmExponentialL2_smoothCoreDifferential,
    inner_suzukiFredholmExponentialForcing_smoothCoreDifferential]

/-- The shifted source-energy norm is bounded above by the ambient source
`L2` norm.  This is the continuity bridge that transfers smooth density to
the weaker completion norm. -/
theorem norm_suzukiShiftedSourceEnergyCoreToCompletion_le_l2
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    ‖suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda
        (⟨u⟩ : SuzukiShiftedSourceEnergyCore
          hsource hequation25 a ha lambda hlambda)‖ ≤
      Real.sqrt ‖suzukiSourceShiftedOperator a lambda‖ * ‖u‖ := by
  rw [norm_suzukiShiftedSourceEnergyCoreToCompletion]
  unfold suzukiSourceShiftedSeminorm
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have henergy :
        (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re ≤
          ‖suzukiSourceShiftedOperator a lambda‖ * ‖u‖ ^ 2 := by
      calc
      (inner Complex (suzukiSourceShiftedOperator a lambda u) u).re ≤
          ‖inner Complex (suzukiSourceShiftedOperator a lambda u) u‖ :=
        Complex.re_le_norm _
      _ ≤ ‖suzukiSourceShiftedOperator a lambda u‖ * ‖u‖ :=
        norm_inner_le_norm _ _
      _ ≤ (‖suzukiSourceShiftedOperator a lambda‖ * ‖u‖) * ‖u‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ u
      _ = ‖suzukiSourceShiftedOperator a lambda‖ * ‖u‖ ^ 2 := by ring
    have hsqrt :
        Real.sqrt ‖suzukiSourceShiftedOperator a lambda‖ ^ 2 =
          ‖suzukiSourceShiftedOperator a lambda‖ :=
      Real.sq_sqrt
        (norm_nonneg (suzukiSourceShiftedOperator a lambda))
    nlinarith

/-- Continuous inclusion of interval source `L2` into the shifted-energy
completion. -/
def suzukiSourceL2ToShiftedEnergyCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiFiniteIntervalZeroMeanL2 a →L[Complex]
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda :=
  ({
    toFun := fun u =>
      suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda
        (⟨u⟩ : SuzukiShiftedSourceEnergyCore
          hsource hequation25 a ha lambda hlambda)
    map_add' := by
      intro u v
      rw [← map_add]
      rfl
    map_smul' := by
      intro c u
      rw [← map_smul]
      rfl
  } : SuzukiFiniteIntervalZeroMeanL2 a →ₗ[Complex]
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda).mkContinuous
    (Real.sqrt ‖suzukiSourceShiftedOperator a lambda‖)
    (norm_suzukiShiftedSourceEnergyCoreToCompletion_le_l2
      hsource hequation25 a ha lambda hlambda)

@[simp]
theorem suzukiSourceL2ToShiftedEnergyCompletion_apply
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceL2ToShiftedEnergyCompletion
        hsource hequation25 a ha lambda hlambda u =
      suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda
        (⟨u⟩ : SuzukiShiftedSourceEnergyCore
          hsource hequation25 a ha lambda hlambda) := by
  rfl

/-- The source-`L2` inclusion has dense range in the shifted completion. -/
theorem denseRange_suzukiSourceL2ToShiftedEnergyCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    DenseRange (suzukiSourceL2ToShiftedEnergyCompletion
      hsource hequation25 a ha lambda hlambda) := by
  apply (denseRange_suzukiShiftedSourceEnergyCoreToCompletion
    hsource hequation25 a ha lambda hlambda).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨u.toL2, rfl⟩

/-- The smooth source differential embedded in the shifted completion. -/
def suzukiShiftedSourceDifferentialCoreLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda :=
  (suzukiSourceL2ToShiftedEnergyCompletion
    hsource hequation25 a ha lambda hlambda).toLinearMap.comp
      (suzukiSmoothCoreDifferentialZeroMeanLinearMap
        (suzukiDF6E_radius_pos ha))

/-- The second differential, regarded as the action on the smooth graph. -/
def suzukiShiftedSourceSecondDifferentialCoreLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda :=
  (suzukiShiftedSourceDifferentialCoreLinearMap
    hsource hequation25 a ha lambda hlambda).comp
      (suzukiSmoothCoreDifferentialLinearMap
        (suzukiDF6E_radius_pos ha))

@[simp]
theorem suzukiShiftedSourceDifferentialCoreLinearMap_apply
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiShiftedSourceDifferentialCoreLinearMap
        hsource hequation25 a ha lambda hlambda v =
      suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda
        (⟨suzukiSmoothCoreDifferentialZeroMeanLinearMap
            (suzukiDF6E_radius_pos ha) v⟩ :
          SuzukiShiftedSourceEnergyCore
            hsource hequation25 a ha lambda hlambda) := by
  rfl

@[simp]
theorem suzukiShiftedSourceSecondDifferentialCoreLinearMap_apply
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiShiftedSourceSecondDifferentialCoreLinearMap
        hsource hequation25 a ha lambda hlambda v =
      suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha lambda hlambda
        (⟨suzukiSmoothCoreDifferentialZeroMeanLinearMap
            (suzukiDF6E_radius_pos ha)
            (suzukiSmoothCoreDifferentialLinearMap
              (suzukiDF6E_radius_pos ha) v)⟩ :
          SuzukiShiftedSourceEnergyCore
            hsource hequation25 a ha lambda hlambda) := by
  rfl

/-- The smooth differential map is injective.  The inverse-Neumann energy
identity detects a zero differential by the `L2` norm of its primitive. -/
theorem injective_suzukiSmoothCoreDifferentialZeroMeanLinearMap
    {a : Real} (ha : 0 < a) :
    Function.Injective
      (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha) := by
  intro u v huv
  have hdiff :
      suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have henergy :=
    inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq ha
      (suzukiSmoothCoreLinearSubmoduleAsCore (u - v))
  change inner Complex
      (suzukiSourceKOperator a
        (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u - v)))
      (suzukiSmoothCoreDifferentialZeroMeanLinearMap ha (u - v)) = _
    at henergy
  rw [hdiff, map_zero, inner_zero_left] at henergy
  have henergyReal := congrArg Complex.re henergy
  simp only [Complex.zero_re, Complex.ofReal_re] at henergyReal
  have hglobal :
      suzukiSmoothCoreToL2
          (suzukiSmoothCoreLinearSubmoduleAsCore (u - v)) = 0 := by
    apply norm_eq_zero.mp
    exact (sq_eq_zero_iff).mp henergyReal.symm
  have hfinite :
      suzukiSmoothCoreFiniteIntervalL2LinearMap a (u - v) = 0 := by
    apply (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry a).injective
    have hzext :=
      suzukiFiniteIntervalL2ZeroExtension_smoothCore (u - v)
    rw [hglobal] at hzext
    have hzextLI :
        suzukiFiniteIntervalL2ZeroExtensionLinearIsometry a
            (suzukiSmoothCoreFiniteIntervalL2LinearMap a (u - v)) = 0 := by
      simpa [suzukiFiniteIntervalL2ZeroExtensionLinearIsometry] using hzext
    rw [hzextLI, map_zero]
  have huvzero : u - v = 0 :=
    (injective_suzukiSmoothCoreFiniteIntervalL2LinearMap a) (by
      simpa using hfinite)
  exact sub_eq_zero.mp huvzero

/-- The smooth differential remains injective after inclusion in the
shifted completion. -/
theorem injective_suzukiShiftedSourceDifferentialCoreLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    Function.Injective (suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha lambda hlambda) := by
  intro u v huv
  apply injective_suzukiSmoothCoreDifferentialZeroMeanLinearMap
    (suzukiDF6E_radius_pos ha)
  apply congrArg SuzukiShiftedSourceEnergyCore.toL2
  apply (suzukiShiftedSourceEnergyCoreToCompletion
    hsource hequation25 a ha lambda hlambda).injective
  exact huv

/-- Compactly supported smooth source differentials are dense in the
shifted completion. -/
theorem denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    DenseRange (suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha lambda hlambda) := by
  exact (denseRange_suzukiSourceL2ToShiftedEnergyCompletion
    hsource hequation25 a ha lambda hlambda).comp
      (suzukiSmoothDifferentialCoreDenseAt a
        (suzukiDF6E_radius_pos ha))
      (suzukiSourceL2ToShiftedEnergyCompletion
        hsource hequation25 a ha lambda hlambda).continuous

/-- The smooth source differential core identified with its injective image
inside the shifted completion. -/
def suzukiShiftedSourceDifferentialCoreRangeEquiv
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiSmoothCoreLinearSubmodule a ≃ₗ[Complex]
      LinearMap.range (suzukiShiftedSourceDifferentialCoreLinearMap
        hsource hequation25 a ha lambda hlambda) :=
  LinearEquiv.ofInjective
    (suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha lambda hlambda)
    (injective_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha lambda hlambda)

/-- Suzuki's transferred `i d/dx` as a densely defined operator on the
shifted source-energy completion.  Its domain is the embedded smooth source
differential core, and its action is the embedded second differential. -/
def suzukiShiftedSourceDifferentialPMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda →ₗ.[Complex]
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda where
  domain := LinearMap.range (suzukiShiftedSourceDifferentialCoreLinearMap
    hsource hequation25 a ha lambda hlambda)
  toFun :=
    (suzukiShiftedSourceSecondDifferentialCoreLinearMap
      hsource hequation25 a ha lambda hlambda).comp
        (suzukiShiftedSourceDifferentialCoreRangeEquiv
          hsource hequation25 a ha lambda hlambda).symm.toLinearMap

@[simp]
theorem suzukiShiftedSourceDifferentialPMap_core_apply
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda
        ⟨suzukiShiftedSourceDifferentialCoreLinearMap
            hsource hequation25 a ha lambda hlambda v,
          LinearMap.mem_range_self
            (suzukiShiftedSourceDifferentialCoreLinearMap
              hsource hequation25 a ha lambda hlambda) v⟩ =
      suzukiShiftedSourceSecondDifferentialCoreLinearMap
        hsource hequation25 a ha lambda hlambda v := by
  change suzukiShiftedSourceSecondDifferentialCoreLinearMap
      hsource hequation25 a ha lambda hlambda
      ((suzukiShiftedSourceDifferentialCoreRangeEquiv
        hsource hequation25 a ha lambda hlambda).symm
        ((suzukiShiftedSourceDifferentialCoreRangeEquiv
          hsource hequation25 a ha lambda hlambda) v)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The transferred completion differential has dense domain. -/
theorem dense_suzukiShiftedSourceDifferentialPMap_domain
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    Dense ((suzukiShiftedSourceDifferentialPMap
      hsource hequation25 a ha lambda hlambda).domain :
        Set (SuzukiShiftedSourceEnergyCompletion
          hsource hequation25 a ha lambda hlambda)) := by
  exact denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
    hsource hequation25 a ha lambda hlambda

/-- The plus Riesz vector satisfies the `+i` deficiency graph equation on
the smooth domain. -/
theorem inner_suzukiDF6FShiftedSourceEnergyPlusVector_secondDifferential
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    inner Complex
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceSecondDifferentialCoreLinearMap
          hsource hequation25 a ha lambda hlambda v) =
      -Complex.I * inner Complex
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceDifferentialCoreLinearMap
          hsource hequation25 a ha lambda hlambda v) := by
  rw [suzukiShiftedSourceSecondDifferentialCoreLinearMap_apply,
    suzukiShiftedSourceDifferentialCoreLinearMap_apply,
    inner_suzukiDF6FShiftedSourceEnergyPlusVector_core,
    inner_suzukiDF6FShiftedSourceEnergyPlusVector_core,
    suzukiFredholmPlusForcing_eq_exponential]
  simpa using
    (inner_suzukiFredholmExponentialForcing_secondDifferential
      (suzukiDF6E_radius_pos ha) 1
      (suzukiSmoothCoreLinearSubmoduleAsCore v))

/-- Minus-sign counterpart, with eigenvalue `-i`. -/
theorem inner_suzukiDF6FShiftedSourceEnergyMinusVector_secondDifferential
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    inner Complex
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceSecondDifferentialCoreLinearMap
          hsource hequation25 a ha lambda hlambda v) =
      Complex.I * inner Complex
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceDifferentialCoreLinearMap
          hsource hequation25 a ha lambda hlambda v) := by
  rw [suzukiShiftedSourceSecondDifferentialCoreLinearMap_apply,
    suzukiShiftedSourceDifferentialCoreLinearMap_apply,
    inner_suzukiDF6FShiftedSourceEnergyMinusVector_core,
    inner_suzukiDF6FShiftedSourceEnergyMinusVector_core,
    suzukiFredholmMinusForcing_eq_exponential]
  simpa using
    (inner_suzukiFredholmExponentialForcing_secondDifferential
      (suzukiDF6E_radius_pos ha) (-1)
      (suzukiSmoothCoreLinearSubmoduleAsCore v))

/-- Formal-adjoint pairing for the plus deficiency vector on the whole
smooth domain. -/
theorem inner_smul_plusVector_eq_inner_differential
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (x : (suzukiShiftedSourceDifferentialPMap
      hsource hequation25 a ha lambda hlambda).domain) :
    inner Complex
        (Complex.I • suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda)
        (x : SuzukiShiftedSourceEnergyCompletion
          hsource hequation25 a ha lambda hlambda) =
      inner Complex
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceDifferentialPMap
          hsource hequation25 a ha lambda hlambda x) := by
  rcases x.2 with ⟨v, hv⟩
  have hx : x =
      ⟨suzukiShiftedSourceDifferentialCoreLinearMap
          hsource hequation25 a ha lambda hlambda v,
        LinearMap.mem_range_self
          (suzukiShiftedSourceDifferentialCoreLinearMap
            hsource hequation25 a ha lambda hlambda) v⟩ :=
    Subtype.ext hv.symm
  rw [hx, suzukiShiftedSourceDifferentialPMap_core_apply,
    inner_smul_left]
  simpa using
    (inner_suzukiDF6FShiftedSourceEnergyPlusVector_secondDifferential
      hsource hequation25 a ha lambda hlambda v).symm

/-- Formal-adjoint pairing for the minus deficiency vector. -/
theorem inner_smul_minusVector_eq_inner_differential
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (x : (suzukiShiftedSourceDifferentialPMap
      hsource hequation25 a ha lambda hlambda).domain) :
    inner Complex
        ((-Complex.I) • suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda)
        (x : SuzukiShiftedSourceEnergyCompletion
          hsource hequation25 a ha lambda hlambda) =
      inner Complex
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceDifferentialPMap
          hsource hequation25 a ha lambda hlambda x) := by
  rcases x.2 with ⟨v, hv⟩
  have hx : x =
      ⟨suzukiShiftedSourceDifferentialCoreLinearMap
          hsource hequation25 a ha lambda hlambda v,
        LinearMap.mem_range_self
          (suzukiShiftedSourceDifferentialCoreLinearMap
            hsource hequation25 a ha lambda hlambda) v⟩ :=
    Subtype.ext hv.symm
  rw [hx, suzukiShiftedSourceDifferentialPMap_core_apply,
    inner_smul_left]
  simpa using
    (inner_suzukiDF6FShiftedSourceEnergyMinusVector_secondDifferential
      hsource hequation25 a ha lambda hlambda v).symm

/-- The canonical plus vector belongs to the maximal adjoint domain of the
completion differential. -/
theorem suzukiDF6FShiftedSourceEnergyPlusVector_mem_adjoint_domain
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda ∈
      (suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda)†.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  exact ⟨Complex.I • suzukiDF6FShiftedSourceEnergyPlusVector
      hsource hequation25 a ha lambda hlambda,
    inner_smul_plusVector_eq_inner_differential
      hsource hequation25 a ha lambda hlambda⟩

/-- The canonical minus vector belongs to the same maximal adjoint domain.
-/
theorem suzukiDF6FShiftedSourceEnergyMinusVector_mem_adjoint_domain
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda ∈
      (suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda)†.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  exact ⟨(-Complex.I) • suzukiDF6FShiftedSourceEnergyMinusVector
      hsource hequation25 a ha lambda hlambda,
    inner_smul_minusVector_eq_inner_differential
      hsource hequation25 a ha lambda hlambda⟩

/-- Exact `+i` maximal-adjoint eigenvalue equation in `H(S_(a,lambda))`. -/
theorem suzukiShiftedSourceDifferential_adjoint_plusVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    (suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda)†
        ⟨suzukiDF6FShiftedSourceEnergyPlusVector
            hsource hequation25 a ha lambda hlambda,
          suzukiDF6FShiftedSourceEnergyPlusVector_mem_adjoint_domain
            hsource hequation25 a ha lambda hlambda⟩ =
      Complex.I • suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda := by
  apply LinearPMap.adjoint_apply_eq
    (dense_suzukiShiftedSourceDifferentialPMap_domain
      hsource hequation25 a ha lambda hlambda)
  exact inner_smul_plusVector_eq_inner_differential
    hsource hequation25 a ha lambda hlambda

/-- Exact `-i` maximal-adjoint eigenvalue equation in `H(S_(a,lambda))`. -/
theorem suzukiShiftedSourceDifferential_adjoint_minusVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    (suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda)†
        ⟨suzukiDF6FShiftedSourceEnergyMinusVector
            hsource hequation25 a ha lambda hlambda,
          suzukiDF6FShiftedSourceEnergyMinusVector_mem_adjoint_domain
            hsource hequation25 a ha lambda hlambda⟩ =
      (-Complex.I) • suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda := by
  apply LinearPMap.adjoint_apply_eq
    (dense_suzukiShiftedSourceDifferentialPMap_domain
      hsource hequation25 a ha lambda hlambda)
  exact inner_smul_minusVector_eq_inner_differential
    hsource hequation25 a ha lambda hlambda

/-- Canonical plus deficiency vector bundled in the maximal adjoint domain.
-/
def suzukiShiftedSourcePlusAdjointVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    (suzukiShiftedSourceDifferentialPMap
      hsource hequation25 a ha lambda hlambda)†.domain :=
  ⟨suzukiDF6FShiftedSourceEnergyPlusVector
      hsource hequation25 a ha lambda hlambda,
    suzukiDF6FShiftedSourceEnergyPlusVector_mem_adjoint_domain
      hsource hequation25 a ha lambda hlambda⟩

/-- Canonical minus deficiency vector bundled in the maximal adjoint domain.
-/
def suzukiShiftedSourceMinusAdjointVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    (suzukiShiftedSourceDifferentialPMap
      hsource hequation25 a ha lambda hlambda)†.domain :=
  ⟨suzukiDF6FShiftedSourceEnergyMinusVector
      hsource hequation25 a ha lambda hlambda,
    suzukiDF6FShiftedSourceEnergyMinusVector_mem_adjoint_domain
      hsource hequation25 a ha lambda hlambda⟩

/-- Green's boundary form of the transferred completion differential on its
maximal adjoint domain. -/
def suzukiShiftedSourceAdjointBoundaryForm
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (x y : (suzukiShiftedSourceDifferentialPMap
      hsource hequation25 a ha lambda hlambda)†.domain) : Complex :=
  inner Complex
      ((suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda)† x)
      (y : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda) -
    inner Complex
      (x : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda)
      ((suzukiShiftedSourceDifferentialPMap
        hsource hequation25 a ha lambda hlambda)† y)

/-- The plus deficiency direction has the expected negative imaginary
boundary square. -/
theorem suzukiShiftedSourceAdjointBoundaryForm_plus_plus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    suzukiShiftedSourceAdjointBoundaryForm
        hsource hequation25 a ha lambda hlambda
        (suzukiShiftedSourcePlusAdjointVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourcePlusAdjointVector
          hsource hequation25 a ha lambda hlambda) =
      -(2 * Complex.I) * inner Complex
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda) := by
  unfold suzukiShiftedSourceAdjointBoundaryForm
    suzukiShiftedSourcePlusAdjointVector
  rw [suzukiShiftedSourceDifferential_adjoint_plusVector,
    inner_smul_left, inner_smul_right]
  simp only [Complex.conj_I]
  ring

/-- The minus deficiency direction has the opposite boundary square. -/
theorem suzukiShiftedSourceAdjointBoundaryForm_minus_minus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    suzukiShiftedSourceAdjointBoundaryForm
        hsource hequation25 a ha lambda hlambda
        (suzukiShiftedSourceMinusAdjointVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceMinusAdjointVector
          hsource hequation25 a ha lambda hlambda) =
      (2 * Complex.I) * inner Complex
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda) := by
  unfold suzukiShiftedSourceAdjointBoundaryForm
    suzukiShiftedSourceMinusAdjointVector
  rw [suzukiShiftedSourceDifferential_adjoint_minusVector,
    inner_smul_left, inner_smul_right]
  simp only [map_neg, Complex.conj_I]
  ring

/-- The two opposite deficiency directions are boundary-orthogonal. -/
theorem suzukiShiftedSourceAdjointBoundaryForm_plus_minus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    suzukiShiftedSourceAdjointBoundaryForm
        hsource hequation25 a ha lambda hlambda
        (suzukiShiftedSourcePlusAdjointVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceMinusAdjointVector
          hsource hequation25 a ha lambda hlambda) = 0 := by
  unfold suzukiShiftedSourceAdjointBoundaryForm
    suzukiShiftedSourcePlusAdjointVector
    suzukiShiftedSourceMinusAdjointVector
  rw [suzukiShiftedSourceDifferential_adjoint_plusVector,
    suzukiShiftedSourceDifferential_adjoint_minusVector,
    inner_smul_left, inner_smul_right]
  simp only [Complex.conj_I]
  ring

/-- Reverse mixed boundary pairing also vanishes. -/
theorem suzukiShiftedSourceAdjointBoundaryForm_minus_plus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    suzukiShiftedSourceAdjointBoundaryForm
        hsource hequation25 a ha lambda hlambda
        (suzukiShiftedSourceMinusAdjointVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourcePlusAdjointVector
          hsource hequation25 a ha lambda hlambda) = 0 := by
  unfold suzukiShiftedSourceAdjointBoundaryForm
    suzukiShiftedSourcePlusAdjointVector
    suzukiShiftedSourceMinusAdjointVector
  rw [suzukiShiftedSourceDifferential_adjoint_plusVector,
    suzukiShiftedSourceDifferential_adjoint_minusVector,
    inner_smul_left, inner_smul_right]
  simp only [map_neg, Complex.conj_I]
  ring

end

end RiemannHypothesisProject.Experiments.M100
