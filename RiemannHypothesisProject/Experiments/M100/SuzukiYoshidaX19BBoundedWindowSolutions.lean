import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceRepresentativeNormalization
import RiemannHypothesisProject.Experiments.M100.DilationEvolution
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaGammaOperatorBridge

/-!
# M100-X19B bounded-window source solutions

On the released interval `SuzukiDF6EInterval`, the DF6F source-dual estimate
constructs canonical weak solutions in Suzuki's shifted source-energy
completion.  This module proves that those solutions are uniquely determined
by their core equations and records an explicit norm estimate.  At the frozen
shift `lambda = 0`, the estimate is uniform in the radius, and the existing
representative normalization identifies the fixed gauge with Suzuki's printed
`exp x + i` and `exp (-x) - i` representatives.

Nothing here asserts interval-`L2` realizability.  That stronger statement is
neither needed for the completion-level weak solution nor compatible with the
existing two-sided reflection obstruction.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiX19BForcingCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- The extension of a source forcing functional has the same explicit
bounded-window estimate as its restriction to the dense energy core. -/
theorem norm_suzukiShiftedSourceEnergyForcingCLM_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5) :
    ‖suzukiShiftedSourceEnergyForcingCLM
        hsource hequation25 a ha lambda hlambda f hdual‖ ≤
      5 / Real.sqrt ((1 / 400000 : Real) - lambda) := by
  have hcore :
      ‖suzukiShiftedSourceEnergyCoreForcingCLM
          hsource hequation25 a ha lambda hlambda f hdual‖ ≤
        5 / Real.sqrt ((1 / 400000 : Real) - lambda) := by
    exact LinearMap.mkContinuous_norm_le _ (by positivity)
      (norm_suzukiShiftedSourceEnergyCoreForcingLinearMap_le_five
        hsource hequation25 ha hlambda f hdual)
  calc
    ‖suzukiShiftedSourceEnergyForcingCLM
        hsource hequation25 a ha lambda hlambda f hdual‖ ≤
        (1 : Real) *
          ‖suzukiShiftedSourceEnergyCoreForcingCLM
            hsource hequation25 a ha lambda hlambda f hdual‖ := by
      exact ContinuousLinearMap.opNorm_extend_le
        (f := suzukiShiftedSourceEnergyCoreForcingCLM
          hsource hequation25 a ha lambda hlambda f hdual)
        (e := (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda).toContinuousLinearMap)
        (N := 1)
        (denseRange_suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda)
        (fun u => by simp)
    _ ≤ (1 : Real) *
        (5 / Real.sqrt ((1 / 400000 : Real) - lambda)) := by
      exact mul_le_mul_of_nonneg_left hcore zero_le_one
    _ = 5 / Real.sqrt ((1 / 400000 : Real) - lambda) := one_mul _

/-- Quantitative existence estimate for the Riesz weak solution. -/
theorem norm_suzukiShiftedSourceEnergyRieszVector_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5) :
    ‖suzukiShiftedSourceEnergyRieszVector
        hsource hequation25 a ha lambda hlambda f hdual‖ ≤
      5 / Real.sqrt ((1 / 400000 : Real) - lambda) := by
  change
    ‖(InnerProductSpace.toDual Complex
      (SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda)).symm
        (suzukiShiftedSourceEnergyForcingCLM
          hsource hequation25 a ha lambda hlambda f hdual)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact norm_suzukiShiftedSourceEnergyForcingCLM_le
    hsource hequation25 a ha lambda hlambda f hdual

/-- A completion vector satisfying the source equation on the dense core is
the canonical Riesz solution. -/
theorem eq_suzukiShiftedSourceEnergyRieszVector_of_weakEquation_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (hweak : ∀ u : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda,
      inner Complex x
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha lambda hlambda u) =
        inner Complex f u.toL2) :
    x = suzukiShiftedSourceEnergyRieszVector
      hsource hequation25 a ha lambda hlambda f hdual := by
  apply ext_inner_right Complex
  intro y
  let p : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda → Prop := fun z =>
    inner Complex x z =
      inner Complex
        (suzukiShiftedSourceEnergyRieszVector
          hsource hequation25 a ha lambda hlambda f hdual) z
  apply DenseRange.induction_on (p := p)
    (denseRange_suzukiShiftedSourceEnergyCoreToCompletion
      hsource hequation25 a ha lambda hlambda) y
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro u
    exact (hweak u).trans
      (inner_suzukiShiftedSourceEnergyRieszVector_core
        hsource hequation25 a ha lambda hlambda f hdual u).symm

/-- The frozen X19B shift lies below the released coercivity threshold. -/
theorem suzukiX19B_zero_lt_shiftThreshold :
    (0 : Real) < 1 / 400000 := by
  norm_num

/-- The fixed-gauge plus solution at the frozen shift `lambda = 0`. -/
def suzukiX19BPlusSolution
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
  suzukiDF6FShiftedSourceEnergyPlusVector
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold

/-- The fixed-gauge minus solution at the frozen shift `lambda = 0`. -/
def suzukiX19BMinusSolution
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
  suzukiDF6FShiftedSourceEnergyMinusVector
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold

/-- The frozen plus solution satisfies the exact source equation on the dense
energy core. -/
theorem inner_suzukiX19BPlusSolution_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold) :
    inner Complex (suzukiX19BPlusSolution hsource hequation25 a ha)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
      inner Complex (suzukiFredholmPlusForcing a) u.toL2 := by
  exact inner_suzukiDF6FShiftedSourceEnergyPlusVector_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u

/-- The frozen minus solution satisfies the exact source equation on the dense
energy core. -/
theorem inner_suzukiX19BMinusSolution_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold) :
    inner Complex (suzukiX19BMinusSolution hsource hequation25 a ha)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
      inner Complex (suzukiFredholmMinusForcing a) u.toL2 := by
  exact inner_suzukiDF6FShiftedSourceEnergyMinusVector_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u

/-- A rational envelope for the frozen-shift Riesz constant. -/
theorem suzukiX19B_rieszConstant_le_fourThousand :
    5 / Real.sqrt (1 / 400000 : Real) ≤ 4000 := by
  have hsqrt_pos : 0 < Real.sqrt (1 / 400000 : Real) :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt_lower :
      (1 / 800 : Real) ≤ Real.sqrt (1 / 400000 : Real) := by
    rw [← Real.sqrt_sq (by norm_num : (0 : Real) ≤ 1 / 800)]
    exact Real.sqrt_le_sqrt (by norm_num)
  calc
    5 / Real.sqrt (1 / 400000 : Real) ≤ 5 / (1 / 800 : Real) := by
      rw [div_le_div_iff_of_pos_left (by norm_num) hsqrt_pos (by norm_num)]
      exact hsqrt_lower
    _ = 4000 := by norm_num

/-- Uniform plus-solution bound on the whole released radius interval. -/
theorem norm_suzukiX19BPlusSolution_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    ‖suzukiX19BPlusSolution hsource hequation25 a ha‖ ≤
      5 / Real.sqrt (1 / 400000 : Real) := by
  simpa [suzukiX19BPlusSolution,
    suzukiDF6FShiftedSourceEnergyPlusVector] using
    (norm_suzukiShiftedSourceEnergyRieszVector_le
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
        (suzukiFredholmPlusForcing a)
        (suzukiSourceKDualBoundAt_fredholmPlus_five ha))

/-- Uniform minus-solution bound on the whole released radius interval. -/
theorem norm_suzukiX19BMinusSolution_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    ‖suzukiX19BMinusSolution hsource hequation25 a ha‖ ≤
      5 / Real.sqrt (1 / 400000 : Real) := by
  simpa [suzukiX19BMinusSolution,
    suzukiDF6FShiftedSourceEnergyMinusVector] using
    (norm_suzukiShiftedSourceEnergyRieszVector_le
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
        (suzukiFredholmMinusForcing a)
        (suzukiSourceKDualBoundAt_fredholmMinus_five ha))

/-- Coarse rational plus-solution bound, convenient for downstream compactness
arguments. -/
theorem norm_suzukiX19BPlusSolution_le_fourThousand
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    ‖suzukiX19BPlusSolution hsource hequation25 a ha‖ ≤ 4000 :=
  (norm_suzukiX19BPlusSolution_le hsource hequation25 a ha).trans
    suzukiX19B_rieszConstant_le_fourThousand

/-- Coarse rational minus-solution bound, convenient for downstream
compactness arguments. -/
theorem norm_suzukiX19BMinusSolution_le_fourThousand
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    ‖suzukiX19BMinusSolution hsource hequation25 a ha‖ ≤ 4000 :=
  (norm_suzukiX19BMinusSolution_le hsource hequation25 a ha).trans
    suzukiX19B_rieszConstant_le_fourThousand

/-- The plus weak equation uniquely selects the frozen-shift solution. -/
theorem eq_suzukiX19BPlusSolution_of_weakEquation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    (hweak : ∀ u : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      inner Complex x
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
        inner Complex (suzukiFredholmPlusForcing a) u.toL2) :
    x = suzukiX19BPlusSolution hsource hequation25 a ha := by
  exact eq_suzukiShiftedSourceEnergyRieszVector_of_weakEquation_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiFredholmPlusForcing a)
      (suzukiSourceKDualBoundAt_fredholmPlus_five ha) x hweak

/-- The minus weak equation uniquely selects the frozen-shift solution. -/
theorem eq_suzukiX19BMinusSolution_of_weakEquation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    (hweak : ∀ u : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      inner Complex x
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
        inner Complex (suzukiFredholmMinusForcing a) u.toL2) :
    x = suzukiX19BMinusSolution hsource hequation25 a ha := by
  exact eq_suzukiShiftedSourceEnergyRieszVector_of_weakEquation_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiFredholmMinusForcing a)
      (suzukiSourceKDualBoundAt_fredholmMinus_five ha) x hweak

/-- The fixed-gauge plus solution has Suzuki's printed ambient
representative. -/
theorem suzukiX19BPlusSolution_printedRepresentative
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiShiftedSourceEnergyAmbientRepresentativeAt
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BPlusSolution hsource hequation25 a ha)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)) := by
  exact suzukiShiftedSourceEnergyPlusVector_printedRepresentative
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold

/-- The fixed-gauge minus solution has Suzuki's printed ambient
representative. -/
theorem suzukiX19BMinusSolution_printedRepresentative
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiShiftedSourceEnergyAmbientRepresentativeAt
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BMinusSolution hsource hequation25 a ha)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)) := by
  exact suzukiShiftedSourceEnergyMinusVector_printedRepresentative
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold

/-- On the compact spectral segment `z = i*c`, `|c| <= 1`, every projected
exponential forcing has the same endpoint-uniform `L2` majorant as the two
anchor forcings. -/
theorem norm_suzukiFredholmExponentialL2_le_uniform_of_abs_le_one
    {a c : Real} (ha : a ∈ SuzukiDF6EInterval) (hc : |c| ≤ 1) :
    ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c‖ ≤
      suzukiDF6FUniformFredholmBound := by
  have hlocal := norm_suzukiFredholmExponentialL2_le
    (suzukiDF6E_radius_pos ha) c
  apply hlocal.trans
  unfold suzukiDF6FUniformFredholmBound
  have hca : |c| * a ≤ suzukiProjectAStar := by
    calc
      |c| * a ≤ 1 * a :=
        mul_le_mul_of_nonneg_right hc (suzukiDF6E_radius_pos ha).le
      _ = a := one_mul a
      _ ≤ suzukiProjectAStar := ha.2
  have hexp : Real.exp (|c| * a) ≤ Real.exp suzukiProjectAStar :=
    Real.exp_le_exp.mpr hca
  have hsqrt : Real.sqrt (2 * a) ≤
      Real.sqrt (2 * suzukiProjectAStar) := by
    exact Real.sqrt_le_sqrt (by linarith [ha.2])
  exact mul_le_mul hexp hsqrt (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- Uniform source-dual bound on the compact imaginary spectral segment. -/
theorem suzukiSourceKDualBoundAt_fredholmExponential_five_of_abs_le_one
    {a c : Real} (ha : a ∈ SuzukiDF6EInterval) (hc : |c| ≤ 1) :
    SuzukiSourceKDualBoundAt a (suzukiFredholmExponentialForcing a c) 5 := by
  intro u
  have hsourceBound := suzukiSourceKDualBoundAt_fredholmExponential
    (suzukiDF6E_radius_pos ha) c u
  have hcoefficient :
      |c| * ‖suzukiFredholmExponentialL2
          (suzukiDF6E_radius_pos ha) c‖ ≤ 5 := by
    calc
      |c| * ‖suzukiFredholmExponentialL2
          (suzukiDF6E_radius_pos ha) c‖ ≤
          1 * suzukiDF6FUniformFredholmBound := by
        exact mul_le_mul hc
          (norm_suzukiFredholmExponentialL2_le_uniform_of_abs_le_one ha hc)
          (norm_nonneg _) zero_le_one
      _ = suzukiDF6FUniformFredholmBound := one_mul _
      _ ≤ 5 := suzukiDF6FUniformFredholmBound_lt_five.le
  exact hsourceBound.trans
    (mul_le_mul_of_nonneg_right hcoefficient
      (suzukiSourceKSeminorm_nonneg a u))

/-- The X19B solution along the compact imaginary spectral segment
`z = i*c`, `|c| <= 1`.  Since `exp(-i*z*x) = exp(c*x)` on this segment, this
is the paper's projected exponential source family with a frozen gauge. -/
def suzukiX19BImaginarySegmentSolution
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (c : Real) (hc : |c| ≤ 1) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
  suzukiShiftedSourceEnergyRieszVector
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiFredholmExponentialForcing a c)
      (suzukiSourceKDualBoundAt_fredholmExponential_five_of_abs_le_one ha hc)

/-- Exact weak equation for every point of the compact imaginary spectral
segment. -/
theorem inner_suzukiX19BImaginarySegmentSolution_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (c : Real) (hc : |c| ≤ 1)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold) :
    inner Complex
        (suzukiX19BImaginarySegmentSolution
          hsource hequation25 a ha c hc)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
      inner Complex (suzukiFredholmExponentialForcing a c) u.toL2 := by
  exact inner_suzukiShiftedSourceEnergyRieszVector_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiFredholmExponentialForcing a c)
      (suzukiSourceKDualBoundAt_fredholmExponential_five_of_abs_le_one ha hc) u

/-- Radius- and spectral-parameter-uniform bound on the compact segment. -/
theorem norm_suzukiX19BImaginarySegmentSolution_le_fourThousand
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (c : Real) (hc : |c| ≤ 1) :
    ‖suzukiX19BImaginarySegmentSolution
        hsource hequation25 a ha c hc‖ ≤ 4000 := by
  have hbound := norm_suzukiShiftedSourceEnergyRieszVector_le
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiFredholmExponentialForcing a c)
      (suzukiSourceKDualBoundAt_fredholmExponential_five_of_abs_le_one ha hc)
  have hbound' :
      ‖suzukiX19BImaginarySegmentSolution
          hsource hequation25 a ha c hc‖ ≤
        5 / Real.sqrt (1 / 400000 : Real) := by
    simpa [suzukiX19BImaginarySegmentSolution] using hbound
  exact hbound'.trans suzukiX19B_rieszConstant_le_fourThousand

/-- The compact spectral family is uniquely selected by its weak source
equation. -/
theorem eq_suzukiX19BImaginarySegmentSolution_of_weakEquation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (c : Real) (hc : |c| ≤ 1)
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    (hweak : ∀ u : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      inner Complex x
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
        inner Complex (suzukiFredholmExponentialForcing a c) u.toL2) :
    x = suzukiX19BImaginarySegmentSolution
      hsource hequation25 a ha c hc := by
  exact eq_suzukiShiftedSourceEnergyRieszVector_of_weakEquation_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiFredholmExponentialForcing a c)
      (suzukiSourceKDualBoundAt_fredholmExponential_five_of_abs_le_one ha hc)
      x hweak

/-- The endpoint `c = 1`, equivalently `z = i`, is the plus anchor. -/
theorem suzukiX19BImaginarySegmentSolution_one_eq_plus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    suzukiX19BImaginarySegmentSolution
        hsource hequation25 a ha 1 (by norm_num) =
      suzukiX19BPlusSolution hsource hequation25 a ha := by
  symm
  apply eq_suzukiX19BImaginarySegmentSolution_of_weakEquation
  intro u
  rw [inner_suzukiX19BPlusSolution_core,
    suzukiFredholmPlusForcing_eq_exponential]

/-- The endpoint `c = -1`, equivalently `z = -i`, is the minus anchor. -/
theorem suzukiX19BImaginarySegmentSolution_neg_one_eq_minus
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    suzukiX19BImaginarySegmentSolution
        hsource hequation25 a ha (-1) (by norm_num) =
      suzukiX19BMinusSolution hsource hequation25 a ha := by
  symm
  apply eq_suzukiX19BImaginarySegmentSolution_of_weakEquation
  intro u
  rw [inner_suzukiX19BMinusSolution_core,
    suzukiFredholmMinusForcing_eq_exponential]

private theorem abs_exp_sub_one_le_abs_mul_exp_abs (t : Real) :
    |Real.exp t - 1| ≤ |t| * Real.exp |t| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (t : Complex) 1
  have h' :
      ‖Complex.exp (t : Complex) - 1‖ ≤ |t| * Real.exp |t| := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hnorm :
      ‖Complex.exp (t : Complex) - 1‖ = |Real.exp t - 1| := by
    rw [← Complex.ofReal_exp]
    norm_cast
  rwa [hnorm] at h'

/-- A fixed difference constant for real exponentials on the released radius
window. -/
def suzukiX19BExponentialDifferencePointConstant : Real :=
  Real.exp suzukiProjectAStar * suzukiProjectAStar *
    Real.exp (2 * suzukiProjectAStar)

theorem suzukiX19BExponentialDifferencePointConstant_nonneg :
    0 ≤ suzukiX19BExponentialDifferencePointConstant := by
  unfold suzukiX19BExponentialDifferencePointConstant
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le suzukiProjectAStar_pos.le)
    (Real.exp_pos _).le

/-- Uniform pointwise Lipschitz estimate for the real exponential family on
the compact `(a,c)` window. -/
theorem abs_exp_mul_sub_exp_mul_le_x19b_pointConstant
    {a c d x : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (hx : x ∈ Set.Icc (-a) a) :
    |Real.exp (c * x) - Real.exp (d * x)| ≤
      suzukiX19BExponentialDifferencePointConstant * |c - d| := by
  have hxabs : |x| ≤ a := (abs_le).2 hx
  have hcd : |c - d| ≤ 2 := by
    calc
      |c - d| ≤ |c| + |d| := abs_sub c d
      _ ≤ 2 := by linarith
  have hargLocal : |(c - d) * x| ≤ |c - d| * suzukiProjectAStar := by
    rw [abs_mul]
    gcongr
    exact hxabs.trans ha.2
  have harg : |(c - d) * x| ≤ 2 * suzukiProjectAStar :=
    hargLocal.trans (mul_le_mul_of_nonneg_right hcd suzukiProjectAStar_pos.le)
  have hdLocal : d * x ≤ suzukiProjectAStar := by
    calc
      d * x ≤ |d * x| := le_abs_self _
      _ = |d| * |x| := abs_mul d x
      _ ≤ 1 * suzukiProjectAStar := by
        exact mul_le_mul hd (hxabs.trans ha.2) (abs_nonneg x) zero_le_one
      _ = suzukiProjectAStar := one_mul _
  have hfactor : Real.exp (d * x) ≤ Real.exp suzukiProjectAStar :=
    Real.exp_le_exp.mpr hdLocal
  have htail := abs_exp_sub_one_le_abs_mul_exp_abs ((c - d) * x)
  have hid :
      Real.exp (c * x) - Real.exp (d * x) =
        Real.exp (d * x) * (Real.exp ((c - d) * x) - 1) := by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 1
    ring
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (d * x) * |Real.exp ((c - d) * x) - 1| ≤
        Real.exp suzukiProjectAStar *
          (|(c - d) * x| * Real.exp |(c - d) * x|) := by
      exact mul_le_mul hfactor htail (abs_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp suzukiProjectAStar *
        ((|c - d| * suzukiProjectAStar) *
          Real.exp (2 * suzukiProjectAStar)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul hargLocal (Real.exp_le_exp.mpr harg)
        (Real.exp_pos _).le
        (mul_nonneg (abs_nonneg _) suzukiProjectAStar_pos.le)
    _ = suzukiX19BExponentialDifferencePointConstant * |c - d| := by
      unfold suzukiX19BExponentialDifferencePointConstant
      ring

/-- The corresponding fixed `L2` Lipschitz constant on the compact radius
window. -/
def suzukiX19BExponentialL2DifferenceConstant : Real :=
  suzukiX19BExponentialDifferencePointConstant *
    Real.sqrt (2 * suzukiProjectAStar)

theorem suzukiX19BExponentialL2DifferenceConstant_nonneg :
    0 ≤ suzukiX19BExponentialL2DifferenceConstant := by
  unfold suzukiX19BExponentialL2DifferenceConstant
  exact mul_nonneg suzukiX19BExponentialDifferencePointConstant_nonneg
    (Real.sqrt_nonneg _)

/-- Quantitative `L2` continuity of the truncated exponential forcing,
uniformly in the released radius window. -/
theorem norm_suzukiFredholmExponentialL2_sub_le_x19b
    {a c d : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) :
    ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
        suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d‖ ≤
      suzukiX19BExponentialL2DifferenceConstant * |c - d| := by
  have hsqrt : 0 < Real.sqrt (2 * a) := by
    exact Real.sqrt_pos.2
      (mul_pos (by norm_num) (suzukiDF6E_radius_pos ha))
  have hbound :
      ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
          suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d‖ ≤
        (suzukiX19BExponentialDifferencePointConstant * |c - d| *
            Real.sqrt (2 * a)) *
          ‖suzukiYoshidaExponentialL2 a (suzukiDF6E_radius_pos ha) 0‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (c := suzukiX19BExponentialDifferencePointConstant * |c - d| *
        Real.sqrt (2 * a))
      (f := suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
        suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
      (g := suzukiYoshidaExponentialL2 a (suzukiDF6E_radius_pos ha) 0)
    filter_upwards [
      suzukiFredholmExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) c,
      suzukiFredholmExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) d,
      Lp.coeFn_sub
        (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c)
        (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d),
      suzukiYoshidaExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) 0] with x hcx hdx hsub hzero
    rw [hsub, Pi.sub_apply, hcx, hdx, hzero]
    by_cases hx : x ∈ Set.Icc (-a) a
    · rw [suzukiFredholmExponentialFunction,
        suzukiFredholmExponentialFunction,
        suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Set.indicator_of_mem hx]
      have hzeroNorm :
          ‖(((Real.sqrt (2 * a))⁻¹ : Complex) *
              Complex.exp
                (Complex.I *
                  (((0 : Int) : Complex) * (Real.pi : Complex) /
                    (a : Complex)) * (x : Complex)))‖ =
            (Real.sqrt (2 * a))⁻¹ := by
        have hsqrtA : 0 < Real.sqrt a :=
          Real.sqrt_pos.2 (suzukiDF6E_radius_pos ha)
        have hsqrtTwo : 0 < Real.sqrt 2 := by positivity
        simp [Real.norm_eq_abs, abs_of_pos hsqrtA,
          abs_of_pos hsqrtTwo]
      rw [hzeroNorm, mul_assoc, mul_inv_cancel₀ hsqrt.ne', mul_one]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact abs_exp_mul_sub_exp_mul_le_x19b_pointConstant ha hc hd hx
    · simp [suzukiFredholmExponentialFunction,
        suzukiYoshidaExponentialFunction, hx]
  have hlocal :
      ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
          suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d‖ ≤
        suzukiX19BExponentialDifferencePointConstant * |c - d| *
          Real.sqrt (2 * a) := by
    simpa [(orthonormal_suzukiYoshidaExponentialL2
      (suzukiDF6E_radius_pos ha)).norm_eq_one] using hbound
  calc
    ‖suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
        suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d‖ ≤
        suzukiX19BExponentialDifferencePointConstant * |c - d| *
          Real.sqrt (2 * a) := hlocal
    _ ≤ suzukiX19BExponentialDifferencePointConstant * |c - d| *
        Real.sqrt (2 * suzukiProjectAStar) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by linarith [ha.2]))
        (mul_nonneg suzukiX19BExponentialDifferencePointConstant_nonneg
          (abs_nonneg _))
    _ = suzukiX19BExponentialL2DifferenceConstant * |c - d| := by
      unfold suzukiX19BExponentialL2DifferenceConstant
      ring

/-- Uniform Lipschitz constant for the projected exponential forcing in the
source-dual norm.  The first summand controls the moving exponential and the
second controls the spectral coefficient created by integration by parts. -/
def suzukiX19BSourceDifferenceConstant : Real :=
  suzukiX19BExponentialL2DifferenceConstant +
    suzukiDF6FUniformFredholmBound

theorem suzukiX19BSourceDifferenceConstant_nonneg :
    0 ≤ suzukiX19BSourceDifferenceConstant := by
  unfold suzukiX19BSourceDifferenceConstant
  exact add_nonneg suzukiX19BExponentialL2DifferenceConstant_nonneg
    suzukiDF6FUniformFredholmBound_pos.le

/-- Quantitative source-dual continuity of the projected exponential forcing
on the compact imaginary spectral segment. -/
theorem suzukiSourceKDualBoundAt_fredholmExponential_sub_x19b
    {a c d : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) :
    SuzukiSourceKDualBoundAt a
      (suzukiFredholmExponentialForcing a c -
        suzukiFredholmExponentialForcing a d)
      (suzukiX19BSourceDifferenceConstant * |c - d|) := by
  apply suzukiSourceKDualBoundAt_of_smoothCore
    (suzukiDF6E_radius_pos ha)
  intro v
  rw [inner_sub_left,
    inner_suzukiFredholmExponentialForcing_smoothCoreDifferential
      (suzukiDF6E_radius_pos ha) c v,
    inner_suzukiFredholmExponentialForcing_smoothCoreDifferential
      (suzukiDF6E_radius_pos ha) d v]
  have hdiffPair :
      ‖inner Complex
          (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
            suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
          (suzukiSmoothCoreToL2 v)‖ ≤
        (suzukiX19BExponentialL2DifferenceConstant * |c - d|) *
          ‖suzukiSmoothCoreToL2 v‖ := by
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (norm_suzukiFredholmExponentialL2_sub_le_x19b ha hc hd)
        (norm_nonneg _))
  have hdPair :
      ‖inner Complex
          (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
          (suzukiSmoothCoreToL2 v)‖ ≤
        suzukiDF6FUniformFredholmBound *
          ‖suzukiSmoothCoreToL2 v‖ := by
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (norm_suzukiFredholmExponentialL2_le_uniform_of_abs_le_one ha hd)
        (norm_nonneg _))
  have halgebra :
      -(Complex.I * (c : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c)
            (suzukiSmoothCoreToL2 v) -
        (-(Complex.I * (d : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v)) =
      -(Complex.I * (c : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
              suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v) -
        (Complex.I * ((c - d : Real) : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v) := by
    rw [inner_sub_left, Complex.ofReal_sub]
    ring
  have hcCoefficientNorm :
      ‖-(Complex.I * (c : Complex))‖ = |c| := by
    simp [Real.norm_eq_abs]
  have hcdCoefficientNorm :
      ‖Complex.I * ((c - d : Real) : Complex)‖ = |c - d| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
  rw [halgebra]
  calc
    ‖-(Complex.I * (c : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
              suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v) -
        (Complex.I * ((c - d : Real) : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v)‖ ≤
        ‖-(Complex.I * (c : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
              suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v)‖ +
        ‖(Complex.I * ((c - d : Real) : Complex)) *
          inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v)‖ := norm_sub_le _ _
    _ = |c| *
          ‖inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) c -
              suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v)‖ +
        |c - d| *
          ‖inner Complex
            (suzukiFredholmExponentialL2 (suzukiDF6E_radius_pos ha) d)
            (suzukiSmoothCoreToL2 v)‖ := by
      rw [norm_mul, hcCoefficientNorm, norm_mul, hcdCoefficientNorm]
    _ ≤ |c| *
          ((suzukiX19BExponentialL2DifferenceConstant * |c - d|) *
            ‖suzukiSmoothCoreToL2 v‖) +
        |c - d| *
          (suzukiDF6FUniformFredholmBound *
            ‖suzukiSmoothCoreToL2 v‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdiffPair (abs_nonneg c))
        (mul_le_mul_of_nonneg_left hdPair (abs_nonneg (c - d)))
    _ ≤ 1 *
          ((suzukiX19BExponentialL2DifferenceConstant * |c - d|) *
            ‖suzukiSmoothCoreToL2 v‖) +
        |c - d| *
          (suzukiDF6FUniformFredholmBound *
            ‖suzukiSmoothCoreToL2 v‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hc
          (mul_nonneg
            (mul_nonneg suzukiX19BExponentialL2DifferenceConstant_nonneg
              (abs_nonneg (c - d)))
            (norm_nonneg _)))
        (le_refl _)
    _ = (suzukiX19BSourceDifferenceConstant * |c - d|) *
        ‖suzukiSmoothCoreToL2 v‖ := by
      unfold suzukiX19BSourceDifferenceConstant
      ring

/-- Lipschitz constant for the completion-valued solution family at the
frozen shift. -/
def suzukiX19BSolutionDifferenceConstant : Real :=
  suzukiX19BSourceDifferenceConstant /
    Real.sqrt (1 / 400000 : Real)

theorem suzukiX19BSolutionDifferenceConstant_nonneg :
    0 ≤ suzukiX19BSolutionDifferenceConstant := by
  unfold suzukiX19BSolutionDifferenceConstant
  exact div_nonneg suzukiX19BSourceDifferenceConstant_nonneg
    (Real.sqrt_nonneg _)

/-- The canonical weak solutions vary Lipschitz-continuously with the
imaginary spectral parameter, uniformly in the released radius window. -/
theorem norm_suzukiX19BImaginarySegmentSolution_sub_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (c d : Real) (hc : |c| ≤ 1) (hd : |d| ≤ 1) :
    ‖suzukiX19BImaginarySegmentSolution
          hsource hequation25 a ha c hc -
        suzukiX19BImaginarySegmentSolution
          hsource hequation25 a ha d hd‖ ≤
      suzukiX19BSolutionDifferenceConstant * |c - d| := by
  let y : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
    suzukiX19BImaginarySegmentSolution
        hsource hequation25 a ha c hc -
      suzukiX19BImaginarySegmentSolution
        hsource hequation25 a ha d hd
  let B : Real := suzukiX19BSolutionDifferenceConstant * |c - d|
  have hsqrt : 0 < Real.sqrt (1 / 400000 : Real) := by positivity
  have hdual :=
    suzukiSourceKDualBoundAt_fredholmExponential_sub_x19b ha hc hd
  have hcore : ∀ u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      ‖inner Complex y
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u)‖ ≤
        B * ‖suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0
            suzukiX19B_zero_lt_shiftThreshold u‖ := by
    intro u
    have hcompare := suzukiDF6F_sourceKSeminorm_le_shiftedSeminorm
      hsource hequation25 ha suzukiX19B_zero_lt_shiftThreshold u.toL2
    have hcompare' :
        Real.sqrt (1 / 400000 : Real) *
            suzukiSourceKSeminorm a u.toL2 ≤
          ‖suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u‖ := by
      rw [← norm_suzukiShiftedSourceEnergyCore u] at hcompare
      simpa using hcompare
    have hscale :
        (suzukiX19BSourceDifferenceConstant * |c - d|) *
            suzukiSourceKSeminorm a u.toL2 ≤
          B * ‖suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u‖ := by
      calc
        (suzukiX19BSourceDifferenceConstant * |c - d|) *
            suzukiSourceKSeminorm a u.toL2 =
            B * (Real.sqrt (1 / 400000 : Real) *
              suzukiSourceKSeminorm a u.toL2) := by
          dsimp only [B]
          unfold suzukiX19BSolutionDifferenceConstant
          field_simp
        _ ≤ B * ‖suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u‖ := by
          exact mul_le_mul_of_nonneg_left hcompare'
            (mul_nonneg suzukiX19BSolutionDifferenceConstant_nonneg
              (abs_nonneg (c - d)))
    calc
      ‖inner Complex y
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u)‖ =
          ‖inner Complex
            (suzukiFredholmExponentialForcing a c -
              suzukiFredholmExponentialForcing a d) u.toL2‖ := by
        dsimp only [y]
        rw [inner_sub_left,
          inner_suzukiX19BImaginarySegmentSolution_core,
          inner_suzukiX19BImaginarySegmentSolution_core,
          inner_sub_left]
      _ ≤ (suzukiX19BSourceDifferenceConstant * |c - d|) *
          suzukiSourceKSeminorm a u.toL2 := hdual u.toL2
      _ ≤ B * ‖suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0
            suzukiX19B_zero_lt_shiftThreshold u‖ := hscale
  have hall : ∀ z : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      ‖inner Complex y z‖ ≤ B * ‖z‖ := by
    intro z
    let p : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold → Prop :=
      fun w => ‖inner Complex y w‖ ≤ B * ‖w‖
    apply DenseRange.induction_on (p := p)
      (denseRange_suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold) z
    · apply isClosed_le
      · fun_prop
      · fun_prop
    · intro u
      exact hcore u
  have hself := hall y
  have hselfNorm : ‖inner Complex y y‖ = ‖y‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [hselfNorm] at hself
  have hy : ‖y‖ ≤ B := by
    by_cases hy0 : ‖y‖ = 0
    · rw [hy0]
      exact mul_nonneg suzukiX19BSolutionDifferenceConstant_nonneg
        (abs_nonneg (c - d))
    · have hypos : 0 < ‖y‖ :=
        lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
      nlinarith
  simpa [y, B] using hy

/-- The compact real parameter interval corresponding to `z = i*c`. -/
abbrev SuzukiX19BImaginarySegment := Set.Icc (-1 : Real) 1

/-- Fixed-radius canonical solution map on the compact imaginary segment. -/
def suzukiX19BImaginarySegmentSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiX19BImaginarySegment →
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
  fun c => suzukiX19BImaginarySegmentSolution
    hsource hequation25 a ha c.1 ((abs_le).2 c.2)

/-- The quantitative real constant packaged as a nonnegative Lipschitz
constant. -/
def suzukiX19BSolutionDifferenceNNReal : NNReal :=
  ⟨suzukiX19BSolutionDifferenceConstant,
    suzukiX19BSolutionDifferenceConstant_nonneg⟩

/-- The fixed-radius solution map is Lipschitz on the whole compact spectral
segment. -/
theorem lipschitzWith_suzukiX19BImaginarySegmentSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    LipschitzWith suzukiX19BSolutionDifferenceNNReal
      (suzukiX19BImaginarySegmentSolutionMap
        hsource hequation25 a ha) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro c d
  have h := norm_suzukiX19BImaginarySegmentSolution_sub_le
    hsource hequation25 a ha c.1 d.1 ((abs_le).2 c.2) ((abs_le).2 d.2)
  rw [show (suzukiX19BSolutionDifferenceNNReal : Real) =
    suzukiX19BSolutionDifferenceConstant by rfl]
  simpa [suzukiX19BImaginarySegmentSolutionMap,
    dist_eq_norm, Subtype.dist_eq, Real.dist_eq] using h

/-- In particular, the canonical fixed-radius solution family is continuous
in the spectral parameter. -/
theorem continuous_suzukiX19BImaginarySegmentSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    Continuous (suzukiX19BImaginarySegmentSolutionMap
      hsource hequation25 a ha) :=
  (lipschitzWith_suzukiX19BImaginarySegmentSolutionMap
    hsource hequation25 a ha).continuous

/-- The image of the compact spectral segment is compact in the shifted
source-energy completion. -/
theorem isCompact_range_suzukiX19BImaginarySegmentSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    IsCompact (Set.range (suzukiX19BImaginarySegmentSolutionMap
      hsource hequation25 a ha)) :=
  isCompact_range
    (continuous_suzukiX19BImaginarySegmentSolutionMap
      hsource hequation25 a ha)

/-! ## Two-dimensional complex spectral window -/

/-- The conjugated complex exponential whose first-slot Hilbert pairing is
the paper-normalized weight `exp (w*x)`. -/
def suzukiX19BComplexExponentialContinuous
    (a : Real) (w : Complex) : C(SuzukiFiniteInterval a, Complex) :=
  ⟨fun x => Complex.exp (conj w * (x.1 : Complex)), by fun_prop⟩

@[simp]
theorem suzukiX19BComplexExponentialContinuous_apply
    (a : Real) (w : Complex) (x : SuzukiFiniteInterval a) :
    suzukiX19BComplexExponentialContinuous a w x =
      Complex.exp (conj w * (x.1 : Complex)) := rfl

/-- Orthogonal projection of the complex exponential onto the closed
zero-mean source space. -/
def suzukiX19BComplexExponentialForcing
    (a : Real) (w : Complex) : SuzukiFiniteIntervalZeroMeanL2 a :=
  suzukiFiniteIntervalContinuousToZeroMeanL2 a
    (suzukiX19BComplexExponentialContinuous a w)

/-- The complex exponential, truncated to Suzuki's source interval. -/
def suzukiX19BComplexExponentialFunction
    (a : Real) (w : Complex) (x : Real) : Complex :=
  Set.indicator (Set.Icc (-a) a)
    (fun y => Complex.exp (conj w * (y : Complex))) x

theorem suzukiX19BComplexExponentialFunction_memLp
    {a : Real} (_ha : 0 < a) (w : Complex) :
    MemLp (suzukiX19BComplexExponentialFunction a w)
      (2 : ENNReal) (volume : Measure Real) := by
  unfold suzukiX19BComplexExponentialFunction
  rw [memLp_indicator_iff_restrict measurableSet_Icc]
  haveI : IsFiniteMeasure
      ((volume : Measure Real).restrict (Set.Icc (-a) a)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_Icc_lt_top : volume (Set.Icc (-a) a) < ⊤)⟩
  refine MemLp.of_bound (C := Real.exp (|w.re| * a)) (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (conj w * (x : Complex)).re = w.re * x := by simp
    _ ≤ |w.re * x| := le_abs_self _
    _ = |w.re| * |x| := abs_mul _ _
    _ ≤ |w.re| * a := by
      exact mul_le_mul_of_nonneg_left ((abs_le).2 hx) (abs_nonneg _)

/-- Global `L2` representative of the truncated complex exponential. -/
def suzukiX19BComplexExponentialL2
    {a : Real} (ha : 0 < a) (w : Complex) : SuzukiL2 :=
  (suzukiX19BComplexExponentialFunction_memLp ha w).toLp
    (suzukiX19BComplexExponentialFunction a w)

theorem suzukiX19BComplexExponentialL2_coeFn
    {a : Real} (ha : 0 < a) (w : Complex) :
    (suzukiX19BComplexExponentialL2 ha w : Real → Complex) =ᵐ[volume]
      suzukiX19BComplexExponentialFunction a w :=
  (suzukiX19BComplexExponentialFunction_memLp ha w).coeFn_toLp

/-- Projection leaves the pairing unchanged against a zero-mean vector. -/
theorem inner_suzukiX19BComplexExponentialForcing
    (a : Real) (w : Complex) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    inner Complex (suzukiX19BComplexExponentialForcing a w) u =
      inner Complex
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiX19BComplexExponentialContinuous a w))
        (u : SuzukiFiniteIntervalL2 a) := by
  change inner Complex
      ((SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiX19BComplexExponentialContinuous a w))) u = _
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right u _

/-- The global first-slot pairing has the paper-normalized exponential
`exp (w*x)`; the conjugation in the representative is forced by the Hilbert
space convention. -/
theorem inner_suzukiX19BComplexExponentialL2_smoothCoreToL2
    {a : Real} (ha : 0 < a) (w : Complex) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiX19BComplexExponentialL2 ha w)
        (suzukiSmoothCoreToL2 v) =
      ∫ x in Set.Icc (-a) a,
        Complex.exp (w * (x : Complex)) * v.1 x := by
  rw [MeasureTheory.L2.inner_def]
  have hExp := suzukiX19BComplexExponentialL2_coeFn ha w
  have hV : (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume]
      fun x => v.1 x := by
    simpa only [suzukiSmoothCoreToL2] using
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  have hpair :
      (fun x : Real => inner Complex
        ((suzukiX19BComplexExponentialL2 ha w : SuzukiL2) x)
        ((suzukiSmoothCoreToL2 v : SuzukiL2) x)) =ᵐ[volume]
      fun x => inner Complex (suzukiX19BComplexExponentialFunction a w x)
        (v.1 x) := by
    filter_upwards [hExp, hV] with x hxExp hxV
    rw [hxExp, hxV]
  rw [integral_congr_ae hpair]
  rw [show (fun x : Real =>
      inner Complex (suzukiX19BComplexExponentialFunction a w x) (v.1 x)) =
      (Set.Icc (-a) a).indicator
        (fun x => Complex.exp (w * (x : Complex)) * v.1 x) by
    funext x
    by_cases hx : x ∈ Set.Icc (-a) a
    · unfold suzukiX19BComplexExponentialFunction
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      simp only [RCLike.inner_apply, starRingEnd_apply]
      change v.1 x * conj (Complex.exp (conj w * (x : Complex))) =
        Complex.exp (w * (x : Complex)) * v.1 x
      rw [← Complex.exp_conj, map_mul, Complex.conj_conj,
        Complex.conj_ofReal]
      ring
    · simp [suzukiX19BComplexExponentialFunction, hx]]
  rw [MeasureTheory.integral_indicator measurableSet_Icc]

private theorem hasDerivAt_suzukiX19BComplexExpMul
    (w : Complex) (x : Real) :
    HasDerivAt (fun y : Real => Complex.exp (w * (y : Complex)))
      (w * Complex.exp (w * (x : Complex))) x := by
  have hlinear : HasDerivAt (fun y : Real => w * (y : Complex)) w x := by
    simpa using (((hasDerivAt_id (x : Complex)).const_mul w).comp_ofReal)
  have hexponential : HasDerivAt
      (fun y : Real => Complex.exp (w * (y : Complex)))
      (Complex.exp (w * (x : Complex)) * w) x :=
    (Complex.hasDerivAt_exp (w * (x : Complex))).comp x hlinear
  simpa only [mul_comm] using hexponential

private theorem suzukiX19BSchwartz_eq_zero_at_endpoints
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    v (-a) = 0 ∧ v a = 0 := by
  have hopen : IsOpen (Function.support v) := v.continuous.isOpen_support
  have hinterior : Function.support v ⊆ interior (Set.Icc (-a) a) :=
    (hopen.subset_interior_iff).2 hsupport
  constructor
  · by_contra hne
    have hmem := hinterior hne
    rw [interior_Icc] at hmem
    exact (lt_irrefl (-a)) hmem.1
  · by_contra hne
    have hmem := hinterior hne
    rw [interior_Icc] at hmem
    exact (lt_irrefl a) hmem.2

/-- Complex-exponential integration by parts with the boundary term removed
by the compact support of the source primitive. -/
theorem setIntegral_suzukiX19BComplexExp_mul_deriv_eq
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (w : Complex) :
    (∫ x in Set.Icc (-a) a,
        Complex.exp (w * (x : Complex)) *
          SchwartzMap.derivCLM Complex Complex v x) =
      -w * ∫ x in Set.Icc (-a) a,
        Complex.exp (w * (x : Complex)) * v x := by
  rcases suzukiX19BSchwartz_eq_zero_at_endpoints ha hsupport with
    ⟨hleft, hright⟩
  have hle : -a ≤ a := by linarith
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -a) (b := a)
    (u := fun x : Real => Complex.exp (w * (x : Complex)))
    (v := fun x : Real => v x)
    (u' := fun x : Real => w * Complex.exp (w * (x : Complex)))
    (v' := fun x : Real => SchwartzMap.derivCLM Complex Complex v x)
    (fun x _ => hasDerivAt_suzukiX19BComplexExpMul w x)
    (fun x _ => by
      simpa only [SchwartzMap.derivCLM_apply] using v.hasDerivAt x)
    ((by fun_prop : Continuous (fun x : Real =>
      w * Complex.exp (w * (x : Complex)))).intervalIntegrable _ _)
    ((SchwartzMap.derivCLM Complex Complex v).continuous.intervalIntegrable _ _)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  rw [hibp, hleft, hright]
  simp only [mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- Exact source-side differential identity for every complex spectral
coefficient. -/
theorem inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential
    {a : Real} (ha : 0 < a) (w : Complex) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiX19BComplexExponentialForcing a w)
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) =
      -(Complex.I * w) *
        inner Complex (suzukiX19BComplexExponentialL2 ha w)
          (suzukiSmoothCoreToL2 v) := by
  rw [inner_suzukiX19BComplexExponentialForcing]
  unfold suzukiSmoothCoreDifferentialZeroMeanL2
  change inner Complex
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiX19BComplexExponentialContinuous a w))
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)) = _
  unfold suzukiFiniteIntervalContinuousToL2
  rw [ContinuousMap.inner_toLp]
  rw [show (∫ x : SuzukiFiniteInterval a,
      (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v x) *
        (starRingEnd Complex)
          (suzukiX19BComplexExponentialContinuous a w x) ∂volume) =
      ∫ x in Set.Icc (-a) a,
        Complex.exp (w * (x : Complex)) *
          (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x) by
    rw [← MeasureTheory.integral_subtype measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    change (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x.1) *
        conj (Complex.exp (conj w * (x.1 : Complex))) =
      Complex.exp (w * (x.1 : Complex)) *
        (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x.1)
    rw [← Complex.exp_conj, map_mul, Complex.conj_conj,
      Complex.conj_ofReal]
    ring]
  rw [show (∫ x in Set.Icc (-a) a,
      Complex.exp (w * (x : Complex)) *
        (Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x)) =
      Complex.I * ∫ x in Set.Icc (-a) a,
        Complex.exp (w * (x : Complex)) *
          SchwartzMap.derivCLM Complex Complex v.1 x by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring]
  rw [setIntegral_suzukiX19BComplexExp_mul_deriv_eq ha
    (fun x hx => ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩) w]
  rw [inner_suzukiX19BComplexExponentialL2_smoothCoreToL2 ha w v]
  ring

/-- Enlarging the radius does not change the complex-exponential integral
against a smooth primitive supported in the smaller interval.  This is the
analytic radius-nesting identity behind the source weak equations. -/
theorem setIntegral_suzukiX19BComplexExp_mul_zeroExtension_eq
    {a b : Real} (hab : a ≤ b) (w : Complex) (v : SuzukiSmoothCore a) :
    (∫ x in Set.Icc (-b) b,
        Complex.exp (w * (x : Complex)) *
          (suzukiSmoothCoreZeroExtension hab v).1 x) =
      ∫ x in Set.Icc (-a) a,
        Complex.exp (w * (x : Complex)) * v.1 x := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
  · intro x hx
    exact ⟨(neg_le_neg hab).trans hx.1, hx.2.trans hab⟩
  · intro x hx
    have hvzero : v.1 x = 0 := by
      by_contra hne
      exact hx.2 ⟨(v.2 hne).1.le, (v.2 hne).2.le⟩
    simp [suzukiSmoothCoreZeroExtension_apply, hvzero]

/-- The global truncated-exponential pairing is exactly compatible with
smooth-core zero extension from a smaller released radius to a larger one. -/
theorem inner_suzukiX19BComplexExponentialL2_zeroExtension
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (w : Complex) (v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiX19BComplexExponentialL2 (ha.trans_le hab) w)
        (suzukiSmoothCoreToL2 (suzukiSmoothCoreZeroExtension hab v)) =
      inner Complex (suzukiX19BComplexExponentialL2 ha w)
        (suzukiSmoothCoreToL2 v) := by
  rw [inner_suzukiX19BComplexExponentialL2_smoothCoreToL2,
    inner_suzukiX19BComplexExponentialL2_smoothCoreToL2]
  exact setIntegral_suzukiX19BComplexExp_mul_zeroExtension_eq hab w v

/-- The projected complex source functional itself is radius-compatible on
the nested smooth differential core. -/
theorem inner_suzukiX19BComplexExponentialForcing_zeroExtension
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (w : Complex) (v : SuzukiSmoothCore a) :
    inner Complex (suzukiX19BComplexExponentialForcing b w)
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
          (suzukiSmoothCoreZeroExtension hab v)) =
      inner Complex (suzukiX19BComplexExponentialForcing a w)
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) := by
  rw [inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential,
    inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential,
    inner_suzukiX19BComplexExponentialL2_zeroExtension ha hab]

/-- A polarized finite-kernel pairing is unchanged when both source slots
are supported in the smaller interval.  This is the two-slot analytic form of
the local-energy radius cancellation. -/
theorem suzukiFiniteKernelPolarizationComplex_eq_of_support_subset
    {a b : Real} (hab : a ≤ b) (kernel : Real → Real)
    {u v : Real → Complex}
    (hu : Function.support u ⊆ Set.Icc (-a) a)
    (hv : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFiniteKernelPolarizationComplex kernel b u v =
      suzukiFiniteKernelPolarizationComplex kernel a u v := by
  unfold suzukiFiniteKernelPolarizationComplex
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (isCompact_suzukiFiniteSquare b).measurableSet
  · intro p hp
    exact ⟨⟨(neg_le_neg hab).trans hp.1.1, hp.1.2.trans hab⟩,
      ⟨(neg_le_neg hab).trans hp.2.1, hp.2.2.trans hab⟩⟩
  · intro p hp
    by_cases hx : p.1 ∈ Set.Icc (-a) a
    · have hy : p.2 ∉ Set.Icc (-a) a := by
        intro hy
        exact hp.2 ⟨hx, hy⟩
      have huy : u p.2 = 0 := by
        by_contra hne
        exact hy (hu hne)
      simp [suzukiKernelPolarizationIntegrand, huy]
    · have hvx : v p.1 = 0 := by
        by_contra hne
        exact hx (hv hne)
      simp [suzukiKernelPolarizationIntegrand, hvx]

/-- The full polarized `G_a` source pairing, not only its diagonal real part,
is exactly invariant when both smooth differentials are zero-extended to a
larger radius. -/
theorem inner_suzukiSourceGOperator_smoothCoreDifferentials_zeroExtension
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (u v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab u)))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
          (suzukiSmoothCoreZeroExtension hab v)) =
      inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanL2 ha u))
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) := by
  unfold suzukiSmoothCoreDifferentialZeroMeanL2
  rw [inner_suzukiSourceGOperator_continuous,
    inner_suzukiSourceGOperator_continuous]
  dsimp only [suzukiSmoothCoreDifferentialFiniteIntervalContinuous]
  rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
      continuous_suzukiScrewFunction
      (suzukiDifferential (suzukiSmoothCoreZeroExtension hab u).1).continuous
      (suzukiDifferential (suzukiSmoothCoreZeroExtension hab v).1).continuous,
    suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
      continuous_suzukiScrewFunction
      (suzukiDifferential u.1).continuous
      (suzukiDifferential v.1).continuous]
  rw [suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiScrewFunction
      (suzukiDifferential (suzukiSmoothCoreZeroExtension hab u).1).continuous
      (suzukiDifferential (suzukiSmoothCoreZeroExtension hab v).1).continuous,
    suzukiFiniteIntervalCoreOperatorPairingComplex_eq_polarization
      continuous_suzukiScrewFunction
      (suzukiDifferential u.1).continuous
      (suzukiDifferential v.1).continuous]
  congr 1
  apply suzukiFiniteKernelPolarizationComplex_eq_of_support_subset hab
  · exact support_suzukiDifferential_subset_Icc (fun x hx ↦
      ⟨(u.2 hx).1.le, (u.2 hx).2.le⟩)
  · exact support_suzukiDifferential_subset_Icc (fun x hx ↦
      ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)

/-- If a larger-radius smooth source is `G_b`-orthogonal to every embedded
smaller smooth differential, then the restriction of its uncompressed
`G_b`-image to the smaller interval has zero zero-mean projection.  Equivalently,
that restricted image is a constant modulo `L2`.  This is the exact analytic
characterization of the smooth energy-orthogonal complement; it does not
identify the source vector itself with a physically annular function. -/
theorem
    suzukiSourceGOperator_restriction_zeroMeanProjection_eq_zero_of_orthogonal
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    suzukiFiniteIntervalContinuousToZeroMeanL2 a
        { toFun := fun x : SuzukiFiniteInterval a =>
            suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
              (suzukiDifferential z.1) x.1
          continuous_toFun :=
            (continuous_suzukiFiniteIntervalCoreOperator
              continuous_suzukiScrewFunction
              (suzukiDifferential z.1).continuous).comp continuous_subtype_val } = 0 := by
  let restrictedG : C(SuzukiFiniteInterval a, Complex) :=
    { toFun := fun x =>
        suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) x.1
      continuous_toFun :=
        (continuous_suzukiFiniteIntervalCoreOperator
          continuous_suzukiScrewFunction
          (suzukiDifferential z.1).continuous).comp continuous_subtype_val }
  let g : SuzukiFiniteIntervalZeroMeanL2 a :=
    suzukiFiniteIntervalContinuousToZeroMeanL2 a restrictedG
  have hg : ∀ p : SuzukiSmoothCore a,
      inner Complex g (suzukiSmoothCoreDifferentialZeroMeanL2 ha p) = 0 := by
    intro p
    have hp := horth p
    unfold suzukiSmoothCoreDifferentialZeroMeanL2 at hp
    rw [inner_suzukiSourceGOperator_continuous] at hp
    have hpPair :
        suzukiFiniteIntervalContinuousOperatorPairingComplex
          suzukiScrewFunction continuous_suzukiScrewFunction b
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous z)
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
            (suzukiSmoothCoreZeroExtension hab p)) = 0 := by
      have hconj := congrArg conj hp
      simpa using hconj
    dsimp only [suzukiSmoothCoreDifferentialFiniteIntervalContinuous] at hpPair
    rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
        continuous_suzukiScrewFunction
        (suzukiDifferential z.1).continuous
        (suzukiDifferential
          (suzukiSmoothCoreZeroExtension hab p).1).continuous] at hpPair
    change suzukiFiniteIntervalCoreOperatorPairingComplex
        suzukiScrewFunction b (suzukiDifferential z.1)
          (suzukiDifferential p.1) = 0 at hpPair
    change inner Complex
        ((SuzukiFiniteIntervalZeroMeanSubspace a).orthogonalProjectionOnto
          (suzukiFiniteIntervalContinuousToL2 a restrictedG))
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha p) = 0
    rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
    change inner Complex
        (suzukiFiniteIntervalContinuousToL2 a restrictedG)
        (suzukiFiniteIntervalContinuousToL2 a
          (suzukiSmoothCoreDifferentialFiniteIntervalContinuous p)) = 0
    unfold suzukiFiniteIntervalContinuousToL2
    rw [ContinuousMap.inner_toLp]
    change (∫ x : SuzukiFiniteInterval a,
      suzukiDifferential p.1 x.1 * conj (restrictedG x)) = 0
    have hset :
        (∫ x in Set.Icc (-b) b,
          suzukiDifferential p.1 x *
            conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
              (suzukiDifferential z.1) x)) =
          ∫ x in Set.Icc (-a) a,
            suzukiDifferential p.1 x *
              conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
                (suzukiDifferential z.1) x) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc
      · intro x hx
        exact ⟨(neg_le_neg hab).trans hx.1, hx.2.trans hab⟩
      · intro x hx
        have hdp : suzukiDifferential p.1 x = 0 := by
          by_contra hne
          exact hx.2 ((support_suzukiDifferential_subset_Icc (fun y hy =>
            ⟨(p.2 hy).1.le, (p.2 hy).2.le⟩)) hne)
        simp [hdp]
    calc
      (∫ x : SuzukiFiniteInterval a,
          suzukiDifferential p.1 x.1 * conj (restrictedG x)) =
          ∫ x in Set.Icc (-a) a,
            suzukiDifferential p.1 x *
              conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
                (suzukiDifferential z.1) x) := by
        exact MeasureTheory.integral_subtype measurableSet_Icc
          (fun x : Real =>
            suzukiDifferential p.1 x *
              conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
                (suzukiDifferential z.1) x))
      _ = ∫ x in Set.Icc (-b) b,
          suzukiDifferential p.1 x *
            conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
              (suzukiDifferential z.1) x) := hset.symm
      _ = ∫ x in Set.Icc (-b) b,
            conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
                (suzukiDifferential z.1) x *
              conj (suzukiDifferential p.1 x)) := by
        apply integral_congr_ae
        filter_upwards with x
        simp [map_mul]
        ring
      _ = conj (∫ x in Set.Icc (-b) b,
            suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
                (suzukiDifferential z.1) x *
              conj (suzukiDifferential p.1 x)) := integral_conj
      _ = conj (suzukiFiniteIntervalCoreOperatorPairingComplex
            suzukiScrewFunction b (suzukiDifferential z.1)
              (suzukiDifferential p.1)) := rfl
      _ = 0 := by rw [hpPair, map_zero]
  have hall : ∀ q : SuzukiFiniteIntervalZeroMeanL2 a,
      inner Complex g q = 0 := by
    intro q
    apply DenseRange.induction_on
      (p := fun q : SuzukiFiniteIntervalZeroMeanL2 a => inner Complex g q = 0)
      (suzukiSmoothDifferentialCoreDenseAt a ha) q
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact hg
  have hself := hall g
  exact inner_self_eq_zero.mp hself

/-- A continuous interval function whose zero-mean projection vanishes is a
constant `L2` class.  Consequently its pairing with any continuous test is the
product of their interval means, divided by the interval length. -/
theorem
    inner_suzukiFiniteIntervalContinuousToL2_eq_meanProduct_of_projection_eq_zero
    {a : Real} (ha : 0 < a)
    (f q : C(SuzukiFiniteInterval a, Complex))
    (hf : suzukiFiniteIntervalContinuousToZeroMeanL2 a f = 0) :
    inner Complex
        (suzukiFiniteIntervalContinuousToL2 a f)
        (suzukiFiniteIntervalContinuousToL2 a q) =
      conj ((∫ x : SuzukiFiniteInterval a, f x ∂volume) / (2 * a)) *
        ∫ x : SuzukiFiniteInterval a, q x ∂volume := by
  let avg : Complex :=
    (∫ x : SuzukiFiniteInterval a, f x ∂volume) / (2 * a)
  let c : C(SuzukiFiniteInterval a, Complex) :=
    suzukiFiniteIntervalConstantContinuous a avg
  have hprojection :
      suzukiFiniteIntervalZeroMeanProjection a
          (suzukiFiniteIntervalContinuousToL2 a f) =
        suzukiFiniteIntervalZeroMeanProjection a
          (suzukiFiniteIntervalContinuousToL2 a c) := by
    change suzukiFiniteIntervalContinuousToZeroMeanL2 a f =
      suzukiFiniteIntervalContinuousToZeroMeanL2 a c
    rw [hf]
    exact (suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero a avg).symm
  have hmeasure :
      (volume : Measure (SuzukiFiniteInterval a)).real univ = 2 * a := by
    rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
      Real.volume_Icc]
    simp [sub_neg_eq_add, ha.le]
    ring
  have hmean :
      suzukiFiniteIntervalMeanCLM a
          (suzukiFiniteIntervalContinuousToL2 a f) =
        suzukiFiniteIntervalMeanCLM a
          (suzukiFiniteIntervalContinuousToL2 a c) := by
    rw [suzukiFiniteIntervalMeanCLM_continuous,
      suzukiFiniteIntervalMeanCLM_continuous]
    change (∫ x : SuzukiFiniteInterval a, f x ∂volume) =
      ∫ _x : SuzukiFiniteInterval a, avg ∂volume
    rw [integral_const, hmeasure]
    dsimp only [avg]
    rw [RCLike.real_smul_eq_coe_mul]
    change (∫ x : SuzukiFiniteInterval a, f x ∂volume) =
      ((2 * a : Real) : Complex) *
        ((∫ x : SuzukiFiniteInterval a, f x ∂volume) /
          (2 * (a : Complex)))
    have haC : ((a : Real) : Complex) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp [haC]
    push_cast
    ring
  have heq :
      suzukiFiniteIntervalContinuousToL2 a f =
        suzukiFiniteIntervalContinuousToL2 a c :=
    suzukiFiniteIntervalL2_eq_of_projection_eq_of_mean_eq hprojection hmean
  have hc :
      suzukiFiniteIntervalContinuousToL2 a c =
        avg • suzukiFiniteIntervalOneComplexL2 a := by
    rw [suzukiFiniteIntervalOneComplexL2, ← map_smul]
    congr 1
    ext x
    simp [c, suzukiFiniteIntervalConstantContinuous]
  rw [heq, hc, inner_smul_left,
    ← suzukiFiniteIntervalMeanCLM_apply,
    suzukiFiniteIntervalMeanCLM_continuous]

/-- Vanishing of the zero-mean projection of the interval restriction of a
globally continuous function forces genuine pointwise constancy on the whole
closed interval, including both endpoints. -/
theorem
    suzukiFiniteIntervalRestriction_eq_mean_of_projection_eq_zero
    {a : Real} (ha : 0 < a) (F : Real → Complex) (hF : Continuous F)
    (hf : suzukiFiniteIntervalContinuousToZeroMeanL2 a
      (suzukiFiniteIntervalRestriction a F hF) = 0) :
    ∀ x ∈ Set.Icc (-a) a,
      F x =
        (∫ y : SuzukiFiniteInterval a, F y.1 ∂volume) / (2 * a) := by
  let f : C(SuzukiFiniteInterval a, Complex) :=
    suzukiFiniteIntervalRestriction a F hF
  let avg : Complex :=
    (∫ x : SuzukiFiniteInterval a, f x ∂volume) / (2 * a)
  let c : C(SuzukiFiniteInterval a, Complex) :=
    suzukiFiniteIntervalConstantContinuous a avg
  have hprojection :
      suzukiFiniteIntervalZeroMeanProjection a
          (suzukiFiniteIntervalContinuousToL2 a f) =
        suzukiFiniteIntervalZeroMeanProjection a
          (suzukiFiniteIntervalContinuousToL2 a c) := by
    change suzukiFiniteIntervalContinuousToZeroMeanL2 a f =
      suzukiFiniteIntervalContinuousToZeroMeanL2 a c
    rw [hf]
    exact (suzukiFiniteIntervalContinuousToZeroMeanL2_const_eq_zero a avg).symm
  have hmeasure :
      (volume : Measure (SuzukiFiniteInterval a)).real univ = 2 * a := by
    rw [Measure.real, Measure.Subtype.volume_univ nullMeasurableSet_Icc,
      Real.volume_Icc]
    simp [sub_neg_eq_add, ha.le]
    ring
  have hmean :
      suzukiFiniteIntervalMeanCLM a
          (suzukiFiniteIntervalContinuousToL2 a f) =
        suzukiFiniteIntervalMeanCLM a
          (suzukiFiniteIntervalContinuousToL2 a c) := by
    rw [suzukiFiniteIntervalMeanCLM_continuous,
      suzukiFiniteIntervalMeanCLM_continuous]
    change (∫ x : SuzukiFiniteInterval a, f x ∂volume) =
      ∫ _x : SuzukiFiniteInterval a, avg ∂volume
    rw [integral_const, hmeasure]
    dsimp only [avg]
    rw [RCLike.real_smul_eq_coe_mul]
    change (∫ x : SuzukiFiniteInterval a, f x ∂volume) =
      ((2 * a : Real) : Complex) *
        ((∫ x : SuzukiFiniteInterval a, f x ∂volume) /
          (2 * (a : Complex)))
    have haC : ((a : Real) : Complex) ≠ 0 := by exact_mod_cast ha.ne'
    field_simp [haC]
    push_cast
    ring
  have heq :
      suzukiFiniteIntervalContinuousToL2 a f =
        suzukiFiniteIntervalContinuousToL2 a c :=
    suzukiFiniteIntervalL2_eq_of_projection_eq_of_mean_eq hprojection hmean
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  have hfCoe :
      (suzukiFiniteIntervalContinuousToL2 a f :
          SuzukiFiniteInterval a → Complex) =ᵐ[volume] f := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a)) f
  have hcCoe :
      (suzukiFiniteIntervalContinuousToL2 a c :
          SuzukiFiniteInterval a → Complex) =ᵐ[volume] c := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a)) c
  have heqCoe :
      (suzukiFiniteIntervalContinuousToL2 a f :
          SuzukiFiniteInterval a → Complex) =ᵐ[volume]
        (suzukiFiniteIntervalContinuousToL2 a c :
          SuzukiFiniteInterval a → Complex) := by
    rw [heq]
  have haeSubtype :
      (fun x : SuzukiFiniteInterval a ↦ F x.1) =ᵐ[volume]
        fun _x : SuzukiFiniteInterval a ↦ avg := by
    simpa [f, c, suzukiFiniteIntervalRestriction,
      suzukiFiniteIntervalConstantContinuous] using
        hfCoe.symm.trans (heqCoe.trans hcCoe)
  have haeReal :
      F =ᵐ[volume.restrict (Set.Icc (-a) a)] fun _x ↦ avg := by
    exact (ae_restrict_iff_subtype measurableSet_Icc).2 haeSubtype
  have hregular :
      Set.Icc (-a) a ⊆ closure (interior (Set.Icc (-a) a)) := by
    rw [interior_Icc, closure_Ioo (by linarith : -a ≠ a)]
  have hEqOn : Set.EqOn F (fun _x ↦ avg) (Set.Icc (-a) a) :=
    MeasureTheory.Measure.eqOn_of_ae_eq haeReal hF.continuousOn
      continuous_const.continuousOn hregular
  intro x hx
  simpa [f, avg, suzukiFiniteIntervalRestriction] using hEqOn hx

/-- Energy orthogonality makes the uncompressed `G_b` image pointwise equal
to its inner-window mean throughout the smaller closed interval.  Continuity
upgrades the preceding zero-projection statement from an `L2` identity and,
in particular, includes the two annular interface points. -/
theorem
    suzukiFiniteIntervalCoreOperator_eq_innerMean_of_orthogonal
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    ∀ x ∈ Set.Icc (-a) a,
      suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) x =
        (∫ y : SuzukiFiniteInterval a,
          suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
            (suzukiDifferential z.1) y.1 ∂volume) / (2 * a) := by
  let G : Real → Complex :=
    suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
      (suzukiDifferential z.1)
  have hG : Continuous G :=
    continuous_suzukiFiniteIntervalCoreOperator
      continuous_suzukiScrewFunction (suzukiDifferential z.1).continuous
  have hf :=
    suzukiSourceGOperator_restriction_zeroMeanProjection_eq_zero_of_orthogonal
      ha hab z horth
  change suzukiFiniteIntervalContinuousToZeroMeanL2 a
      (suzukiFiniteIntervalRestriction a G hG) = 0 at hf
  exact suzukiFiniteIntervalRestriction_eq_mean_of_projection_eq_zero
    ha G hG hf

/-- The centered `G_b` image vanishes at both interfaces of the physical
annulus.  These are the endpoint conditions needed to move the differential
off the primitive without reintroducing a trace term. -/
theorem
    suzukiFiniteIntervalCoreOperator_interfaceValues_eq_innerMean_of_orthogonal
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    let innerGMean : Complex :=
      (∫ y : SuzukiFiniteInterval a,
        suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) y.1 ∂volume) / (2 * a)
    suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) a = innerGMean ∧
      suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) (-a) = innerGMean := by
  dsimp only
  have hpoint :=
    suzukiFiniteIntervalCoreOperator_eq_innerMean_of_orthogonal
      ha hab z horth
  constructor
  · exact hpoint a ⟨neg_le_self ha.le, le_rfl⟩
  · exact hpoint (-a) ⟨le_rfl, neg_le_self ha.le⟩

/-- Inward dilation of a smooth primitive.  The extra factor `exp (-t)`
relative to the `L2`-normalized Burnol dilation makes its Suzuki differential
exactly the `L2`-normalized dilation of the original differential.  Its support
radius contracts from `b` to `b / exp t`. -/
def suzukiX19BInwardDilationSmoothCore
    {b : Real} (t : Real) (z : SuzukiSmoothCore b) :
    SuzukiSmoothCore (b / Real.exp t) := by
  let w : SchwartzLineTestFunction :=
    (Real.exp (-t) : Complex) • burnolDilation t z.1
  refine ⟨w, ?_⟩
  intro x hx
  have hdil : x ∈ Function.support (burnolDilation t z.1) := by
    rw [Function.mem_support]
    change (Real.exp (-t) : Complex) * burnolDilation t z.1 x ≠ 0 at hx
    exact (mul_ne_zero_iff_left (by exact_mod_cast Real.exp_ne_zero (-t))).mp hx
  have hscaled := z.2 ((mem_support_burnolDilation_iff t x z.1).mp hdil)
  constructor
  · rw [← neg_div]
    apply (div_lt_iff₀ (Real.exp_pos t)).2
    simpa [mul_comm] using hscaled.1
  · apply (lt_div_iff₀ (Real.exp_pos t)).2
    simpa [mul_comm] using hscaled.2

@[simp]
theorem suzukiX19BInwardDilationSmoothCore_apply
    {b : Real} (t : Real) (z : SuzukiSmoothCore b) (x : Real) :
    (suzukiX19BInwardDilationSmoothCore t z).1 x =
      (Real.exp (-t / 2) : Complex) * z.1 (Real.exp t * x) := by
  change (Real.exp (-t) : Complex) *
      ((Real.exp (t / 2) : Complex) * z.1 (Real.exp t * x)) = _
  rw [← mul_assoc]
  congr 1
  norm_cast
  rw [← Real.exp_add]
  congr 1
  ring

theorem suzukiX19BInwardDilation_radius_lt
    {b t : Real} (hb : 0 < b) (ht : 0 < t) :
    b / Real.exp t < b := by
  apply (div_lt_iff₀ (Real.exp_pos t)).2
  have hexp : 1 < Real.exp t := (Real.one_lt_exp_iff).2 ht
  nlinarith

/-- The normalization in `suzukiX19BInwardDilationSmoothCore` makes Suzuki's
differential commute exactly with the `L2`-normalized dilation. -/
theorem suzukiDifferential_suzukiX19BInwardDilationSmoothCore_apply
    {b : Real} (t : Real) (z : SuzukiSmoothCore b) (x : Real) :
    suzukiDifferential (suzukiX19BInwardDilationSmoothCore t z).1 x =
      burnolDilation t (suzukiDifferential z.1) x := by
  have hinner :=
    (z.1.hasDerivAt (Real.exp t * x)).scomp x
      (hasDerivAt_const_mul (x := x) (Real.exp t))
  have hderiv := hinner.const_mul (Real.exp (-t / 2) : Complex)
  have hderivEq :
      deriv (fun y : Real ↦
        (Real.exp (-t / 2) : Complex) * z.1 (Real.exp t * y)) x =
      (Real.exp (-t / 2) : Complex) * Real.exp t *
        deriv (fun y : Real ↦ z.1 y) (Real.exp t * x) := by
    simpa only [Function.comp_apply, Complex.real_smul, mul_assoc] using
      hderiv.deriv
  have hwfun :
      (fun y : Real ↦ (suzukiX19BInwardDilationSmoothCore t z).1 y) =
        fun y : Real ↦
          (Real.exp (-t / 2) : Complex) * z.1 (Real.exp t * y) := by
    funext y
    exact suzukiX19BInwardDilationSmoothCore_apply t z y
  have hwderiv := congrArg (fun f : Real → Complex ↦ deriv f x) hwfun
  rw [burnolDilation_apply, suzukiDifferential_apply,
    suzukiDifferential_apply]
  rw [SchwartzMap.derivCLM_apply, SchwartzMap.derivCLM_apply,
    hwderiv, hderivEq]
  have hcoef :
      (Real.exp (-t / 2) : Complex) * (Real.exp t : Complex) =
        (Real.exp (t / 2) : Complex) := by
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hcoef]
  ring

/-- Inward dilation commutes exactly with the Suzuki differential as an
identity of Schwartz functions, not merely after passage to `L²`. -/
theorem suzukiDifferential_suzukiX19BInwardDilationSmoothCore
    {b t : Real} (z : SuzukiSmoothCore b) :
    suzukiDifferential (suzukiX19BInwardDilationSmoothCore t z).1 =
      burnolDilation t (suzukiDifferential z.1) := by
  ext x
  exact suzukiDifferential_suzukiX19BInwardDilationSmoothCore_apply t z x

/-- The squared pointwise error of the normalized dilation tends to zero in
integral as the inward parameter tends to zero.  Compact support supplies one
fixed integrable majorant for all sufficiently small nonnegative parameters. -/
theorem tendsto_integral_norm_sq_burnolDilation_sub
    {b : Real} (hb : 0 < b) (f : SchwartzLineTestFunction)
    (hsupport : Function.support f ⊆ Set.Icc (-b) b) :
    Filter.Tendsto
      (fun t : Real ↦ ∫ x : Real, ‖burnolDilation t f x - f x‖ ^ 2)
      (nhdsWithin (0 : Real) (Set.Ici 0)) (nhds 0) := by
  let M : Real := SchwartzMap.seminorm Complex 0 0 f
  let C : Real := (Real.exp (1 / 2) * M + M) ^ 2
  let majorant : Real → Real :=
    Set.indicator (Set.Icc (-b) b) (fun _x ↦ C)
  let Q : Real → Real → Real := fun t x ↦
    ‖burnolDilation t f x - f x‖ ^ 2
  have hM : 0 ≤ M := by
    positivity
  have hmajorant : Integrable majorant := by
    have hon : IntegrableOn (fun _x : Real ↦ C) (Set.Icc (-b) b) :=
      continuous_const.continuousOn.integrableOn_compact isCompact_Icc
    exact hon.integrable_indicator measurableSet_Icc
  have hmeas : ∀ᶠ t : Real in nhdsWithin (0 : Real) (Set.Ici 0),
      AEStronglyMeasurable (Q t) volume := by
    filter_upwards with t
    exact (((burnolDilation t f).continuous.sub f.continuous).norm.pow 2)
      |>.aestronglyMeasurable
  have hupperNhds : ∀ᶠ t : Real in nhds (0 : Real), t ≤ 1 := by
    filter_upwards [Iio_mem_nhds (show (0 : Real) < 1 by norm_num)] with t ht
    exact ht.le
  have hupper : ∀ᶠ t : Real in nhdsWithin (0 : Real) (Set.Ici 0),
      t ≤ 1 :=
    hupperNhds.filter_mono inf_le_left
  have hlower : ∀ᶠ t : Real in nhdsWithin (0 : Real) (Set.Ici 0),
      0 ≤ t := by
    exact self_mem_nhdsWithin
  have hbound : ∀ᶠ t : Real in nhdsWithin (0 : Real) (Set.Ici 0),
      ∀ᵐ x : Real ∂volume, ‖Q t x‖ ≤ majorant x := by
    filter_upwards [hlower, hupper] with t ht0 ht1
    filter_upwards with x
    have hexpOne : 1 ≤ Real.exp t := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr ht0
    have hradius : b / Real.exp t ≤ b := by
      apply (div_le_iff₀ (Real.exp_pos t)).2
      nlinarith
    by_cases hx : x ∈ Set.Icc (-b) b
    · simp only [majorant, Set.indicator_of_mem hx]
      have hfBound : ‖f x‖ ≤ M :=
        SchwartzMap.norm_le_seminorm Complex f x
      have hfScaledBound : ‖f (Real.exp t * x)‖ ≤ M :=
        SchwartzMap.norm_le_seminorm Complex f (Real.exp t * x)
      have hexpHalf : Real.exp (t / 2) ≤ Real.exp (1 / 2) := by
        exact Real.exp_le_exp.mpr (by linarith)
      have hdilBound : ‖burnolDilation t f x‖ ≤ Real.exp (1 / 2) * M := by
        rw [burnolDilation_apply, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul hexpHalf hfScaledBound
          (norm_nonneg _) (Real.exp_pos _).le
      have hsub : ‖burnolDilation t f x - f x‖ ≤
          Real.exp (1 / 2) * M + M :=
        (norm_sub_le _ _).trans (add_le_add hdilBound hfBound)
      have hsum : 0 ≤ Real.exp (1 / 2) * M + M :=
        add_nonneg (mul_nonneg (Real.exp_pos _).le hM) hM
      dsimp only [Q, majorant, C]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _) hsum).2 hsub
    · simp only [majorant, Set.indicator_of_notMem hx]
      have hfx : f x = 0 := by
        rw [← Function.notMem_support]
        exact fun hmem ↦ hx (hsupport hmem)
      have hdilSupport :=
        support_burnolDilation_subset_Icc (a := t) hsupport
      have hdilx : burnolDilation t f x = 0 := by
        rw [← Function.notMem_support]
        intro hmem
        have hnegRadius : -b ≤ -b / Real.exp t := by
          rw [neg_div]
          exact neg_le_neg hradius
        exact hx ⟨hnegRadius.trans (hdilSupport hmem).1,
          (hdilSupport hmem).2.trans hradius⟩
      have hQ : Q t x = 0 := by
        dsimp only [Q]
        rw [hdilx, hfx]
        norm_num
      rw [hQ]
      simp
  have hlimit : ∀ᵐ x : Real ∂volume,
      Filter.Tendsto (fun t : Real ↦ Q t x)
        (nhdsWithin (0 : Real) (Set.Ici 0)) (nhds 0) := by
    filter_upwards with x
    have hscale : Filter.Tendsto (fun t : Real ↦ Real.exp t * x)
        (nhdsWithin (0 : Real) (Set.Ici 0)) (nhds x) := by
      have hcont : Continuous (fun t : Real ↦ Real.exp t * x) :=
        Real.continuous_exp.mul continuous_const
      have hfilter : nhdsWithin (0 : Real) (Set.Ici 0) ≤ nhds 0 :=
        inf_le_left
      simpa only [Real.exp_zero, one_mul] using
        (hcont.tendsto 0).mono_left hfilter
    have hamp : Filter.Tendsto
        (fun t : Real ↦ Complex.exp ((t : Complex) / 2))
        (nhdsWithin (0 : Real) (Set.Ici 0)) (nhds 1) := by
      have hcont : Continuous
          (fun t : Real ↦ Complex.exp ((t : Complex) / 2)) :=
        Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp continuous_id).div_const 2)
      have hfilter : nhdsWithin (0 : Real) (Set.Ici 0) ≤ nhds 0 :=
        inf_le_left
      simpa only [Complex.ofReal_zero, zero_div, Complex.exp_zero] using
        (hcont.tendsto 0).mono_left hfilter
    have hvalue := f.continuous.continuousAt.tendsto.comp hscale
    have herror := ((hamp.mul hvalue).sub_const (f x)).norm.pow 2
    simpa [Q, burnolDilation_apply] using herror
  have hdct := tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hlimit
  simpa [Q] using hdct

/-- Compactly supported normalized dilations converge strongly in global
`L²` as the inward parameter tends to zero through nonnegative values. -/
theorem tendsto_burnolDilation_toLp
    {b : Real} (hb : 0 < b) (f : SchwartzLineTestFunction)
    (hsupport : Function.support f ⊆ Set.Icc (-b) b) :
    Filter.Tendsto
      (fun t : Real ↦
        ((burnolDilation t f).memLp (2 : ENNReal)
          (volume : Measure Real)).toLp (burnolDilation t f))
      (nhdsWithin (0 : Real) (Set.Ici 0))
      (nhds ((f.memLp (2 : ENNReal) (volume : Measure Real)).toLp f)) := by
  let F : Real → SuzukiL2 := fun t ↦
    ((burnolDilation t f).memLp (2 : ENNReal)
      (volume : Measure Real)).toLp (burnolDilation t f)
  let F0 : SuzukiL2 :=
    (f.memLp (2 : ENNReal) (volume : Measure Real)).toLp f
  have hnormSq (t : Real) :
      ‖F t - F0‖ ^ 2 =
        ∫ x : Real, ‖burnolDilation t f x - f x‖ ^ 2 := by
    have hmemDil := (burnolDilation t f).memLp
      (2 : ENNReal) (volume : Measure Real)
    have hmemF := f.memLp (2 : ENNReal) (volume : Measure Real)
    have hnorm := norm_sq_toLp_eq_integral_norm_sq
      (⇑(burnolDilation t f) - ⇑f) (hmemDil.sub hmemF)
    rw [hmemDil.toLp_sub hmemF] at hnorm
    simpa only [F, F0, Pi.sub_apply] using hnorm
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsq : Filter.Tendsto (fun t : Real ↦ ‖F t - F0‖ ^ 2)
      (nhdsWithin (0 : Real) (Set.Ici 0)) (nhds 0) := by
    simpa only [hnormSq] using
      tendsto_integral_norm_sq_burnolDilation_sub hb f hsupport
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Every bounded-window smooth primitive is the strong-`L²` differential
limit of its strictly inward-dilated copies.  Together with
`suzukiX19BInwardDilation_radius_lt`, this is the analytic smaller-radius
density statement for the boundary-reaching case. -/
theorem tendsto_suzukiDifferential_inwardDilation_toLp
    {b : Real} (hb : 0 < b) (z : SuzukiSmoothCore b) :
    Filter.Tendsto
      (fun t : Real ↦
        ((suzukiDifferential
            (suzukiX19BInwardDilationSmoothCore t z).1).memLp
              (2 : ENNReal) (volume : Measure Real)).toLp
          (suzukiDifferential
            (suzukiX19BInwardDilationSmoothCore t z).1))
      (nhdsWithin (0 : Real) (Set.Ici 0))
      (nhds ((suzukiDifferential z.1).memLp
        (2 : ENNReal) (volume : Measure Real) |>.toLp
          (suzukiDifferential z.1))) := by
  have hsupport : Function.support (suzukiDifferential z.1) ⊆
      Set.Icc (-b) b :=
    support_suzukiDifferential_subset_Icc fun x hx ↦
      ⟨(z.2 hx).1.le, (z.2 hx).2.le⟩
  simpa only [suzukiDifferential_suzukiX19BInwardDilationSmoothCore] using
    tendsto_burnolDilation_toLp hb (suzukiDifferential z.1) hsupport

/-- A canonical positive sequence of inward parameters tending to zero. -/
def suzukiX19BInwardParameter (n : Nat) : Real :=
  1 / (n + 1)

theorem suzukiX19BInwardParameter_pos (n : Nat) :
    0 < suzukiX19BInwardParameter n := by
  unfold suzukiX19BInwardParameter
  positivity

theorem tendsto_suzukiX19BInwardParameter :
    Filter.Tendsto suzukiX19BInwardParameter Filter.atTop
      (nhdsWithin (0 : Real) (Set.Ici 0)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · change Filter.Tendsto (fun n : Nat ↦ (1 : Real) / (n + 1))
      Filter.atTop (nhds 0)
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  · exact Filter.Eventually.of_forall fun n ↦
      (suzukiX19BInwardParameter_pos n).le

/-- The canonical smaller-radius core obtained from the positive inward
parameter sequence. -/
def suzukiX19BInwardDilationSequence
    {b : Real} (z : SuzukiSmoothCore b) (n : Nat) :
    SuzukiSmoothCore
      (b / Real.exp (suzukiX19BInwardParameter n)) :=
  suzukiX19BInwardDilationSmoothCore (suzukiX19BInwardParameter n) z

theorem suzukiX19BInwardDilationSequence_radius_lt
    {b : Real} (hb : 0 < b) (n : Nat) :
    b / Real.exp (suzukiX19BInwardParameter n) < b :=
  suzukiX19BInwardDilation_radius_lt hb
    (suzukiX19BInwardParameter_pos n)

/-- The same smaller-radius core, viewed in the original `b`-window without
changing its representative. -/
def suzukiX19BInwardDilationSequenceAtRadius
    {b : Real} (hb : 0 < b) (z : SuzukiSmoothCore b) (n : Nat) :
    SuzukiSmoothCore b :=
  suzukiSmoothCoreZeroExtension
    (suzukiX19BInwardDilationSequence_radius_lt hb n).le
    (suzukiX19BInwardDilationSequence z n)

/-- The canonical strictly-smaller-radius sequence converges in the global
`L²` norm of Suzuki differentials. -/
theorem tendsto_suzukiX19BInwardDilationSequence_differential_toLp
    {b : Real} (hb : 0 < b) (z : SuzukiSmoothCore b) :
    Filter.Tendsto
      (fun n : Nat ↦
        ((suzukiDifferential
            (suzukiX19BInwardDilationSequence z n).1).memLp
              (2 : ENNReal) (volume : Measure Real)).toLp
          (suzukiDifferential
            (suzukiX19BInwardDilationSequence z n).1))
      Filter.atTop
      (nhds ((suzukiDifferential z.1).memLp
        (2 : ENNReal) (volume : Measure Real) |>.toLp
          (suzukiDifferential z.1))) := by
  exact (tendsto_suzukiDifferential_inwardDilation_toLp hb z).comp
    tendsto_suzukiX19BInwardParameter

/-- After unchanged-representative inclusion into the original window, the
strictly smaller-radius differentials converge in the actual closed
zero-mean interval source space.  This is the fixed-window density statement
needed to pass bounded source-operator pairings to the radius boundary. -/
theorem tendsto_suzukiX19BInwardDilationSequence_source
    {b : Real} (hb : 0 < b) (z : SuzukiSmoothCore b) :
    Filter.Tendsto
      (fun n : Nat ↦ suzukiSmoothCoreDifferentialZeroMeanL2 hb
        (suzukiX19BInwardDilationSequenceAtRadius hb z n))
      Filter.atTop
      (nhds (suzukiSmoothCoreDifferentialZeroMeanL2 hb z)) := by
  let V : Nat → SuzukiL2 := fun n ↦
    ((suzukiDifferential
        (suzukiX19BInwardDilationSequence z n).1).memLp
          (2 : ENNReal) (volume : Measure Real)).toLp
      (suzukiDifferential (suzukiX19BInwardDilationSequence z n).1)
  let V0 : SuzukiL2 :=
    ((suzukiDifferential z.1).memLp
      (2 : ENNReal) (volume : Measure Real)).toLp
        (suzukiDifferential z.1)
  have hglobal : Filter.Tendsto V Filter.atTop (nhds V0) := by
    exact tendsto_suzukiX19BInwardDilationSequence_differential_toLp hb z
  have hrestricted : Filter.Tendsto
      (fun n ↦ suzukiL2RestrictToFiniteInterval b (V n))
      Filter.atTop
      (nhds (suzukiL2RestrictToFiniteInterval b V0)) :=
    ((suzukiL2RestrictToFiniteInterval b).continuous.tendsto V0).comp hglobal
  have hterm (n : Nat) :
      suzukiL2RestrictToFiniteInterval b (V n) =
        (suzukiSmoothCoreDifferentialZeroMeanL2 hb
          (suzukiX19BInwardDilationSequenceAtRadius hb z n) :
            SuzukiFiniteIntervalL2 b) := by
    change suzukiL2RestrictToFiniteInterval b (V n) =
      suzukiFiniteIntervalContinuousToL2 b
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous
          (suzukiX19BInwardDilationSequenceAtRadius hb z n))
    apply suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
      (g := fun x : Real ↦ suzukiDifferential
        (suzukiX19BInwardDilationSequence z n).1 x)
    · exact ((suzukiDifferential
          (suzukiX19BInwardDilationSequence z n).1).memLp
            (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
    · intro x
      rfl
  have htarget :
      suzukiL2RestrictToFiniteInterval b V0 =
        (suzukiSmoothCoreDifferentialZeroMeanL2 hb z :
          SuzukiFiniteIntervalL2 b) := by
    change suzukiL2RestrictToFiniteInterval b V0 =
      suzukiFiniteIntervalContinuousToL2 b
        (suzukiSmoothCoreDifferentialFiniteIntervalContinuous z)
    apply suzukiL2RestrictToFiniteInterval_eq_continuous_of_coe_ae
      (g := fun x : Real ↦ suzukiDifferential z.1 x)
    · exact ((suzukiDifferential z.1).memLp
          (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
    · intro x
      rfl
  rw [tendsto_subtype_rng]
  convert hrestricted using 1
  · funext n
    exact (hterm n).symm
  · exact congrArg nhds htarget.symm

/-- A smooth `b`-window source that is energy-orthogonal to every strictly
smaller smooth core has zero diagonal `G_b` energy.  Inward dilation supplies
the missing boundary-reaching approximation, so no support gap is assumed. -/
theorem inner_suzukiSourceGOperator_eq_zero_of_orthogonal_all_smaller
    {b : Real} (hb : 0 < b) (z : SuzukiSmoothCore b)
    (horth : ∀ (a : Real) (ha : 0 < a) (_hab : a < b)
      (p : SuzukiSmoothCore a),
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 hb z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 hb
            (suzukiSmoothCoreZeroExtension _hab.le p)) = 0) :
    inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 hb z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 hb z) = 0 := by
  let g : SuzukiFiniteIntervalZeroMeanL2 b :=
    suzukiSourceGOperator b
      (suzukiSmoothCoreDifferentialZeroMeanL2 hb z)
  let u : Nat → SuzukiFiniteIntervalZeroMeanL2 b := fun n ↦
    suzukiSmoothCoreDifferentialZeroMeanL2 hb
      (suzukiX19BInwardDilationSequenceAtRadius hb z n)
  let u0 : SuzukiFiniteIntervalZeroMeanL2 b :=
    suzukiSmoothCoreDifferentialZeroMeanL2 hb z
  have hu : Filter.Tendsto u Filter.atTop (nhds u0) :=
    tendsto_suzukiX19BInwardDilationSequence_source hb z
  have hpair : Filter.Tendsto (fun n : Nat ↦ inner Complex g (u n))
      Filter.atTop (nhds (inner Complex g u0)) :=
    Filter.Tendsto.inner (𝕜 := Complex) tendsto_const_nhds hu
  have heq (n : Nat) : inner Complex g (u n) = 0 := by
    have ha : 0 < b / Real.exp (suzukiX19BInwardParameter n) :=
      div_pos hb (Real.exp_pos _)
    have hab := suzukiX19BInwardDilationSequence_radius_lt hb n
    simpa only [g, u, suzukiX19BInwardDilationSequenceAtRadius] using
      horth (b / Real.exp (suzukiX19BInwardParameter n)) ha hab
        (suzukiX19BInwardDilationSequence z n)
  have hzero : Filter.Tendsto (fun n : Nat ↦ inner Complex g (u n))
      Filter.atTop (nhds 0) := by
    simpa only [heq] using
      (tendsto_const_nhds : Filter.Tendsto
        (fun _n : Nat ↦ (0 : Complex)) Filter.atTop (nhds 0))
  exact tendsto_nhds_unique hpair hzero

/-- Frozen source energy has no nonzero smooth defect orthogonal to all
strictly smaller radii. -/
theorem suzukiSourceShiftedSeminorm_zero_of_orthogonal_all_smaller
    {b : Real} (hb : 0 < b) (z : SuzukiSmoothCore b)
    (horth : ∀ (a : Real) (ha : 0 < a) (_hab : a < b)
      (p : SuzukiSmoothCore a),
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 hb z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 hb
            (suzukiSmoothCoreZeroExtension _hab.le p)) = 0) :
    suzukiSourceShiftedSeminorm b 0
      (suzukiSmoothCoreDifferentialZeroMeanL2 hb z) = 0 := by
  unfold suzukiSourceShiftedSeminorm
  rw [re_inner_suzukiSourceShiftedOperator]
  simp only [zero_mul, sub_zero]
  rw [inner_suzukiSourceGOperator_eq_zero_of_orthogonal_all_smaller
    hb z horth, Complex.zero_re, Real.sqrt_zero]

/-- An energy-orthogonal larger-window smooth source is annihilated as soon
as its primitive is already supported in the smaller open interval.  Thus a
fixed compactly supported smooth source cannot persist in the orthogonal
radius defect once the inner radius passes its support. -/
theorem
    inner_suzukiSourceGOperator_eq_zero_of_orthogonal_of_support_subset
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (hz : Function.support z.1 ⊆ Set.Ioo (-a) a)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) = 0 := by
  let p : SuzukiSmoothCore a := ⟨z.1, hz⟩
  simpa [p, suzukiSmoothCoreZeroExtension] using horth p

/-- The same eventual-annihilation statement in the frozen source-energy
seminorm used by X19B. -/
theorem
    suzukiSourceShiftedSeminorm_zero_of_orthogonal_of_support_subset
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (hz : Function.support z.1 ⊆ Set.Ioo (-a) a)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    suzukiSourceShiftedSeminorm b 0
      (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) = 0 := by
  unfold suzukiSourceShiftedSeminorm
  rw [re_inner_suzukiSourceShiftedOperator]
  simp only [zero_mul, sub_zero]
  rw [inner_suzukiSourceGOperator_eq_zero_of_orthogonal_of_support_subset
    ha hab z hz horth, Complex.zero_re, Real.sqrt_zero]

/-- The interval mean of Suzuki's differential is the exact endpoint jump of
its primitive, with no support assumption at the smaller radius. -/
theorem integral_suzukiDifferential_finiteInterval_eq_boundary
    {a : Real} (ha : 0 < a) (v : SchwartzLineTestFunction) :
    (∫ x : SuzukiFiniteInterval a, suzukiDifferential v x.1 ∂volume) =
      Complex.I * (v a - v (-a)) := by
  rw [show (∫ x : SuzukiFiniteInterval a,
      suzukiDifferential v x.1 ∂volume) =
      ∫ x in Set.Icc (-a) a, suzukiDifferential v x by
    exact MeasureTheory.integral_subtype measurableSet_Icc _]
  simp only [suzukiDifferential_apply]
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  congr 1
  apply intervalIntegral.integral_deriv_eq_sub'
    (f := fun x : Real => v x)
  · funext x
    exact (SchwartzMap.derivCLM_apply Complex v x).symm
  · exact fun x _ => v.differentiableAt
  · exact (SchwartzMap.derivCLM Complex Complex v).continuous.continuousOn

/-- For a smooth source energy-orthogonal to the embedded smaller core, the
entire inner-interval `G_b` contribution is the single constant channel times
the primitive's endpoint jump.  All nonconstant inner modes vanish exactly. -/
theorem
    inner_suzukiSourceGOperator_innerInterval_eq_boundaryChannel_of_orthogonal
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    let restrictedG : C(SuzukiFiniteInterval a, Complex) :=
      { toFun := fun x =>
          suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
            (suzukiDifferential z.1) x.1
        continuous_toFun :=
          (continuous_suzukiFiniteIntervalCoreOperator
            continuous_suzukiScrewFunction
            (suzukiDifferential z.1).continuous).comp continuous_subtype_val }
    let restrictedD : C(SuzukiFiniteInterval a, Complex) :=
      suzukiFiniteIntervalRestriction a (suzukiDifferential z.1)
        (suzukiDifferential z.1).continuous
    inner Complex
        (suzukiFiniteIntervalContinuousToL2 a restrictedG)
        (suzukiFiniteIntervalContinuousToL2 a restrictedD) =
      conj ((∫ x : SuzukiFiniteInterval a, restrictedG x ∂volume) /
          (2 * a)) *
        (Complex.I * (z.1 a - z.1 (-a))) := by
  dsimp only
  let restrictedG : C(SuzukiFiniteInterval a, Complex) :=
    { toFun := fun x =>
        suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) x.1
      continuous_toFun :=
        (continuous_suzukiFiniteIntervalCoreOperator
          continuous_suzukiScrewFunction
          (suzukiDifferential z.1).continuous).comp continuous_subtype_val }
  let restrictedD : C(SuzukiFiniteInterval a, Complex) :=
    suzukiFiniteIntervalRestriction a (suzukiDifferential z.1)
      (suzukiDifferential z.1).continuous
  have hf : suzukiFiniteIntervalContinuousToZeroMeanL2 a restrictedG = 0 := by
    exact
      suzukiSourceGOperator_restriction_zeroMeanProjection_eq_zero_of_orthogonal
        ha hab z horth
  rw [inner_suzukiFiniteIntervalContinuousToL2_eq_meanProduct_of_projection_eq_zero
    ha restrictedG restrictedD hf]
  congr 1
  exact integral_suzukiDifferential_finiteInterval_eq_boundary ha z.1

/-- Exact analytic decomposition of a smooth larger-radius source energy that
is orthogonal to the embedded smaller core.  Its full `G_b` energy is the sum
of one explicit inner boundary channel and the literal outer-annulus kernel
pairing.  This intermediate form exposes the channel that the subsequent
global-zero-mean cancellation absorbs into the centered annular pairing. -/
theorem
    inner_suzukiSourceGOperator_eq_boundaryChannel_add_outerAnnulus_of_orthogonal
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) =
      conj ((∫ x : SuzukiFiniteInterval a,
          suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
            (suzukiDifferential z.1) x.1 ∂volume) / (2 * a)) *
          (Complex.I * (z.1 a - z.1 (-a))) +
        ∫ x in Set.Icc (-b) b \ Set.Icc (-a) a,
          suzukiDifferential z.1 x *
            conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
              (suzukiDifferential z.1) x) := by
  let restrictedG : C(SuzukiFiniteInterval a, Complex) :=
    { toFun := fun x =>
        suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) x.1
      continuous_toFun :=
        (continuous_suzukiFiniteIntervalCoreOperator
          continuous_suzukiScrewFunction
          (suzukiDifferential z.1).continuous).comp continuous_subtype_val }
  let restrictedD : C(SuzukiFiniteInterval a, Complex) :=
    suzukiFiniteIntervalRestriction a (suzukiDifferential z.1)
      (suzukiDifferential z.1).continuous
  let integrand : Real → Complex := fun x =>
    suzukiDifferential z.1 x *
      conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
        (suzukiDifferential z.1) x)
  have hsource :
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) =
        ∫ x in Set.Icc (-b) b, integrand x := by
    unfold suzukiSmoothCoreDifferentialZeroMeanL2
    rw [inner_suzukiSourceGOperator_continuous]
    dsimp only [suzukiSmoothCoreDifferentialFiniteIntervalContinuous]
    rw [suzukiFiniteIntervalContinuousOperatorPairingComplex_restriction
      continuous_suzukiScrewFunction
      (suzukiDifferential z.1).continuous
      (suzukiDifferential z.1).continuous]
    unfold suzukiFiniteIntervalCoreOperatorPairingComplex
    calc
      conj (∫ x in Set.Icc (-b) b,
          suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
              (suzukiDifferential z.1) x *
            conj (suzukiDifferential z.1 x)) =
          ∫ x in Set.Icc (-b) b,
            conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
                (suzukiDifferential z.1) x *
              conj (suzukiDifferential z.1 x)) := integral_conj.symm
      _ = ∫ x in Set.Icc (-b) b, integrand x := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [integrand]
        simp [map_mul]
        ring
  have hinner :=
    inner_suzukiSourceGOperator_innerInterval_eq_boundaryChannel_of_orthogonal
      ha hab z horth
  dsimp only at hinner
  have hinnerSet :
      (∫ x in Set.Icc (-a) a, integrand x) =
        conj ((∫ x : SuzukiFiniteInterval a, restrictedG x ∂volume) /
            (2 * a)) *
          (Complex.I * (z.1 a - z.1 (-a))) := by
    calc
      (∫ x in Set.Icc (-a) a, integrand x) =
          ∫ x : SuzukiFiniteInterval a,
            restrictedD x * conj (restrictedG x) ∂volume := by
        exact (MeasureTheory.integral_subtype measurableSet_Icc integrand).symm
      _ = inner Complex
          (suzukiFiniteIntervalContinuousToL2 a restrictedG)
          (suzukiFiniteIntervalContinuousToL2 a restrictedD) := by
        unfold suzukiFiniteIntervalContinuousToL2
        rw [ContinuousMap.inner_toLp]
      _ = conj ((∫ x : SuzukiFiniteInterval a, restrictedG x ∂volume) /
            (2 * a)) *
          (Complex.I * (z.1 a - z.1 (-a))) := hinner
  have hintegrable : IntegrableOn integrand (Set.Icc (-b) b) := by
    have hcontinuous : Continuous integrand := by
      dsimp only [integrand]
      exact (suzukiDifferential z.1).continuous.mul
        (Complex.continuous_conj.comp
          (continuous_suzukiFiniteIntervalCoreOperator
            continuous_suzukiScrewFunction
            (suzukiDifferential z.1).continuous))
    exact hcontinuous.continuousOn.integrableOn_compact isCompact_Icc
  have hsubset : Set.Icc (-a) a ⊆ Set.Icc (-b) b :=
    Set.Icc_subset_Icc (neg_le_neg hab) hab
  have hdiff :=
    MeasureTheory.setIntegral_sdiff measurableSet_Icc hintegrable hsubset
  calc
    inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) =
        ∫ x in Set.Icc (-b) b, integrand x := hsource
    _ = (∫ x in Set.Icc (-a) a, integrand x) +
        ∫ x in Set.Icc (-b) b \ Set.Icc (-a) a, integrand x := by
      rw [hdiff]
      ring
    _ = conj ((∫ x : SuzukiFiniteInterval a, restrictedG x ∂volume) /
            (2 * a)) *
          (Complex.I * (z.1 a - z.1 (-a))) +
        ∫ x in Set.Icc (-b) b \ Set.Icc (-a) a, integrand x := by
      rw [hinnerSet]

/-- Orthogonality localizes the complete smooth source energy exactly to the
outer annulus once the constant inner `G_b` channel is subtracted.  The
apparently free endpoint jump cancels because the full differential has zero
mean.  This is the cancellation form needed by the remaining radius estimate:
there is no point-trace term left to bound. -/
theorem
    inner_suzukiSourceGOperator_eq_outerAnnulus_centered_of_orthogonal
    {a b : Real} (ha : 0 < a) (hab : a ≤ b)
    (z : SuzukiSmoothCore b)
    (horth : ∀ p : SuzukiSmoothCore a,
      inner Complex
          (suzukiSourceGOperator b
            (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab p)) = 0) :
    let innerGMean : Complex :=
      (∫ x : SuzukiFiniteInterval a,
        suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
          (suzukiDifferential z.1) x.1 ∂volume) / (2 * a)
    inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) =
      ∫ x in Set.Icc (-b) b \ Set.Icc (-a) a,
        suzukiDifferential z.1 x *
          conj (suzukiFiniteIntervalCoreOperator suzukiScrewFunction b
            (suzukiDifferential z.1) x - innerGMean) := by
  dsimp only
  let D : Real → Complex := suzukiDifferential z.1
  let G : Real → Complex :=
    suzukiFiniteIntervalCoreOperator suzukiScrewFunction b D
  let innerGMean : Complex :=
    (∫ x : SuzukiFiniteInterval a, G x.1 ∂volume) / (2 * a)
  let outer : Set Real := Set.Icc (-b) b \ Set.Icc (-a) a
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsubset : Set.Icc (-a) a ⊆ Set.Icc (-b) b :=
    Set.Icc_subset_Icc (neg_le_neg hab) hab
  have hDContinuous : Continuous D := (suzukiDifferential z.1).continuous
  have hDIntegrable : IntegrableOn D (Set.Icc (-b) b) :=
    hDContinuous.continuousOn.integrableOn_compact isCompact_Icc
  have hGContinuous : Continuous G :=
    continuous_suzukiFiniteIntervalCoreOperator
      continuous_suzukiScrewFunction hDContinuous
  have hDGIntegrable : IntegrableOn (fun x => D x * conj (G x)) outer := by
    exact ((hDContinuous.mul
      (Complex.continuous_conj.comp hGContinuous)).continuousOn
        |>.integrableOn_compact isCompact_Icc).mono_set Set.sdiff_subset
  have hDConstIntegrable :
      IntegrableOn (fun x => D x * conj innerGMean) outer := by
    exact ((hDContinuous.mul continuous_const).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Set.sdiff_subset
  have hfullD : (∫ x in Set.Icc (-b) b, D x) = 0 := by
    rw [← MeasureTheory.integral_subtype measurableSet_Icc]
    exact integral_suzukiSmoothCoreDifferentialFiniteIntervalContinuous_eq_zero
      hb z
  have hinnerD :
      (∫ x in Set.Icc (-a) a, D x) =
        Complex.I * (z.1 a - z.1 (-a)) := by
    rw [← MeasureTheory.integral_subtype measurableSet_Icc]
    exact integral_suzukiDifferential_finiteInterval_eq_boundary ha z.1
  have houterD :
      (∫ x in outer, D x) =
        -(Complex.I * (z.1 a - z.1 (-a))) := by
    dsimp only [outer]
    rw [MeasureTheory.setIntegral_sdiff measurableSet_Icc hDIntegrable hsubset,
      hfullD, hinnerD, zero_sub]
  have henergy :=
    inner_suzukiSourceGOperator_eq_boundaryChannel_add_outerAnnulus_of_orthogonal
      ha hab z horth
  change inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) =
      ∫ x in outer, D x * conj (G x - innerGMean)
  change inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab) z) =
      conj innerGMean * (Complex.I * (z.1 a - z.1 (-a))) +
        ∫ x in outer, D x * conj (G x) at henergy
  rw [show (∫ x in outer, D x * conj (G x - innerGMean)) =
      (∫ x in outer, D x * conj (G x)) -
        ∫ x in outer, D x * conj innerGMean by
    rw [← MeasureTheory.integral_sub hDGIntegrable hDConstIntegrable]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp only [map_sub]
    ring]
  rw [MeasureTheory.integral_mul_const, houterD]
  rw [henergy]
  ring

/-- A smooth bump concentrated at the right endpoint of the smaller window.
Its support radius is the free parameter `delta`; this family detects the
whole-core point-trace obstruction independently of the later orthogonal
cancellation. -/
def suzukiX19BEndpointBump (a delta : Real) (hdelta : 0 < delta) :
    ContDiffBump a where
  rIn := delta / 2
  rOut := delta
  rIn_pos := half_pos hdelta
  rIn_lt_rOut := half_lt_self hdelta

/-- The endpoint bump as a complex Schwartz test function. -/
def suzukiX19BEndpointBumpSchwartz
    (a delta : Real) (hdelta : 0 < delta) : SchwartzLineTestFunction :=
  (suzukiX19BEndpointBump a delta hdelta).hasCompactSupport.toSchwartzMap
      (suzukiX19BEndpointBump a delta hdelta).contDiff |>.postcompCLM
    Complex.ofRealCLM

@[simp]
theorem suzukiX19BEndpointBumpSchwartz_apply
    (a delta : Real) (hdelta : 0 < delta) (x : Real) :
    suzukiX19BEndpointBumpSchwartz a delta hdelta x =
      (suzukiX19BEndpointBump a delta hdelta x : Complex) := by
  rfl

/-- If the bump radius fits inside the annular gap, the endpoint bump belongs
to the larger smooth primitive core. -/
def suzukiX19BEndpointBumpSmoothCore
    {a b delta : Real} (ha : 0 < a) (hdelta : 0 < delta)
    (hgap : delta < b - a) : SuzukiSmoothCore b := by
  refine ⟨suzukiX19BEndpointBumpSchwartz a delta hdelta, ?_⟩
  intro x hx
  have hxBall : x ∈ Metric.ball a delta := by
    change (suzukiX19BEndpointBump a delta hdelta x : Complex) ≠ 0 at hx
    have hxReal : suzukiX19BEndpointBump a delta hdelta x ≠ 0 :=
      Complex.ofReal_ne_zero.mp hx
    have hxSupport :
        x ∈ Function.support (suzukiX19BEndpointBump a delta hdelta) := hxReal
    rw [(suzukiX19BEndpointBump a delta hdelta).support_eq] at hxSupport
    exact hxSupport
  rw [Metric.mem_ball, Real.dist_eq] at hxBall
  constructor <;> linarith [le_abs_self (x - a), neg_le_abs (x - a)]

@[simp]
theorem suzukiX19BEndpointBumpSmoothCore_apply
    {a b delta : Real} (ha : 0 < a) (hdelta : 0 < delta)
    (hgap : delta < b - a) (x : Real) :
    (suzukiX19BEndpointBumpSmoothCore ha hdelta hgap).1 x =
      (suzukiX19BEndpointBump a delta hdelta x : Complex) := by
  rfl

/-- The concentrated primitive retains unit point trace at the smaller
right endpoint. -/
@[simp]
theorem suzukiX19BEndpointBumpSmoothCore_endpoint
    {a b delta : Real} (ha : 0 < a) (hdelta : 0 < delta)
    (hgap : delta < b - a) :
    (suzukiX19BEndpointBumpSmoothCore ha hdelta hgap).1 a = 1 := by
  rw [suzukiX19BEndpointBumpSmoothCore_apply]
  norm_cast
  exact (suzukiX19BEndpointBump a delta hdelta).one_of_mem_closedBall
    (by
      change dist a a ≤ delta / 2
      rw [dist_self]
      exact (half_pos hdelta).le)

/-- Quantitative endpoint-trace witness: the unit-trace primitive has global
`L2` norm at most the square root of the length of its support interval. -/
theorem norm_suzukiSmoothCoreToL2_endpointBump_le
    {a b delta : Real} (ha : 0 < a) (hdelta : 0 < delta)
    (hgap : delta < b - a) :
    ‖suzukiSmoothCoreToL2
        (suzukiX19BEndpointBumpSmoothCore ha hdelta hgap)‖ ≤
      Real.sqrt (2 * delta) := by
  let v : SuzukiSmoothCore b :=
    suzukiX19BEndpointBumpSmoothCore ha hdelta hgap
  let indicator : SuzukiL2 :=
    MeasureTheory.indicatorConstLp 2
      (measurableSet_Icc : MeasurableSet (Set.Icc (a - delta) (a + delta)))
      (measure_Icc_lt_top.ne)
      (1 : Complex)
  have hIndicator :
      (indicator : Real → Complex) =ᵐ[volume]
        Set.indicator (Set.Icc (a - delta) (a + delta))
          (fun _ ↦ (1 : Complex)) := by
    exact MeasureTheory.indicatorConstLp_coeFn
  have hnorm : ‖suzukiSmoothCoreToL2 v‖ ≤ ‖indicator‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
      hIndicator] with x hv hindicator
    change ‖(suzukiSmoothCoreToL2 v : Real → Complex) x‖ ≤
      ‖(indicator : Real → Complex) x‖
    rw [show (suzukiSmoothCoreToL2 v : Real → Complex) x = v.1 x by
      simpa only [suzukiSmoothCoreToL2] using hv]
    rw [hindicator]
    change ‖(suzukiX19BEndpointBump a delta hdelta x : Complex)‖ ≤ _
    by_cases hx : x ∈ Set.Icc (a - delta) (a + delta)
    · rw [Set.indicator_of_mem hx]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ((suzukiX19BEndpointBump a delta hdelta).nonneg),
        norm_one]
      exact (suzukiX19BEndpointBump a delta hdelta).le_one
    · rw [Set.indicator_of_notMem hx, norm_zero]
      have hdist : delta ≤ dist x a := by
        rw [Real.dist_eq]
        by_cases hleft : x < a - delta
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · have hright : a + delta < x := by
            by_contra hnotRight
            exact hx ⟨le_of_not_gt hleft, le_of_not_gt hnotRight⟩
          rw [abs_of_nonneg (by linarith)]
          linarith
      rw [(suzukiX19BEndpointBump a delta hdelta).zero_of_le_dist hdist,
        Complex.ofReal_zero, norm_zero]
  calc
    ‖suzukiSmoothCoreToL2
        (suzukiX19BEndpointBumpSmoothCore ha hdelta hgap)‖ =
        ‖suzukiSmoothCoreToL2 v‖ := rfl
    _ ≤ ‖indicator‖ := hnorm
    _ = Real.sqrt (2 * delta) := by
      unfold indicator
      rw [MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num)]
      simp only [norm_one, one_mul, ENNReal.toReal_ofNat, one_div]
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal]
      · rw [Real.sqrt_eq_rpow]
        congr 1
        · ring
        · simp [div_eq_mul_inv]
      · linarith

/-- No proposed nonnegative constant can control the endpoint trace on the
whole smooth core by the primitive `L2` norm once the bump width is chosen
below both the annular gap and that constant's square-root scale.  This remains
a guardrail against separating the intermediate boundary channel, although
the channel cancels on the energy-orthogonal subclass. -/
theorem not_forall_suzukiSmoothCore_endpoint_norm_le_mul_L2
    {a b delta C : Real} (ha : 0 < a) (hdelta : 0 < delta)
    (hgap : delta < b - a) (hC : 0 ≤ C)
    (hsmall : C * Real.sqrt (2 * delta) < 1) :
    ¬ ∀ v : SuzukiSmoothCore b,
      ‖v.1 a‖ ≤ C * ‖suzukiSmoothCoreToL2 v‖ := by
  intro htrace
  let v : SuzukiSmoothCore b :=
    suzukiX19BEndpointBumpSmoothCore ha hdelta hgap
  have hvTrace : ‖v.1 a‖ = 1 := by
    change ‖(suzukiX19BEndpointBumpSmoothCore ha hdelta hgap).1 a‖ = 1
    rw [suzukiX19BEndpointBumpSmoothCore_endpoint, norm_one]
  have hvNorm : ‖suzukiSmoothCoreToL2 v‖ ≤ Real.sqrt (2 * delta) :=
    norm_suzukiSmoothCoreToL2_endpointBump_le ha hdelta hgap
  have hbound := htrace v
  rw [hvTrace] at hbound
  have : (1 : Real) ≤ C * Real.sqrt (2 * delta) :=
    hbound.trans (mul_le_mul_of_nonneg_left hvNorm hC)
  linarith

/-- The diagonal `G_a` source energy is exactly invariant under enlarging the
radius on a smooth differential supported in the smaller interval. -/
theorem re_inner_suzukiSourceGOperator_smoothCoreDifferential_zeroExtension
    {a b : Real} (ha : 0 < a) (hab : a ≤ b) (v : SuzukiSmoothCore a) :
    (inner Complex
        (suzukiSourceGOperator b
          (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
            (suzukiSmoothCoreZeroExtension hab v)))
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
          (suzukiSmoothCoreZeroExtension hab v))).re =
      (inner Complex
        (suzukiSourceGOperator a
          (suzukiSmoothCoreDifferentialZeroMeanL2 ha v))
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v)).re := by
  exact congrArg Complex.re
    (inner_suzukiSourceGOperator_smoothCoreDifferentials_zeroExtension
      ha hab v v)

/-- Hence the frozen-shift source-energy seminorm is exactly invariant on the
nested smooth differential core. -/
theorem suzukiSourceShiftedSeminorm_zero_smoothCoreDifferential_zeroExtension
    {a b : Real} (ha : 0 < a) (hab : a ≤ b) (v : SuzukiSmoothCore a) :
    suzukiSourceShiftedSeminorm b 0
        (suzukiSmoothCoreDifferentialZeroMeanL2 (ha.trans_le hab)
          (suzukiSmoothCoreZeroExtension hab v)) =
      suzukiSourceShiftedSeminorm a 0
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) := by
  unfold suzukiSourceShiftedSeminorm
  congr 1
  rw [re_inner_suzukiSourceShiftedOperator,
    re_inner_suzukiSourceShiftedOperator]
  simp only [zero_mul, sub_zero]
  exact re_inner_suzukiSourceGOperator_smoothCoreDifferential_zeroExtension
    ha hab v

/-- Completion-core norms at two nested released radii agree exactly on the
same smooth differential.  This is the analytic norm identity needed before
any topological extension to the completed spaces. -/
theorem norm_suzukiShiftedSourceEnergyCore_smoothDifferential_zeroExtension
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (v : SuzukiSmoothCore a) :
    ‖(⟨suzukiSmoothCoreDifferentialZeroMeanL2
          (suzukiDF6E_radius_pos hb)
          (suzukiSmoothCoreZeroExtension hab v)⟩ :
        SuzukiShiftedSourceEnergyCore
          hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold)‖ =
      ‖(⟨suzukiSmoothCoreDifferentialZeroMeanL2
          (suzukiDF6E_radius_pos ha) v⟩ :
        SuzukiShiftedSourceEnergyCore
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)‖ := by
  rw [norm_suzukiShiftedSourceEnergyCore,
    norm_suzukiShiftedSourceEnergyCore]
  exact
    suzukiSourceShiftedSeminorm_zero_smoothCoreDifferential_zeroExtension
      (suzukiDF6E_radius_pos ha) hab v

/-- Radius widening as a complex-linear map on the bundled smooth core. -/
def suzukiX19BSmoothCoreWidenLinearMap
    {a b : Real} (hab : a ≤ b) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiSmoothCoreLinearSubmodule b where
  toFun := suzukiSmoothCoreLinearSubmoduleWiden hab
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' c v := by
    apply Subtype.ext
    rfl

/-- The smaller smooth differential core mapped into the larger shifted
source-energy completion by unchanged-representative radius widening. -/
def suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b) :
    SuzukiSmoothCoreLinearSubmodule a →ₗ[Complex]
      SuzukiShiftedSourceEnergyCompletion hsource hequation25 b hb 0
        suzukiX19B_zero_lt_shiftThreshold :=
  (suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold).comp
    (suzukiX19BSmoothCoreWidenLinearMap hab)

/-- Exact norm preservation of the smooth differential core under the
completion-valued radius-widening map. -/
theorem norm_suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    ‖suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
        hsource hequation25 ha hb hab v‖ =
      ‖suzukiShiftedSourceDifferentialCoreLinearMap
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold v‖ := by
  change
    ‖suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold
        (⟨suzukiSmoothCoreDifferentialZeroMeanL2
          (suzukiDF6E_radius_pos hb)
          (suzukiSmoothCoreLinearSubmoduleAsCore
            (suzukiSmoothCoreLinearSubmoduleWiden hab v))⟩ :
          SuzukiShiftedSourceEnergyCore hsource hequation25 b hb 0
            suzukiX19B_zero_lt_shiftThreshold)‖ =
      ‖suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
        (⟨suzukiSmoothCoreDifferentialZeroMeanL2
          (suzukiDF6E_radius_pos ha)
          (suzukiSmoothCoreLinearSubmoduleAsCore v)⟩ :
          SuzukiShiftedSourceEnergyCore hsource hequation25 a ha 0
            suzukiX19B_zero_lt_shiftThreshold)‖
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map,
    suzukiSmoothCoreLinearSubmoduleAsCore_widen]
  exact norm_suzukiShiftedSourceEnergyCore_smoothDifferential_zeroExtension
    hsource hequation25 ha hb hab
      (suzukiSmoothCoreLinearSubmoduleAsCore v)

/-- Canonical radius-widening map between the frozen shifted source-energy
completions.  It is the unique bounded extension of unchanged-representative
widening on the dense smooth differential core. -/
noncomputable def suzukiX19BShiftedCompletionZeroExtension
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b) :
    SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
        suzukiX19B_zero_lt_shiftThreshold →L[Complex]
      SuzukiShiftedSourceEnergyCompletion hsource hequation25 b hb 0
        suzukiX19B_zero_lt_shiftThreshold :=
  LinearMap.extendOfNorm
    (suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
      hsource hequation25 ha hb hab)
    (suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)

/-- The completion radius-widening map agrees with literal smooth-core
zero extension on the canonical dense differential image. -/
theorem suzukiX19BShiftedCompletionZeroExtension_apply_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (v : SuzukiSmoothCoreLinearSubmodule a) :
    suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hb hab
        (suzukiShiftedSourceDifferentialCoreLinearMap
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold v) =
      suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
        hsource hequation25 ha hb hab v := by
  apply LinearMap.extendOfNorm_eq
    (denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
  refine ⟨1, fun u ↦ ?_⟩
  rw [one_mul]
  exact (norm_suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
    hsource hequation25 ha hb hab u).le

/-- Radius widening preserves the norm of every completed source-energy
vector, by density of the smooth differential core. -/
theorem norm_suzukiX19BShiftedCompletionZeroExtension
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (x : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
      suzukiX19B_zero_lt_shiftThreshold) :
    ‖suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hb hab x‖ = ‖x‖ := by
  apply DenseRange.induction_on
    (p := fun y : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold =>
      ‖suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab y‖ = ‖y‖)
    (denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    x
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    rw [suzukiX19BShiftedCompletionZeroExtension_apply_core]
    exact norm_suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
      hsource hequation25 ha hb hab v

/-- Frozen shifted source-energy radius widening bundled as a linear
isometry. -/
noncomputable def suzukiX19BShiftedCompletionZeroExtensionLinearIsometry
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b) :
    SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
        suzukiX19B_zero_lt_shiftThreshold →ₗᵢ[Complex]
      SuzukiShiftedSourceEnergyCompletion hsource hequation25 b hb 0
        suzukiX19B_zero_lt_shiftThreshold where
  toFun := suzukiX19BShiftedCompletionZeroExtension
    hsource hequation25 ha hb hab
  map_add' := map_add _
  map_smul' := map_smul _
  norm_map' := norm_suzukiX19BShiftedCompletionZeroExtension
    hsource hequation25 ha hb hab

/-- Radius widening by the identity inequality is the identity on the frozen
shifted completion. -/
theorem suzukiX19BShiftedCompletionZeroExtension_self
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (x : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
      suzukiX19B_zero_lt_shiftThreshold) :
    suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha ha le_rfl x = x := by
  apply DenseRange.induction_on
    (p := fun y : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold =>
      suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha ha le_rfl y = y)
    (denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    x
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    rw [suzukiX19BShiftedCompletionZeroExtension_apply_core]
    rfl

/-- Frozen completion radius widening is transitive across nested released
radii. -/
theorem suzukiX19BShiftedCompletionZeroExtension_trans
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b c : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hc : c ∈ SuzukiDF6EInterval)
    (hab : a ≤ b) (hbc : b ≤ c)
    (x : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
      suzukiX19B_zero_lt_shiftThreshold) :
    suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 hb hc hbc
        (suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab x) =
      suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hc (hab.trans hbc) x := by
  apply DenseRange.induction_on
    (p := fun y : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold =>
      suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 hb hc hbc
          (suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab y) =
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hc (hab.trans hbc) y)
    (denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    x
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    calc
      suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 hb hc hbc
          (suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab
            (suzukiShiftedSourceDifferentialCoreLinearMap
              hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold v)) =
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 hb hc hbc
          (suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
            hsource hequation25 ha hb hab v) := congrArg _
              (suzukiX19BShiftedCompletionZeroExtension_apply_core
                hsource hequation25 ha hb hab v)
      _ = suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
          hsource hequation25 hb hc hbc
          (suzukiSmoothCoreLinearSubmoduleWiden hab v) := by
        change
          suzukiX19BShiftedCompletionZeroExtension
              hsource hequation25 hb hc hbc
              (suzukiShiftedSourceDifferentialCoreLinearMap
                hsource hequation25 b hb 0
                suzukiX19B_zero_lt_shiftThreshold
                (suzukiSmoothCoreLinearSubmoduleWiden hab v)) = _
        exact suzukiX19BShiftedCompletionZeroExtension_apply_core
          hsource hequation25 hb hc hbc
          (suzukiSmoothCoreLinearSubmoduleWiden hab v)
      _ = suzukiX19BShiftedCompletionCoreZeroExtensionLinearMap
          hsource hequation25 ha hc (hab.trans hbc) v := by
        rfl
      _ = suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hc (hab.trans hbc)
          (suzukiShiftedSourceDifferentialCoreLinearMap
            hsource hequation25 a ha 0
            suzukiX19B_zero_lt_shiftThreshold v) :=
        (suzukiX19BShiftedCompletionZeroExtension_apply_core
          hsource hequation25 ha hc (hab.trans hbc) v).symm

/-- The canonical inward-dilated core, viewed as a bundled smooth core at the
original radius. -/
def suzukiX19BInwardDilationSequenceAtRadiusLinearSubmodule
    {b : Real} (hb : 0 < b) (v : SuzukiSmoothCoreLinearSubmodule b)
    (n : Nat) : SuzukiSmoothCoreLinearSubmodule b :=
  ⟨(suzukiX19BInwardDilationSequenceAtRadius hb
      (suzukiSmoothCoreLinearSubmoduleAsCore v) n).1,
    (suzukiX19BInwardDilationSequenceAtRadius hb
      (suzukiSmoothCoreLinearSubmoduleAsCore v) n).2⟩

@[simp]
theorem suzukiSmoothCoreLinearSubmoduleAsCore_inwardDilationSequenceAtRadius
    {b : Real} (hb : 0 < b) (v : SuzukiSmoothCoreLinearSubmodule b)
    (n : Nat) :
    suzukiSmoothCoreLinearSubmoduleAsCore
        (suzukiX19BInwardDilationSequenceAtRadiusLinearSubmodule hb v n) =
      suzukiX19BInwardDilationSequenceAtRadius hb
        (suzukiSmoothCoreLinearSubmoduleAsCore v) n := by
  apply Subtype.ext
  rfl

/-- The strictly inward smooth approximants converge in the actual frozen
shifted source-energy completion at the original radius.  This transfers the
analytic `L2` localization theorem through the existing continuous source-`L2`
inclusion. -/
theorem tendsto_suzukiX19BInwardDilationSequence_completion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (v : SuzukiSmoothCoreLinearSubmodule b) :
    Filter.Tendsto
      (fun n : Nat ↦
        suzukiShiftedSourceDifferentialCoreLinearMap
          hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold
          (suzukiX19BInwardDilationSequenceAtRadiusLinearSubmodule
            (suzukiDF6E_radius_pos hb) v n))
      Filter.atTop
      (nhds (suzukiShiftedSourceDifferentialCoreLinearMap
        hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold v)) := by
  have hsourceL2 := tendsto_suzukiX19BInwardDilationSequence_source
    (suzukiDF6E_radius_pos hb)
    (suzukiSmoothCoreLinearSubmoduleAsCore v)
  have hcompletion :=
    ((suzukiSourceL2ToShiftedEnergyCompletion
      hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold).continuous
        |>.tendsto
          (suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos hb)
            (suzukiSmoothCoreLinearSubmoduleAsCore v))).comp hsourceL2
  simpa [suzukiShiftedSourceDifferentialCoreLinearMap_apply,
    suzukiSourceL2ToShiftedEnergyCompletion_apply,
    suzukiSmoothCoreLinearSubmoduleAsCore_inwardDilationSequenceAtRadius,
    suzukiSmoothCoreDifferentialZeroMeanLinearMap,
    Function.comp_def] using hcompletion

/-- The radii of the canonical inward-dilation sequence tend back to the
original radius. -/
theorem tendsto_suzukiX19BInwardDilationSequence_radius
    (b : Real) :
    Filter.Tendsto
      (fun n : Nat ↦ b / Real.exp (suzukiX19BInwardParameter n))
      Filter.atTop (nhds b) := by
  have hparameter : Filter.Tendsto suzukiX19BInwardParameter
      Filter.atTop (nhds (0 : Real)) :=
    tendsto_suzukiX19BInwardParameter.mono_right inf_le_left
  have hcontinuous : ContinuousAt
      (fun t : Real ↦ b / Real.exp t) 0 := by
    exact continuousAt_const.div Real.continuous_exp.continuousAt
      (Real.exp_ne_zero 0)
  simpa only [Real.exp_zero, div_one, Function.comp_def] using
    hcontinuous.tendsto.comp hparameter

/-- At every non-left-endpoint released radius, the canonical inward radii
eventually remain inside the released interval. -/
theorem eventually_suzukiX19BInwardDilationSequence_radius_mem
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b) :
    ∀ᶠ n : Nat in Filter.atTop,
      b / Real.exp (suzukiX19BInwardParameter n) ∈ SuzukiDF6EInterval := by
  have hlower : ∀ᶠ n : Nat in Filter.atTop,
      Real.log 2 / 2 < b / Real.exp (suzukiX19BInwardParameter n) :=
    tendsto_suzukiX19BInwardDilationSequence_radius b
      (Ioi_mem_nhds hleft)
  filter_upwards [hlower] with n hn
  change Real.log 2 / 2 ≤
      b / Real.exp (suzukiX19BInwardParameter n) ∧
    b / Real.exp (suzukiX19BInwardParameter n) ≤ suzukiProjectAStar
  exact ⟨hn.le,
    (suzukiX19BInwardDilationSequence_radius_lt
      (suzukiDF6E_radius_pos hb) n).le.trans hb.2⟩

/-- All vectors obtained from completions at released radii strictly below
`b`, transported into the frozen completion at `b`. -/
def suzukiX19BStrictSmallerCompletionImages
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval) :
    Set (SuzukiShiftedSourceEnergyCompletion hsource hequation25 b hb 0
      suzukiX19B_zero_lt_shiftThreshold) :=
  {y | ∃ (a : Real) (ha : a ∈ SuzukiDF6EInterval) (hab : a < b)
      (x : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
        suzukiX19B_zero_lt_shiftThreshold),
    suzukiX19BShiftedCompletionZeroExtension
      hsource hequation25 ha hb hab.le x = y}

/-- The image of the dense smooth differential core at an interior released
radius lies in the closure of the strict smaller-radius completion images. -/
theorem suzukiShiftedSourceDifferentialCoreLinearMap_mem_closure_strictSmaller
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b)
    (v : SuzukiSmoothCoreLinearSubmodule b) :
    suzukiShiftedSourceDifferentialCoreLinearMap
        hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold v ∈
      closure (suzukiX19BStrictSmallerCompletionImages
        hsource hequation25 hb) := by
  apply mem_closure_of_tendsto
    (tendsto_suzukiX19BInwardDilationSequence_completion
      hsource hequation25 hb v)
  filter_upwards [eventually_suzukiX19BInwardDilationSequence_radius_mem
    hb hleft] with n hn
  let a : Real := b / Real.exp (suzukiX19BInwardParameter n)
  let vn : SuzukiSmoothCoreLinearSubmodule a :=
    ⟨(suzukiX19BInwardDilationSequence
        (suzukiSmoothCoreLinearSubmoduleAsCore v) n).1,
      (suzukiX19BInwardDilationSequence
        (suzukiSmoothCoreLinearSubmoduleAsCore v) n).2⟩
  have hab : a < b :=
    suzukiX19BInwardDilationSequence_radius_lt
      (suzukiDF6E_radius_pos hb) n
  refine ⟨a, hn, hab,
    suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a hn 0 suzukiX19B_zero_lt_shiftThreshold vn, ?_⟩
  rw [suzukiX19BShiftedCompletionZeroExtension_apply_core]
  change suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiSmoothCoreLinearSubmoduleWiden hab.le vn) =
    suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BInwardDilationSequenceAtRadiusLinearSubmodule
        (suzukiDF6E_radius_pos hb) v n)
  congr 1

/-- The union of all strict smaller-radius completion images is dense in the
frozen shifted completion at every interior point of the released window. -/
theorem dense_suzukiX19BStrictSmallerCompletionImages
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b) :
    Dense (suzukiX19BStrictSmallerCompletionImages
      hsource hequation25 hb) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ closure (Set.range
      (suzukiShiftedSourceDifferentialCoreLinearMap
        hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold)) :=
    denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold x
  rw [← closure_closure]
  apply closure_mono _ hx
  rintro _ ⟨v, rfl⟩
  exact suzukiShiftedSourceDifferentialCoreLinearMap_mem_closure_strictSmaller
    hsource hequation25 hb hleft v

/-- At an interior released radius, pairings against all transported strict
smaller-radius completions determine a completed vector uniquely. -/
theorem eq_of_inner_suzukiX19BShiftedCompletionZeroExtension_all_smaller
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b)
    (x y : SuzukiShiftedSourceEnergyCompletion hsource hequation25 b hb 0
      suzukiX19B_zero_lt_shiftThreshold)
    (hpair : ∀ (a : Real) (ha : a ∈ SuzukiDF6EInterval) (hab : a < b)
      (u : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
        suzukiX19B_zero_lt_shiftThreshold),
      inner Complex x
          (suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab.le u) =
        inner Complex y
          (suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab.le u)) :
    x = y := by
  apply ext_inner_right Complex
  intro z
  apply DenseRange.induction_on
    (p := fun q : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold =>
      inner Complex x q = inner Complex y q)
    ((dense_suzukiX19BStrictSmallerCompletionImages
      hsource hequation25 hb hleft).denseRange_val)
    z
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · rintro ⟨val, hval⟩
    rcases hval with ⟨a, ha, hab, u, hu⟩
    change inner Complex x val = inner Complex y val
    rw [← hu]
    exact hpair a ha hab u

/-- The completion-level radius defect vanishes when it is orthogonal to every
transported strict smaller-radius completion. -/
theorem eq_zero_of_inner_suzukiX19BShiftedCompletionZeroExtension_all_smaller
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b)
    (x : SuzukiShiftedSourceEnergyCompletion hsource hequation25 b hb 0
      suzukiX19B_zero_lt_shiftThreshold)
    (horth : ∀ (a : Real) (ha : a ∈ SuzukiDF6EInterval) (hab : a < b)
      (u : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
        suzukiX19B_zero_lt_shiftThreshold),
      inner Complex x
        (suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab.le u) = 0) :
    x = 0 := by
  apply eq_of_inner_suzukiX19BShiftedCompletionZeroExtension_all_smaller
    hsource hequation25 hb hleft x 0
  intro a ha hab u
  simpa only [inner_zero_left] using horth a ha hab u

/-- The exact `L2` size of the annulus exposed when the symmetric source
interval grows from radius `a` to radius `b`. -/
theorem norm_suzukiL2IntervalIndicator_sub_eq_sqrt_radiusGap
    {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖suzukiL2IntervalIndicator b - suzukiL2IntervalIndicator a‖ =
      Real.sqrt (2 * (b - a)) := by
  rw [← dist_eq_norm, dist_comm]
  unfold suzukiL2IntervalIndicator
  rw [MeasureTheory.dist_indicatorConstLp_eq_norm,
    MeasureTheory.norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat, one_div]
  have hsub : Set.Icc (-a) a ⊆ Set.Icc (-b) b :=
    Set.Icc_subset_Icc (neg_le_neg hab) hab
  rw [symmDiff_of_le hsub]
  rw [measureReal_def, measure_sdiff
    hsub measurableSet_Icc.nullMeasurableSet
    (measure_Icc_lt_top.ne)]
  rw [Real.volume_Icc, Real.volume_Icc]
  rw [ENNReal.toReal_sub_of_le]
  · rw [ENNReal.toReal_ofReal, ENNReal.toReal_ofReal]
    · rw [Real.sqrt_eq_rpow]
      congr 1
      · ring
      · simp [div_eq_mul_inv]
    · linarith
    · linarith
  · exact ENNReal.ofReal_le_ofReal (by linarith)
  · exact ENNReal.ofReal_ne_top

/-- Uniform annulus-defect estimate for the truncated complex exponential.
The newly exposed forcing vanishes at the explicit square-root rate as the
larger radius approaches the smaller radius. -/
theorem norm_suzukiX19BComplexExponentialL2_radius_sub_le
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1) :
    ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w‖ ≤
      Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a)) := by
  have hsub : Set.Icc (-a) a ⊆ Set.Icc (-b) b :=
    Set.Icc_subset_Icc (neg_le_neg hab) hab
  have hbound :
      ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
          suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w‖ ≤
        Real.exp suzukiProjectAStar *
          ‖suzukiL2IntervalIndicator b - suzukiL2IntervalIndicator a‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (c := Real.exp suzukiProjectAStar)
      (f := suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w)
      (g := suzukiL2IntervalIndicator b - suzukiL2IntervalIndicator a)
    have hIndB :
        (suzukiL2IntervalIndicator b : Real → Complex) =ᵐ[volume]
          Set.indicator (Set.Icc (-b) b) (fun _ ↦ (1 : Complex)) := by
      exact MeasureTheory.indicatorConstLp_coeFn
    have hIndA :
        (suzukiL2IntervalIndicator a : Real → Complex) =ᵐ[volume]
          Set.indicator (Set.Icc (-a) a) (fun _ ↦ (1 : Complex)) := by
      exact MeasureTheory.indicatorConstLp_coeFn
    filter_upwards [
      suzukiX19BComplexExponentialL2_coeFn
        (suzukiDF6E_radius_pos hb) w,
      suzukiX19BComplexExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) w,
      Lp.coeFn_sub
        (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w)
        (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w),
      hIndB, hIndA,
      Lp.coeFn_sub (suzukiL2IntervalIndicator b)
        (suzukiL2IntervalIndicator a)] with x hExpB hExpA hExpSub hIndBx hIndAx hIndSub
    rw [hExpSub, Pi.sub_apply, hExpB, hExpA,
      hIndSub, Pi.sub_apply, hIndBx, hIndAx]
    by_cases hxb : x ∈ Set.Icc (-b) b
    · by_cases hxa : x ∈ Set.Icc (-a) a
      · simp [suzukiX19BComplexExponentialFunction, hxa, hxb]
      · simp only [suzukiX19BComplexExponentialFunction,
          Set.indicator_of_mem hxb, Set.indicator_of_notMem hxa,
          sub_zero, norm_one, mul_one]
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        calc
          (conj w * (x : Complex)).re = w.re * x := by simp
          _ ≤ |w.re * x| := le_abs_self _
          _ = |w.re| * |x| := abs_mul _ _
          _ ≤ 1 * suzukiProjectAStar := by
            exact mul_le_mul
              ((Complex.abs_re_le_norm w).trans hw)
              (((abs_le).2 hxb).trans hb.2)
              (abs_nonneg x) zero_le_one
          _ = suzukiProjectAStar := one_mul _
    · have hxa : x ∉ Set.Icc (-a) a := fun hx ↦ hxb (hsub hx)
      simp [suzukiX19BComplexExponentialFunction, hxa, hxb]
  calc
    ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w‖ ≤
        Real.exp suzukiProjectAStar *
          ‖suzukiL2IntervalIndicator b - suzukiL2IntervalIndicator a‖ := hbound
    _ = Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a)) := by
      rw [norm_suzukiL2IntervalIndicator_sub_eq_sqrt_radiusGap
        (suzukiDF6E_radius_pos ha).le hab]

/-- The same annulus modulus controls the resulting source functional on
every global `L2` test vector. -/
theorem norm_inner_suzukiX19BComplexExponentialL2_radius_sub_le
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1) (v : SuzukiL2) :
    ‖inner Complex
        (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
          suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w) v‖ ≤
      (Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a))) * ‖v‖ := by
  calc
    ‖inner Complex
        (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
          suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w) v‖ ≤
        ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
          suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w‖ * ‖v‖ :=
      norm_inner_le_norm _ _
    _ ≤ (Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a))) * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (norm_suzukiX19BComplexExponentialL2_radius_sub_le
          ha hb hab w hw) (norm_nonneg _)

/-- On smooth differentials whose primitives lie in the physical annulus,
the radius modulus is a genuine source-`K` dual estimate.  The remaining
X19B radius issue is therefore the nonlocal energy-orthogonal localization,
not the size of forcing already localized to the annulus. -/
theorem norm_inner_suzukiX19BComplexExponentialForcing_physicalAnnulus_le
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1) (v : SuzukiSmoothCore b)
    (hv : ∀ x ∈ Set.Icc (-a) a, v.1 x = 0) :
    ‖inner Complex (suzukiX19BComplexExponentialForcing b w)
        (suzukiSmoothCoreDifferentialZeroMeanL2
          (suzukiDF6E_radius_pos hb) v)‖ ≤
      (Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a))) *
        suzukiSourceKSeminorm b
          (suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos hb) v) := by
  rw [inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential]
  have hEa : inner Complex
      (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w)
      (suzukiSmoothCoreToL2 v) = 0 := by
    rw [MeasureTheory.L2.inner_def]
    have hExp := suzukiX19BComplexExponentialL2_coeFn
      (suzukiDF6E_radius_pos ha) w
    have hV : (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume]
        fun x ↦ v.1 x := by
      simpa only [suzukiSmoothCoreToL2] using
        (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
    apply integral_eq_zero_of_ae
    filter_upwards [hExp, hV] with x hxExp hxV
    rw [hxExp, hxV]
    by_cases hxa : x ∈ Set.Icc (-a) a
    · simp [suzukiX19BComplexExponentialFunction, hxa, hv x hxa]
    · simp [suzukiX19BComplexExponentialFunction, hxa]
  have hEb : inner Complex
      (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w)
      (suzukiSmoothCoreToL2 v) =
    inner Complex
      (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w)
      (suzukiSmoothCoreToL2 v) := by
    rw [inner_sub_left, hEa, sub_zero]
  rw [hEb, norm_mul]
  have hpair :=
    norm_inner_suzukiX19BComplexExponentialL2_radius_sub_le
      ha hb hab w hw (suzukiSmoothCoreToL2 v)
  calc
    ‖-(Complex.I * w)‖ *
        ‖inner Complex
          (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos hb) w -
            suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w)
          (suzukiSmoothCoreToL2 v)‖ ≤
        1 * ((Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a))) *
          ‖suzukiSmoothCoreToL2 v‖) := by
      exact mul_le_mul (by simpa using hw) hpair (norm_nonneg _) zero_le_one
    _ = (Real.exp suzukiProjectAStar * Real.sqrt (2 * (b - a))) *
        suzukiSourceKSeminorm b
          (suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos hb) v) := by
      rw [one_mul,
        suzukiSourceKSeminorm_smoothCoreDifferential_eq_norm]

/-- Elementary `L2` majorant for a truncated complex exponential.  Only the
real part of the coefficient contributes to its modulus. -/
theorem norm_suzukiX19BComplexExponentialL2_le
    {a : Real} (ha : 0 < a) (w : Complex) :
    ‖suzukiX19BComplexExponentialL2 ha w‖ ≤
      Real.exp (|w.re| * a) * Real.sqrt (2 * a) := by
  have hbound : ‖suzukiX19BComplexExponentialL2 ha w‖ ≤
      (Real.exp (|w.re| * a) * Real.sqrt (2 * a)) *
        ‖suzukiYoshidaExponentialL2 a ha 0‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (c := Real.exp (|w.re| * a) * Real.sqrt (2 * a))
      (f := suzukiX19BComplexExponentialL2 ha w)
      (g := suzukiYoshidaExponentialL2 a ha 0)
    filter_upwards [
      suzukiX19BComplexExponentialL2_coeFn ha w,
      suzukiYoshidaExponentialL2_coeFn ha 0] with x hcomplex hzero
    rw [hcomplex, hzero]
    by_cases hx : x ∈ Set.Icc (-a) a
    · rw [suzukiX19BComplexExponentialFunction,
        suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hsqrt : 0 < Real.sqrt (2 * a) := by positivity
      have hexp : Real.exp (w.re * x) ≤ Real.exp (|w.re| * a) := by
        apply Real.exp_le_exp.mpr
        calc
          w.re * x ≤ |w.re * x| := le_abs_self _
          _ = |w.re| * |x| := abs_mul _ _
          _ ≤ |w.re| * a := by
            exact mul_le_mul_of_nonneg_left ((abs_le).2 hx) (abs_nonneg _)
      have hcomplexNorm :
          ‖Complex.exp (conj w * (x : Complex))‖ =
            Real.exp (w.re * x) := by
        rw [Complex.norm_exp]
        congr 1
        simp
      have hzeroNorm :
          ‖(((Real.sqrt (2 * a))⁻¹ : Complex) *
              Complex.exp
                (Complex.I *
                  (((0 : Int) : Complex) * (Real.pi : Complex) /
                    (a : Complex)) * (x : Complex)))‖ =
            (Real.sqrt (2 * a))⁻¹ := by
        have hsqrtA : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
        have hsqrtTwo : 0 < Real.sqrt 2 := by positivity
        simp [Real.norm_eq_abs, abs_of_pos hsqrtA,
          abs_of_pos hsqrtTwo]
      rw [hcomplexNorm, hzeroNorm, mul_assoc,
        mul_inv_cancel₀ hsqrt.ne', mul_one]
      exact hexp
    · simp [suzukiX19BComplexExponentialFunction,
        suzukiYoshidaExponentialFunction, hx]
  simpa [(orthonormal_suzukiYoshidaExponentialL2 ha).norm_eq_one]
    using hbound

/-- The endpoint Fredholm constant controls every complex exponential in the
closed unit disk. -/
theorem norm_suzukiX19BComplexExponentialL2_le_uniform_of_norm_le_one
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) (w : Complex)
    (hw : ‖w‖ ≤ 1) :
    ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w‖ ≤
      suzukiDF6FUniformFredholmBound := by
  have hlocal := norm_suzukiX19BComplexExponentialL2_le
    (suzukiDF6E_radius_pos ha) w
  apply hlocal.trans
  unfold suzukiDF6FUniformFredholmBound
  have hre : |w.re| ≤ 1 := (Complex.abs_re_le_norm w).trans hw
  have hwa : |w.re| * a ≤ suzukiProjectAStar := by
    calc
      |w.re| * a ≤ 1 * a :=
        mul_le_mul_of_nonneg_right hre (suzukiDF6E_radius_pos ha).le
      _ = a := one_mul a
      _ ≤ suzukiProjectAStar := ha.2
  have hexp : Real.exp (|w.re| * a) ≤ Real.exp suzukiProjectAStar :=
    Real.exp_le_exp.mpr hwa
  have hsqrt : Real.sqrt (2 * a) ≤
      Real.sqrt (2 * suzukiProjectAStar) :=
    Real.sqrt_le_sqrt (by linarith [ha.2])
  exact mul_le_mul hexp hsqrt (Real.sqrt_nonneg _) (Real.exp_pos _).le

/-- Every projected complex exponential has the source-dual constant given
by the norm of its spectral coefficient times its `L2` norm. -/
theorem suzukiSourceKDualBoundAt_x19bComplexExponential
    {a : Real} (ha : 0 < a) (w : Complex) :
    SuzukiSourceKDualBoundAt a
      (suzukiX19BComplexExponentialForcing a w)
      (‖w‖ * ‖suzukiX19BComplexExponentialL2 ha w‖) := by
  apply suzukiSourceKDualBoundAt_of_smoothCore ha
  intro v
  rw [inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential
    ha w v]
  calc
    ‖-(Complex.I * w) *
        inner Complex (suzukiX19BComplexExponentialL2 ha w)
          (suzukiSmoothCoreToL2 v)‖ =
        ‖w‖ * ‖inner Complex (suzukiX19BComplexExponentialL2 ha w)
          (suzukiSmoothCoreToL2 v)‖ := by simp
    _ ≤ ‖w‖ *
        (‖suzukiX19BComplexExponentialL2 ha w‖ *
          ‖suzukiSmoothCoreToL2 v‖) := by
      gcongr
      exact norm_inner_le_norm _ _
    _ = (‖w‖ * ‖suzukiX19BComplexExponentialL2 ha w‖) *
        ‖suzukiSmoothCoreToL2 v‖ := by ring

/-- Uniform source-dual bound on the two-dimensional closed unit disk. -/
theorem suzukiSourceKDualBoundAt_x19bComplexExponential_five
    {a : Real} (ha : a ∈ SuzukiDF6EInterval) (w : Complex)
    (hw : ‖w‖ ≤ 1) :
    SuzukiSourceKDualBoundAt a
      (suzukiX19BComplexExponentialForcing a w) 5 := by
  intro u
  have hsourceBound := suzukiSourceKDualBoundAt_x19bComplexExponential
    (suzukiDF6E_radius_pos ha) w u
  have hcoefficient :
      ‖w‖ * ‖suzukiX19BComplexExponentialL2
          (suzukiDF6E_radius_pos ha) w‖ ≤ 5 := by
    calc
      ‖w‖ * ‖suzukiX19BComplexExponentialL2
          (suzukiDF6E_radius_pos ha) w‖ ≤
          1 * suzukiDF6FUniformFredholmBound := by
        exact mul_le_mul hw
          (norm_suzukiX19BComplexExponentialL2_le_uniform_of_norm_le_one
            ha w hw)
          (norm_nonneg _) zero_le_one
      _ = suzukiDF6FUniformFredholmBound := one_mul _
      _ ≤ 5 := suzukiDF6FUniformFredholmBound_lt_five.le
  exact hsourceBound.trans
    (mul_le_mul_of_nonneg_right hcoefficient
      (suzukiSourceKSeminorm_nonneg a u))

/-- Canonical X19B weak solution for every complex spectral coefficient in
the closed unit disk. -/
def suzukiX19BComplexUnitDiskSolution
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w : Complex) (hw : ‖w‖ ≤ 1) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
  suzukiShiftedSourceEnergyRieszVector
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BComplexExponentialForcing a w)
      (suzukiSourceKDualBoundAt_x19bComplexExponential_five ha w hw)

/-- Exact weak source equation throughout the two-dimensional unit disk. -/
theorem inner_suzukiX19BComplexUnitDiskSolution_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w : Complex) (hw : ‖w‖ ≤ 1)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold) :
    inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
      inner Complex (suzukiX19BComplexExponentialForcing a w) u.toL2 := by
  exact inner_suzukiShiftedSourceEnergyRieszVector_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BComplexExponentialForcing a w)
      (suzukiSourceKDualBoundAt_x19bComplexExponential_five ha w hw) u

/-- At nested released radii, the canonical solutions induce the same weak
source functional on every smooth differential supported in the smaller
interval.  No identification of the two completion spaces is assumed. -/
theorem inner_suzukiX19BComplexUnitDiskSolution_zeroExtension
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1) (v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 b hb w hw)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold
          ⟨suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos hb)
            (suzukiSmoothCoreZeroExtension hab v)⟩) =
      inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
          ⟨suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos ha) v⟩) := by
  rw [inner_suzukiX19BComplexUnitDiskSolution_core,
    inner_suzukiX19BComplexUnitDiskSolution_core]
  exact inner_suzukiX19BComplexExponentialForcing_zeroExtension
    (suzukiDF6E_radius_pos ha) hab w v

/-- The nested-radius weak solution identity extends from the dense smooth
differential core to every vector in the smaller shifted completion. -/
theorem inner_suzukiX19BComplexUnitDiskSolution_completionZeroExtension
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1)
    (u : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
      suzukiX19B_zero_lt_shiftThreshold) :
    inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 b hb w hw)
        (suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab u) =
      inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw) u := by
  apply DenseRange.induction_on
    (p := fun q : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold =>
      inner Complex
          (suzukiX19BComplexUnitDiskSolution
            hsource hequation25 b hb w hw)
          (suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab q) =
        inner Complex
          (suzukiX19BComplexUnitDiskSolution
            hsource hequation25 a ha w hw) q)
    (denseRange_suzukiShiftedSourceDifferentialCoreLinearMap
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    u
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro v
    rw [suzukiX19BShiftedCompletionZeroExtension_apply_core]
    change inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 b hb w hw)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 b hb 0 suzukiX19B_zero_lt_shiftThreshold
          ⟨suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos hb)
            (suzukiSmoothCoreLinearSubmoduleAsCore
              (suzukiSmoothCoreLinearSubmoduleWiden hab v))⟩) =
      inner Complex
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
          ⟨suzukiSmoothCoreDifferentialZeroMeanL2
            (suzukiDF6E_radius_pos ha)
            (suzukiSmoothCoreLinearSubmoduleAsCore v)⟩)
    rw [suzukiSmoothCoreLinearSubmoduleAsCore_widen]
    exact inner_suzukiX19BComplexUnitDiskSolution_zeroExtension
      hsource hequation25 ha hb hab w hw
        (suzukiSmoothCoreLinearSubmoduleAsCore v)

/-- The difference between the larger solution and the transported smaller
solution is orthogonal to the entire transported smaller completion. -/
theorem inner_suzukiX19BComplexUnitDiskSolution_sub_zeroExtension
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1)
    (u : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
      suzukiX19B_zero_lt_shiftThreshold) :
    inner Complex
        (suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
          suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab
            (suzukiX19BComplexUnitDiskSolution
              hsource hequation25 a ha w hw))
        (suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab u) = 0 := by
  rw [inner_sub_left,
    inner_suzukiX19BComplexUnitDiskSolution_completionZeroExtension]
  have hinner :=
    (suzukiX19BShiftedCompletionZeroExtensionLinearIsometry
      hsource hequation25 ha hb hab).inner_map_map
      (suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha w hw) u
  change inner Complex
      (suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hb hab
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw))
      (suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hb hab u) =
    inner Complex
      (suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha w hw) u
    at hinner
  rw [hinner]
  exact sub_self _

/-- The transported smaller solution is the best approximation to the larger
solution among all vectors transported from that smaller completion. -/
theorem norm_suzukiX19BComplexUnitDiskSolution_sub_zeroExtension_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hb : b ∈ SuzukiDF6EInterval) (hab : a ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1)
    (u : SuzukiShiftedSourceEnergyCompletion hsource hequation25 a ha 0
      suzukiX19B_zero_lt_shiftThreshold) :
    ‖suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab
          (suzukiX19BComplexUnitDiskSolution
            hsource hequation25 a ha w hw)‖ ≤
      ‖suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab u‖ := by
  let residual :=
    suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
      suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hb hab
        (suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha w hw)
  let correction := suzukiX19BShiftedCompletionZeroExtension
    hsource hequation25 ha hb hab
      (suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha w hw - u)
  have horth : inner Complex residual correction = 0 := by
    exact inner_suzukiX19BComplexUnitDiskSolution_sub_zeroExtension
      hsource hequation25 ha hb hab w hw
        (suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha w hw - u)
  have hsum : residual + correction =
      suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab u := by
    dsimp only [residual, correction]
    rw [map_sub]
    abel
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    residual correction horth
  rw [hsum] at hpyth
  dsimp only [residual] at hpyth ⊢
  nlinarith [sq_nonneg ‖correction‖,
    norm_nonneg
      (suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb hab u)]

/-- At every interior released radius, the canonical solution is a strong
completion-norm limit of canonical solutions transported from strict smaller
released radii. -/
theorem exists_strictSmaller_suzukiX19BComplexUnitDiskSolution_close
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b)
    (w : Complex) (hw : ‖w‖ ≤ 1) {ε : Real} (hε : 0 < ε) :
    ∃ (a : Real) (ha : a ∈ SuzukiDF6EInterval) (hab : a < b),
      ‖suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
          suzukiX19BShiftedCompletionZeroExtension
            hsource hequation25 ha hb hab.le
            (suzukiX19BComplexUnitDiskSolution
              hsource hequation25 a ha w hw)‖ < ε := by
  have hclosure :
      suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw ∈
        closure (suzukiX19BStrictSmallerCompletionImages
          hsource hequation25 hb) :=
    dense_suzukiX19BStrictSmallerCompletionImages
      hsource hequation25 hb hleft _
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hclosure ε hε
  rcases hy with ⟨a, ha, hab, u, hu⟩
  refine ⟨a, ha, hab, ?_⟩
  apply lt_of_le_of_lt
    (norm_suzukiX19BComplexUnitDiskSolution_sub_zeroExtension_le
      hsource hequation25 ha hb hab.le w hw u)
  simpa only [hu, dist_eq_norm] using hdist

/-- The transported-solution approximation error decreases when the smaller
radius is enlarged. -/
theorem norm_suzukiX19BComplexUnitDiskSolution_radius_mono
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a c b : Real} (ha : a ∈ SuzukiDF6EInterval)
    (hc : c ∈ SuzukiDF6EInterval) (hb : b ∈ SuzukiDF6EInterval)
    (hac : a ≤ c) (hcb : c ≤ b)
    (w : Complex) (hw : ‖w‖ ≤ 1) :
    ‖suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 hc hb hcb
          (suzukiX19BComplexUnitDiskSolution
            hsource hequation25 c hc w hw)‖ ≤
      ‖suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
        suzukiX19BShiftedCompletionZeroExtension
          hsource hequation25 ha hb (hac.trans hcb)
          (suzukiX19BComplexUnitDiskSolution
            hsource hequation25 a ha w hw)‖ := by
  have hbest :=
    norm_suzukiX19BComplexUnitDiskSolution_sub_zeroExtension_le
      hsource hequation25 hc hb hcb w hw
      (suzukiX19BShiftedCompletionZeroExtension
        hsource hequation25 ha hc hac
        (suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw))
  rw [suzukiX19BShiftedCompletionZeroExtension_trans] at hbest
  exact hbest

/-- Strong one-sided radius continuity on the released window: for every
interior radius `b` and tolerance, all sufficiently large smaller released
radii have transported canonical solutions within that tolerance of the
radius-`b` solution. -/
theorem eventually_suzukiX19BComplexUnitDiskSolution_close_from_below
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b)
    (w : Complex) (hw : ‖w‖ ≤ 1) {ε : Real} (hε : 0 < ε) :
    ∃ (a₀ : Real) (ha₀ : a₀ ∈ SuzukiDF6EInterval) (ha₀b : a₀ < b),
      ∀ (a : Real) (ha : a ∈ SuzukiDF6EInterval)
        (ha₀a : a₀ ≤ a) (hab : a ≤ b),
        ‖suzukiX19BComplexUnitDiskSolution hsource hequation25 b hb w hw -
            suzukiX19BShiftedCompletionZeroExtension
              hsource hequation25 ha hb hab
              (suzukiX19BComplexUnitDiskSolution
                hsource hequation25 a ha w hw)‖ < ε := by
  obtain ⟨a₀, ha₀, ha₀b, hclose⟩ :=
    exists_strictSmaller_suzukiX19BComplexUnitDiskSolution_close
      hsource hequation25 hb hleft w hw hε
  refine ⟨a₀, ha₀, ha₀b, ?_⟩
  intro a ha ha₀a hab
  exact lt_of_le_of_lt
    (norm_suzukiX19BComplexUnitDiskSolution_radius_mono
      hsource hequation25 ha₀ ha hb ha₀a hab w hw)
    hclose

/-- Radius- and spectral-parameter-uniform solution bound on the complex
unit disk. -/
theorem norm_suzukiX19BComplexUnitDiskSolution_le_fourThousand
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w : Complex) (hw : ‖w‖ ≤ 1) :
    ‖suzukiX19BComplexUnitDiskSolution
        hsource hequation25 a ha w hw‖ ≤ 4000 := by
  have hbound := norm_suzukiShiftedSourceEnergyRieszVector_le
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BComplexExponentialForcing a w)
      (suzukiSourceKDualBoundAt_x19bComplexExponential_five ha w hw)
  have hbound' :
      ‖suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw‖ ≤
        5 / Real.sqrt (1 / 400000 : Real) := by
    simpa [suzukiX19BComplexUnitDiskSolution] using hbound
  exact hbound'.trans suzukiX19B_rieszConstant_le_fourThousand

/-- The weak source equation uniquely selects the unit-disk solution. -/
theorem eq_suzukiX19BComplexUnitDiskSolution_of_weakEquation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w : Complex) (hw : ‖w‖ ≤ 1)
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold)
    (hweak : ∀ u : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      inner Complex x
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold u) =
        inner Complex (suzukiX19BComplexExponentialForcing a w) u.toL2) :
    x = suzukiX19BComplexUnitDiskSolution
      hsource hequation25 a ha w hw := by
  exact eq_suzukiShiftedSourceEnergyRieszVector_of_weakEquation_core
    hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold
      (suzukiX19BComplexExponentialForcing a w)
      (suzukiSourceKDualBoundAt_x19bComplexExponential_five ha w hw) x hweak

/-- On the real diameter, the complex exponential is exactly the original
real-exponential continuous source. -/
theorem suzukiX19BComplexExponentialContinuous_ofReal
    (a c : Real) :
    suzukiX19BComplexExponentialContinuous a (c : Complex) =
      suzukiFredholmExponentialContinuous a c := by
  ext x
  simp only [suzukiX19BComplexExponentialContinuous_apply,
    suzukiFredholmExponentialContinuous_apply]
  rw [Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_exp]

/-- Hence the new projected source family restricts to the previously
verified source family on the full real diameter. -/
theorem suzukiX19BComplexExponentialForcing_ofReal
    (a c : Real) :
    suzukiX19BComplexExponentialForcing a (c : Complex) =
      suzukiFredholmExponentialForcing a c := by
  unfold suzukiX19BComplexExponentialForcing
  rw [suzukiX19BComplexExponentialContinuous_ofReal]
  rfl

/-- The two-dimensional unit-disk solution genuinely extends the previously
closed compact segment, point by point. -/
theorem suzukiX19BComplexUnitDiskSolution_ofReal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (c : Real) (hc : |c| ≤ 1) :
    suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha (c : Complex)
        (by simpa [Complex.norm_real, Real.norm_eq_abs] using hc) =
      suzukiX19BImaginarySegmentSolution
        hsource hequation25 a ha c hc := by
  apply eq_suzukiX19BImaginarySegmentSolution_of_weakEquation
  intro u
  rw [inner_suzukiX19BComplexUnitDiskSolution_core,
    suzukiX19BComplexExponentialForcing_ofReal]

/-- Pointwise Lipschitz estimate for complex exponentials on the closed unit
disk, uniform over the released radius window. -/
theorem norm_suzukiX19BComplexExp_sub_le_pointConstant
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (w q : Complex) (hw : ‖w‖ ≤ 1) (hq : ‖q‖ ≤ 1)
    {x : Real} (hx : x ∈ Set.Icc (-a) a) :
    ‖Complex.exp (conj w * (x : Complex)) -
        Complex.exp (conj q * (x : Complex))‖ ≤
      suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ := by
  have hxabs : |x| ≤ a := (abs_le).2 hx
  have hwq : ‖w - q‖ ≤ 2 := by
    calc
      ‖w - q‖ ≤ ‖w‖ + ‖q‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hargLocal : ‖conj (w - q) * (x : Complex)‖ ≤
      ‖w - q‖ * suzukiProjectAStar := by
    rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hxabs.trans ha.2) (norm_nonneg _)
  have harg : ‖conj (w - q) * (x : Complex)‖ ≤
      2 * suzukiProjectAStar :=
    hargLocal.trans
      (mul_le_mul_of_nonneg_right hwq suzukiProjectAStar_pos.le)
  have hqLocal : q.re * x ≤ suzukiProjectAStar := by
    calc
      q.re * x ≤ |q.re * x| := le_abs_self _
      _ = |q.re| * |x| := abs_mul _ _
      _ ≤ 1 * suzukiProjectAStar := by
        exact mul_le_mul
          ((Complex.abs_re_le_norm q).trans hq)
          (hxabs.trans ha.2) (abs_nonneg x) zero_le_one
      _ = suzukiProjectAStar := one_mul _
  have hfactor : ‖Complex.exp (conj q * (x : Complex))‖ ≤
      Real.exp suzukiProjectAStar := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using hqLocal
  have htail := Complex.norm_exp_sub_sum_le_norm_mul_exp
    (conj (w - q) * (x : Complex)) 1
  have htail' :
      ‖Complex.exp (conj (w - q) * (x : Complex)) - 1‖ ≤
        ‖conj (w - q) * (x : Complex)‖ *
          Real.exp ‖conj (w - q) * (x : Complex)‖ := by
    simpa using htail
  have hid :
      Complex.exp (conj w * (x : Complex)) -
          Complex.exp (conj q * (x : Complex)) =
        Complex.exp (conj q * (x : Complex)) *
          (Complex.exp (conj (w - q) * (x : Complex)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    simp only [map_sub]
    ring
  rw [hid, norm_mul]
  calc
    ‖Complex.exp (conj q * (x : Complex))‖ *
        ‖Complex.exp (conj (w - q) * (x : Complex)) - 1‖ ≤
      Real.exp suzukiProjectAStar *
        (‖conj (w - q) * (x : Complex)‖ *
          Real.exp ‖conj (w - q) * (x : Complex)‖) := by
      exact mul_le_mul hfactor htail' (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp suzukiProjectAStar *
        ((‖w - q‖ * suzukiProjectAStar) *
          Real.exp (2 * suzukiProjectAStar)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul hargLocal (Real.exp_le_exp.mpr harg)
        (Real.exp_pos _).le
        (mul_nonneg (norm_nonneg _) suzukiProjectAStar_pos.le)
    _ = suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ := by
      unfold suzukiX19BExponentialDifferencePointConstant
      ring

/-- Quantitative `L2` continuity of the complex exponential representatives
on the full spectral unit disk. -/
theorem norm_suzukiX19BComplexExponentialL2_sub_le
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (w q : Complex) (hw : ‖w‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q‖ ≤
      suzukiX19BExponentialL2DifferenceConstant * ‖w - q‖ := by
  have hsqrt : 0 < Real.sqrt (2 * a) := by
    exact Real.sqrt_pos.2
      (mul_pos (by norm_num) (suzukiDF6E_radius_pos ha))
  have hbound :
      ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
          suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q‖ ≤
        (suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ *
            Real.sqrt (2 * a)) *
          ‖suzukiYoshidaExponentialL2 a (suzukiDF6E_radius_pos ha) 0‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
      (c := suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ *
        Real.sqrt (2 * a))
      (f := suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
      (g := suzukiYoshidaExponentialL2 a (suzukiDF6E_radius_pos ha) 0)
    filter_upwards [
      suzukiX19BComplexExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) w,
      suzukiX19BComplexExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) q,
      Lp.coeFn_sub
        (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w)
        (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q),
      suzukiYoshidaExponentialL2_coeFn
        (suzukiDF6E_radius_pos ha) 0] with x hwx hqx hsub hzero
    rw [hsub, Pi.sub_apply, hwx, hqx, hzero]
    by_cases hx : x ∈ Set.Icc (-a) a
    · rw [suzukiX19BComplexExponentialFunction,
        suzukiX19BComplexExponentialFunction,
        suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Set.indicator_of_mem hx]
      have hzeroNorm :
          ‖(((Real.sqrt (2 * a))⁻¹ : Complex) *
              Complex.exp
                (Complex.I *
                  (((0 : Int) : Complex) * (Real.pi : Complex) /
                    (a : Complex)) * (x : Complex)))‖ =
            (Real.sqrt (2 * a))⁻¹ := by
        have hsqrtA : 0 < Real.sqrt a :=
          Real.sqrt_pos.2 (suzukiDF6E_radius_pos ha)
        have hsqrtTwo : 0 < Real.sqrt 2 := by positivity
        simp [Real.norm_eq_abs, abs_of_pos hsqrtA,
          abs_of_pos hsqrtTwo]
      rw [hzeroNorm, mul_assoc, mul_inv_cancel₀ hsqrt.ne', mul_one]
      exact norm_suzukiX19BComplexExp_sub_le_pointConstant ha w q hw hq hx
    · simp [suzukiX19BComplexExponentialFunction,
        suzukiYoshidaExponentialFunction, hx]
  have hlocal :
      ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
          suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q‖ ≤
        suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ *
          Real.sqrt (2 * a) := by
    simpa [(orthonormal_suzukiYoshidaExponentialL2
      (suzukiDF6E_radius_pos ha)).norm_eq_one] using hbound
  calc
    ‖suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
        suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q‖ ≤
        suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ *
          Real.sqrt (2 * a) := hlocal
    _ ≤ suzukiX19BExponentialDifferencePointConstant * ‖w - q‖ *
        Real.sqrt (2 * suzukiProjectAStar) := by
      exact mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by linarith [ha.2]))
        (mul_nonneg suzukiX19BExponentialDifferencePointConstant_nonneg
          (norm_nonneg _))
    _ = suzukiX19BExponentialL2DifferenceConstant * ‖w - q‖ := by
      unfold suzukiX19BExponentialL2DifferenceConstant
      ring

/-- Quantitative source-dual continuity of the projected complex exponential
forcing on the full spectral unit disk. -/
theorem suzukiSourceKDualBoundAt_x19bComplexExponential_sub
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    (w q : Complex) (hw : ‖w‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    SuzukiSourceKDualBoundAt a
      (suzukiX19BComplexExponentialForcing a w -
        suzukiX19BComplexExponentialForcing a q)
      (suzukiX19BSourceDifferenceConstant * ‖w - q‖) := by
  apply suzukiSourceKDualBoundAt_of_smoothCore
    (suzukiDF6E_radius_pos ha)
  intro v
  rw [inner_sub_left,
    inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential
      (suzukiDF6E_radius_pos ha) w v,
    inner_suzukiX19BComplexExponentialForcing_smoothCoreDifferential
      (suzukiDF6E_radius_pos ha) q v]
  have hdiffPair :
      ‖inner Complex
          (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
            suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
          (suzukiSmoothCoreToL2 v)‖ ≤
        (suzukiX19BExponentialL2DifferenceConstant * ‖w - q‖) *
          ‖suzukiSmoothCoreToL2 v‖ := by
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (norm_suzukiX19BComplexExponentialL2_sub_le ha w q hw hq)
        (norm_nonneg _))
  have hqPair :
      ‖inner Complex
          (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
          (suzukiSmoothCoreToL2 v)‖ ≤
        suzukiDF6FUniformFredholmBound * ‖suzukiSmoothCoreToL2 v‖ := by
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right
        (norm_suzukiX19BComplexExponentialL2_le_uniform_of_norm_le_one
          ha q hq)
        (norm_nonneg _))
  have halgebra :
      -(Complex.I * w) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w)
            (suzukiSmoothCoreToL2 v) -
        (-(Complex.I * q) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v)) =
      -(Complex.I * w) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
              suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v) -
        (Complex.I * (w - q)) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v) := by
    rw [inner_sub_left]
    ring
  rw [halgebra]
  calc
    ‖-(Complex.I * w) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
              suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v) -
        (Complex.I * (w - q)) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v)‖ ≤
        ‖-(Complex.I * w) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
              suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v)‖ +
        ‖(Complex.I * (w - q)) *
          inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v)‖ := norm_sub_le _ _
    _ = ‖w‖ *
          ‖inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) w -
              suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v)‖ +
        ‖w - q‖ *
          ‖inner Complex
            (suzukiX19BComplexExponentialL2 (suzukiDF6E_radius_pos ha) q)
            (suzukiSmoothCoreToL2 v)‖ := by simp
    _ ≤ ‖w‖ *
          ((suzukiX19BExponentialL2DifferenceConstant * ‖w - q‖) *
            ‖suzukiSmoothCoreToL2 v‖) +
        ‖w - q‖ *
          (suzukiDF6FUniformFredholmBound *
            ‖suzukiSmoothCoreToL2 v‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hdiffPair (norm_nonneg w))
        (mul_le_mul_of_nonneg_left hqPair (norm_nonneg (w - q)))
    _ ≤ 1 *
          ((suzukiX19BExponentialL2DifferenceConstant * ‖w - q‖) *
            ‖suzukiSmoothCoreToL2 v‖) +
        ‖w - q‖ *
          (suzukiDF6FUniformFredholmBound *
            ‖suzukiSmoothCoreToL2 v‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hw
          (mul_nonneg
            (mul_nonneg suzukiX19BExponentialL2DifferenceConstant_nonneg
              (norm_nonneg (w - q)))
            (norm_nonneg _)))
        (le_refl _)
    _ = (suzukiX19BSourceDifferenceConstant * ‖w - q‖) *
        ‖suzukiSmoothCoreToL2 v‖ := by
      unfold suzukiX19BSourceDifferenceConstant
      ring

/-- The canonical unit-disk weak solutions vary Lipschitz-continuously with
the full complex spectral coefficient. -/
theorem norm_suzukiX19BComplexUnitDiskSolution_sub_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w q : Complex) (hw : ‖w‖ ≤ 1) (hq : ‖q‖ ≤ 1) :
    ‖suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha w hw -
        suzukiX19BComplexUnitDiskSolution
          hsource hequation25 a ha q hq‖ ≤
      suzukiX19BSolutionDifferenceConstant * ‖w - q‖ := by
  let y : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
    suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha w hw -
      suzukiX19BComplexUnitDiskSolution hsource hequation25 a ha q hq
  let B : Real := suzukiX19BSolutionDifferenceConstant * ‖w - q‖
  have hsqrt : 0 < Real.sqrt (1 / 400000 : Real) := by positivity
  have hdual :=
    suzukiSourceKDualBoundAt_x19bComplexExponential_sub ha w q hw hq
  have hcore : ∀ u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      ‖inner Complex y
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u)‖ ≤
        B * ‖suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0
            suzukiX19B_zero_lt_shiftThreshold u‖ := by
    intro u
    have hcompare := suzukiDF6F_sourceKSeminorm_le_shiftedSeminorm
      hsource hequation25 ha suzukiX19B_zero_lt_shiftThreshold u.toL2
    have hcompare' :
        Real.sqrt (1 / 400000 : Real) *
            suzukiSourceKSeminorm a u.toL2 ≤
          ‖suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u‖ := by
      rw [← norm_suzukiShiftedSourceEnergyCore u] at hcompare
      simpa using hcompare
    have hscale :
        (suzukiX19BSourceDifferenceConstant * ‖w - q‖) *
            suzukiSourceKSeminorm a u.toL2 ≤
          B * ‖suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u‖ := by
      calc
        (suzukiX19BSourceDifferenceConstant * ‖w - q‖) *
            suzukiSourceKSeminorm a u.toL2 =
            B * (Real.sqrt (1 / 400000 : Real) *
              suzukiSourceKSeminorm a u.toL2) := by
          dsimp only [B]
          unfold suzukiX19BSolutionDifferenceConstant
          field_simp
        _ ≤ B * ‖suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u‖ := by
          exact mul_le_mul_of_nonneg_left hcompare'
            (mul_nonneg suzukiX19BSolutionDifferenceConstant_nonneg
              (norm_nonneg (w - q)))
    calc
      ‖inner Complex y
          (suzukiShiftedSourceEnergyCoreToCompletion
            hsource hequation25 a ha 0
              suzukiX19B_zero_lt_shiftThreshold u)‖ =
          ‖inner Complex
            (suzukiX19BComplexExponentialForcing a w -
              suzukiX19BComplexExponentialForcing a q) u.toL2‖ := by
        dsimp only [y]
        rw [inner_sub_left,
          inner_suzukiX19BComplexUnitDiskSolution_core,
          inner_suzukiX19BComplexUnitDiskSolution_core,
          inner_sub_left]
      _ ≤ (suzukiX19BSourceDifferenceConstant * ‖w - q‖) *
          suzukiSourceKSeminorm a u.toL2 := hdual u.toL2
      _ ≤ B * ‖suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha 0
            suzukiX19B_zero_lt_shiftThreshold u‖ := hscale
  have hall : ∀ z : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold,
      ‖inner Complex y z‖ ≤ B * ‖z‖ := by
    intro z
    let p : SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold → Prop :=
      fun t => ‖inner Complex y t‖ ≤ B * ‖t‖
    apply DenseRange.induction_on (p := p)
      (denseRange_suzukiShiftedSourceEnergyCoreToCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold) z
    · apply isClosed_le
      · fun_prop
      · fun_prop
    · intro u
      exact hcore u
  have hself := hall y
  have hselfNorm : ‖inner Complex y y‖ = ‖y‖ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K]
  rw [hselfNorm] at hself
  have hy : ‖y‖ ≤ B := by
    by_cases hy0 : ‖y‖ = 0
    · rw [hy0]
      exact mul_nonneg suzukiX19BSolutionDifferenceConstant_nonneg
        (norm_nonneg (w - q))
    · have hypos : 0 < ‖y‖ :=
        lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy0)
      nlinarith
  simpa [y, B] using hy

/-- The closed complex unit disk used as the two-dimensional spectral
parameter space. -/
abbrev SuzukiX19BComplexUnitDisk := Metric.closedBall (0 : Complex) 1

/-- Fixed-radius canonical solution map on the full complex unit disk. -/
def suzukiX19BComplexUnitDiskSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    SuzukiX19BComplexUnitDisk →
      SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha 0 suzukiX19B_zero_lt_shiftThreshold :=
  fun w => suzukiX19BComplexUnitDiskSolution
    hsource hequation25 a ha w.1 (by
      have h := w.2
      change w.1 ∈ Metric.closedBall (0 : Complex) 1 at h
      rw [Metric.mem_closedBall] at h
      simpa [dist_eq_norm] using h)

/-- The fixed-radius complex-disk solution map is Lipschitz. -/
theorem lipschitzWith_suzukiX19BComplexUnitDiskSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    LipschitzWith suzukiX19BSolutionDifferenceNNReal
      (suzukiX19BComplexUnitDiskSolutionMap hsource hequation25 a ha) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro w q
  have hw : ‖w.1‖ ≤ 1 := by
    have h := w.2
    change w.1 ∈ Metric.closedBall (0 : Complex) 1 at h
    rw [Metric.mem_closedBall] at h
    simpa [dist_eq_norm] using h
  have hq : ‖q.1‖ ≤ 1 := by
    have h := q.2
    change q.1 ∈ Metric.closedBall (0 : Complex) 1 at h
    rw [Metric.mem_closedBall] at h
    simpa [dist_eq_norm] using h
  have h := norm_suzukiX19BComplexUnitDiskSolution_sub_le
    hsource hequation25 a ha w.1 q.1 hw hq
  rw [show (suzukiX19BSolutionDifferenceNNReal : Real) =
    suzukiX19BSolutionDifferenceConstant by rfl]
  simpa [suzukiX19BComplexUnitDiskSolutionMap,
    dist_eq_norm, Subtype.dist_eq] using h

/-- Hence the full unit-disk solution family is continuous at every fixed
released radius. -/
theorem continuous_suzukiX19BComplexUnitDiskSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    Continuous (suzukiX19BComplexUnitDiskSolutionMap
      hsource hequation25 a ha) :=
  (lipschitzWith_suzukiX19BComplexUnitDiskSolutionMap
    hsource hequation25 a ha).continuous

/-- The image of the full two-dimensional spectral disk is compact in the
shifted source-energy completion. -/
theorem isCompact_range_suzukiX19BComplexUnitDiskSolutionMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    IsCompact (Set.range (suzukiX19BComplexUnitDiskSolutionMap
      hsource hequation25 a ha)) :=
  isCompact_range
    (continuous_suzukiX19BComplexUnitDiskSolutionMap
      hsource hequation25 a ha)

end

end RiemannHypothesisProject.Experiments.M100
