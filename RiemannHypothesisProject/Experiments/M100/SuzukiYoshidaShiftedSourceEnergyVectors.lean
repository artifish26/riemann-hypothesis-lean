import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceEnergyCompletion
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmUniformBound
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# M100-DF6F canonical vectors in the shifted source-energy completion

The checked source-dual forcing estimates and the comparison between the
`K_a` and shifted norms make the projected plus/minus forcing functionals
continuous on `H(S_(a,lambda))`.  Fréchet--Riesz therefore constructs canonical
completion vectors satisfying the exact weak equations.  This is an existence
theorem in the completion only; it does not assert that either vector lies in
the interval-`L2` core image.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace ComplexConjugate

/-- The ambient pairing with `f`, regarded algebraically as a functional on
the shifted source-energy core. -/
def suzukiShiftedSourceEnergyCoreForcingLinearMap
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a) :
    SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda →ₗ[Complex] Complex where
  toFun u := inner Complex f u.toL2
  map_add' u v := by
    rw [SuzukiShiftedSourceEnergyCore.toL2_add, inner_add_right]
  map_smul' c u := by
    rw [SuzukiShiftedSourceEnergyCore.toL2_smul]
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (inner_smul_right f u.toL2 c)

@[simp]
theorem suzukiShiftedSourceEnergyCoreForcingLinearMap_apply
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    suzukiShiftedSourceEnergyCoreForcingLinearMap
        hsource hequation25 a ha lambda hlambda f u =
      inner Complex f u.toL2 :=
  rfl

/-- The rational Fredholm source-dual bound becomes a genuine operator bound
in the shifted source-energy norm. -/
theorem norm_suzukiShiftedSourceEnergyCoreForcingLinearMap_le_five
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    {a : Real} (ha : a ∈ SuzukiDF6EInterval)
    {lambda : Real} (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    ‖suzukiShiftedSourceEnergyCoreForcingLinearMap
        hsource hequation25 a ha lambda hlambda f u‖ ≤
      (5 / Real.sqrt ((1 / 400000 : Real) - lambda)) * ‖u‖ := by
  have hcoefficient : 0 < (1 / 400000 : Real) - lambda := by
    linarith
  have hsqrt : 0 < Real.sqrt ((1 / 400000 : Real) - lambda) :=
    Real.sqrt_pos.2 hcoefficient
  have hcompare :=
    suzukiDF6F_sourceKSeminorm_le_shiftedSeminorm
      hsource hequation25 ha hlambda u.toL2
  rw [← norm_suzukiShiftedSourceEnergyCore u] at hcompare
  calc
    ‖suzukiShiftedSourceEnergyCoreForcingLinearMap
        hsource hequation25 a ha lambda hlambda f u‖ =
        ‖inner Complex f u.toL2‖ := rfl
    _ ≤ 5 * suzukiSourceKSeminorm a u.toL2 := hdual u.toL2
    _ = (5 / Real.sqrt ((1 / 400000 : Real) - lambda)) *
        (Real.sqrt ((1 / 400000 : Real) - lambda) *
          suzukiSourceKSeminorm a u.toL2) := by
      symm
      calc
        (5 / Real.sqrt ((1 / 400000 : Real) - lambda)) *
            (Real.sqrt ((1 / 400000 : Real) - lambda) *
              suzukiSourceKSeminorm a u.toL2) =
            5 *
              (Real.sqrt ((1 / 400000 : Real) - lambda) /
                Real.sqrt ((1 / 400000 : Real) - lambda)) *
              suzukiSourceKSeminorm a u.toL2 := by ring
        _ = 5 * suzukiSourceKSeminorm a u.toL2 := by
          rw [div_self hsqrt.ne', mul_one]
    _ ≤ (5 / Real.sqrt ((1 / 400000 : Real) - lambda)) * ‖u‖ := by
      exact mul_le_mul_of_nonneg_left hcompare (by positivity)

/-- The bounded forcing functional on the shifted source-energy core. -/
def suzukiShiftedSourceEnergyCoreForcingCLM
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5) :
    SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda →L[Complex] Complex :=
  (suzukiShiftedSourceEnergyCoreForcingLinearMap
    hsource hequation25 a ha lambda hlambda f).mkContinuous
      (5 / Real.sqrt ((1 / 400000 : Real) - lambda))
      (norm_suzukiShiftedSourceEnergyCoreForcingLinearMap_le_five
        hsource hequation25 ha hlambda f hdual)

@[simp]
theorem suzukiShiftedSourceEnergyCoreForcingCLM_apply
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    suzukiShiftedSourceEnergyCoreForcingCLM
        hsource hequation25 a ha lambda hlambda f hdual u =
      inner Complex f u.toL2 :=
  rfl

/-- Continuous extension of the forcing functional from the dense core to
the whole shifted completion. -/
def suzukiShiftedSourceEnergyForcingCLM
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5) :
    SuzukiShiftedSourceEnergyCompletion
        hsource hequation25 a ha lambda hlambda →L[Complex] Complex :=
  ContinuousLinearMap.extend
    (suzukiShiftedSourceEnergyCoreForcingCLM
      hsource hequation25 a ha lambda hlambda f hdual)
    (suzukiShiftedSourceEnergyCoreToCompletion
      hsource hequation25 a ha lambda hlambda).toContinuousLinearMap

@[simp]
theorem suzukiShiftedSourceEnergyForcingCLM_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    suzukiShiftedSourceEnergyForcingCLM
        hsource hequation25 a ha lambda hlambda f hdual
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda u) =
      inner Complex f u.toL2 := by
  change
    (suzukiShiftedSourceEnergyCoreForcingCLM
        hsource hequation25 a ha lambda hlambda f hdual).extend
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda).toContinuousLinearMap
        ((suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda).toContinuousLinearMap u) =
      inner Complex f u.toL2
  rw [ContinuousLinearMap.extend_eq _
    (denseRange_suzukiShiftedSourceEnergyCoreToCompletion
      hsource hequation25 a ha lambda hlambda)
    (suzukiShiftedSourceEnergyCoreToCompletion
      hsource hequation25 a ha lambda hlambda).isometry.isUniformInducing]
  rfl

/-- The Fréchet--Riesz vector representing one bounded forcing functional in
the shifted source-energy completion. -/
def suzukiShiftedSourceEnergyRieszVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda :=
  (InnerProductSpace.toDual Complex
    (SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)).symm
        (suzukiShiftedSourceEnergyForcingCLM
          hsource hequation25 a ha lambda hlambda f hdual)

/-- Exact weak equation for the Riesz vector on the whole completion. -/
theorem inner_suzukiShiftedSourceEnergyRieszVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda) :
    inner Complex
        (suzukiShiftedSourceEnergyRieszVector
          hsource hequation25 a ha lambda hlambda f hdual) x =
      suzukiShiftedSourceEnergyForcingCLM
        hsource hequation25 a ha lambda hlambda f hdual x := by
  exact InnerProductSpace.toDual_symm_apply

/-- Core form of the exact weak equation. -/
theorem inner_suzukiShiftedSourceEnergyRieszVector_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    inner Complex
        (suzukiShiftedSourceEnergyRieszVector
          hsource hequation25 a ha lambda hlambda f hdual)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda u) =
      inner Complex f u.toL2 := by
  rw [inner_suzukiShiftedSourceEnergyRieszVector,
    suzukiShiftedSourceEnergyForcingCLM_core]

/-- If the Riesz vector is individually represented by an interval-`L2` core
vector, its weak equation forces the literal projected operator equation. -/
theorem suzukiSourceShiftedOperator_realizedL2_eq_of_rieszVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (f : SuzukiFiniteIntervalZeroMeanL2 a)
    (hdual : SuzukiSourceKDualBoundAt a f 5)
    (hx : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiShiftedSourceEnergyRieszVector
        hsource hequation25 a ha lambda hlambda f hdual)) :
    suzukiSourceShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2
          (suzukiShiftedSourceEnergyRieszVector
            hsource hequation25 a ha lambda hlambda f hdual) hx) =
      f := by
  apply ext_inner_right Complex
  intro v
  have hweak := inner_suzukiShiftedSourceEnergyRieszVector_core
    hsource hequation25 a ha lambda hlambda f hdual
      (⟨v⟩ : SuzukiShiftedSourceEnergyCore
        hsource hequation25 a ha lambda hlambda)
  have hrealized :=
    suzukiShiftedSourceEnergyCoreToCompletion_realizedL2
      (suzukiShiftedSourceEnergyRieszVector
        hsource hequation25 a ha lambda hlambda f hdual) hx
  rw [← hrealized] at hweak
  simpa [suzukiShiftedSourceEnergyCoreToCompletion] using hweak

/-- Canonical plus vector in the shifted completion, selected by the projected
`exp(x) + i` forcing functional. -/
def suzukiDF6FShiftedSourceEnergyPlusVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda :=
  suzukiShiftedSourceEnergyRieszVector
    hsource hequation25 a ha lambda hlambda
      (suzukiFredholmPlusForcing a)
      (suzukiSourceKDualBoundAt_fredholmPlus_five ha)

/-- Canonical minus vector in the shifted completion. -/
def suzukiDF6FShiftedSourceEnergyMinusVector
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda :=
  suzukiShiftedSourceEnergyRieszVector
    hsource hequation25 a ha lambda hlambda
      (suzukiFredholmMinusForcing a)
      (suzukiSourceKDualBoundAt_fredholmMinus_five ha)

/-- Exact weak plus equation on every shifted-energy core vector. -/
theorem inner_suzukiDF6FShiftedSourceEnergyPlusVector_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    inner Complex
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda u) =
      inner Complex (suzukiFredholmPlusForcing a) u.toL2 := by
  exact inner_suzukiShiftedSourceEnergyRieszVector_core
    hsource hequation25 a ha lambda hlambda
      (suzukiFredholmPlusForcing a)
      (suzukiSourceKDualBoundAt_fredholmPlus_five ha) u

/-- Exact weak minus equation on every shifted-energy core vector. -/
theorem inner_suzukiDF6FShiftedSourceEnergyMinusVector_core
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda) :
    inner Complex
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda)
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda u) =
      inner Complex (suzukiFredholmMinusForcing a) u.toL2 := by
  exact inner_suzukiShiftedSourceEnergyRieszVector_core
    hsource hequation25 a ha lambda hlambda
      (suzukiFredholmMinusForcing a)
      (suzukiSourceKDualBoundAt_fredholmMinus_five ha) u

/-- Realizability of the canonical plus completion vector is enough to obtain
the projected plus Fredholm equation. -/
theorem suzukiDF6FShiftedSourceEnergyPlusVector_projected_of_realizable
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (hx : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda)) :
    suzukiSourceShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2
          (suzukiDF6FShiftedSourceEnergyPlusVector
            hsource hequation25 a ha lambda hlambda) hx) =
      suzukiFredholmPlusForcing a := by
  exact suzukiSourceShiftedOperator_realizedL2_eq_of_rieszVector
    hsource hequation25 a ha lambda hlambda
      (suzukiFredholmPlusForcing a)
      (suzukiSourceKDualBoundAt_fredholmPlus_five ha) hx

/-- Minus-sign counterpart. -/
theorem suzukiDF6FShiftedSourceEnergyMinusVector_projected_of_realizable
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (hx : SuzukiShiftedSourceEnergyL2Realizable
      (suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda)) :
    suzukiSourceShiftedOperator a lambda
        (suzukiShiftedSourceEnergyRealizedL2
          (suzukiDF6FShiftedSourceEnergyMinusVector
            hsource hequation25 a ha lambda hlambda) hx) =
      suzukiFredholmMinusForcing a := by
  exact suzukiSourceShiftedOperator_realizedL2_eq_of_rieszVector
    hsource hequation25 a ha lambda hlambda
      (suzukiFredholmMinusForcing a)
      (suzukiSourceKDualBoundAt_fredholmMinus_five ha) hx

end

end RiemannHypothesisProject.Experiments.M100
