import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaShiftedSourceDeficiency
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmAdjointTransport

/-!
# M100-DF6F shifted-source representative normalization

Suzuki's Section 8.3 adjoint calculation takes place in `H(S_a)`, although
that completion need not embed into interval `L2`.  The calculation therefore
determines the displayed `S_a v` only modulo the constant line: zero-mean
source tests see its orthogonal projection and nothing else.  The paper then
chooses a scale for the deficiency vector so that the constant residual is
`1`, producing the representatives `exp x + i` and `exp (-x) - i`.

This module records that normalization at the correct level.  An ambient
function represents a completion vector when its zero-mean projection gives
the vector's core functional.  The canonical Riesz vectors select the
unit-coefficient exponential class.  A separately visible scalar mean fixes
the constant representative and recovers Suzuki's printed formulas.  No
interval-`L2` realization of either completion vector is asserted.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped InnerProductSpace

local instance suzukiShiftedSourceRepresentativeZeroMeanCompleteSpace
    (a : Real) : CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- An ambient interval-`L2` function represents a shifted-completion vector
when its zero-mean projection induces exactly the vector's core functional.
This is the completion-native meaning of the formal expression `S_a v`. -/
def SuzukiShiftedSourceEnergyAmbientRepresentativeAt
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (x : SuzukiShiftedSourceEnergyCompletion
      hsource hequation25 a ha lambda hlambda)
    (rhs : SuzukiFiniteIntervalL2 a) : Prop :=
  ∀ u : SuzukiShiftedSourceEnergyCore
      hsource hequation25 a ha lambda hlambda,
    inner Complex x
        (suzukiShiftedSourceEnergyCoreToCompletion
          hsource hequation25 a ha lambda hlambda u) =
      inner Complex (suzukiFiniteIntervalZeroMeanProjection a rhs) u.toL2

/-- For the canonical plus vector, being an ambient representative is
equivalent to having the projected `exp x` forcing. -/
theorem suzukiShiftedSourceEnergyPlusVector_represents_iff_projection_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (rhs : SuzukiFiniteIntervalL2 a) :
    SuzukiShiftedSourceEnergyAmbientRepresentativeAt
        hsource hequation25 a ha lambda hlambda
        (suzukiDF6FShiftedSourceEnergyPlusVector
          hsource hequation25 a ha lambda hlambda) rhs ↔
      suzukiFiniteIntervalZeroMeanProjection a rhs =
        suzukiFredholmPlusForcing a := by
  constructor
  · intro hrep
    apply ext_inner_right Complex
    intro u
    exact (hrep ⟨u⟩).symm.trans
      (inner_suzukiDF6FShiftedSourceEnergyPlusVector_core
        hsource hequation25 a ha lambda hlambda ⟨u⟩)
  · intro hprojection u
    rw [inner_suzukiDF6FShiftedSourceEnergyPlusVector_core,
      hprojection]

/-- Minus-sign representative/projection characterization. -/
theorem suzukiShiftedSourceEnergyMinusVector_represents_iff_projection_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (rhs : SuzukiFiniteIntervalL2 a) :
    SuzukiShiftedSourceEnergyAmbientRepresentativeAt
        hsource hequation25 a ha lambda hlambda
        (suzukiDF6FShiftedSourceEnergyMinusVector
          hsource hequation25 a ha lambda hlambda) rhs ↔
      suzukiFiniteIntervalZeroMeanProjection a rhs =
        suzukiFredholmMinusForcing a := by
  constructor
  · intro hrep
    apply ext_inner_right Complex
    intro u
    exact (hrep ⟨u⟩).symm.trans
      (inner_suzukiDF6FShiftedSourceEnergyMinusVector_core
        hsource hequation25 a ha lambda hlambda ⟨u⟩)
  · intro hprojection u
    rw [inner_suzukiDF6FShiftedSourceEnergyMinusVector_core,
      hprojection]

/-- Suzuki's printed `exp x + i` function represents the canonical plus
deficiency vector in the shifted completion. -/
theorem suzukiShiftedSourceEnergyPlusVector_printedRepresentative
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyAmbientRepresentativeAt
      hsource hequation25 a ha lambda hlambda
      (suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a)) := by
  rw [suzukiShiftedSourceEnergyPlusVector_represents_iff_projection_eq]
  rfl

/-- Suzuki's printed `exp (-x) - i` function represents the canonical minus
deficiency vector. -/
theorem suzukiShiftedSourceEnergyMinusVector_printedRepresentative
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real)) :
    SuzukiShiftedSourceEnergyAmbientRepresentativeAt
      hsource hequation25 a ha lambda hlambda
      (suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda)
      (suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a)) := by
  rw [suzukiShiftedSourceEnergyMinusVector_represents_iff_projection_eq]
  rfl

/-- An ambient interval function is uniquely determined by its zero-mean
projection and its scalar mean. -/
theorem suzukiFiniteIntervalL2_eq_of_projection_eq_of_mean_eq
    {a : Real} {f g : SuzukiFiniteIntervalL2 a}
    (hprojection : suzukiFiniteIntervalZeroMeanProjection a f =
      suzukiFiniteIntervalZeroMeanProjection a g)
    (hmean : suzukiFiniteIntervalMeanCLM a f =
      suzukiFiniteIntervalMeanCLM a g) :
    f = g := by
  let residual : SuzukiFiniteIntervalL2 a := f - g
  have hzeroMean : residual ∈ SuzukiFiniteIntervalZeroMeanSubspace a := by
    rw [mem_suzukiFiniteIntervalZeroMeanSubspace]
    dsimp only [residual]
    rw [map_sub, hmean, sub_self]
  have hprojectionZero :
      suzukiFiniteIntervalZeroMeanProjection a residual = 0 := by
    dsimp only [residual]
    rw [map_sub, hprojection, sub_self]
  have horthogonal : residual ∈
      (SuzukiFiniteIntervalZeroMeanSubspace a)ᗮ := by
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mp hprojectionZero
  have hzero : residual = 0 := by
    have hmem : residual ∈
        (⊥ : Submodule Complex (SuzukiFiniteIntervalL2 a)) := by
      rw [← (SuzukiFiniteIntervalZeroMeanSubspace a).inf_orthogonal_eq_bot]
      exact ⟨hzeroMean, horthogonal⟩
    simpa using hmem
  exact sub_eq_zero.mp hzero

/-- The completion representative relation plus Suzuki's explicit scalar
normalization uniquely selects the printed plus representative. -/
theorem suzukiShiftedSourceEnergyPlusVector_representative_eq_printed
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (rhs : SuzukiFiniteIntervalL2 a)
    (hrep : SuzukiShiftedSourceEnergyAmbientRepresentativeAt
      hsource hequation25 a ha lambda hlambda
      (suzukiDF6FShiftedSourceEnergyPlusVector
        hsource hequation25 a ha lambda hlambda) rhs)
    (hmean : suzukiFiniteIntervalMeanCLM a rhs =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) +
        ((2 * a : Real) : Complex) * Complex.I) :
    rhs = suzukiFiniteIntervalContinuousToL2 a
      (suzukiFredholmPlusContinuous a) := by
  apply suzukiFiniteIntervalL2_eq_of_projection_eq_of_mean_eq
  · exact (suzukiShiftedSourceEnergyPlusVector_represents_iff_projection_eq
      hsource hequation25 a ha lambda hlambda rhs).mp hrep
  · exact hmean.trans
      (suzukiFiniteIntervalMeanCLM_fredholmPlus_eq
        (suzukiDF6E_radius_pos ha)).symm

/-- Minus-sign normalized representative uniqueness. -/
theorem suzukiShiftedSourceEnergyMinusVector_representative_eq_printed
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (rhs : SuzukiFiniteIntervalL2 a)
    (hrep : SuzukiShiftedSourceEnergyAmbientRepresentativeAt
      hsource hequation25 a ha lambda hlambda
      (suzukiDF6FShiftedSourceEnergyMinusVector
        hsource hequation25 a ha lambda hlambda) rhs)
    (hmean : suzukiFiniteIntervalMeanCLM a rhs =
      ((Real.exp a - Real.exp (-a) : Real) : Complex) -
        ((2 * a : Real) : Complex) * Complex.I) :
    rhs = suzukiFiniteIntervalContinuousToL2 a
      (suzukiFredholmMinusContinuous a) := by
  apply suzukiFiniteIntervalL2_eq_of_projection_eq_of_mean_eq
  · exact (suzukiShiftedSourceEnergyMinusVector_represents_iff_projection_eq
      hsource hequation25 a ha lambda hlambda rhs).mp hrep
  · exact hmean.trans
      (suzukiFiniteIntervalMeanCLM_fredholmMinus_eq
        (suzukiDF6E_radius_pos ha)).symm

/-- Exact completion-level plus normalization law: the displayed formula is
equivalent to the intrinsic representative relation together with its one
visible scalar mean. -/
theorem suzukiShiftedSourceEnergyPlusVector_eq_printed_iff
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (rhs : SuzukiFiniteIntervalL2 a) :
    rhs = suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmPlusContinuous a) ↔
      SuzukiShiftedSourceEnergyAmbientRepresentativeAt
          hsource hequation25 a ha lambda hlambda
          (suzukiDF6FShiftedSourceEnergyPlusVector
            hsource hequation25 a ha lambda hlambda) rhs ∧
        suzukiFiniteIntervalMeanCLM a rhs =
          ((Real.exp a - Real.exp (-a) : Real) : Complex) +
            ((2 * a : Real) : Complex) * Complex.I := by
  constructor
  · intro hrhs
    subst rhs
    exact ⟨suzukiShiftedSourceEnergyPlusVector_printedRepresentative
      hsource hequation25 a ha lambda hlambda,
      suzukiFiniteIntervalMeanCLM_fredholmPlus_eq
        (suzukiDF6E_radius_pos ha)⟩
  · rintro ⟨hrep, hmean⟩
    exact suzukiShiftedSourceEnergyPlusVector_representative_eq_printed
      hsource hequation25 a ha lambda hlambda rhs hrep hmean

/-- Exact completion-level minus normalization law. -/
theorem suzukiShiftedSourceEnergyMinusVector_eq_printed_iff
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (lambda : Real) (hlambda : lambda < (1 / 400000 : Real))
    (rhs : SuzukiFiniteIntervalL2 a) :
    rhs = suzukiFiniteIntervalContinuousToL2 a
        (suzukiFredholmMinusContinuous a) ↔
      SuzukiShiftedSourceEnergyAmbientRepresentativeAt
          hsource hequation25 a ha lambda hlambda
          (suzukiDF6FShiftedSourceEnergyMinusVector
            hsource hequation25 a ha lambda hlambda) rhs ∧
        suzukiFiniteIntervalMeanCLM a rhs =
          ((Real.exp a - Real.exp (-a) : Real) : Complex) -
            ((2 * a : Real) : Complex) * Complex.I := by
  constructor
  · intro hrhs
    subst rhs
    exact ⟨suzukiShiftedSourceEnergyMinusVector_printedRepresentative
      hsource hequation25 a ha lambda hlambda,
      suzukiFiniteIntervalMeanCLM_fredholmMinus_eq
        (suzukiDF6E_radius_pos ha)⟩
  · rintro ⟨hrep, hmean⟩
    exact suzukiShiftedSourceEnergyMinusVector_representative_eq_printed
      hsource hequation25 a ha lambda hlambda rhs hrep hmean

end

end RiemannHypothesisProject.Experiments.M100
