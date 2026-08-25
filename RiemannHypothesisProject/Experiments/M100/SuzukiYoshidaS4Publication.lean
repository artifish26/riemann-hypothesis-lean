import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaX19BBoundedWindowSolutions
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaBoundaryCutoffSource
import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25GammaTailLimit

/-!
# Suzuki S4 compact-window publication surface

This module instantiates the two source packages retained explicitly by X19B
with their independently checked DF6F inhabitants.  It exposes the bounded
closed-unit-disk solution family without a residual source premise.

The conclusions remain restricted to `SuzukiDF6EInterval`.  They do not state
all-radius nondegeneracy, identify a completed-zeta limit, prove global Weil
positivity, or imply the Riemann Hypothesis.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set
open scoped InnerProductSpace

/-- The checked DF6F form-core source package used by the S4 publication
surface. -/
abbrev suzukiS4ExponentialFormCoreSource :
    SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar :=
  suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff suzukiProjectAStar

/-- The checked DF6F equation-(2.5) package used by the S4 publication
surface. -/
abbrev suzukiS4Equation25SourceIdentity :
    SuzukiEquation25SourceIdentityAt suzukiProjectAStar :=
  suzukiEquation25SourceIdentityAt_proved suzukiProjectAStar

/-- The canonical S4 solution throughout the released compact radius window
and the closed complex spectral unit disk. -/
abbrev suzukiS4CompactWindowSolution
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w : Complex) (hw : ‖w‖ ≤ 1) :=
  suzukiX19BComplexUnitDiskSolution
    suzukiS4ExponentialFormCoreSource
    suzukiS4Equation25SourceIdentity a ha w hw

/-- The S4 solution family is uniformly bounded by `4000` on the product of
the released radius window and the closed complex unit disk. -/
theorem suzukiS4CompactWindowSolution_norm_le_fourThousand
    (a : Real) (ha : a ∈ SuzukiDF6EInterval)
    (w : Complex) (hw : ‖w‖ ≤ 1) :
    ‖suzukiS4CompactWindowSolution a ha w hw‖ ≤ 4000 :=
  norm_suzukiX19BComplexUnitDiskSolution_le_fourThousand
    suzukiS4ExponentialFormCoreSource
    suzukiS4Equation25SourceIdentity a ha w hw

/-- At each released radius, the canonical solution map on the closed complex
unit disk is Lipschitz with the explicit X19B constant. -/
theorem suzukiS4CompactWindowSolutionMap_lipschitz
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    LipschitzWith suzukiX19BSolutionDifferenceNNReal
      (suzukiX19BComplexUnitDiskSolutionMap
        suzukiS4ExponentialFormCoreSource
        suzukiS4Equation25SourceIdentity a ha) :=
  lipschitzWith_suzukiX19BComplexUnitDiskSolutionMap
    suzukiS4ExponentialFormCoreSource
    suzukiS4Equation25SourceIdentity a ha

/-- At each released radius, the image of the closed complex unit disk is
compact in the genuine frozen source-energy completion. -/
theorem suzukiS4CompactWindowSolutionMap_isCompact_range
    (a : Real) (ha : a ∈ SuzukiDF6EInterval) :
    IsCompact (Set.range (suzukiX19BComplexUnitDiskSolutionMap
      suzukiS4ExponentialFormCoreSource
      suzukiS4Equation25SourceIdentity a ha)) :=
  isCompact_range_suzukiX19BComplexUnitDiskSolutionMap
    suzukiS4ExponentialFormCoreSource
    suzukiS4Equation25SourceIdentity a ha

/-- Strong directed radius continuity from below on the interior of the
released window, after the canonical isometric completion transport. -/
theorem eventually_suzukiS4CompactWindowSolution_close_from_below
    {b : Real} (hb : b ∈ SuzukiDF6EInterval)
    (hleft : Real.log 2 / 2 < b)
    (w : Complex) (hw : ‖w‖ ≤ 1) {ε : Real} (hε : 0 < ε) :
    ∃ (a₀ : Real) (_ha₀ : a₀ ∈ SuzukiDF6EInterval) (_ha₀b : a₀ < b),
      ∀ (a : Real) (ha : a ∈ SuzukiDF6EInterval)
        (_ha₀a : a₀ ≤ a) (hab : a ≤ b),
        ‖suzukiS4CompactWindowSolution b hb w hw -
            suzukiX19BShiftedCompletionZeroExtension
              suzukiS4ExponentialFormCoreSource
              suzukiS4Equation25SourceIdentity ha hb hab
              (suzukiS4CompactWindowSolution a ha w hw)‖ < ε :=
  eventually_suzukiX19BComplexUnitDiskSolution_close_from_below
    suzukiS4ExponentialFormCoreSource
    suzukiS4Equation25SourceIdentity hb hleft w hw hε

end

end RiemannHypothesisProject.Experiments.M100
