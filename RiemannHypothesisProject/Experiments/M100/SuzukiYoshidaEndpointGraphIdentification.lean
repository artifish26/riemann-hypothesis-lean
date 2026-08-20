import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaComparisonEntries
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierBoundaryLimit

/-!
# Exact graph representatives for the endpoint exponential lifts

This module begins the closed-graph identification stage of QF2.  The B2S
source theorem supplies both a logarithmic Fourier-domain witness and a
smooth-core approximation for each endpoint exponential.  We expose those
choices, build the corresponding element of the radius completion directly,
and prove that it is the canonical lift already used by the comparison
kernel.

The result removes any dependence on the implementation of
`Classical.choose`: the canonical lift has exactly the graph representative
specified by the source approximation.  Identification of the extended
low-frequency map with the concrete endpoint multiplier is left to the next
stage.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter Set
open scoped Topology

/-- The logarithmic Fourier-domain witness selected from the B2S source
theorem for one endpoint exponential. -/
noncomputable def suzukiYoshidaExponentialFourierDomainOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    SuzukiLogFourierDomain (suzukiYoshidaExponentialL2 r hr n) :=
  Classical.choose (hsource hr n)

/-- The smooth-core sequence selected together with the source-domain
witness. -/
noncomputable def suzukiYoshidaExponentialApproximationOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) : Nat → SuzukiSmoothCore r :=
  Classical.choose (Classical.choose_spec (hsource hr n))

/-- The selected source sequence converges to the explicit logarithmic graph
of the endpoint exponential. -/
theorem suzukiYoshidaExponentialApproximationOfSource_tendsto
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    Tendsto
      (fun k => suzukiSmoothCoreToLogGraph
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
      atTop
      (nhds (suzukiYoshidaExponentialLogGraph hr n
        (suzukiYoshidaExponentialFourierDomainOfSource hsource hr n))) :=
  Classical.choose_spec (Classical.choose_spec (hsource hr n))

/-- The endpoint completion element built directly from the source-specified
graph representative. -/
noncomputable def suzukiYoshidaExponentialLogRadiusCompletionOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) : SuzukiLogRadiusCompletion r :=
  ⟨suzukiYoshidaExponentialLogGraph hr n
      (suzukiYoshidaExponentialFourierDomainOfSource hsource hr n), by
    apply mem_closure_of_tendsto
      (suzukiYoshidaExponentialApproximationOfSource_tendsto
        hsource hr n)
    exact Filter.Eventually.of_forall fun k =>
      Set.mem_range_self
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k)⟩

/-- Hilbert-completion version of the direct source graph representative. -/
noncomputable def suzukiYoshidaExponentialDirectLinearCompletionOfSource
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) : SuzukiLogRadiusLinearCompletion r :=
  suzukiLogRadiusCompletionToLinear
    (suzukiYoshidaExponentialLogRadiusCompletionOfSource hsource hr n)

@[simp]
theorem suzukiYoshidaExponentialDirectLinearCompletionOfSource_toL2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    suzukiLogRadiusLinearCompletionToL2
        (suzukiYoshidaExponentialDirectLinearCompletionOfSource
          hsource hr n) =
      suzukiYoshidaExponentialL2 r hr n :=
  rfl

/-- The selected smooth-core sequence converges in the legacy radius
completion to the direct endpoint representative. -/
theorem suzukiYoshidaExponentialApproximationOfSource_tendsto_legacy
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    Tendsto
      (fun k => suzukiSmoothCoreToLogRadiusCompletion
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
      atTop
      (nhds (suzukiYoshidaExponentialLogRadiusCompletionOfSource
        hsource hr n)) := by
  rw [tendsto_subtype_rng]
  exact suzukiYoshidaExponentialApproximationOfSource_tendsto
    hsource hr n

/-- The same selected sequence converges in the Hilbert radius completion. -/
theorem suzukiYoshidaExponentialApproximationOfSource_tendsto_linear
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    Tendsto
      (fun k => suzukiSmoothCoreToLogRadiusLinearCompletion
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
      atTop
      (nhds (suzukiYoshidaExponentialDirectLinearCompletionOfSource
        hsource hr n)) := by
  change Tendsto
    (suzukiLogRadiusCompletionHilbertHomeomorph ∘
      fun k => suzukiSmoothCoreToLogRadiusCompletion
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
    atTop
    (nhds (suzukiLogRadiusCompletionHilbertHomeomorph
      (suzukiYoshidaExponentialLogRadiusCompletionOfSource
        hsource hr n)))
  exact
    (suzukiLogRadiusCompletionHilbertHomeomorph.continuous.tendsto
      (suzukiYoshidaExponentialLogRadiusCompletionOfSource
        hsource hr n)).comp
      (suzukiYoshidaExponentialApproximationOfSource_tendsto_legacy
        hsource hr n)

/-- The canonical comparison-kernel lift is the direct source graph lift.
Injectivity of the physical `L²` coordinate makes this independent of both
choice implementations. -/
theorem suzukiYoshidaExponentialLinearCompletionOfSource_eq_direct
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    suzukiYoshidaExponentialLinearCompletionOfSource hsource hr n =
      suzukiYoshidaExponentialDirectLinearCompletionOfSource
        hsource hr n := by
  apply suzukiLogRadiusLinearCompletionToL2_injective r
  rw [suzukiYoshidaExponentialLinearCompletionOfSource_toL2,
    suzukiYoshidaExponentialDirectLinearCompletionOfSource_toL2]

/-- Consequently the canonical lift has the exact source-specified legacy
graph representative, including its weighted Fourier coordinate. -/
theorem suzukiYoshidaExponentialLinearCompletionOfSource_legacyGraph
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    (suzukiLogRadiusLinearCompletionToLegacy
      (suzukiYoshidaExponentialLinearCompletionOfSource
        hsource hr n)).1 =
      suzukiYoshidaExponentialLogGraph hr n
        (suzukiYoshidaExponentialFourierDomainOfSource hsource hr n) := by
  rw [suzukiYoshidaExponentialLinearCompletionOfSource_eq_direct]
  rfl

end

end RiemannHypothesisProject.Experiments.M100
