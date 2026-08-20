import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualEnclosures

/-!
# B3R-E frozen comparison-energy trial-solve identities

This module exposes the exact finite algebra already encoded by the DF6D4
Galerkin data. The rational approximant remains a trial solve: both solve
residuals are retained literally.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators

/-- The even DF6D4 solve residual is exactly `C^T - E_A X`. -/
theorem suzukiDF6D5B3RE_evenGalerkinSolveResidual_eq
    (k : Fin 256) (i : Fin 45) :
    suzukiDF6D4EvenGalerkinSolveResidual k i =
      suzukiDF6D4EvenCompleteCrossEntry i k -
        ∑ l : Fin 256,
          suzukiDF6D4EvenComparisonGalerkinEntry k l *
            (suzukiDF6D4EvenGalerkinApproximant l i : Real) := by
  rfl

/-- The odd DF6D4 solve residual is exactly `C^T - E_A X`. -/
theorem suzukiDF6D5B3RE_oddGalerkinSolveResidual_eq
    (k : Fin 256) (i : Fin 44) :
    suzukiDF6D4OddGalerkinSolveResidual k i =
      suzukiDF6D4OddCompleteCrossEntry i k -
        ∑ l : Fin 256,
          suzukiDF6D4OddComparisonGalerkinEntry k l *
            (suzukiDF6D4OddGalerkinApproximant l i : Real) := by
  rfl

/-- The even Galerkin base is the exact entrywise expansion of
`C X + X^T C^T - X^T E_A X`. -/
theorem suzukiDF6D5B3RE_evenGalerkinBaseEntry_eq
    (i j : Fin 45) :
    suzukiDF6D4EvenGalerkinBaseEntry i j =
      (∑ k : Fin 256,
        suzukiDF6D4EvenCompleteCrossEntry i k *
          (suzukiDF6D4EvenGalerkinApproximant k j : Real)) +
      (∑ k : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
          suzukiDF6D4EvenCompleteCrossEntry j k) -
      ∑ k : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
          ∑ l : Fin 256,
            suzukiDF6D4EvenComparisonGalerkinEntry k l *
              (suzukiDF6D4EvenGalerkinApproximant l j : Real) := by
  unfold suzukiDF6D4EvenGalerkinBaseEntry
    suzukiDF6D4EvenGalerkinSolveResidual
  simp_rw [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The odd Galerkin base is the exact entrywise expansion of
`C X + X^T C^T - X^T E_A X`. -/
theorem suzukiDF6D5B3RE_oddGalerkinBaseEntry_eq
    (i j : Fin 44) :
    suzukiDF6D4OddGalerkinBaseEntry i j =
      (∑ k : Fin 256,
        suzukiDF6D4OddCompleteCrossEntry i k *
          (suzukiDF6D4OddGalerkinApproximant k j : Real)) +
      (∑ k : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k i : Real) *
          suzukiDF6D4OddCompleteCrossEntry j k) -
      ∑ k : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k i : Real) *
          ∑ l : Fin 256,
            suzukiDF6D4OddComparisonGalerkinEntry k l *
              (suzukiDF6D4OddGalerkinApproximant l j : Real) := by
  unfold suzukiDF6D4OddGalerkinBaseEntry
    suzukiDF6D4OddGalerkinSolveResidual
  simp_rw [mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

end

end RiemannHypothesisProject.Experiments.M100
