import RiemannHypothesisProject.PrimeMoment.Asymptotic

/-!
# Unconditional Li cutoff covariance limit

The exact finite-cutoff covariance theorem is instantiated with the complete
PNT-derived prime-moment family.  No source proposition remains in this
consumer.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Filter
open scoped Topology

/-- The canonical common-cutoff limit for the `n`th Li inverse Mellin test. -/
def liCutoffCovarianceLimit (n : Nat) : Real :=
  -(∑ j ∈ Finset.range n,
    (-1 : Real) ^ j * (n.choose (j + 1) : Real) / j.factorial *
      liPrimeMomentLimit j)

/-- The regularized Li cutoff covariance converges unconditionally from the
pinned PNT source. -/
theorem tendsto_liCutoffCovariance_unconditional (n : Nat) :
    Tendsto (liCutoffCovariance n) atTop
      (nhds (liCutoffCovarianceLimit n)) := by
  exact tendsto_liCutoffCovariance_of_primeMomentAsymptotics
    n liPrimeMomentLimit (bombieriLagariasPrimeMomentAsymptotics_range n)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
