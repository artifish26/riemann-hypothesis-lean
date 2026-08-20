import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualTargetIntervalCache
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Live-entry admission for the final M100-DF6D4 residual certificates

The generated certificates contain untrusted rational interval and Gram data.
This module checks, by exact rational computation, that every cached live
target interval lies inside its generated certificate interval.  The symbolic
cache-equality theorems then transport the existing analytic entry
containments to the certificate grids.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem suzukiDF6D4EvenResidualTargetEntryIntervals_admitted :
    let solveResidual := suzukiDF6D4IntervalMatrixCache
      suzukiDF6D4EvenGalerkinSolveResidualInterval
    let residualColumn := suzukiDF6D4IntervalMatrixCache fun r : Fin 300 =>
      suzukiDF6D4EvenResidualColumnInterval (301 + r.val)
    ∀ i j : Fin 45,
      (suzukiDF6D4EvenResidualTargetCertificate.entry i j).lower ≤
          (suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches
            solveResidual residualColumn i j).lower ∧
        (suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches
          solveResidual residualColumn i j).upper ≤
          (suzukiDF6D4EvenResidualTargetCertificate.entry i j).upper := by
  native_decide

theorem suzukiDF6D4OddResidualTargetEntryIntervals_admitted :
    let solveResidual := suzukiDF6D4IntervalMatrixCache
      suzukiDF6D4OddGalerkinSolveResidualInterval
    let residualColumn := suzukiDF6D4IntervalMatrixCache fun r : Fin 300 =>
      suzukiDF6D4OddResidualColumnInterval (301 + r.val)
    ∀ i j : Fin 44,
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).lower ≤
          (suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches
            solveResidual residualColumn i j).lower ∧
        (suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches
          solveResidual residualColumn i j).upper ≤
          (suzukiDF6D4OddResidualTargetCertificate.entry i j).upper := by
  native_decide

theorem suzukiDF6D4EvenResidualTargetCertificateEntry_contains
    (i j : Fin 45) :
    (suzukiDF6D4EvenResidualTargetCertificate.entry i j).Contains
      (suzukiDF6D4EvenResidualCertificateTargetMatrix i j) := by
  let solveResidual := suzukiDF6D4IntervalMatrixCache
    suzukiDF6D4EvenGalerkinSolveResidualInterval
  let residualColumn := suzukiDF6D4IntervalMatrixCache fun r : Fin 300 =>
    suzukiDF6D4EvenResidualColumnInterval (301 + r.val)
  have hadmitted := suzukiDF6D4EvenResidualTargetEntryIntervals_admitted
  have heq :
      suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches
          solveResidual residualColumn i j =
        suzukiDF6D4EvenResidualCertificateTargetEntryInterval i j := by
    apply suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches_eq
    · intro k row
      simpa only [solveResidual] using
        suzukiDF6D4IntervalMatrixCacheEntry_eq
          suzukiDF6D4EvenGalerkinSolveResidualInterval k row
    · intro r row
      simpa only [residualColumn] using
        suzukiDF6D4IntervalMatrixCacheEntry_eq
          (fun r : Fin 300 =>
            suzukiDF6D4EvenResidualColumnInterval (301 + r.val)) r row
  exact RationalInterval.contains_of_widen
    (hadmitted i j).1 (hadmitted i j).2
    (heq ▸ suzukiDF6D4EvenResidualCertificateTargetEntryInterval_contains i j)

theorem suzukiDF6D4OddResidualTargetCertificateEntry_contains
    (i j : Fin 44) :
    (suzukiDF6D4OddResidualTargetCertificate.entry i j).Contains
      (suzukiDF6D4OddResidualCertificateTargetMatrix i j) := by
  let solveResidual := suzukiDF6D4IntervalMatrixCache
    suzukiDF6D4OddGalerkinSolveResidualInterval
  let residualColumn := suzukiDF6D4IntervalMatrixCache fun r : Fin 300 =>
    suzukiDF6D4OddResidualColumnInterval (301 + r.val)
  have hadmitted := suzukiDF6D4OddResidualTargetEntryIntervals_admitted
  have heq :
      suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches
          solveResidual residualColumn i j =
        suzukiDF6D4OddResidualCertificateTargetEntryInterval i j := by
    apply suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches_eq
    · intro k row
      simpa only [solveResidual] using
        suzukiDF6D4IntervalMatrixCacheEntry_eq
          suzukiDF6D4OddGalerkinSolveResidualInterval k row
    · intro r row
      simpa only [residualColumn] using
        suzukiDF6D4IntervalMatrixCacheEntry_eq
          (fun r : Fin 300 =>
            suzukiDF6D4OddResidualColumnInterval (301 + r.val)) r row
  exact RationalInterval.contains_of_widen
    (hadmitted i j).1 (hadmitted i j).2
    (heq ▸ suzukiDF6D4OddResidualCertificateTargetEntryInterval_contains i j)

end RiemannHypothesisProject.Experiments.M100
