import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly

/-!
# Cached strict-target interval grids for M100-DF6D4

The live residual-certificate interval formulas intentionally expose every
finite sum.  Evaluating the full target grid naively repeats the same
256-dimensional solve residuals and 300 explicit residual columns inside
every matrix cell.  This module caches those exact rational intervals once,
reassembles the target grids from the caches, and proves the cached formulas
equal the original live formulas.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def suzukiDF6D4IntervalMatrixCache
    {m n : Nat} {α : Type} [Inhabited α]
    (entry : Fin m → Fin n → α) : Array (Array α) :=
  Array.ofFn fun i => Array.ofFn fun j => entry i j

def suzukiDF6D4IntervalMatrixCacheEntry
    {m n : Nat} {α : Type} [Inhabited α]
    (cache : Array (Array α)) (i : Fin m) (j : Fin n) : α :=
  (cache[i.val]!)[j.val]!

theorem suzukiDF6D4IntervalMatrixCacheEntry_eq
    {m n : Nat} {α : Type} [Inhabited α]
    (entry : Fin m → Fin n → α) (i : Fin m) (j : Fin n) :
    suzukiDF6D4IntervalMatrixCacheEntry
      (suzukiDF6D4IntervalMatrixCache entry) i j = entry i j := by
  simp [suzukiDF6D4IntervalMatrixCacheEntry,
    suzukiDF6D4IntervalMatrixCache, i.isLt, j.isLt]

def suzukiDF6D4EvenSolveResidualIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4IntervalMatrixCache
    suzukiDF6D4EvenGalerkinSolveResidualInterval

def suzukiDF6D4OddSolveResidualIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4IntervalMatrixCache
    suzukiDF6D4OddGalerkinSolveResidualInterval

def suzukiDF6D4EvenResidualColumnIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4IntervalMatrixCache fun r : Fin 300 =>
    suzukiDF6D4EvenResidualColumnInterval (301 + r.val)

def suzukiDF6D4OddResidualColumnIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4IntervalMatrixCache fun r : Fin 300 =>
    suzukiDF6D4OddResidualColumnInterval (301 + r.val)

def suzukiDF6D4EvenGalerkinBaseEntryIntervalFromCache
    (solveResidual : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  RationalInterval.sum Finset.univ fun k : Fin 256 =>
    (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k j)
      (suzukiDF6D4EvenCompleteCrossEntryInterval i k)).add
    (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
      (suzukiDF6D4IntervalMatrixCacheEntry
        solveResidual k j))

def suzukiDF6D4OddGalerkinBaseEntryIntervalFromCache
    (solveResidual : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  RationalInterval.sum Finset.univ fun k : Fin 256 =>
    (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k j)
      (suzukiDF6D4OddCompleteCrossEntryInterval i k)).add
    (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
      (suzukiDF6D4IntervalMatrixCacheEntry
        solveResidual k j))

def suzukiDF6D4EvenFiniteResidualGramEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (suzukiDF6D4IntervalMatrixCacheEntry
        solveResidual k i).mulCentered
      (suzukiDF6D4IntervalMatrixCacheEntry
        solveResidual k j)).add
    (RationalInterval.sum Finset.univ fun r : Fin 300 =>
      (suzukiDF6D4IntervalMatrixCacheEntry
        residualColumn r i).mulCentered
      (suzukiDF6D4IntervalMatrixCacheEntry
        residualColumn r j))

def suzukiDF6D4OddFiniteResidualGramEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (suzukiDF6D4IntervalMatrixCacheEntry
        solveResidual k i).mulCentered
      (suzukiDF6D4IntervalMatrixCacheEntry
        solveResidual k j)).add
    (RationalInterval.sum Finset.univ fun r : Fin 300 =>
      (suzukiDF6D4IntervalMatrixCacheEntry
        residualColumn r i).mulCentered
      (suzukiDF6D4IntervalMatrixCacheEntry
        residualColumn r j))

def suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.scale suzukiDF6D4EvenStrictComparisonCoefficient
    (suzukiDF6D4EvenEndpointEntryInterval i j)).sub
    (((suzukiDF6D4EvenGalerkinBaseEntryIntervalFromCache
        solveResidual i j).add
      (RationalInterval.scale (1 / 5)
        (suzukiDF6D4EvenFiniteResidualGramEntryIntervalFromCaches
          solveResidual residualColumn i j))).add
      (RationalInterval.scale (1 / 5)
        (suzukiDF6D4EvenAnalyticTailEntryInterval i j)))

def suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.scale suzukiDF6D4OddStrictComparisonCoefficient
    (suzukiDF6D4OddEndpointEntryInterval i j)).sub
    (((suzukiDF6D4OddGalerkinBaseEntryIntervalFromCache
        solveResidual i j).add
      (RationalInterval.scale (1 / 5)
        (suzukiDF6D4OddFiniteResidualGramEntryIntervalFromCaches
          solveResidual residualColumn i j))).add
      (RationalInterval.scale (1 / 5)
        (suzukiDF6D4OddAnalyticTailEntryInterval i j)))

def suzukiDF6D4EvenCachedGalerkinBaseEntryInterval
    (i j : Fin 45) : RationalInterval :=
  suzukiDF6D4EvenGalerkinBaseEntryIntervalFromCache
    suzukiDF6D4EvenSolveResidualIntervalCache i j

def suzukiDF6D4OddCachedGalerkinBaseEntryInterval
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4OddGalerkinBaseEntryIntervalFromCache
    suzukiDF6D4OddSolveResidualIntervalCache i j

def suzukiDF6D4EvenCachedFiniteResidualGramEntryInterval
    (i j : Fin 45) : RationalInterval :=
  suzukiDF6D4EvenFiniteResidualGramEntryIntervalFromCaches
    suzukiDF6D4EvenSolveResidualIntervalCache
    suzukiDF6D4EvenResidualColumnIntervalCache i j

def suzukiDF6D4OddCachedFiniteResidualGramEntryInterval
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4OddFiniteResidualGramEntryIntervalFromCaches
    suzukiDF6D4OddSolveResidualIntervalCache
    suzukiDF6D4OddResidualColumnIntervalCache i j

def suzukiDF6D4EvenCachedResidualCertificateTargetEntryInterval
    (i j : Fin 45) : RationalInterval :=
  suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches
    suzukiDF6D4EvenSolveResidualIntervalCache
    suzukiDF6D4EvenResidualColumnIntervalCache i j

def suzukiDF6D4OddCachedResidualCertificateTargetEntryInterval
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches
    suzukiDF6D4OddSolveResidualIntervalCache
    suzukiDF6D4OddResidualColumnIntervalCache i j

theorem suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches_eq
    (solveResidual residualColumn : Array (Array RationalInterval))
    (hsolve : ∀ k : Fin 256, ∀ i : Fin 45,
      suzukiDF6D4IntervalMatrixCacheEntry solveResidual k i =
        suzukiDF6D4EvenGalerkinSolveResidualInterval k i)
    (hcolumn : ∀ r : Fin 300, ∀ i : Fin 45,
      suzukiDF6D4IntervalMatrixCacheEntry residualColumn r i =
        suzukiDF6D4EvenResidualColumnInterval (301 + r.val) i)
    (i j : Fin 45) :
    suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches
        solveResidual residualColumn i j =
      suzukiDF6D4EvenResidualCertificateTargetEntryInterval i j := by
  simp only [suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches,
    suzukiDF6D4EvenResidualCertificateTargetEntryInterval,
    suzukiDF6D4EvenCouplingUpperEntryInterval,
    suzukiDF6D4EvenGalerkinBaseEntryIntervalFromCache,
    suzukiDF6D4EvenGalerkinBaseEntryInterval,
    suzukiDF6D4EvenFiniteResidualGramEntryIntervalFromCaches,
    suzukiDF6D4EvenFiniteResidualGramEntryInterval, hsolve, hcolumn]

theorem suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches_eq
    (solveResidual residualColumn : Array (Array RationalInterval))
    (hsolve : ∀ k : Fin 256, ∀ i : Fin 44,
      suzukiDF6D4IntervalMatrixCacheEntry solveResidual k i =
        suzukiDF6D4OddGalerkinSolveResidualInterval k i)
    (hcolumn : ∀ r : Fin 300, ∀ i : Fin 44,
      suzukiDF6D4IntervalMatrixCacheEntry residualColumn r i =
        suzukiDF6D4OddResidualColumnInterval (301 + r.val) i)
    (i j : Fin 44) :
    suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches
        solveResidual residualColumn i j =
      suzukiDF6D4OddResidualCertificateTargetEntryInterval i j := by
  simp only [suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches,
    suzukiDF6D4OddResidualCertificateTargetEntryInterval,
    suzukiDF6D4OddCouplingUpperEntryInterval,
    suzukiDF6D4OddGalerkinBaseEntryIntervalFromCache,
    suzukiDF6D4OddGalerkinBaseEntryInterval,
    suzukiDF6D4OddFiniteResidualGramEntryIntervalFromCaches,
    suzukiDF6D4OddFiniteResidualGramEntryInterval, hsolve, hcolumn]

theorem suzukiDF6D4EvenCachedGalerkinBaseEntryInterval_eq
    (i j : Fin 45) :
    suzukiDF6D4EvenCachedGalerkinBaseEntryInterval i j =
      suzukiDF6D4EvenGalerkinBaseEntryInterval i j := by
  simp only [suzukiDF6D4EvenCachedGalerkinBaseEntryInterval,
    suzukiDF6D4EvenGalerkinBaseEntryIntervalFromCache,
    suzukiDF6D4EvenGalerkinBaseEntryInterval,
    suzukiDF6D4EvenSolveResidualIntervalCache,
    suzukiDF6D4IntervalMatrixCacheEntry_eq]

theorem suzukiDF6D4OddCachedGalerkinBaseEntryInterval_eq
    (i j : Fin 44) :
    suzukiDF6D4OddCachedGalerkinBaseEntryInterval i j =
      suzukiDF6D4OddGalerkinBaseEntryInterval i j := by
  simp only [suzukiDF6D4OddCachedGalerkinBaseEntryInterval,
    suzukiDF6D4OddGalerkinBaseEntryIntervalFromCache,
    suzukiDF6D4OddGalerkinBaseEntryInterval,
    suzukiDF6D4OddSolveResidualIntervalCache,
    suzukiDF6D4IntervalMatrixCacheEntry_eq]

theorem suzukiDF6D4EvenCachedFiniteResidualGramEntryInterval_eq
    (i j : Fin 45) :
    suzukiDF6D4EvenCachedFiniteResidualGramEntryInterval i j =
      suzukiDF6D4EvenFiniteResidualGramEntryInterval i j := by
  simp only [suzukiDF6D4EvenCachedFiniteResidualGramEntryInterval,
    suzukiDF6D4EvenFiniteResidualGramEntryIntervalFromCaches,
    suzukiDF6D4EvenFiniteResidualGramEntryInterval,
    suzukiDF6D4EvenSolveResidualIntervalCache,
    suzukiDF6D4EvenResidualColumnIntervalCache,
    suzukiDF6D4IntervalMatrixCacheEntry_eq]

theorem suzukiDF6D4OddCachedFiniteResidualGramEntryInterval_eq
    (i j : Fin 44) :
    suzukiDF6D4OddCachedFiniteResidualGramEntryInterval i j =
      suzukiDF6D4OddFiniteResidualGramEntryInterval i j := by
  simp only [suzukiDF6D4OddCachedFiniteResidualGramEntryInterval,
    suzukiDF6D4OddFiniteResidualGramEntryIntervalFromCaches,
    suzukiDF6D4OddFiniteResidualGramEntryInterval,
    suzukiDF6D4OddSolveResidualIntervalCache,
    suzukiDF6D4OddResidualColumnIntervalCache,
    suzukiDF6D4IntervalMatrixCacheEntry_eq]

theorem suzukiDF6D4EvenCachedResidualCertificateTargetEntryInterval_eq
    (i j : Fin 45) :
    suzukiDF6D4EvenCachedResidualCertificateTargetEntryInterval i j =
      suzukiDF6D4EvenResidualCertificateTargetEntryInterval i j := by
  apply suzukiDF6D4EvenResidualCertificateTargetEntryIntervalFromCaches_eq
  · intro k row
    exact suzukiDF6D4IntervalMatrixCacheEntry_eq _ k row
  · intro r row
    exact suzukiDF6D4IntervalMatrixCacheEntry_eq _ r row

theorem suzukiDF6D4OddCachedResidualCertificateTargetEntryInterval_eq
    (i j : Fin 44) :
    suzukiDF6D4OddCachedResidualCertificateTargetEntryInterval i j =
      suzukiDF6D4OddResidualCertificateTargetEntryInterval i j := by
  apply suzukiDF6D4OddResidualCertificateTargetEntryIntervalFromCaches_eq
  · intro k row
    exact suzukiDF6D4IntervalMatrixCacheEntry_eq _ k row
  · intro r row
    exact suzukiDF6D4IntervalMatrixCacheEntry_eq _ r row

end RiemannHypothesisProject.Experiments.M100
