import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly

/-!
# Exact rational target-grid exporter for M100-DF6D4

This tool prints the rational interval endpoints already assembled and checked
by Lean.  The companion Python generator uses the output only to construct a
rational Gram factor; Lean subsequently rechecks both the factor and its
connection to the live target intervals.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

private def cacheMatrix {m n : Nat} {α : Type} [Inhabited α]
    (entry : Fin m → Fin n → α) : Array (Array α) :=
  Array.ofFn fun i => Array.ofFn fun j => entry i j

private def cacheEntry {α : Type} [Inhabited α]
    (cache : Array (Array α)) (i j : Nat) : α :=
  (cache[i]!)[j]!

private def evenTargetFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  let galerkinBase :=
    RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k j)
        (suzukiDF6D4EvenCompleteCrossEntryInterval i k)).add
      (RationalInterval.scale (suzukiDF6D4EvenGalerkinApproximant k i)
        (cacheEntry solveResidual k.val j.val))
  let finiteResidualGram :=
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (cacheEntry solveResidual k.val i.val).mulCentered
        (cacheEntry solveResidual k.val j.val)).add
    (RationalInterval.sum Finset.univ fun r : Fin 300 =>
      (cacheEntry residualColumn r.val i.val).mulCentered
        (cacheEntry residualColumn r.val j.val))
  let couplingUpper :=
    (galerkinBase.add
      (RationalInterval.scale (1 / 5) finiteResidualGram)).add
      (RationalInterval.scale (1 / 5)
        (suzukiDF6D4EvenAnalyticTailEntryInterval i j))
  (RationalInterval.scale suzukiDF6D4EvenStrictComparisonCoefficient
    (suzukiDF6D4EvenEndpointEntryInterval i j)).sub couplingUpper

private def oddTargetFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  let galerkinBase :=
    RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k j)
        (suzukiDF6D4OddCompleteCrossEntryInterval i k)).add
      (RationalInterval.scale (suzukiDF6D4OddGalerkinApproximant k i)
        (cacheEntry solveResidual k.val j.val))
  let finiteResidualGram :=
    (RationalInterval.sum Finset.univ fun k : Fin 256 =>
      (cacheEntry solveResidual k.val i.val).mulCentered
        (cacheEntry solveResidual k.val j.val)).add
    (RationalInterval.sum Finset.univ fun r : Fin 300 =>
      (cacheEntry residualColumn r.val i.val).mulCentered
        (cacheEntry residualColumn r.val j.val))
  let couplingUpper :=
    (galerkinBase.add
      (RationalInterval.scale (1 / 5) finiteResidualGram)).add
      (RationalInterval.scale (1 / 5)
        (suzukiDF6D4OddAnalyticTailEntryInterval i j))
  (RationalInterval.scale suzukiDF6D4OddStrictComparisonCoefficient
    (suzukiDF6D4OddEndpointEntryInterval i j)).sub couplingUpper

private def printGrid {n : Nat}
    (name : String) (entry : Fin n → Fin n → RationalInterval) : IO Unit := do
  IO.println s!"BEGIN {name} {n}"
  for i in List.finRange n do
    for j in List.finRange n do
      let interval := entry i j
      IO.println s!"{interval.lower}\t{interval.upper}"
  IO.println s!"END {name}"

def runResidualTargetGridExport : IO Unit := do
  let evenSolveResidual := cacheMatrix
    suzukiDF6D4EvenGalerkinSolveResidualInterval
  let oddSolveResidual := cacheMatrix
    suzukiDF6D4OddGalerkinSolveResidualInterval
  let evenResidualColumn := cacheMatrix fun r : Fin 300 =>
    suzukiDF6D4EvenResidualColumnInterval (301 + r.val)
  let oddResidualColumn := cacheMatrix fun r : Fin 300 =>
    suzukiDF6D4OddResidualColumnInterval (301 + r.val)
  printGrid "suzukiDF6D4EvenResidualTarget"
    (evenTargetFromCaches evenSolveResidual evenResidualColumn)
  printGrid "suzukiDF6D4OddResidualTarget"
    (oddTargetFromCaches oddSolveResidual oddResidualColumn)

end RiemannHypothesisProject.Experiments.M100

def main : IO Unit :=
  RiemannHypothesisProject.Experiments.M100.runResidualTargetGridExport
