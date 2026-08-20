import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointOddAdditiveGrid

/-!
# Exact rational target-grid exporter for M100-DF6D5

The companion generator uses this exporter only to construct a rational Gram
factor.  Lean subsequently rechecks the factor and the bridge from the
DF6D4-admitted target matrix to the shifted DF6D5 target.
-/

namespace RiemannHypothesisProject.Experiments.M100

private def printGrid {n : Nat}
    (name : String) (entry : Fin n → Fin n → RationalInterval) : IO Unit := do
  IO.println s!"BEGIN {name} {n}"
  for i in List.finRange n do
    for j in List.finRange n do
      let interval := entry i j
      IO.println s!"{interval.lower}\t{interval.upper}"
  IO.println s!"END {name}"

def runDF6D5OddAdditiveTargetGridExport : IO Unit :=
  printGrid "suzukiDF6D5OddAdditiveTarget"
    suzukiDF6D5OddAdditiveTargetEntryInterval

end RiemannHypothesisProject.Experiments.M100

def main : IO Unit :=
  RiemannHypothesisProject.Experiments.M100.runDF6D5OddAdditiveTargetGridExport
