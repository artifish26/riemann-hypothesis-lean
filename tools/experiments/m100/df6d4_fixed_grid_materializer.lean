import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell

/-!
# DF6D4 fixed-grid materializer

Emit the bounded even-parity Stage-0/1/2 literal blocks used to test the
three-stage verifier architecture.  The generated data are checked in
separate modules; this exporter is not itself a proof artifact.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

private def coefficientDenominator : Nat :=
  1000000000000000000000000

private def evenCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def oddCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4OddGalerkinApproximantData[k * 44 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def fixedGridOf (I : RationalInterval) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval suzukiDF6D4FixedGridDenominator I

private def stage0ComparisonRow00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 0 k)

private def stage0SolveCrossRow00 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4EvenCompleteCrossEntryInterval i 0)

private def stage0ComparisonPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 301)

private def stage0FullPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4FullEvenOffDiagonalInterval
      (suzukiDF6D4EvenLowMode i) 301)

private def stage0TargetCrossColumn00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4EvenCompleteCrossEntryInterval 0 k)

private def stage0Endpoint00 : Array FixedGridInterval :=
  #[fixedGridOf (suzukiDF6D4EvenEndpointEntryInterval 0 0)]

private def stage0AnalyticTail00 : Array FixedGridInterval :=
  #[fixedGridOf (suzukiDF6D4EvenAnalyticTailEntryInterval 0 0)]

private def dotForColumn
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def stage1SolveRow00 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (stage0SolveCrossRow00[i.val]!).sub
      (dotForColumn i.val stage0ComparisonRow00)

private def stage1ResidualRow301 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (stage0FullPrefixRow301[i.val]!).sub
      (dotForColumn i.val stage0ComparisonPrefixRow301)

private def stage1SolveColumn00 : Array FixedGridInterval :=
  Array.ofFn fun j : Fin 256 =>
    let comparisonRow := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval j k)
    (fixedGridOf (suzukiDF6D4EvenCompleteCrossEntryInterval 0 j)).sub
      (dotForColumn 0 comparisonRow)

private def stage1ResidualColumn00 : Array FixedGridInterval :=
  Array.ofFn fun r : Fin 300 =>
    let mode := 301 + r.val
    let comparisonRow := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
        (suzukiDF6D4GalerkinMode k) mode)
    (fixedGridOf (suzukiDF6D4FullEvenOffDiagonalInterval 0 mode)).sub
      (dotForColumn 0 comparisonRow)

private def stage2GalerkinBase00 : FixedGridInterval :=
  (dotForColumn 0 stage0TargetCrossColumn00).add
    (dotForColumn 0 stage1SolveColumn00)

private def stage2FiniteResidualGram00 : FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum suzukiDF6D4FixedGridDenominator
    (fun k : Fin 256 => stage1SolveColumn00[k.val]!)
    (fun k : Fin 256 => stage1SolveColumn00[k.val]!)).add
  (FixedGridInterval.mulCenteredFinSum suzukiDF6D4FixedGridDenominator
    (fun r : Fin 300 => stage1ResidualColumn00[r.val]!)
    (fun r : Fin 300 => stage1ResidualColumn00[r.val]!))

private def stage2Target00 : Array FixedGridInterval :=
  #[
    (FixedGridInterval.scale (19 / 1000 * (1 - 1 / 1000000000) : Rat)
      stage0Endpoint00[0]!).sub
      (((stage2GalerkinBase00.add
        (FixedGridInterval.scale (1 / 5 : Rat) stage2FiniteResidualGram00)).add
        (FixedGridInterval.scale (1 / 5 : Rat) stage0AnalyticTail00[0]!)))
  ]

private def oddStage0ComparisonRow00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4OddComparisonGalerkinEntryInterval 0 k)

private def oddStage0SolveCrossRow00 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4OddCompleteCrossEntryInterval i 0)

private def oddStage0ComparisonPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4ComparisonOddOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 301)

private def oddStage0FullPrefixRow301 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4FullOddOffDiagonalInterval
      (suzukiDF6D4OddLowMode i) 301)

private def oddStage0TargetCrossColumn00 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4OddCompleteCrossEntryInterval 0 k)

private def oddStage0Endpoint00 : Array FixedGridInterval :=
  #[fixedGridOf (suzukiDF6D4OddEndpointEntryInterval 0 0)]

private def oddStage0AnalyticTail00 : Array FixedGridInterval :=
  #[fixedGridOf (suzukiDF6D4OddAnalyticTailEntryInterval 0 0)]

private def oddDotForColumn
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => oddCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def oddStage1SolveRow00 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (oddStage0SolveCrossRow00[i.val]!).sub
      (oddDotForColumn i.val oddStage0ComparisonRow00)

private def oddStage1ResidualRow301 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (oddStage0FullPrefixRow301[i.val]!).sub
      (oddDotForColumn i.val oddStage0ComparisonPrefixRow301)

private def oddStage1SolveColumn00 : Array FixedGridInterval :=
  Array.ofFn fun j : Fin 256 =>
    let comparisonRow := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4OddComparisonGalerkinEntryInterval j k)
    (fixedGridOf (suzukiDF6D4OddCompleteCrossEntryInterval 0 j)).sub
      (oddDotForColumn 0 comparisonRow)

private def oddStage1ResidualColumn00 : Array FixedGridInterval :=
  Array.ofFn fun r : Fin 300 =>
    let mode := 301 + r.val
    let comparisonRow := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4ComparisonOddOffDiagonalInterval
        (suzukiDF6D4GalerkinMode k) mode)
    (fixedGridOf (suzukiDF6D4FullOddOffDiagonalInterval 1 mode)).sub
      (oddDotForColumn 0 comparisonRow)

private def oddStage2GalerkinBase00 : FixedGridInterval :=
  (oddDotForColumn 0 oddStage0TargetCrossColumn00).add
    (oddDotForColumn 0 oddStage1SolveColumn00)

private def oddStage2FiniteResidualGram00 : FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum suzukiDF6D4FixedGridDenominator
    (fun k : Fin 256 => oddStage1SolveColumn00[k.val]!)
    (fun k : Fin 256 => oddStage1SolveColumn00[k.val]!)).add
  (FixedGridInterval.mulCenteredFinSum suzukiDF6D4FixedGridDenominator
    (fun r : Fin 300 => oddStage1ResidualColumn00[r.val]!)
    (fun r : Fin 300 => oddStage1ResidualColumn00[r.val]!))

private def oddStage2Target00 : Array FixedGridInterval :=
  #[
    (FixedGridInterval.scale (2 / 5 * (1 - 1 / 1000000000) : Rat)
      oddStage0Endpoint00[0]!).sub
      (((oddStage2GalerkinBase00.add
        (FixedGridInterval.scale (1 / 5 : Rat) oddStage2FiniteResidualGram00)).add
        (FixedGridInterval.scale (1 / 5 : Rat) oddStage0AnalyticTail00[0]!)))
  ]

private def stage0ComparisonRow01 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval 1 k)

private def stage0SolveCrossRow01 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4EvenCompleteCrossEntryInterval i 1)

private def stage0ComparisonPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 302)

private def stage0FullPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 => fixedGridOf
    (suzukiDF6D4FullEvenOffDiagonalInterval
      (suzukiDF6D4EvenLowMode i) 302)

private def stage1SolveRow01 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (stage0SolveCrossRow01[i.val]!).sub
      (dotForColumn i.val stage0ComparisonRow01)

private def stage1ResidualRow302 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 45 =>
    (stage0FullPrefixRow302[i.val]!).sub
      (dotForColumn i.val stage0ComparisonPrefixRow302)

private def oddStage0ComparisonRow01 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4OddComparisonGalerkinEntryInterval 1 k)

private def oddStage0SolveCrossRow01 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4OddCompleteCrossEntryInterval i 1)

private def oddStage0ComparisonPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun k : Fin 256 => fixedGridOf
    (suzukiDF6D4ComparisonOddOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) 302)

private def oddStage0FullPrefixRow302 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 => fixedGridOf
    (suzukiDF6D4FullOddOffDiagonalInterval
      (suzukiDF6D4OddLowMode i) 302)

private def oddStage1SolveRow01 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (oddStage0SolveCrossRow01[i.val]!).sub
      (oddDotForColumn i.val oddStage0ComparisonRow01)

private def oddStage1ResidualRow302 : Array FixedGridInterval :=
  Array.ofFn fun i : Fin 44 =>
    (oddStage0FullPrefixRow302[i.val]!).sub
      (oddDotForColumn i.val oddStage0ComparisonPrefixRow302)

private def emitInterval (I : FixedGridInterval) : IO Unit :=
  IO.println s!"{I.lower},{I.upper}"

private def emitBlock (name : String)
    (data : Array FixedGridInterval) : IO Unit := do
  IO.println s!"BEGIN {name}"
  for I in data do
    emitInterval I
  IO.println s!"END {name}"

def runDF6D4FixedGridMaterializer : IO Unit := do
  emitBlock "stage0ComparisonRow00" stage0ComparisonRow00
  emitBlock "stage0SolveCrossRow00" stage0SolveCrossRow00
  emitBlock "stage0ComparisonPrefixRow301" stage0ComparisonPrefixRow301
  emitBlock "stage0FullPrefixRow301" stage0FullPrefixRow301
  emitBlock "stage0TargetCrossColumn00" stage0TargetCrossColumn00
  emitBlock "stage0Endpoint00" stage0Endpoint00
  emitBlock "stage0AnalyticTail00" stage0AnalyticTail00
  emitBlock "stage1SolveRow00" stage1SolveRow00
  emitBlock "stage1ResidualRow301" stage1ResidualRow301
  emitBlock "stage1SolveColumn00" stage1SolveColumn00
  emitBlock "stage1ResidualColumn00" stage1ResidualColumn00
  emitBlock "stage2Target00" stage2Target00
  emitBlock "oddStage0ComparisonRow00" oddStage0ComparisonRow00
  emitBlock "oddStage0SolveCrossRow00" oddStage0SolveCrossRow00
  emitBlock "oddStage0ComparisonPrefixRow301" oddStage0ComparisonPrefixRow301
  emitBlock "oddStage0FullPrefixRow301" oddStage0FullPrefixRow301
  emitBlock "oddStage0TargetCrossColumn00" oddStage0TargetCrossColumn00
  emitBlock "oddStage0Endpoint00" oddStage0Endpoint00
  emitBlock "oddStage0AnalyticTail00" oddStage0AnalyticTail00
  emitBlock "oddStage1SolveRow00" oddStage1SolveRow00
  emitBlock "oddStage1ResidualRow301" oddStage1ResidualRow301
  emitBlock "oddStage1SolveColumn00" oddStage1SolveColumn00
  emitBlock "oddStage1ResidualColumn00" oddStage1ResidualColumn00
  emitBlock "oddStage2Target00" oddStage2Target00
  emitBlock "stage0ComparisonRow01" stage0ComparisonRow01
  emitBlock "stage0SolveCrossRow01" stage0SolveCrossRow01
  emitBlock "stage0ComparisonPrefixRow302" stage0ComparisonPrefixRow302
  emitBlock "stage0FullPrefixRow302" stage0FullPrefixRow302
  emitBlock "stage1SolveRow01" stage1SolveRow01
  emitBlock "stage1ResidualRow302" stage1ResidualRow302
  emitBlock "oddStage0ComparisonRow01" oddStage0ComparisonRow01
  emitBlock "oddStage0SolveCrossRow01" oddStage0SolveCrossRow01
  emitBlock "oddStage0ComparisonPrefixRow302" oddStage0ComparisonPrefixRow302
  emitBlock "oddStage0FullPrefixRow302" oddStage0FullPrefixRow302
  emitBlock "oddStage1SolveRow01" oddStage1SolveRow01
  emitBlock "oddStage1ResidualRow302" oddStage1ResidualRow302

end RiemannHypothesisProject.Experiments.M100

def main : IO Unit :=
  RiemannHypothesisProject.Experiments.M100.runDF6D4FixedGridMaterializer
