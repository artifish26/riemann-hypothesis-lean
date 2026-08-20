import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridCell

/-!
# Parameterized DF6D4 fixed-grid row-shard exporter

For `index < 256`, emit one even/odd comparison-and-solve row.  For
`index < 300`, also emit the corresponding explicit-residual row at mode
`301 + index`.  The Python driver turns this output into independent data,
Stage-0, and Stage-1 modules.
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

private def evenDot
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def oddDot
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => oddCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def emitInterval (I : FixedGridInterval) : IO Unit :=
  IO.println s!"{I.lower},{I.upper}"

private def emitBlock (name : String)
    (data : Array FixedGridInterval) : IO Unit := do
  IO.println s!"BEGIN {name}"
  for I in data do
    emitInterval I
  IO.println s!"END {name}"

def runDF6D4FixedGridRowShardMaterializer (index : Nat) : IO Unit := do
  if hindex : index < 256 then
    let row : Fin 256 := ⟨index, hindex⟩
    let evenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4EvenTabulatedComparisonGalerkinEntryInterval row k)
    let evenCross := Array.ofFn fun i : Fin 45 => fixedGridOf
      (suzukiDF6D4EvenCompleteCrossEntryInterval i row)
    let evenSolve := Array.ofFn fun i : Fin 45 =>
      (evenCross[i.val]!).sub (evenDot i.val evenComparison)
    let oddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4OddComparisonGalerkinEntryInterval row k)
    let oddCross := Array.ofFn fun i : Fin 44 => fixedGridOf
      (suzukiDF6D4OddCompleteCrossEntryInterval i row)
    let oddSolve := Array.ofFn fun i : Fin 44 =>
      (oddCross[i.val]!).sub (oddDot i.val oddComparison)
    emitBlock "evenComparison" evenComparison
    emitBlock "evenCross" evenCross
    emitBlock "evenSolve" evenSolve
    emitBlock "oddComparison" oddComparison
    emitBlock "oddCross" oddCross
    emitBlock "oddSolve" oddSolve
  if index < 300 then
    let mode := 301 + index
    let evenComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4TabulatedComparisonEvenOffDiagonalInterval
        (suzukiDF6D4GalerkinMode k) mode)
    let evenFull := Array.ofFn fun i : Fin 45 => fixedGridOf
      (suzukiDF6D4FullEvenOffDiagonalInterval
        (suzukiDF6D4EvenLowMode i) mode)
    let evenResidual := Array.ofFn fun i : Fin 45 =>
      (evenFull[i.val]!).sub (evenDot i.val evenComparison)
    let oddComparison := Array.ofFn fun k : Fin 256 => fixedGridOf
      (suzukiDF6D4ComparisonOddOffDiagonalInterval
        (suzukiDF6D4GalerkinMode k) mode)
    let oddFull := Array.ofFn fun i : Fin 44 => fixedGridOf
      (suzukiDF6D4FullOddOffDiagonalInterval
        (suzukiDF6D4OddLowMode i) mode)
    let oddResidual := Array.ofFn fun i : Fin 44 =>
      (oddFull[i.val]!).sub (oddDot i.val oddComparison)
    emitBlock "evenResidualComparison" evenComparison
    emitBlock "evenFull" evenFull
    emitBlock "evenResidual" evenResidual
    emitBlock "oddResidualComparison" oddComparison
    emitBlock "oddFull" oddFull
    emitBlock "oddResidual" oddResidual

end RiemannHypothesisProject.Experiments.M100

def main (args : List String) : IO UInt32 := do
  match args with
  | [rawIndex] =>
      match rawIndex.toNat? with
      | some index =>
          if index < 300 then
            RiemannHypothesisProject.Experiments.M100.runDF6D4FixedGridRowShardMaterializer
              index
            return 0
          else
            IO.eprintln "row-shard index must be below 300"
            return 2
      | none =>
          IO.eprintln "row-shard index must be a natural number"
          return 2
  | _ =>
      IO.eprintln "usage: <exporter> <index>"
      return 2
