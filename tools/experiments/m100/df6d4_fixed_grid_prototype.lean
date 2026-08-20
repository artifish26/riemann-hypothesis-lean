import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComparisonTable

/-!
# M100-DF6D4 fixed-grid performance prototype

This is a runtime experiment, not a proof artifact.  It forces the dominant
even-parity solve-residual and explicit residual-column caches while keeping
all intermediate interval endpoints as integer numerators over `10^16`.
Comparison transforms come from the already checked frozen lookup table.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

structure FixedGridInterval where
  lower : Int
  upper : Int
deriving DecidableEq, Inhabited, Repr

private def gridDenominator : Int := 10000000000000000

private def roundLowerNumerator (q : Rat) : Int :=
  (q.num * gridDenominator) / (q.den : Int)

private def roundUpperNumerator (q : Rat) : Int :=
  -((-(q.num * gridDenominator)) / (q.den : Int))

private def FixedGridInterval.ofRationalInterval
    (I : RationalInterval) : FixedGridInterval :=
  { lower := roundLowerNumerator I.lower
    upper := roundUpperNumerator I.upper }

private def FixedGridInterval.add
    (I J : FixedGridInterval) : FixedGridInterval :=
  { lower := I.lower + J.lower
    upper := I.upper + J.upper }

private def FixedGridInterval.sub
    (I J : FixedGridInterval) : FixedGridInterval :=
  { lower := I.lower - J.upper
    upper := I.upper - J.lower }

private def scaleLowerNumerator
    (q : Rat) (I : FixedGridInterval) : Int :=
  if 0 <= q then
    (q.num * I.lower) / (q.den : Int)
  else
    (q.num * I.upper) / (q.den : Int)

private def scaleUpperNumerator
    (q : Rat) (I : FixedGridInterval) : Int :=
  if 0 <= q then
    -((-(q.num * I.upper)) / (q.den : Int))
  else
    -((-(q.num * I.lower)) / (q.den : Int))

private def FixedGridInterval.scale
    (q : Rat) (I : FixedGridInterval) : FixedGridInterval :=
  { lower := scaleLowerNumerator q I
    upper := scaleUpperNumerator q I }

private def FixedGridInterval.scaleInt
    (a : Int) (I : FixedGridInterval) : FixedGridInterval :=
  if 0 <= a then
    { lower := a * I.lower, upper := a * I.upper }
  else
    { lower := a * I.upper, upper := a * I.lower }

private def scaleArraySumAux
    (coefficient : Nat -> Rat) (entries : Array FixedGridInterval) :
    Nat -> FixedGridInterval
  | 0 => { lower := 0, upper := 0 }
  | n + 1 =>
      (scaleArraySumAux coefficient entries n).add
        ((entries[n]!).scale (coefficient n))

private def scaleArraySum
    (coefficient : Nat -> Rat)
    (entries : Array FixedGridInterval) : FixedGridInterval :=
  scaleArraySumAux coefficient entries entries.size

private def dotArraySumAux
    (coefficient : Nat -> Int) (entries : Array FixedGridInterval) :
    Nat -> FixedGridInterval
  | 0 => { lower := 0, upper := 0 }
  | n + 1 =>
      (dotArraySumAux coefficient entries n).add
        ((entries[n]!).scaleInt (coefficient n))

private def dotArraySum
    (Q : Nat) (coefficient : Nat -> Int)
    (entries : Array FixedGridInterval) : FixedGridInterval :=
  (dotArraySumAux coefficient entries entries.size).scale (1 / Q)

private def tabulatedComparisonEvenOffDiagonalBracketInterval
    (left right : Nat) : RationalInterval :=
  let difference := right - left
  let differenceCoefficient : Rat :=
    suzukiDF6D4AlternatingSign difference / difference
  let totalCoefficient : Rat :=
    suzukiDF6D4AlternatingSign (left + right) / (left + right)
  (RationalInterval.scale differenceCoefficient
      ((suzukiDF6D4TabulatedComparisonSineTransformInterval right).sub
        (suzukiDF6D4TabulatedComparisonSineTransformInterval left))).add
    (RationalInterval.scale totalCoefficient
      ((suzukiDF6D4TabulatedComparisonSineTransformInterval left).add
        (suzukiDF6D4TabulatedComparisonSineTransformInterval right)))

private def tabulatedComparisonEvenOffDiagonalInterval
    (left right : Nat) : RationalInterval :=
  (suzukiDF6D4EvenConvolutionPrefactorInterval left right).mulLeftNonneg
    (tabulatedComparisonEvenOffDiagonalBracketInterval left right)

private def evenComparisonGalerkinGridEntry
    (i j : Fin 256) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval <|
    if i = j then
      suzukiDF6D4TabulatedEvenComparisonDiagonalInterval
        (suzukiDF6D4GalerkinMode i)
    else if i.val < j.val then
      tabulatedComparisonEvenOffDiagonalInterval
        (suzukiDF6D4GalerkinMode i) (suzukiDF6D4GalerkinMode j)
    else
      tabulatedComparisonEvenOffDiagonalInterval
        (suzukiDF6D4GalerkinMode j) (suzukiDF6D4GalerkinMode i)

private def evenComparisonPrefixGridEntry
    (r : Fin 300) (k : Fin 256) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval <|
    tabulatedComparisonEvenOffDiagonalInterval
      (suzukiDF6D4GalerkinMode k) (301 + r.val)

private def evenCompleteCrossGridEntry
    (j : Fin 256) (i : Fin 45) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval
    (suzukiDF6D4EvenCompleteCrossEntryInterval i j)

private def evenFullPrefixGridEntry
    (r : Fin 300) (i : Fin 45) : FixedGridInterval :=
  FixedGridInterval.ofRationalInterval
    (suzukiDF6D4FullEvenOffDiagonalInterval
      (suzukiDF6D4EvenLowMode i) (301 + r.val))

private def evenComparisonGalerkinGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun i : Fin 256 =>
    Array.ofFn fun j : Fin 256 => evenComparisonGalerkinGridEntry i j

private def evenComparisonPrefixGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun r : Fin 300 =>
    Array.ofFn fun k : Fin 256 => evenComparisonPrefixGridEntry r k

private def evenCompleteCrossGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun j : Fin 256 =>
    Array.ofFn fun i : Fin 45 => evenCompleteCrossGridEntry j i

private def evenFullPrefixGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun r : Fin 300 =>
    Array.ofFn fun i : Fin 45 => evenFullPrefixGridEntry r i

private def evenCoefficient (k i : Nat) : Rat :=
  suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!

private def coefficientDenominator : Nat :=
  1000000000000000000000000

private def evenCoefficientNumerator (k i : Nat) : Int :=
  let q := evenCoefficient k i
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def evenCoefficientsHaveCommonDenominator : Bool :=
  suzukiDF6D4EvenGalerkinApproximantData.all fun q =>
    let numerator :=
      q.num * ((coefficientDenominator / q.den : Nat) : Int)
    q == (numerator : Rat) / coefficientDenominator

private def evenSolveResidualGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun j : Fin 256 =>
    Array.ofFn fun i : Fin 45 =>
      ((evenCompleteCrossGridCache[j.val]!)[i.val]!).sub
        (scaleArraySum
          (fun k => evenCoefficient k i.val)
          (evenComparisonGalerkinGridCache[j.val]!))

private def evenResidualColumnGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun r : Fin 300 =>
    Array.ofFn fun i : Fin 45 =>
      ((evenFullPrefixGridCache[r.val]!)[i.val]!).sub
        (scaleArraySum
          (fun k => evenCoefficient k i.val)
          (evenComparisonPrefixGridCache[r.val]!))

private def evenSolveResidualCommonDotGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun j : Fin 256 =>
    Array.ofFn fun i : Fin 45 =>
      ((evenCompleteCrossGridCache[j.val]!)[i.val]!).sub
        (dotArraySum coefficientDenominator
          (fun k => evenCoefficientNumerator k i.val)
          (evenComparisonGalerkinGridCache[j.val]!))

private def evenResidualColumnCommonDotGridCache :
    Array (Array FixedGridInterval) :=
  Array.ofFn fun r : Fin 300 =>
    Array.ofFn fun i : Fin 45 =>
      ((evenFullPrefixGridCache[r.val]!)[i.val]!).sub
        (dotArraySum coefficientDenominator
          (fun k => evenCoefficientNumerator k i.val)
          (evenComparisonPrefixGridCache[r.val]!))

private def intervalChecksum
    (seed : Int) (I : FixedGridInterval) : Int :=
  seed + 3 * I.lower + 5 * I.upper

private def matrixChecksum
    (matrix : Array (Array FixedGridInterval)) : Int :=
  matrix.foldl
    (fun outer row => row.foldl intervalChecksum outer) 0

def runDF6D4FixedGridPrototype : IO Unit := do
  let solveChecksum := matrixChecksum evenSolveResidualGridCache
  let residualChecksum := matrixChecksum evenResidualColumnGridCache
  IO.println "DF6D4_FIXED_GRID_PROTOTYPE"
  IO.println s!"solve_rows={evenSolveResidualGridCache.size}"
  IO.println s!"residual_rows={evenResidualColumnGridCache.size}"
  IO.println s!"solve_checksum={solveChecksum}"
  IO.println s!"residual_checksum={residualChecksum}"

private def evenSolveResidualGridRow
    (j : Fin 256) : Array FixedGridInterval :=
  let comparisonRow := Array.ofFn fun k : Fin 256 =>
    evenComparisonGalerkinGridEntry j k
  Array.ofFn fun i : Fin 45 =>
    (evenCompleteCrossGridEntry j i).sub
      (scaleArraySum
        (fun k => evenCoefficient k i.val)
        comparisonRow)

private def evenSolveResidualGridRow00Data : Array FixedGridInterval :=
  #[{ lower := -15832, upper := 20231 },
    { lower := -28432, upper := 22236 },
    { lower := -22031, upper := 28169 },
    { lower := -27129, upper := 21173 },
    { lower := -20348, upper := 26124 },
    { lower := -26530, upper := 20684 },
    { lower := -21793, upper := 27900 },
    { lower := -27951, upper := 21827 },
    { lower := -19996, upper := 25734 },
    { lower := -23565, upper := 18211 },
    { lower := -18902, upper := 24410 },
    { lower := -27553, upper := 21459 },
    { lower := -22435, upper := 28738 },
    { lower := -25678, upper := 19894 },
    { lower := -16629, upper := 21693 },
    { lower := -22212, upper := 17007 },
    { lower := -21090, upper := 27184 },
    { lower := -30478, upper := 23773 },
    { lower := -21039, upper := 27160 },
    { lower := -20825, upper := 15798 },
    { lower := -14989, upper := 19866 },
    { lower := -26662, upper := 20545 },
    { lower := -25903, upper := 33227 },
    { lower := -30672, upper := 23786 },
    { lower := -16144, upper := 21409 },
    { lower := -17586, upper := 12969 },
    { lower := -19735, upper := 25875 },
    { lower := -37362, upper := 29112 },
    { lower := -29043, upper := 37299 },
    { lower := -24558, upper := 18549 },
    { lower := -11149, upper := 15575 },
    { lower := -24740, upper := 18602 },
    { lower := -34487, upper := 44055 },
    { lower := -50018, upper := 39281 },
    { lower := -25435, upper := 33180 },
    { lower := -14468, upper := 10081 },
    { lower := -17161, upper := 23116 },
    { lower := -57857, upper := 45664 },
    { lower := -64426, upper := 80656 },
    { lower := -59675, upper := 47297 },
    { lower := -12459, upper := 17013 },
    { lower := -20417, upper := 15573 },
    { lower := -93276, upper := 114305 },
    { lower := -260036, upper := 214279 },
    { lower := -304375, upper := 364218 }]

example : evenSolveResidualGridRow00Data = evenSolveResidualGridRow 0 := by
  native_decide

def runDF6D4FixedGridRowPrototype : IO Unit := do
  let row := evenSolveResidualGridRow 0
  IO.println "DF6D4_FIXED_GRID_ROW_PROTOTYPE"
  IO.println s!"row_size={row.size}"
  IO.println s!"row_data={repr row}"

def reportDF6D4MaterializedRowCheck : IO Unit :=
  IO.println "DF6D4_MATERIALIZED_ROW_CHECK=PASS"

def runDF6D4CommonDotPrototype : IO Unit := do
  let solveChecksum := matrixChecksum evenSolveResidualCommonDotGridCache
  let residualChecksum := matrixChecksum evenResidualColumnCommonDotGridCache
  IO.println "DF6D4_COMMON_DOT_PROTOTYPE"
  IO.println s!"solve_rows={evenSolveResidualCommonDotGridCache.size}"
  IO.println s!"residual_rows={evenResidualColumnCommonDotGridCache.size}"
  IO.println s!"solve_checksum={solveChecksum}"
  IO.println s!"residual_checksum={residualChecksum}"

def reportDF6D4CoefficientGridCheck : IO Unit :=
  IO.println s!"DF6D4_COEFFICIENT_GRID_EXACT={evenCoefficientsHaveCommonDenominator}"

end RiemannHypothesisProject.Experiments.M100

def main : IO Unit :=
  RiemannHypothesisProject.Experiments.M100.reportDF6D4CoefficientGridCheck
