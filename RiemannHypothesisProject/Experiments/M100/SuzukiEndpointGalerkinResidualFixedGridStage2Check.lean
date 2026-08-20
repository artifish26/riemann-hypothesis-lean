import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStageData

/-!
# DF6D4 fixed-grid Stage-2 bounded target check

This module recomputes the even `(0,0)` final target solely from materialized
Stage-0 and Stage-1 literals.  It also checks admission into the generated
rational certificate interval.  No live analytic formula is imported.
-/

namespace RiemannHypothesisProject.Experiments.M100

private def fixedGridDenominator : Nat :=
  1000000000000000000

private def coefficientDenominator : Nat :=
  1000000000000000000000000

private def evenCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4EvenGalerkinApproximantData[k * 45 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def oddCoefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4OddGalerkinApproximantData[k * 44 + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def dotForColumn
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => evenCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def galerkinBase00FromLiterals : FixedGridInterval :=
  (dotForColumn 0 suzukiDF6D4FixedGridStage0TargetCrossColumn00Data).add
    (dotForColumn 0 suzukiDF6D4FixedGridStage1SolveColumn00Data)

private def finiteResidualGram00FromLiterals : FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun k : Fin 256 => suzukiDF6D4FixedGridStage1SolveColumn00Data[k.val]!)
    (fun k : Fin 256 => suzukiDF6D4FixedGridStage1SolveColumn00Data[k.val]!)).add
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun r : Fin 300 =>
      suzukiDF6D4FixedGridStage1ResidualColumn00Data[r.val]!)
    (fun r : Fin 300 =>
      suzukiDF6D4FixedGridStage1ResidualColumn00Data[r.val]!))

private def target00FromLiterals : FixedGridInterval :=
  (FixedGridInterval.scale (19 / 1000 * (1 - 1 / 1000000000) : Rat)
    suzukiDF6D4FixedGridStage0Endpoint00Data[0]!).sub
    (((galerkinBase00FromLiterals.add
      (FixedGridInterval.scale (1 / 5 : Rat)
        finiteResidualGram00FromLiterals)).add
      (FixedGridInterval.scale (1 / 5 : Rat)
        suzukiDF6D4FixedGridStage0AnalyticTail00Data[0]!)))

private def oddDotForColumn
    (i : Nat) (entries : Array FixedGridInterval) : FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => oddCoefficientNumerator k i)
    (fun k : Fin 256 => entries[k.val]!)

private def oddGalerkinBase00FromLiterals : FixedGridInterval :=
  (oddDotForColumn 0
    suzukiDF6D4FixedGridOddStage0TargetCrossColumn00Data).add
    (oddDotForColumn 0 suzukiDF6D4FixedGridOddStage1SolveColumn00Data)

private def oddFiniteResidualGram00FromLiterals : FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun k : Fin 256 =>
      suzukiDF6D4FixedGridOddStage1SolveColumn00Data[k.val]!)
    (fun k : Fin 256 =>
      suzukiDF6D4FixedGridOddStage1SolveColumn00Data[k.val]!)).add
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun r : Fin 300 =>
      suzukiDF6D4FixedGridOddStage1ResidualColumn00Data[r.val]!)
    (fun r : Fin 300 =>
      suzukiDF6D4FixedGridOddStage1ResidualColumn00Data[r.val]!))

private def oddTarget00FromLiterals : FixedGridInterval :=
  (FixedGridInterval.scale (2 / 5 * (1 - 1 / 1000000000) : Rat)
    suzukiDF6D4FixedGridOddStage0Endpoint00Data[0]!).sub
    (((oddGalerkinBase00FromLiterals.add
      (FixedGridInterval.scale (1 / 5 : Rat)
        oddFiniteResidualGram00FromLiterals)).add
      (FixedGridInterval.scale (1 / 5 : Rat)
        suzukiDF6D4FixedGridOddStage0AnalyticTail00Data[0]!)))

theorem suzukiDF6D4FixedGridStage2BoundedBlock_valid :
    suzukiDF6D4FixedGridStage2Target00Data = #[target00FromLiterals] := by
  native_decide

theorem suzukiDF6D4FixedGridStage2Target00_admitted :
    (suzukiDF6D4EvenResidualTargetCertificate.entry 0 0).lower <=
        (FixedGridInterval.toRationalInterval fixedGridDenominator
          target00FromLiterals).lower /\
      (FixedGridInterval.toRationalInterval fixedGridDenominator
        target00FromLiterals).upper <=
        (suzukiDF6D4EvenResidualTargetCertificate.entry 0 0).upper := by
  native_decide

theorem suzukiDF6D4FixedGridOddStage2BoundedBlock_valid :
    suzukiDF6D4FixedGridOddStage2Target00Data =
      #[oddTarget00FromLiterals] := by
  native_decide

theorem suzukiDF6D4FixedGridOddStage2Target00_admitted :
    (suzukiDF6D4OddResidualTargetCertificate.entry 0 0).lower <=
        (FixedGridInterval.toRationalInterval fixedGridDenominator
          oddTarget00FromLiterals).lower /\
      (FixedGridInterval.toRationalInterval fixedGridDenominator
        oddTarget00FromLiterals).upper <=
        (suzukiDF6D4OddResidualTargetCertificate.entry 0 0).upper := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
