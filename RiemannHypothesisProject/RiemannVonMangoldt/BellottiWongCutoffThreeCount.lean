import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannHypothesisProject.RiemannVonMangoldtConcretePublishedSources
import RiemannHypothesisProject.RiemannVonMangoldt.ResidualAxisCompactBound

/-!
# Bellotti-Wong cutoff-three closed-ball count

This module derives a coarse quadratic closed-ball zero count directly from
the published Bellotti-Wong exact `N(T)` theorem.  Sampling at `n + 3` keeps
the entire tail above the published threshold `exp 1`, so no separate
small-height zero-free theorem is needed.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- Moving one natural step to the right enlarges the quadratic p-series
factor by at most four. -/
theorem successor_quadraticTailFactor_le_four (n : Nat) :
    |((n + 1 : Nat) : Real) + 1| ^ (2 : Real) <=
      4 * |(n : Real) + 1| ^ (2 : Real) := by
  have hn_nonneg : (0 : Real) <= n := Nat.cast_nonneg n
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  norm_num [Nat.cast_add]
  nlinarith

/-- The linear real-axis contribution at radius `n + 3` is absorbed by the
same quadratic tail factor. -/
theorem cutoffThree_linearAxis_le_four_quadratic (n : Nat) :
    (((n + 3 : Nat) : Real) + 1) <=
      4 * |(n : Real) + 1| ^ (2 : Real) := by
  have hn_nonneg : (0 : Real) <= n := Nat.cast_nonneg n
  rw [abs_of_nonneg (by positivity)]
  norm_num [Nat.cast_add]
  nlinarith

namespace BellottiWongPublishedExactNTTheorem

/-- The exact Bellotti-Wong count has a coarse quadratic bound at every
cutoff-three natural height.  The cutoff alone puts the argument in the
published domain, avoiding any low-zero hypothesis. -/
theorem heightCount_cutoffThree_le_quadratic_noLowZero
    (source : BellottiWongPublishedExactNTTheorem)
    (n : Nat) :
    source.heightCount ((n + 3 : Nat) : Real) <=
      800 * |(n : Real) + 1| ^ (2 : Real) := by
  have hvalid :
      bellottiWongValidFrom <= ((n + 3 : Nat) : Real) := by
    rw [bellottiWongValidFrom]
    exact (le_of_lt Real.exp_one_lt_three).trans (by
      norm_num [Nat.cast_add])
  have habs := source.published_abs_error_le ((n + 3 : Nat) : Real) hvalid
  have hheight :
      source.heightCount ((n + 3 : Nat) : Real) <=
        riemannVonMangoldtMainTerm ((n + 3 : Nat) : Real) +
          bellottiWongErrorTerm ((n + 3 : Nat) : Real) := by
    have hdiff :
        source.heightCount ((n + 3 : Nat) : Real) -
              riemannVonMangoldtMainTerm ((n + 3 : Nat) : Real) <=
            bellottiWongErrorTerm ((n + 3 : Nat) : Real) :=
      (le_abs_self _).trans habs
    linarith
  have hmain0 := riemannVonMangoldtMainTerm_cutoffTwo_le_quadratic (n + 1)
  have herror0 := bellottiWongErrorTerm_cutoffTwo_le_quadratic (n + 1)
  have hmain :
      riemannVonMangoldtMainTerm ((n + 3 : Nat) : Real) <=
        400 * |(n : Real) + 1| ^ (2 : Real) := by
    have hmain' :
        riemannVonMangoldtMainTerm ((n + 3 : Nat) : Real) <=
          100 * |((n + 1 : Nat) : Real) + 1| ^ (2 : Real) := by
      simpa [Nat.add_assoc] using hmain0
    have hfactor := successor_quadraticTailFactor_le_four n
    nlinarith
  have herror :
      bellottiWongErrorTerm ((n + 3 : Nat) : Real) <=
        400 * |(n : Real) + 1| ^ (2 : Real) := by
    have herror' :
        bellottiWongErrorTerm ((n + 3 : Nat) : Real) <=
          100 * |((n + 1 : Nat) : Real) + 1| ^ (2 : Real) := by
      simpa [Nat.add_assoc] using herror0
    have hfactor := successor_quadraticTailFactor_le_four n
    nlinarith
  linarith

/-- Bellotti-Wong plus real-axis classification gives a cutoff-three
quadratic bound for the actual completed-zeta closed-ball window, without a
small-height zero-free input. -/
theorem closedBall_card_cutoffThree_le_quadratic_noLowZero
    (source : BellottiWongPublishedExactNTTheorem)
    (hrealAxis : RealAxisZetaZeroClassification)
    (n : Nat) :
    ((closedBallZero.zetaZeroSubtypeFinset (n + 3)).card : Real) <=
      2000 * |(n : Real) + 1| ^ (2 : Real) := by
  have hpositive := source.positiveClosedBall_card_le_heightCount (n + 3)
  have hnegative := source.negativeClosedBall_card_le_heightCount (n + 3)
  have hheight := source.heightCount_cutoffThree_le_quadratic_noLowZero n
  have haxis := source.axisWindowCard_le_of_realAxisZeroClassification hrealAxis (n + 3)
  have haxisQuadratic := cutoffThree_linearAxis_le_four_quadratic n
  calc
    ((closedBallZero.zetaZeroSubtypeFinset (n + 3)).card : Real) <=
        ((closedBallZeroPositiveOrdinateFinset (n + 3)).card : Real) +
          ((closedBallZeroNegativeOrdinateFinset (n + 3)).card : Real) +
          ((closedBallZeroAxisOrdinateFinset (n + 3)).card : Real) :=
      closedBallZero_card_le_ordinateWindowCards (n + 3)
    _ <= source.heightCount ((n + 3 : Nat) : Real) +
          source.heightCount ((n + 3 : Nat) : Real) +
          (((n + 3 : Nat) : Real) + 1) := by
      gcongr
      simpa using haxis
    _ <= 2000 * |(n : Real) + 1| ^ (2 : Real) := by
      have hfactor_nonneg : 0 <= |(n : Real) + 1| ^ (2 : Real) := by positivity
      nlinarith

/-- The no-low-zero closed-ball estimate as the p-series counting structure
used by the restricted polynomial-Gaussian route. -/
noncomputable def toPolynomialZeroCountingEstimateCutoffThreeNoLowZero
    (source : BellottiWongPublishedExactNTTheorem)
    (hrealAxis : RealAxisZetaZeroClassification) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  SchwartzRiemannWeilCumulativeWindowCountingEstimate.toPolynomialZeroCountingEstimate
    (SchwartzRiemannWeilCumulativeWindowCountingEstimate.ofExactWindowCardPolynomialBound
      closedBallZero 3 2000 2 (by norm_num)
      (source.closedBall_card_cutoffThree_le_quadratic_noLowZero hrealAxis))

/-- The direct Bellotti-Wong count uses cutoff `3`. -/
theorem toPolynomialZeroCountingEstimateCutoffThreeNoLowZero_cutoff
    (source : BellottiWongPublishedExactNTTheorem)
    (hrealAxis : RealAxisZetaZeroClassification) :
    (source.toPolynomialZeroCountingEstimateCutoffThreeNoLowZero hrealAxis).cutoff = 3 := by
  rfl

/-- The direct Bellotti-Wong count has quadratic growth. -/
theorem toPolynomialZeroCountingEstimateCutoffThreeNoLowZero_growth
    (source : BellottiWongPublishedExactNTTheorem)
    (hrealAxis : RealAxisZetaZeroClassification) :
    (source.toPolynomialZeroCountingEstimateCutoffThreeNoLowZero hrealAxis).growth = 2 := by
  rfl

/-- The exact Bellotti-Wong theorem alone gives a cutoff-three quadratic
closed-ball count.  Residual real-axis zeroes need not be classified: they all
lie in one fixed compact window, whose finite cardinality is absorbed into the
counting constant. -/
theorem closedBall_card_cutoffThree_le_quadratic_noLowZeroOrRealAxisHypothesis
    (source : BellottiWongPublishedExactNTTheorem)
    (n : Nat) :
    ((closedBallZero.zetaZeroSubtypeFinset (n + 3)).card : Real) <=
      (1604 + residualRealAxisCompactCard) *
        |(n : Real) + 1| ^ (2 : Real) := by
  let R : Real := |(n : Real) + 1| ^ (2 : Real)
  have hpositive := source.positiveClosedBall_card_le_heightCount (n + 3)
  have hnegative := source.negativeClosedBall_card_le_heightCount (n + 3)
  have hheight := source.heightCount_cutoffThree_le_quadratic_noLowZero n
  have haxis := closedBallZeroAxis_card_cutoffThree_le_compactQuadratic n
  calc
    ((closedBallZero.zetaZeroSubtypeFinset (n + 3)).card : Real) <=
        ((closedBallZeroPositiveOrdinateFinset (n + 3)).card : Real) +
          ((closedBallZeroNegativeOrdinateFinset (n + 3)).card : Real) +
          ((closedBallZeroAxisOrdinateFinset (n + 3)).card : Real) :=
      closedBallZero_card_le_ordinateWindowCards (n + 3)
    _ <= source.heightCount ((n + 3 : Nat) : Real) +
          source.heightCount ((n + 3 : Nat) : Real) +
          (4 + residualRealAxisCompactCard) * R := by
      gcongr
    _ <= 800 * R + 800 * R +
          (4 + residualRealAxisCompactCard) * R := by
      gcongr
    _ = (1604 + residualRealAxisCompactCard) *
          |(n : Real) + 1| ^ (2 : Real) := by
      dsimp [R]
      ring

/-- Bellotti-Wong's exact published `N(T)` theorem as a quadratic p-series
counting estimate, with neither a low-height zero-free hypothesis nor a full
real-axis zero classification. -/
noncomputable def toPolynomialZeroCountingEstimateCutoffThree
    (source : BellottiWongPublishedExactNTTheorem) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  SchwartzRiemannWeilCumulativeWindowCountingEstimate.toPolynomialZeroCountingEstimate
    (SchwartzRiemannWeilCumulativeWindowCountingEstimate.ofExactWindowCardPolynomialBound
      closedBallZero 3 (1604 + residualRealAxisCompactCard) 2
      (by nlinarith [residualRealAxisCompactCard_nonneg])
      source.closedBall_card_cutoffThree_le_quadratic_noLowZeroOrRealAxisHypothesis)

theorem toPolynomialZeroCountingEstimateCutoffThree_cutoff
    (source : BellottiWongPublishedExactNTTheorem) :
    source.toPolynomialZeroCountingEstimateCutoffThree.cutoff = 3 := by
  rfl

theorem toPolynomialZeroCountingEstimateCutoffThree_growth
    (source : BellottiWongPublishedExactNTTheorem) :
    source.toPolynomialZeroCountingEstimateCutoffThree.growth = 2 := by
  rfl

end BellottiWongPublishedExactNTTheorem

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
