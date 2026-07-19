import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import RiemannHypothesisProject.RiemannVonMangoldtPublishedBounds

/-!
# Bellotti-Wong first-row parameters

This module records the exact rational values behind the decimal parameters in
the first row of Bellotti-Wong's table and proves the elementary geometric
side conditions of their general theorem.  The separate source condition
involving their zeta-bound quantity `theta_(1+eta)` is analytic and is not
claimed here.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

/-- The height `T_0 = 30610046000` used for the first table row. -/
def bellottiWongHighRangeThreshold : Real := 30610046000

/-- Bellotti-Wong's first-row center parameter `c = 1.000225`. -/
def bellottiWongFirstRowC : Real := 1000225 / 1000000

/-- Bellotti-Wong's first-row radius parameter `r = 1.000605`. -/
def bellottiWongFirstRowR : Real := 1000605 / 1000000

/-- Bellotti-Wong's first-row strip parameter `eta = 0.000158`. -/
def bellottiWongFirstRowEta : Real := 158 / 1000000

/-- The derived parameter `sigma_1 = c + (c - 1/2)^2 / r`. -/
def bellottiWongSigmaOne (c r : Real) : Real :=
  c + (c - 1 / 2) ^ 2 / r

/-- The derived parameter `delta = 2c - sigma_1 - 1/2`. -/
def bellottiWongDelta (c r : Real) : Real :=
  2 * c - bellottiWongSigmaOne c r - 1 / 2

/-- Bellotti-Wong's piecewise angular cutoff `theta_y`. -/
def bellottiWongTheta (c r y : Real) : Real :=
  if c + r <= y then
    0
  else if c - r <= y then
    Real.arccos ((y - c) / r)
  else
    Real.pi

/--
The purely algebraic parameter conditions in Bellotti-Wong's general theorem.
The paper's additional `theta_(1+eta) <= 2.1` hypothesis is deliberately kept
outside this proposition because it depends on explicit zeta estimates.
-/
def BellottiWongGeneralTheoremGeometricConditions
    (c r eta : Real) : Prop :=
  0 < c ∧
  0 < r ∧
  0 < eta ∧
  -(1 / 2 : Real) < c - r ∧
  c - r < 1 - c ∧
  1 - c < -eta ∧
  -eta < (1 / 4 : Real) ∧
  (1 / 4 : Real) <= bellottiWongDelta c r ∧
  bellottiWongDelta c r < (1 / 2 : Real) ∧
  (1 / 2 : Real) < 1 + eta ∧
  1 + eta < bellottiWongSigmaOne c r ∧
  bellottiWongSigmaOne c r < c + r

/-- The exact first-row decimal parameters satisfy every algebraic condition. -/
theorem bellottiWongFirstRow_geometricConditions :
    BellottiWongGeneralTheoremGeometricConditions
      bellottiWongFirstRowC bellottiWongFirstRowR bellottiWongFirstRowEta := by
  norm_num [BellottiWongGeneralTheoremGeometricConditions,
    bellottiWongFirstRowC, bellottiWongFirstRowR, bellottiWongFirstRowEta,
    bellottiWongDelta, bellottiWongSigmaOne]

/-- For the first row, `theta_(1+eta)` lies in the arccosine branch. -/
theorem bellottiWongFirstRow_theta_eq :
    bellottiWongTheta bellottiWongFirstRowC bellottiWongFirstRowR
        (1 + bellottiWongFirstRowEta) =
      Real.arccos
        (((1 + bellottiWongFirstRowEta) - bellottiWongFirstRowC) /
          bellottiWongFirstRowR) := by
  unfold bellottiWongTheta
  rw [if_neg, if_pos]
  · norm_num [bellottiWongFirstRowC, bellottiWongFirstRowR,
      bellottiWongFirstRowEta]
  · norm_num [bellottiWongFirstRowC, bellottiWongFirstRowR,
      bellottiWongFirstRowEta]

/-- The first-row arccosine argument is strictly greater than `-1/2`. -/
theorem bellottiWongFirstRow_neg_one_half_lt_thetaArgument :
    -(1 / 2 : Real) <
      ((1 + bellottiWongFirstRowEta) - bellottiWongFirstRowC) /
        bellottiWongFirstRowR := by
  norm_num [bellottiWongFirstRowC, bellottiWongFirstRowR,
    bellottiWongFirstRowEta]

/-- The first-row parameters satisfy the remaining `theta_(1+eta) <= 2.1` condition. -/
theorem bellottiWongFirstRow_thetaCondition :
    bellottiWongTheta bellottiWongFirstRowC bellottiWongFirstRowR
        (1 + bellottiWongFirstRowEta) <= (21 : Real) / 10 := by
  rw [bellottiWongFirstRow_theta_eq]
  have hmono :
      Real.arccos
          (((1 + bellottiWongFirstRowEta) - bellottiWongFirstRowC) /
            bellottiWongFirstRowR) <=
        Real.arccos (-(1 / 2 : Real)) :=
    Real.arccos_le_arccos
      bellottiWongFirstRow_neg_one_half_lt_thetaArgument.le
  have hacos_half : Real.arccos (1 / 2 : Real) = Real.pi / 3 := by
    rw [← Real.cos_pi_div_three]
    exact Real.arccos_cos (by positivity) (by nlinarith [Real.pi_pos])
  have hacos_neg_half :
      Real.arccos (-(1 / 2 : Real)) = 2 * Real.pi / 3 := by
    rw [Real.arccos_neg, hacos_half]
    ring
  calc
    Real.arccos
        (((1 + bellottiWongFirstRowEta) - bellottiWongFirstRowC) /
          bellottiWongFirstRowR) <=
        Real.arccos (-(1 / 2 : Real)) := hmono
    _ = 2 * Real.pi / 3 := hacos_neg_half
    _ <= (21 : Real) / 10 := by nlinarith [Real.pi_lt_d2]

/-- The paper's large-height split is above its stated general-theorem floor `e`. -/
theorem bellottiWong_validFrom_le_highRangeThreshold :
    bellottiWongValidFrom <= bellottiWongHighRangeThreshold := by
  rw [bellottiWongValidFrom, bellottiWongHighRangeThreshold]
  exact Real.exp_one_lt_three.le.trans (by norm_num)

/-- Every height in the high range lies in Bellotti-Wong's stated domain. -/
theorem bellottiWong_validFrom_le_of_highRange
    {T : Real} (hT : bellottiWongHighRangeThreshold <= T) :
    bellottiWongValidFrom <= T :=
  bellottiWong_validFrom_le_highRangeThreshold.trans hT

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
