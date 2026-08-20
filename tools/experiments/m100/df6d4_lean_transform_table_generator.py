#!/usr/bin/env python3
"""Generate the exact Lean DF6D4 complete-transform table.

This script mirrors the rational definitions in the DF6D4 Lean interval
evaluators.  It is only a fast materializer: the generated Lean module checks
all 603 cells against the proved live evaluator with ``native_decide``.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from math import factorial
from pathlib import Path


@dataclass(frozen=True)
class Interval:
    lower: Q
    upper: Q

    @staticmethod
    def point(value: Q | int) -> "Interval":
        q = Q(value)
        return Interval(q, q)

    def add(self, other: "Interval") -> "Interval":
        return Interval(self.lower + other.lower, self.upper + other.upper)

    def neg(self) -> "Interval":
        return Interval(-self.upper, -self.lower)

    def sub(self, other: "Interval") -> "Interval":
        return self.add(other.neg())

    def scale(self, value: Q | int) -> "Interval":
        q = Q(value)
        endpoints = (q * self.lower, q * self.upper)
        return Interval(min(endpoints), max(endpoints))

    def mul_nonneg(self, other: "Interval") -> "Interval":
        return Interval(self.lower * other.lower, self.upper * other.upper)

    def mul_left_nonneg(self, other: "Interval") -> "Interval":
        return Interval(
            min(self.lower * other.lower, self.upper * other.lower),
            max(self.lower * other.upper, self.upper * other.upper),
        )

    def pow_nonneg(self, exponent: int) -> "Interval":
        return Interval(self.lower**exponent, self.upper**exponent)

    def inv_pos(self) -> "Interval":
        return Interval(1 / self.upper, 1 / self.lower)

    def div_nonneg(self, other: "Interval") -> "Interval":
        return self.mul_nonneg(other.inv_pos())

    def round_out(self, denominator: int) -> "Interval":
        def down(q: Q) -> Q:
            return Q((q * denominator).numerator // (q * denominator).denominator,
                     denominator)

        def up(q: Q) -> Q:
            scaled = q * denominator
            ceiling = -((-scaled.numerator) // scaled.denominator)
            return Q(ceiling, denominator)

        return Interval(down(self.lower), up(self.upper))


PI = Interval(Q(314159265358979323846, 10**20), Q(314159265358979323847, 10**20))
LOG_TWO = Interval(Q(693147180559945309, 10**18), Q(693147180559945310, 10**18))
SQRT_TWO = Interval(Q(1414213562373095048, 10**18), Q(1414213562373095049, 10**18))
A_STAR = Interval(Q(42867814670054956, 10**17), Q(42867814670054957, 10**17))
EXP_NEG_A = Interval(Q(651369540883008815, 10**18), Q(651369540883008823, 10**18))


def wave_number(mode: int) -> Interval:
    return PI.scale(mode).div_nonneg(A_STAR)


def digamma_summand(n: int, y: Interval) -> Interval:
    d = Q(n) + Q(1, 4)

    def value(x: Q) -> Q:
        return x / (d * d + x * x)

    lower_value = value(y.lower)
    upper_value = value(y.upper)
    if y.upper <= d:
        return Interval(lower_value, upper_value)
    if d <= y.lower:
        return Interval(upper_value, lower_value)
    return Interval(min(lower_value, upper_value), Q(1, 2) / d)


def arctan_small(interval: Interval) -> Interval:
    return Interval(
        interval.lower - interval.upper**3 / 3,
        interval.upper - interval.lower**3 / 3 + interval.upper**5 / 5,
    )


def frozen_digamma(mode: int) -> Interval:
    y = wave_number(mode).scale(Q(1, 2))
    partial = Interval.point(0)
    for n in range(16384):
        partial = partial.add(digamma_summand(n, y)).round_out(10**18)
    d = Q(16384) + Q(1, 4)
    argument = y.div_nonneg(Interval.point(d))
    first = digamma_summand(16384, y)
    correction = y.div_nonneg(Interval.point(3 * d**3))
    center = arctan_small(argument).add(first.scale(Q(1, 2)))
    tail = Interval(center.lower, center.upper + correction.upper)
    return partial.add(tail).round_out(10**16)


def restoration_term(mode: int, k: int) -> Interval:
    wave = wave_number(mode)
    exponential = EXP_NEG_A.pow_nonneg(4 * k + 1)
    numerator = wave.mul_nonneg(exponential)
    decay = Q(2 * k) + Q(1, 2)
    denominator = Interval.point(decay**2).add(wave.pow_nonneg(2))
    return numerator.div_nonneg(denominator).scale(2)


def frozen_restoration(mode: int) -> Interval:
    partial = Interval.point(0)
    for k in range(128):
        partial = partial.add(restoration_term(mode, k)).round_out(10**18)
    wave = wave_number(mode)
    decay = Q(2 * 128) + Q(1, 2)
    numerator = wave.mul_nonneg(EXP_NEG_A.pow_nonneg(4 * 128 + 1))
    first = numerator.div_nonneg(Interval.point(decay**2)).scale(2)
    ratio_denominator = Interval.point(1).sub(EXP_NEG_A.pow_nonneg(4))
    tail_bound = first.div_nonneg(ratio_denominator)
    return partial.add(Interval(0, tail_bound.upper)).round_out(10**16)


def sine_taylor(terms: int, interval: Interval) -> Interval:
    partial = Interval.point(0)
    for n in range(terms):
        coefficient = Q((-1) ** n, factorial(2 * n + 1))
        partial = partial.add(interval.pow_nonneg(2 * n + 1).scale(coefficient))
    error = interval.upper ** (2 * terms + 1) / factorial(2 * terms + 1)
    return partial.add(Interval(-error, error))


def cosine_taylor(terms: int, interval: Interval) -> Interval:
    partial = Interval.point(0)
    for n in range(terms):
        coefficient = Q((-1) ** n, factorial(2 * n))
        partial = partial.add(interval.pow_nonneg(2 * n).scale(coefficient))
    error = interval.upper ** (2 * terms) / factorial(2 * terms)
    return partial.add(Interval(-error, error))


def prime_quadrant(mode: int) -> int:
    return (3233881577099095 * mode + 500000000000000) // 1000000000000000


def quarter_sine_interval(q: int, sine: Interval, cosine: Interval) -> Interval:
    match q % 4:
        case 0:
            return sine
        case 1:
            return cosine
        case 2:
            return sine.neg()
        case 3:
            return cosine.neg()
    raise AssertionError("unreachable")


def frozen_prime_sine(mode: int) -> Interval:
    angle = PI.scale(mode).mul_nonneg(LOG_TWO).div_nonneg(A_STAR)
    shift = PI.scale(Q(prime_quadrant(mode), 2))
    residual = angle.sub(shift)
    absolute = residual.neg() if residual.upper <= 0 else residual
    sine = sine_taylor(7, absolute)
    if residual.upper <= 0:
        sine = sine.neg()
    cosine = cosine_taylor(7, absolute)
    return quarter_sine_interval(prime_quadrant(mode), sine, cosine).round_out(10**16)


def pole_transform(mode: int) -> Interval:
    wave = wave_number(mode)
    exp_a = EXP_NEG_A.inv_pos()
    cosh_minus_one = exp_a.add(EXP_NEG_A).scale(Q(1, 2)).sub(Interval.point(1))
    numerator = wave.mul_nonneg(cosh_minus_one)
    denominator = wave.pow_nonneg(2).add(Interval.point(Q(1, 4)))
    return numerator.div_nonneg(denominator).scale(-4)


def prime_transform(mode: int) -> Interval:
    coefficient = SQRT_TWO.mul_nonneg(LOG_TWO)
    return coefficient.mul_left_nonneg(frozen_prime_sine(mode)).scale(-1)


def frozen_complete_transform(mode: int) -> Interval:
    complete = pole_transform(mode).sub(
        frozen_digamma(mode).sub(frozen_restoration(mode))
    ).add(prime_transform(mode))
    return complete.round_out(10**16)


def rat_literal(q: Q) -> str:
    return f"({q.numerator} / {q.denominator} : Rat)"


HEADER = """import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformEnclosures

/-!
# Frozen complete sine-transform table through the DF6D4 residual cutoff

This file is generated by `df6d4_lean_transform_table_generator.py`.  Its 603
exact rational intervals are evaluations of the proved analytic enclosure,
not imported floating-point or Arb claims.  The endpoint audit below makes
Lean check every table cell against the live evaluator.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

def suzukiDF6D4FullCompleteSineTransformIntervalData :
    Array RationalInterval := #[
"""

FOOTER = """]

theorem suzukiDF6D4FullCompleteSineTransformIntervalData_size :
    suzukiDF6D4FullCompleteSineTransformIntervalData.size = 603 := by
  native_decide

def suzukiDF6D4FullTabulatedCompleteSineTransformInterval
    (mode : Nat) : RationalInterval :=
  suzukiDF6D4FullCompleteSineTransformIntervalData[mode]!

set_option maxHeartbeats 0 in
theorem suzukiDF6D4FullTabulatedCompleteSineTransformInterval_endpoints
    (mode : Nat) (hmode : mode ≤ 602) :
    (suzukiDF6D4FullTabulatedCompleteSineTransformInterval mode).lower =
        (suzukiDF6D4FrozenCompleteSineTransformInterval mode).lower ∧
      (suzukiDF6D4FullTabulatedCompleteSineTransformInterval mode).upper =
        (suzukiDF6D4FrozenCompleteSineTransformInterval mode).upper := by
  interval_cases mode <;> native_decide

theorem suzukiDF6D4FullTabulatedCompleteSineTransformInterval_eq
    (mode : Nat) (hmode : mode ≤ 602) :
    suzukiDF6D4FullTabulatedCompleteSineTransformInterval mode =
      suzukiDF6D4FrozenCompleteSineTransformInterval mode := by
  cases htab : suzukiDF6D4FullTabulatedCompleteSineTransformInterval mode with
  | mk tabLower tabUpper =>
    cases hfrozen : suzukiDF6D4FrozenCompleteSineTransformInterval mode with
    | mk frozenLower frozenUpper =>
      have h :=
        suzukiDF6D4FullTabulatedCompleteSineTransformInterval_endpoints
          mode hmode
      simp only [htab, hfrozen] at h
      rcases h with ⟨hlower, hupper⟩
      cases hlower
      cases hupper
      rfl

theorem suzukiDF6D4FullTabulatedCompleteSineTransformInterval_contains
    (mode : Nat) (hmode : mode ≤ 602) :
    (suzukiDF6D4FullTabulatedCompleteSineTransformInterval mode).Contains
      (suzukiDF6D4CompleteSineTransform mode) := by
  rw [suzukiDF6D4FullTabulatedCompleteSineTransformInterval_eq mode hmode]
  exact suzukiDF6D4FrozenCompleteSineTransformInterval_contains mode hmode

end

end RiemannHypothesisProject.Experiments.M100
"""


def main() -> None:
    rows = []
    for mode in range(603):
        interval = frozen_complete_transform(mode)
        comma = "," if mode < 602 else ""
        rows.append(
            f"  ⟨{rat_literal(interval.lower)}, "
            f"{rat_literal(interval.upper)}⟩{comma}"
        )
    target = Path(
        "RiemannHypothesisProject/Experiments/M100/"
        "SuzukiEndpointCompleteSineTransformFullTable.lean"
    )
    target.write_text(HEADER + "\n".join(rows) + "\n" + FOOTER, encoding="utf-8")


if __name__ == "__main__":
    main()
