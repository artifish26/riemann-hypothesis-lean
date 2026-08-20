#!/usr/bin/env python3
"""M100-X00 symmetry-preserving synthetic zero route filter.

This probe constructs finite zero multisets closed under conjugation and the
functional reflection ``rho -> 1 - rho``.  It evaluates multiplicity-aware Li
coefficients in the same positive-ordinate/conjugate-paired convention used by
the Lean project and forms the corresponding finite Lagarias Li-basis Gram
matrix.

The models are synthetic and are not zeta zero data.  A negative coefficient
or Gram diagonal is a counterexample to a symmetry-only positivity mechanism,
not evidence about the Riemann hypothesis.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from decimal import Decimal, getcontext, localcontext
from typing import Iterable, Sequence


ZERO = Decimal(0)
ONE = Decimal(1)
TWO = Decimal(2)


@dataclass(frozen=True)
class DecimalComplex:
    """The small subset of complex arithmetic needed by the Li summand."""

    real: Decimal
    imag: Decimal

    def __add__(self, other: DecimalComplex) -> DecimalComplex:
        return DecimalComplex(self.real + other.real, self.imag + other.imag)

    def __sub__(self, other: DecimalComplex) -> DecimalComplex:
        return DecimalComplex(self.real - other.real, self.imag - other.imag)

    def __mul__(self, other: DecimalComplex) -> DecimalComplex:
        return DecimalComplex(
            self.real * other.real - self.imag * other.imag,
            self.real * other.imag + self.imag * other.real,
        )

    def __truediv__(self, other: DecimalComplex) -> DecimalComplex:
        denominator = other.real * other.real + other.imag * other.imag
        if denominator == ZERO:
            raise ZeroDivisionError("division by the zero synthetic root")
        return DecimalComplex(
            (self.real * other.real + self.imag * other.imag) / denominator,
            (self.imag * other.real - self.real * other.imag) / denominator,
        )

    def conjugate(self) -> DecimalComplex:
        return DecimalComplex(self.real, -self.imag)

    def functional_reflection(self) -> DecimalComplex:
        return DecimalComplex(ONE - self.real, -self.imag)

    def pow_nat(self, exponent: int) -> DecimalComplex:
        if exponent < 0:
            raise ValueError("pow_nat requires a nonnegative exponent")
        result = DecimalComplex(ONE, ZERO)
        base = self
        remaining = exponent
        while remaining:
            if remaining & 1:
                result = result * base
            base = base * base
            remaining //= 2
        return result


COMPLEX_ONE = DecimalComplex(ONE, ZERO)


@dataclass(frozen=True)
class WeightedPositiveZero:
    rho: DecimalComplex
    multiplicity: int
    orbit_label: str


@dataclass(frozen=True)
class SyntheticZeroOrbit:
    """One conjugation/functional-reflection orbit at positive height."""

    label: str
    beta: Decimal
    gamma: Decimal
    multiplicity: int = 1

    def __post_init__(self) -> None:
        if not ZERO < self.beta < ONE:
            raise ValueError("beta must lie strictly between 0 and 1")
        if self.gamma <= ZERO:
            raise ValueError("gamma must be positive")
        if self.multiplicity <= 0:
            raise ValueError("multiplicity must be positive")

    def positive_representatives(self) -> tuple[WeightedPositiveZero, ...]:
        left = WeightedPositiveZero(
            DecimalComplex(self.beta, self.gamma),
            self.multiplicity,
            self.label,
        )
        if self.beta == ONE - self.beta:
            return (left,)
        right = WeightedPositiveZero(
            DecimalComplex(ONE - self.beta, self.gamma),
            self.multiplicity,
            self.label,
        )
        return (left, right)


@dataclass(frozen=True)
class SyntheticZeroModel:
    name: str
    orbits: tuple[SyntheticZeroOrbit, ...]

    def positive_representatives_in_input_order(
        self,
    ) -> tuple[WeightedPositiveZero, ...]:
        return tuple(
            representative
            for orbit in self.orbits
            for representative in orbit.positive_representatives()
        )

    def canonical_positive_representatives(
        self,
        height_cutoff: Decimal | None = None,
    ) -> tuple[WeightedPositiveZero, ...]:
        representatives = (
            representative
            for orbit in self.orbits
            if height_cutoff is None or orbit.gamma <= height_cutoff
            for representative in orbit.positive_representatives()
        )
        return tuple(
            sorted(
                representatives,
                key=lambda item: (
                    item.rho.imag,
                    item.rho.real,
                    item.orbit_label,
                ),
            )
        )

    def full_member_multiplicities(
        self,
    ) -> dict[tuple[Decimal, Decimal], int]:
        members: dict[tuple[Decimal, Decimal], int] = {}
        for representative in self.canonical_positive_representatives():
            for rho in (representative.rho, representative.rho.conjugate()):
                key = (rho.real, rho.imag)
                members[key] = members.get(key, 0) + representative.multiplicity
        return members

    def is_symmetry_closed(self) -> bool:
        members = self.full_member_multiplicities()
        for (real, imag), multiplicity in members.items():
            rho = DecimalComplex(real, imag)
            conjugate = rho.conjugate()
            reflected = rho.functional_reflection()
            if members.get((conjugate.real, conjugate.imag)) != multiplicity:
                return False
            if members.get((reflected.real, reflected.imag)) != multiplicity:
                return False
        return True

    def distinct_full_zero_count(self) -> int:
        return len(self.full_member_multiplicities())

    def multiplicity_expanded_zero_count(self) -> int:
        return sum(self.full_member_multiplicities().values())


def li_complex_summand(rho: DecimalComplex, n: int) -> DecimalComplex:
    """Return ``1 - (1 - rho^-1)^n``."""

    return COMPLEX_ONE - (COMPLEX_ONE - COMPLEX_ONE / rho).pow_nat(n)


def paired_li_real_summand(rho: DecimalComplex, n: int) -> Decimal:
    """Pair one positive root with its conjugate and take the real value."""

    return TWO * li_complex_summand(rho, n).real


def coefficient_from_representatives(
    representatives: Iterable[WeightedPositiveZero],
    n: int,
) -> Decimal:
    value = ZERO
    for representative in representatives:
        value += Decimal(representative.multiplicity) * paired_li_real_summand(
            representative.rho,
            n,
        )
    return value


def li_coefficient(
    model: SyntheticZeroModel,
    n: int,
    height_cutoff: Decimal | None = None,
) -> Decimal:
    return coefficient_from_representatives(
        model.canonical_positive_representatives(height_cutoff),
        n,
    )


def li_coefficients(
    model: SyntheticZeroModel,
    n_max: int,
    height_cutoff: Decimal | None = None,
) -> list[Decimal]:
    return [
        li_coefficient(model, n, height_cutoff)
        for n in range(1, n_max + 1)
    ]


def li_basis_gram(
    coefficients: Sequence[Decimal],
    basis_size: int,
) -> list[list[Decimal]]:
    """Use ``G_nm = lambda_n + lambda_m - lambda_|n-m|``."""

    if basis_size > len(coefficients):
        raise ValueError("basis_size cannot exceed the computed coefficient range")
    lambda_with_zero = [ZERO, *coefficients]
    return [
        [
            lambda_with_zero[n]
            + lambda_with_zero[m]
            - lambda_with_zero[abs(n - m)]
            for m in range(1, basis_size + 1)
        ]
        for n in range(1, basis_size + 1)
    ]


def minimum_with_index(values: Sequence[Decimal]) -> tuple[Decimal, int]:
    minimum = min(values)
    return minimum, values.index(minimum) + 1


def maximum_gram_symmetry_error(matrix: Sequence[Sequence[Decimal]]) -> Decimal:
    return max(
        abs(matrix[i][j] - matrix[j][i])
        for i in range(len(matrix))
        for j in range(len(matrix))
    )


def decimal_close(left: Decimal, right: Decimal, tolerance: Decimal) -> bool:
    scale = max(ONE, abs(left), abs(right))
    return abs(left - right) <= tolerance * scale


def build_models() -> dict[str, SyntheticZeroModel]:
    critical = SyntheticZeroModel(
        "critical_line_pair",
        (SyntheticZeroOrbit("critical-5", Decimal("0.5"), Decimal("5")),),
    )
    off_line = SyntheticZeroModel(
        "off_line_quartet",
        (SyntheticZeroOrbit("off-line-5", Decimal("0.7"), Decimal("5")),),
    )
    off_line_triple = SyntheticZeroModel(
        "off_line_quartet_multiplicity_three",
        (
            SyntheticZeroOrbit(
                "off-line-5-m3",
                Decimal("0.7"),
                Decimal("5"),
                multiplicity=3,
            ),
        ),
    )
    ordering = SyntheticZeroModel(
        "ordering_adversary",
        (
            SyntheticZeroOrbit(
                "critical-3-m2",
                Decimal("0.5"),
                Decimal("3"),
                multiplicity=2,
            ),
            SyntheticZeroOrbit("off-line-5", Decimal("0.7"), Decimal("5")),
            SyntheticZeroOrbit("critical-9", Decimal("0.5"), Decimal("9")),
        ),
    )
    promotion = SyntheticZeroModel(
        "finite_window_promotion_adversary",
        (
            SyntheticZeroOrbit("critical-3", Decimal("0.5"), Decimal("3")),
            SyntheticZeroOrbit(
                "off-line-5-m8",
                Decimal("0.7"),
                Decimal("5"),
                multiplicity=8,
            ),
        ),
    )
    return {
        model.name: model
        for model in (
            critical,
            off_line,
            off_line_triple,
            ordering,
            promotion,
        )
    }


def evaluate_model(
    model: SyntheticZeroModel,
    n_max: int,
    gram_basis: int,
    height_cutoff: Decimal | None = None,
) -> dict[str, object]:
    coefficients = li_coefficients(model, n_max, height_cutoff)
    minimum, minimum_n = minimum_with_index(coefficients)
    gram = li_basis_gram(coefficients, gram_basis)
    diagonal = [gram[index][index] for index in range(gram_basis)]
    minimum_diagonal, minimum_diagonal_n = minimum_with_index(diagonal)
    return {
        "coefficients": coefficients,
        "minimum": minimum,
        "minimum_n": minimum_n,
        "gram_minimum_diagonal": minimum_diagonal,
        "gram_minimum_diagonal_n": minimum_diagonal_n,
        "gram_symmetry_error": maximum_gram_symmetry_error(gram),
    }


def evaluate_off_line_minimum(n_max: int, precision: int) -> tuple[Decimal, int]:
    with localcontext() as context:
        context.prec = precision
        model = build_models()["off_line_quartet"]
        return minimum_with_index(li_coefficients(model, n_max))


def run_probe(precision: int, verification_precision: int, n_max: int, gram_basis: int) -> dict[str, object]:
    tolerance = Decimal(1).scaleb(-(precision - 20))
    models = build_models()
    critical = models["critical_line_pair"]
    off_line = models["off_line_quartet"]
    off_line_triple = models["off_line_quartet_multiplicity_three"]
    ordering = models["ordering_adversary"]
    promotion = models["finite_window_promotion_adversary"]

    critical_result = evaluate_model(critical, n_max, gram_basis)
    off_line_result = evaluate_model(off_line, n_max, gram_basis)

    symmetry_closed = all(model.is_symmetry_closed() for model in models.values())

    base_coefficients = off_line_result["coefficients"]
    triple_coefficients = li_coefficients(off_line_triple, n_max)
    multiplicity_scaling = all(
        decimal_close(triple, Decimal(3) * base, tolerance)
        for base, triple in zip(base_coefficients, triple_coefficients)
    )

    reversed_ordering = SyntheticZeroModel(
        "ordering_adversary_reversed",
        tuple(reversed(ordering.orbits)),
    )
    cutoffs = (Decimal("4"), Decimal("6"), Decimal("10"))
    canonical_order_invariant = all(
        li_coefficients(ordering, n_max, cutoff)
        == li_coefficients(reversed_ordering, n_max, cutoff)
        for cutoff in cutoffs
    )

    unsafe_prefix_n = min(32, n_max)
    unsafe_prefix_forward = coefficient_from_representatives(
        ordering.positive_representatives_in_input_order()[:1],
        unsafe_prefix_n,
    )
    unsafe_prefix_reversed = coefficient_from_representatives(
        reversed_ordering.positive_representatives_in_input_order()[:1],
        unsafe_prefix_n,
    )
    unsafe_prefix_order_dependent = not decimal_close(
        unsafe_prefix_forward,
        unsafe_prefix_reversed,
        tolerance,
    )

    low_window = li_coefficients(promotion, n_max, Decimal("4"))
    full_window = li_coefficients(promotion, n_max, Decimal("6"))
    low_window_minimum, low_window_minimum_n = minimum_with_index(low_window)
    full_window_minimum, full_window_minimum_n = minimum_with_index(full_window)
    finite_window_promotion_trap = (
        low_window_minimum >= ZERO and full_window_minimum < ZERO
    )

    low_precision_minimum, low_precision_n = evaluate_off_line_minimum(
        n_max,
        precision,
    )
    high_precision_minimum, high_precision_n = evaluate_off_line_minimum(
        n_max,
        verification_precision,
    )
    precision_delta = abs(low_precision_minimum - high_precision_minimum)
    precision_stable = (
        low_precision_n == high_precision_n
        and decimal_close(
            low_precision_minimum,
            high_precision_minimum,
            tolerance,
        )
    )

    off_line_negative = off_line_result["minimum"] < ZERO
    negative_gram_witness = off_line_result["gram_minimum_diagonal"] < ZERO
    critical_nonnegative_in_range = critical_result["minimum"] >= ZERO
    gram_symmetric = (
        critical_result["gram_symmetry_error"] == ZERO
        and off_line_result["gram_symmetry_error"] == ZERO
    )

    audits = {
        "symmetry_closure": symmetry_closed,
        "multiplicity_scaling": multiplicity_scaling,
        "canonical_height_order_invariance": canonical_order_invariant,
        "unsafe_prefix_order_dependence_observed": unsafe_prefix_order_dependent,
        "finite_window_promotion_trap_observed": finite_window_promotion_trap,
        "precision_stability": precision_stable,
        "gram_symmetry": gram_symmetric,
        "critical_control_nonnegative_in_test_range": critical_nonnegative_in_range,
        "off_line_negative_li_coefficient": off_line_negative,
        "off_line_negative_gram_diagonal": negative_gram_witness,
    }
    passed = all(audits.values())

    return {
        "id": "M100-X00",
        "status": "REFUTED" if passed else "INCONCLUSIVE",
        "refuted_mechanism": "symmetry-only global Li/Weil positivity",
        "arithmetic": "Python Decimal",
        "parameters": {
            "precision": precision,
            "verification_precision": verification_precision,
            "n_max": n_max,
            "gram_basis": gram_basis,
            "canonical_cutoffs": [str(cutoff) for cutoff in cutoffs],
        },
        "critical_control": {
            "distinct_full_zeroes": critical.distinct_full_zero_count(),
            "multiplicity_expanded_zeroes": critical.multiplicity_expanded_zero_count(),
            "minimum_li_coefficient": critical_result["minimum"],
            "minimum_li_index": critical_result["minimum_n"],
            "minimum_gram_diagonal": critical_result["gram_minimum_diagonal"],
            "minimum_gram_diagonal_index": critical_result[
                "gram_minimum_diagonal_n"
            ],
        },
        "off_line_countermodel": {
            "distinct_full_zeroes": off_line.distinct_full_zero_count(),
            "multiplicity_expanded_zeroes": off_line.multiplicity_expanded_zero_count(),
            "minimum_li_coefficient": off_line_result["minimum"],
            "minimum_li_index": off_line_result["minimum_n"],
            "minimum_gram_diagonal": off_line_result["gram_minimum_diagonal"],
            "minimum_gram_diagonal_index": off_line_result[
                "gram_minimum_diagonal_n"
            ],
        },
        "ordering_audit": {
            "unsafe_prefix_index": unsafe_prefix_n,
            "forward_first_prefix": unsafe_prefix_forward,
            "reversed_first_prefix": unsafe_prefix_reversed,
        },
        "finite_window_audit": {
            "height_4_minimum": low_window_minimum,
            "height_4_minimum_index": low_window_minimum_n,
            "height_6_minimum": full_window_minimum,
            "height_6_minimum_index": full_window_minimum_n,
        },
        "precision_audit": {
            "low_precision_minimum": low_precision_minimum,
            "low_precision_index": low_precision_n,
            "high_precision_minimum": high_precision_minimum,
            "high_precision_index": high_precision_n,
            "absolute_delta": precision_delta,
            "relative_tolerance": tolerance,
        },
        "audits": audits,
        "decision": (
            "reject any positivity argument using only the tested symmetries, "
            "multiplicity bookkeeping, and canonical height truncation"
            if passed
            else "do not draw a route decision until the failed audits are repaired"
        ),
        "passed": passed,
    }


def serializable(value: object) -> object:
    if isinstance(value, Decimal):
        return str(value)
    if isinstance(value, dict):
        return {key: serializable(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [serializable(item) for item in value]
    return value


def format_decimal(value: Decimal) -> str:
    return f"{value:.18E}"


def print_text_report(result: dict[str, object]) -> None:
    parameters = result["parameters"]
    critical = result["critical_control"]
    off_line = result["off_line_countermodel"]
    ordering = result["ordering_audit"]
    finite_window = result["finite_window_audit"]
    precision = result["precision_audit"]
    audits = result["audits"]

    print("M100-X00 symmetry-preserving synthetic zero probe")
    print("warning: synthetic finite model; this is not zeta zero data or RH evidence")
    print(
        f"arithmetic=Decimal precision={parameters['precision']} "
        f"verification_precision={parameters['verification_precision']} "
        f"n_max={parameters['n_max']} gram_basis={parameters['gram_basis']}"
    )
    print()
    print("critical-line control")
    print(
        "  full_zeroes="
        f"{critical['distinct_full_zeroes']} "
        f"expanded={critical['multiplicity_expanded_zeroes']}"
    )
    print(
        "  min_lambda="
        f"{format_decimal(critical['minimum_li_coefficient'])} "
        f"at n={critical['minimum_li_index']}"
    )
    print(
        "  min_gram_diagonal="
        f"{format_decimal(critical['minimum_gram_diagonal'])} "
        f"at basis n={critical['minimum_gram_diagonal_index']}"
    )
    print()
    print("off-line quartet countermodel beta=0.7 gamma=5")
    print(
        "  full_zeroes="
        f"{off_line['distinct_full_zeroes']} "
        f"expanded={off_line['multiplicity_expanded_zeroes']}"
    )
    print(
        "  min_lambda="
        f"{format_decimal(off_line['minimum_li_coefficient'])} "
        f"at n={off_line['minimum_li_index']}"
    )
    print(
        "  Li-basis Gram witness: e_"
        f"{off_line['minimum_gram_diagonal_index']} has quadratic value "
        f"{format_decimal(off_line['minimum_gram_diagonal'])}"
    )
    print()
    print("adversarial truncation checks")
    print(
        "  unsafe first-prefix values at n="
        f"{ordering['unsafe_prefix_index']}: "
        f"forward={format_decimal(ordering['forward_first_prefix'])} "
        f"reversed={format_decimal(ordering['reversed_first_prefix'])}"
    )
    print(
        "  finite-window trap: "
        f"height<=4 min={format_decimal(finite_window['height_4_minimum'])} "
        f"at n={finite_window['height_4_minimum_index']}; "
        f"height<=6 min={format_decimal(finite_window['height_6_minimum'])} "
        f"at n={finite_window['height_6_minimum_index']}"
    )
    print()
    print("precision audit")
    print(
        f"  low={format_decimal(precision['low_precision_minimum'])} "
        f"high={format_decimal(precision['high_precision_minimum'])} "
        f"delta={format_decimal(precision['absolute_delta'])}"
    )
    print()
    print("audits")
    for name, passed in audits.items():
        print(f"  {name}: {'PASS' if passed else 'FAIL'}")
    print()
    print(f"status={result['status']}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--precision",
        type=int,
        default=80,
        help="Decimal precision for the reported run (default: 80)",
    )
    parser.add_argument(
        "--verification-extra-precision",
        type=int,
        default=40,
        help="extra digits used by the independent precision audit (default: 40)",
    )
    parser.add_argument(
        "--n-max",
        type=int,
        default=64,
        help="largest Li coefficient index (default: 64)",
    )
    parser.add_argument(
        "--gram-basis",
        type=int,
        default=48,
        help="Li-basis Gram dimension (default: 48)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit the complete machine-readable result",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if args.precision < 40:
        raise SystemExit("--precision must be at least 40")
    if args.verification_extra_precision < 10:
        raise SystemExit("--verification-extra-precision must be at least 10")
    if args.n_max < 32:
        raise SystemExit("--n-max must be at least 32 for the default countermodel")
    if not 32 <= args.gram_basis <= args.n_max:
        raise SystemExit("--gram-basis must lie between 32 and --n-max")

    verification_precision = args.precision + args.verification_extra_precision
    getcontext().prec = verification_precision
    with localcontext() as context:
        context.prec = args.precision
        result = run_probe(
            args.precision,
            verification_precision,
            args.n_max,
            args.gram_basis,
        )

    if args.json:
        print(json.dumps(serializable(result), indent=2, sort_keys=True))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
