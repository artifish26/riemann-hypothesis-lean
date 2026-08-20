#!/usr/bin/env python3
"""M100-X04 finite-cutoff prime/pole/Gamma Li-kernel audit.

This probe mirrors ``LiCriterion.CutoffCovariance``.  It keeps the endpoint
counterterm and finite von Mangoldt sum at one natural cutoff, adds the
classical rational-pole and Archimedean coefficients, and forms the Lagarias
kernel ``K(n,m)=c_n+c_m-c_|n-m|`` component by component.

All calculations are float64 diagnostics.  The matching finite-cutoff matrix
decomposition is proved exactly in the experimental Lean module
``ArithmeticCutoffKernel.lean``.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import dataclass
from typing import Sequence

from li_basis_gram_probe import (
    CoefficientSettings,
    EULER_GAMMA,
    jacobi_eigensystem,
    keiper_li_coefficients,
    li_basis_gram,
    riemann_zeta_euler_maclaurin,
)


@dataclass(frozen=True)
class EigenRange:
    minimum: float
    maximum: float
    negative_count: int
    positive_count: int
    near_zero_count: int


def parse_int_list(value: str) -> list[int]:
    try:
        result = [int(item.strip()) for item in value.split(",") if item.strip()]
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a comma-separated integer list") from error
    if not result:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return result


def von_mangoldt_table(maximum: int) -> list[float]:
    is_prime = bytearray(b"\x01") * (maximum + 1)
    if maximum >= 0:
        is_prime[0] = 0
    if maximum >= 1:
        is_prime[1] = 0
    for candidate in range(2, math.isqrt(maximum) + 1):
        if is_prime[candidate]:
            start = candidate * candidate
            count = (maximum - start) // candidate + 1
            is_prime[start : maximum + 1 : candidate] = b"\x00" * count
    values = [0.0] * (maximum + 1)
    for prime in range(2, maximum + 1):
        if not is_prime[prime]:
            continue
        logarithm = math.log(prime)
        power = prime
        while power <= maximum:
            values[power] = logarithm
            if power > maximum // prime:
                break
            power *= prime
    return values


def prime_moment_snapshots(
    maximum_moment: int,
    cutoffs: Sequence[int],
) -> dict[int, list[float]]:
    maximum_cutoff = max(cutoffs)
    mangoldt = von_mangoldt_table(maximum_cutoff)
    cumulative = [0.0] * (maximum_moment + 1)
    snapshots: dict[int, list[float]] = {}
    requested = set(cutoffs)
    for number in range(1, maximum_cutoff + 1):
        weight = mangoldt[number]
        if weight != 0.0:
            logarithm = math.log(number)
            power = 1.0
            scaled_weight = weight / number
            for moment in range(maximum_moment + 1):
                cumulative[moment] += scaled_weight * power
                power *= logarithm
        if number in requested:
            snapshots[number] = list(cumulative)
    return snapshots


def li_moment_weight(index: int, moment: int) -> float:
    return (
        (-1.0) ** moment
        * math.comb(index, moment + 1)
        / math.factorial(moment)
    )


def endpoint_coefficient(index: int, cutoff: int) -> float:
    logarithm = math.log(cutoff)
    return sum(
        li_moment_weight(index, moment)
        * logarithm ** (moment + 1)
        / (moment + 1)
        for moment in range(index)
    )


def finite_prime_coefficient(
    index: int,
    moment_cutoffs: Sequence[float],
) -> float:
    return sum(
        li_moment_weight(index, moment) * moment_cutoffs[moment]
        for moment in range(index)
    )


def prime_moment_remainders(
    maximum_moment: int,
    cutoff: int,
    moment_cutoffs: Sequence[float],
) -> list[float]:
    logarithm = math.log(cutoff)
    return [
        moment_cutoffs[moment]
        - logarithm ** (moment + 1) / (moment + 1)
        for moment in range(maximum_moment + 1)
    ]


def covariance_coefficient_from_remainders(
    index: int,
    remainders: Sequence[float],
) -> float:
    return -sum(
        li_moment_weight(index, moment) * remainders[moment]
        for moment in range(index)
    )


def archimedean_coefficients(maximum_index: int) -> tuple[list[float], list[float]]:
    """Return the rational-pole and Gamma/pi coefficient sequences."""

    pole = [0.0] + [1.0] * maximum_index
    gamma = [0.0]
    zeta_settings = CoefficientSettings(0.65, 1024, 64, 12)
    zeta_values = {
        index: riemann_zeta_euler_maclaurin(
            complex(index, 0.0),
            zeta_settings.zeta_cutoff,
            zeta_settings.zeta_terms,
        ).real
        for index in range(2, maximum_index + 1)
    }
    for index in range(1, maximum_index + 1):
        value = -0.5 * index * (EULER_GAMMA + math.log(4.0 * math.pi))
        value += sum(
            (-1.0) ** order
            * math.comb(index, order)
            * (1.0 - 2.0 ** (-order))
            * zeta_values[order]
            for order in range(2, index + 1)
        )
        gamma.append(value)
    return pole, gamma


def eigen_range(matrix: Sequence[Sequence[float]], sign_tolerance: float) -> EigenRange:
    eigenvalues, _vectors, _sweeps, _residual = jacobi_eigensystem(
        matrix,
        1.0e-14,
        100,
    )
    return EigenRange(
        minimum=eigenvalues[0],
        maximum=eigenvalues[-1],
        negative_count=sum(value < -sign_tolerance for value in eigenvalues),
        positive_count=sum(value > sign_tolerance for value in eigenvalues),
        near_zero_count=sum(abs(value) <= sign_tolerance for value in eigenvalues),
    )


def matrix_maximum_recombination_error(
    total: Sequence[Sequence[float]],
    components: Sequence[Sequence[Sequence[float]]],
) -> float:
    return max(
        abs(
            total[row][column]
            - sum(component[row][column] for component in components)
        )
        for row in range(len(total))
        for column in range(len(total))
    )


def inverse_mellin_polynomial(index: int, logarithm: float) -> float:
    return sum(
        math.comb(index, degree + 1)
        * logarithm**degree
        / math.factorial(degree)
        for degree in range(index)
    )


def finite_prime_atom_coefficients(
    prime_power: int,
    mangoldt_weight: float,
    maximum_index: int,
) -> list[float]:
    logarithm = -math.log(prime_power)
    scale = mangoldt_weight / prime_power
    return [0.0] + [
        scale * inverse_mellin_polynomial(index, logarithm)
        for index in range(1, maximum_index + 1)
    ]


def run_probe(args: argparse.Namespace) -> dict[str, object]:
    maximum_dimension = max(args.dimensions)
    maximum_cutoff = max(args.cutoffs)
    snapshots = prime_moment_snapshots(maximum_dimension - 1, args.cutoffs)
    pole, gamma = archimedean_coefficients(maximum_dimension)
    actual_settings = CoefficientSettings(0.65, 1024, 64, 12)
    actual = keiper_li_coefficients(maximum_dimension, actual_settings).coefficients
    cutoff_results = []
    for cutoff in args.cutoffs:
        moment_cutoffs = snapshots[cutoff]
        remainders = prime_moment_remainders(
            maximum_dimension - 1,
            cutoff,
            moment_cutoffs,
        )
        endpoint = [0.0] + [
            endpoint_coefficient(index, cutoff)
            for index in range(1, maximum_dimension + 1)
        ]
        finite_prime = [0.0] + [
            finite_prime_coefficient(index, moment_cutoffs)
            for index in range(1, maximum_dimension + 1)
        ]
        covariance_direct = [
            endpoint[index] - finite_prime[index]
            for index in range(maximum_dimension + 1)
        ]
        covariance_moments = [0.0] + [
            covariance_coefficient_from_remainders(index, remainders)
            for index in range(1, maximum_dimension + 1)
        ]
        total = [
            covariance_direct[index] + pole[index] + gamma[index]
            for index in range(maximum_dimension + 1)
        ]
        dimension_results = []
        for dimension in args.dimensions:
            endpoint_matrix = li_basis_gram(endpoint, dimension)
            negative_prime_matrix = li_basis_gram(
                [-value for value in finite_prime],
                dimension,
            )
            covariance_matrix = li_basis_gram(covariance_direct, dimension)
            pole_matrix = li_basis_gram(pole, dimension)
            gamma_matrix = li_basis_gram(gamma, dimension)
            total_matrix = li_basis_gram(total, dimension)
            dimension_results.append({
                "dimension": dimension,
                "endpoint": vars(eigen_range(endpoint_matrix, args.sign_tolerance)),
                "negative_finite_prime": vars(
                    eigen_range(negative_prime_matrix, args.sign_tolerance)
                ),
                "covariance": vars(
                    eigen_range(covariance_matrix, args.sign_tolerance)
                ),
                "pole": vars(eigen_range(pole_matrix, args.sign_tolerance)),
                "gamma": vars(eigen_range(gamma_matrix, args.sign_tolerance)),
                "total": vars(eigen_range(total_matrix, args.sign_tolerance)),
                "maximum_component_recombination_error": (
                    matrix_maximum_recombination_error(
                        total_matrix,
                        [
                            covariance_matrix,
                            pole_matrix,
                            gamma_matrix,
                        ],
                    )
                ),
            })
        coefficient_error = max(
            abs(total[index] - actual[index])
            for index in range(1, maximum_dimension + 1)
        )
        cutoff_results.append({
            "cutoff": cutoff,
            "maximum_covariance_identity_error": max(
                abs(left - right)
                for left, right in zip(covariance_direct, covariance_moments)
            ),
            "maximum_actual_li_coefficient_error": coefficient_error,
            "coefficients": {
                "endpoint": endpoint,
                "finite_prime": finite_prime,
                "covariance": covariance_direct,
                "pole": pole,
                "gamma": gamma,
                "total": total,
                "actual": actual,
            },
            "sections": dimension_results,
        })
    mangoldt = von_mangoldt_table(maximum_cutoff)
    atom_results = []
    for prime_power in args.prime_powers:
        weight = mangoldt[prime_power]
        coefficients = finite_prime_atom_coefficients(
            prime_power,
            weight,
            maximum_dimension,
        )
        matrix = li_basis_gram(coefficients, maximum_dimension)
        atom_results.append({
            "prime_power": prime_power,
            "von_mangoldt": weight,
            "finite_prime_atom": vars(eigen_range(matrix, args.sign_tolerance)),
            "negative_covariance_atom": vars(
                eigen_range(
                    [[-value for value in row] for row in matrix],
                    args.sign_tolerance,
                )
            ),
        })
    maximum_covariance_error = max(
        result["maximum_covariance_identity_error"]
        for result in cutoff_results
    )
    maximum_recombination_error = max(
        section["maximum_component_recombination_error"]
        for result in cutoff_results
        for section in result["sections"]
    )
    all_atoms_indefinite = all(
        result["finite_prime_atom"]["negative_count"] > 0
        and result["finite_prime_atom"]["positive_count"] > 0
        for result in atom_results
        if result["von_mangoldt"] > 0.0
    )
    passed = (
        maximum_covariance_error <= args.identity_tolerance
        and maximum_recombination_error <= args.identity_tolerance
        and actual[1] > 0.0
        and all(result["von_mangoldt"] > 0.0 for result in atom_results)
    )
    return {
        "id": "M100-X04",
        "status": "PROMOTABLE",
        "hardness": "PARTIAL",
        "arithmetic": "Python float64 plus exact experimental Lean algebra",
        "cutoffs": args.cutoffs,
        "dimensions": args.dimensions,
        "prime_powers": args.prime_powers,
        "coefficient_split": (
            "endpoint - finite_prime + rational_pole + gamma_pi"
        ),
        "cutoff_results": cutoff_results,
        "prime_power_atom_results": atom_results,
        "maximum_covariance_identity_error": maximum_covariance_error,
        "maximum_component_recombination_error": maximum_recombination_error,
        "all_tested_finite_prime_atoms_indefinite": all_atoms_indefinite,
        "passed": passed,
        "decision": (
            "retain the exact common-cutoff component kernel; reject naive "
            "termwise prime-power PSD and require a cross-component completion "
            "of squares with the actual Archimedean normalization visible"
        ),
    }


def format_number(value: float) -> str:
    return f"{value:.12e}"


def print_text_report(result: dict[str, object]) -> None:
    print("M100-X04 finite-cutoff arithmetic Li-kernel probe")
    print("warning: finite float64 diagnostics; the exact decomposition is in Lean")
    print(f"split={result['coefficient_split']}")
    print()
    print("common-cutoff sections")
    for cutoff_result in result["cutoff_results"]:
        print(
            f"  cutoff={cutoff_result['cutoff']} "
            "covariance_identity_error="
            f"{format_number(cutoff_result['maximum_covariance_identity_error'])} "
            "actual_coefficient_error="
            f"{format_number(cutoff_result['maximum_actual_li_coefficient_error'])}"
        )
        for section in cutoff_result["sections"]:
            print(
                f"    dimension={section['dimension']:2d} "
                f"endpoint_min={format_number(section['endpoint']['minimum'])} "
                "negative_prime_min="
                f"{format_number(section['negative_finite_prime']['minimum'])} "
                f"gamma_min={format_number(section['gamma']['minimum'])} "
                f"total_min={format_number(section['total']['minimum'])}"
            )
    print()
    print("finite-prime atom audit")
    for atom in result["prime_power_atom_results"]:
        spectrum = atom["finite_prime_atom"]
        print(
            f"  q={atom['prime_power']:2d} "
            f"min={format_number(spectrum['minimum'])} "
            f"max={format_number(spectrum['maximum'])} "
            f"negative={spectrum['negative_count']} "
            f"positive={spectrum['positive_count']}"
        )
    print()
    print(
        "maximum component recombination error="
        f"{format_number(result['maximum_component_recombination_error'])}"
    )
    print(
        "all tested finite-prime atoms indefinite="
        f"{result['all_tested_finite_prime_atoms_indefinite']}"
    )
    print(f"status={result['status']}")
    print(f"audit_status={'PASS' if result['passed'] else 'FAIL'}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cutoffs",
        type=parse_int_list,
        default=parse_int_list("100,1000,10000,100000"),
    )
    parser.add_argument(
        "--dimensions",
        type=parse_int_list,
        default=parse_int_list("4,8,12"),
    )
    parser.add_argument(
        "--prime-powers",
        type=parse_int_list,
        default=parse_int_list("2,3,4,5,8,9"),
    )
    parser.add_argument("--sign-tolerance", type=float, default=1.0e-9)
    parser.add_argument("--identity-tolerance", type=float, default=1.0e-5)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if any(cutoff < 2 for cutoff in args.cutoffs):
        raise SystemExit("every cutoff must be at least two")
    if any(dimension <= 0 for dimension in args.dimensions):
        raise SystemExit("every dimension must be positive")
    if any(
        prime_power < 2 or prime_power > max(args.cutoffs)
        for prime_power in args.prime_powers
    ):
        raise SystemExit("prime powers must lie between two and the largest cutoff")
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
