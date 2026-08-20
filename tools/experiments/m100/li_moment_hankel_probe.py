#!/usr/bin/env python3
"""M100-X07 positive-moment route filter for the actual zeta Li sequence.

The Li coefficients are extracted arithmetically from the completed-xi
Keiper--Li generating function using the independently audited X03 code.  No
zero table or critical-line assumption is used.  This script tests the first
Hankel log-convexity condition and finite Hankel eigenvalues for the raw
sequence and several explicitly named normalizations.

The calculation uses Python float64 with baseline/refined contour audits.  A
negative minor is a route filter, not an interval-certified theorem about the
exact Lean coefficient.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Callable, Sequence

from li_basis_gram_probe import (
    EULER_GAMMA,
    CoefficientResult,
    CoefficientSettings,
    jacobi_eigensystem,
    keiper_li_coefficients,
    numerical_audit,
)


@dataclass(frozen=True)
class HankelResult:
    family: str
    dimension: int
    first_terms: list[float]
    first_minor: float
    minimum_eigenvalue: float
    maximum_eigenvalue: float
    negative_eigenvalue_count: int
    jacobi_sweeps: int
    jacobi_residual: float


def parse_int_list(value: str) -> list[int]:
    try:
        result = [int(item.strip()) for item in value.split(",") if item.strip()]
    except ValueError as error:
        raise argparse.ArgumentTypeError(
            "expected a comma-separated integer list"
        ) from error
    if not result:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return result


def relative_difference(left: float, right: float) -> float:
    return abs(left - right) / max(1.0, abs(left), abs(right))


def hankel_matrix(moment: Sequence[float], dimension: int) -> list[list[float]]:
    return [
        [moment[row + column] for column in range(dimension)]
        for row in range(dimension)
    ]


def evaluate_hankel_family(
    family: str,
    moment: Sequence[float],
    dimensions: Sequence[int],
    eigen_tolerance: float,
    maximum_jacobi_sweeps: int,
    negative_tolerance: float,
) -> list[HankelResult]:
    first_minor = moment[0] * moment[2] - moment[1] * moment[1]
    results: list[HankelResult] = []
    for dimension in dimensions:
        matrix = hankel_matrix(moment, dimension)
        eigenvalues, _vectors, sweeps, residual = jacobi_eigensystem(
            matrix,
            eigen_tolerance,
            maximum_jacobi_sweeps,
        )
        results.append(
            HankelResult(
                family=family,
                dimension=dimension,
                first_terms=list(moment[: min(len(moment), 2 * dimension - 1)]),
                first_minor=first_minor,
                minimum_eigenvalue=eigenvalues[0],
                maximum_eigenvalue=eigenvalues[-1],
                negative_eigenvalue_count=sum(
                    value < -negative_tolerance for value in eigenvalues
                ),
                jacobi_sweeps=sweeps,
                jacobi_residual=residual,
            )
        )
    return results


def build_moment_families(
    coefficients: CoefficientResult,
    maximum_moment_index: int,
    shifts: Sequence[int],
) -> dict[str, list[float]]:
    values = coefficients.coefficients
    families: dict[str, list[float]] = {}
    for shift in shifts:
        families[f"raw_shift_{shift}"] = [
            values[index + shift]
            for index in range(maximum_moment_index + 1)
        ]
    families["keiper_lambda_over_n"] = [
        values[index + 1] / (index + 1)
        for index in range(maximum_moment_index + 1)
    ]
    families["lambda_over_n_squared"] = [
        values[index + 1] / ((index + 1) ** 2)
        for index in range(maximum_moment_index + 1)
    ]
    families["first_increment"] = [
        values[index + 1] - values[index]
        for index in range(maximum_moment_index + 1)
    ]
    return families


def evaluate_all_families(
    families: dict[str, list[float]],
    dimensions: Sequence[int],
    args: argparse.Namespace,
) -> list[HankelResult]:
    return [
        result
        for family, moment in families.items()
        for result in evaluate_hankel_family(
            family,
            moment,
            dimensions,
            args.eigen_tolerance,
            args.maximum_jacobi_sweeps,
            args.negative_tolerance,
        )
    ]


def result_key(result: HankelResult) -> tuple[str, int]:
    return result.family, result.dimension


def compare_results(
    baseline: Sequence[HankelResult],
    refined: Sequence[HankelResult],
) -> dict[str, object]:
    baseline_by_key = {result_key(result): result for result in baseline}
    comparisons: list[dict[str, object]] = []
    for result in refined:
        first = baseline_by_key[result_key(result)]
        comparisons.append(
            {
                "family": result.family,
                "dimension": result.dimension,
                "first_minor_relative_delta": relative_difference(
                    first.first_minor,
                    result.first_minor,
                ),
                "minimum_eigenvalue_relative_delta": relative_difference(
                    first.minimum_eigenvalue,
                    result.minimum_eigenvalue,
                ),
                "minimum_eigenvalue_sign_stable": (
                    (first.minimum_eigenvalue < 0.0)
                    == (result.minimum_eigenvalue < 0.0)
                ),
            }
        )
    return {
        "maximum_first_minor_relative_delta": max(
            item["first_minor_relative_delta"] for item in comparisons
        ),
        "maximum_minimum_eigenvalue_relative_delta": max(
            item["minimum_eigenvalue_relative_delta"] for item in comparisons
        ),
        "all_minimum_eigenvalue_signs_stable": all(
            item["minimum_eigenvalue_sign_stable"] for item in comparisons
        ),
        "comparisons": comparisons,
    }


def positive_control_results(
    dimensions: Sequence[int],
    args: argparse.Namespace,
) -> list[HankelResult]:
    maximum_moment_index = 2 * max(dimensions) - 2
    hilbert_moments = [
        1.0 / (index + 1) for index in range(maximum_moment_index + 1)
    ]
    two_atom_moments = [
        0.4 * (0.2**index) + 0.6 * (0.8**index)
        for index in range(maximum_moment_index + 1)
    ]
    return [
        *evaluate_hankel_family(
            "uniform_measure_on_unit_interval",
            hilbert_moments,
            dimensions,
            args.eigen_tolerance,
            args.maximum_jacobi_sweeps,
            args.negative_tolerance,
        ),
        *evaluate_hankel_family(
            "two_positive_atoms",
            two_atom_moments,
            dimensions,
            args.eigen_tolerance,
            args.maximum_jacobi_sweeps,
            args.negative_tolerance,
        ),
    ]


def run_probe(args: argparse.Namespace) -> dict[str, object]:
    maximum_moment_index = 2 * max(args.dimensions) - 2
    maximum_coefficient_index = max(
        maximum_moment_index + max(args.shifts),
        maximum_moment_index + 1,
    )
    baseline_settings = CoefficientSettings(
        radius=args.baseline_radius,
        contour_samples=args.baseline_samples,
        zeta_cutoff=args.baseline_zeta_cutoff,
        zeta_terms=args.baseline_zeta_terms,
    )
    refined_settings = CoefficientSettings(
        radius=args.refined_radius,
        contour_samples=args.refined_samples,
        zeta_cutoff=args.refined_zeta_cutoff,
        zeta_terms=args.refined_zeta_terms,
    )
    baseline_coefficients = keiper_li_coefficients(
        maximum_coefficient_index,
        baseline_settings,
    )
    refined_coefficients = keiper_li_coefficients(
        maximum_coefficient_index,
        refined_settings,
    )
    baseline_families = build_moment_families(
        baseline_coefficients,
        maximum_moment_index,
        args.shifts,
    )
    refined_families = build_moment_families(
        refined_coefficients,
        maximum_moment_index,
        args.shifts,
    )
    baseline_results = evaluate_all_families(
        baseline_families,
        args.dimensions,
        args,
    )
    refined_results = evaluate_all_families(
        refined_families,
        args.dimensions,
        args,
    )
    comparison = compare_results(baseline_results, refined_results)
    controls = positive_control_results(args.dimensions, args)
    audit = numerical_audit(refined_settings)
    exact_lambda_one = (
        1.0 + 0.5 * EULER_GAMMA - 0.5 * math.log(4.0 * math.pi)
    )
    maximum_coefficient_delta = max(
        relative_difference(left, right)
        for left, right in zip(
            baseline_coefficients.coefficients[1:],
            refined_coefficients.coefficients[1:],
        )
    )
    first_results = {
        result.family: result
        for result in refined_results
        if result.dimension == min(args.dimensions)
    }
    required_negative_families = (
        "raw_shift_1",
        "keiper_lambda_over_n",
        "lambda_over_n_squared",
        "first_increment",
    )
    stable_required_negatives = all(
        first_results[family].first_minor < -args.negative_tolerance
        for family in required_negative_families
    )
    control_minimum = min(result.minimum_eigenvalue for result in controls)
    audits_passed = (
        abs(refined_coefficients.coefficients[1] - exact_lambda_one)
        <= args.lambda_one_tolerance
        and maximum_coefficient_delta <= args.coefficient_tolerance
        and refined_coefficients.maximum_imaginary_leakage
        <= args.imaginary_tolerance
        and refined_coefficients.logarithm_closure_error
        <= args.logarithm_closure_tolerance
        and audit["zeta_two_error"] <= args.special_value_tolerance
        and audit["zeta_zero_error"] <= args.special_value_tolerance
        and audit["xi_functional_symmetry_error"]
        <= args.functional_symmetry_tolerance
        and comparison["maximum_first_minor_relative_delta"]
        <= args.refinement_tolerance
        and stable_required_negatives
        and control_minimum >= -args.negative_tolerance
    )
    return {
        "id": "M100-X07",
        "status": "REFUTED",
        "hardness": "RH_HARD",
        "scope": (
            "raw shifted Li coefficients and the explicitly tested Keiper, "
            "n-squared, and first-increment positive-moment candidates"
        ),
        "arithmetic": "Python float64",
        "coefficient_identity": (
            "log(2*xi(1/(1-z))) = sum(lambda_n*z^n/n, n>=1)"
        ),
        "baseline_settings": asdict(baseline_settings),
        "refined_settings": asdict(refined_settings),
        "dimensions": args.dimensions,
        "shifts": args.shifts,
        "exact_lambda_one": exact_lambda_one,
        "baseline_coefficient_result": asdict(baseline_coefficients),
        "refined_coefficient_result": asdict(refined_coefficients),
        "maximum_coefficient_relative_delta": maximum_coefficient_delta,
        "numerical_audit": audit,
        "baseline_results": [asdict(result) for result in baseline_results],
        "refined_results": [asdict(result) for result in refined_results],
        "refinement_audit": comparison,
        "positive_measure_controls": [asdict(result) for result in controls],
        "required_negative_families": list(required_negative_families),
        "passed": audits_passed,
        "decision": (
            "reject direct positive Hamburger/Stieltjes moment models for the "
            "raw Li sequence and the tested elementary normalizations; require "
            "a nontrivial arithmetic transform with its positivity proved "
            "before revisiting the moment lane"
        ),
    }


def format_number(value: float) -> str:
    return f"{value:.12e}"


def print_text_report(result: dict[str, object]) -> None:
    baseline = result["baseline_settings"]
    refined = result["refined_settings"]
    coefficients = result["refined_coefficient_result"]
    audit = result["numerical_audit"]
    comparison = result["refinement_audit"]
    print("M100-X07 actual-zeta Li moment Hankel probe")
    print("warning: float64 route filter; exact negative minors are not certified")
    print(
        "baseline="
        f"radius:{baseline['radius']:g} samples:{baseline['contour_samples']} "
        f"zeta_cutoff:{baseline['zeta_cutoff']} terms:{baseline['zeta_terms']}"
    )
    print(
        "refined="
        f"radius:{refined['radius']:g} samples:{refined['contour_samples']} "
        f"zeta_cutoff:{refined['zeta_cutoff']} terms:{refined['zeta_terms']}"
    )
    print()
    print("coefficient audits")
    print(
        f"  lambda_1={format_number(coefficients['coefficients'][1])} "
        f"exact={format_number(result['exact_lambda_one'])}"
    )
    print(
        "  max baseline/refined coefficient delta="
        f"{format_number(result['maximum_coefficient_relative_delta'])}"
    )
    print(
        "  max imaginary leakage="
        f"{format_number(coefficients['maximum_imaginary_leakage'])}"
    )
    print(
        f"  zeta(2) error={format_number(audit['zeta_two_error'])} "
        f"xi symmetry error={format_number(audit['xi_functional_symmetry_error'])}"
    )
    print(
        "  max first-minor refinement delta="
        f"{format_number(comparison['maximum_first_minor_relative_delta'])}"
    )
    print()
    print("first Hankel minors and smallest tested eigenvalues")
    for item in result["refined_results"]:
        if item["dimension"] != min(result["dimensions"]):
            continue
        family_results = [
            candidate
            for candidate in result["refined_results"]
            if candidate["family"] == item["family"]
        ]
        minimum = min(
            candidate["minimum_eigenvalue"] for candidate in family_results
        )
        print(
            f"  {item['family']}: "
            f"m0={format_number(item['first_terms'][0])} "
            f"m1={format_number(item['first_terms'][1])} "
            f"m2={format_number(item['first_terms'][2])} "
            f"minor={format_number(item['first_minor'])} "
            f"min_eigen={format_number(minimum)}"
        )
    print()
    control_minimum = min(
        item["minimum_eigenvalue"] for item in result["positive_measure_controls"]
    )
    print(
        "positive-measure control minimum eigenvalue="
        f"{format_number(control_minimum)}"
    )
    print(f"status={result['status']}")
    print(f"audit_status={'PASS' if result['passed'] else 'FAIL'}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dimensions",
        type=parse_int_list,
        default=parse_int_list("2,3,4,6"),
    )
    parser.add_argument(
        "--shifts",
        type=parse_int_list,
        default=parse_int_list("1,2,3,4"),
    )
    parser.add_argument("--baseline-radius", type=float, default=0.55)
    parser.add_argument("--baseline-samples", type=int, default=256)
    parser.add_argument("--baseline-zeta-cutoff", type=int, default=32)
    parser.add_argument("--baseline-zeta-terms", type=int, default=8)
    parser.add_argument("--refined-radius", type=float, default=0.65)
    parser.add_argument("--refined-samples", type=int, default=1024)
    parser.add_argument("--refined-zeta-cutoff", type=int, default=64)
    parser.add_argument("--refined-zeta-terms", type=int, default=12)
    parser.add_argument("--eigen-tolerance", type=float, default=1.0e-14)
    parser.add_argument("--maximum-jacobi-sweeps", type=int, default=100)
    parser.add_argument("--negative-tolerance", type=float, default=1.0e-8)
    parser.add_argument("--lambda-one-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--coefficient-tolerance", type=float, default=2.0e-8)
    parser.add_argument("--imaginary-tolerance", type=float, default=1.0e-8)
    parser.add_argument("--logarithm-closure-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--special-value-tolerance", type=float, default=1.0e-11)
    parser.add_argument("--functional-symmetry-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--refinement-tolerance", type=float, default=1.0e-8)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if any(dimension < 2 for dimension in args.dimensions):
        raise SystemExit("every Hankel dimension must be at least two")
    if any(shift < 1 for shift in args.shifts):
        raise SystemExit("every raw Li shift must be positive")
    if args.baseline_samples <= 4 * max(args.dimensions):
        raise SystemExit("baseline contour resolution is too small")
    if args.refined_samples <= 4 * max(args.dimensions):
        raise SystemExit("refined contour resolution is too small")
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
