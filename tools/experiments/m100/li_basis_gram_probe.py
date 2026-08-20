#!/usr/bin/env python3
"""M100-X03 numerical probe of the actual zeta Li-basis Gram matrix.

The production identity is

    K(n,m) = lambda_n + lambda_m - lambda_|n-m|,

with diagonal ``K(n,n) = 2*lambda_n``.  The coefficients are extracted from
the exact Keiper--Li generating function

    log(2*xi(1/(1-z))) = sum_{n>=1} lambda_n*z^n/n.

This is a deterministic float64 discovery calculation, not a proof of a sign.
Complete positive semidefiniteness of the actual infinite matrix is RH-hard.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import asdict, dataclass
from typing import Sequence


EULER_GAMMA = 0.5772156649015328606
LANCZOS_G = 7.0
LANCZOS_COEFFICIENTS = (
    0.99999999999980993,
    676.5203681218851,
    -1259.1392167224028,
    771.32342877765313,
    -176.61502916214059,
    12.507343278686905,
    -0.13857109526572012,
    9.9843695780195716e-6,
    1.5056327351493116e-7,
)
BERNOULLI_EVEN = (
    (1, 6),
    (-1, 30),
    (1, 42),
    (-1, 30),
    (5, 66),
    (-691, 2730),
    (7, 6),
    (-3617, 510),
    (43867, 798),
    (-174611, 330),
    (854513, 138),
    (-236364091, 2730),
)


@dataclass(frozen=True)
class CoefficientSettings:
    radius: float
    contour_samples: int
    zeta_cutoff: int
    zeta_terms: int


@dataclass(frozen=True)
class CoefficientResult:
    coefficients: list[float]
    maximum_imaginary_leakage: float
    logarithm_closure_error: float
    maximum_logarithm_phase_step: float


@dataclass(frozen=True)
class GramSectionResult:
    dimension: int
    minimum_eigenvalue: float
    maximum_eigenvalue: float
    condition_estimate: float
    jacobi_sweeps: int
    jacobi_residual: float
    minimum_direction: list[float]


def parse_int_list(value: str) -> list[int]:
    try:
        result = [int(item.strip()) for item in value.split(",") if item.strip()]
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a comma-separated integer list") from error
    if not result:
        raise argparse.ArgumentTypeError("expected at least one integer")
    return result


def complex_log_gamma(value: complex) -> complex:
    """Lanczos approximation to the principal complex log-Gamma function."""

    if value.real < 0.5:
        return (
            math.log(math.pi)
            - cmath.log(cmath.sin(math.pi * value))
            - complex_log_gamma(1.0 - value)
        )
    shifted = value - 1.0
    series = complex(LANCZOS_COEFFICIENTS[0], 0.0)
    for index, coefficient in enumerate(LANCZOS_COEFFICIENTS[1:], start=1):
        series += coefficient / (shifted + index)
    scale = shifted + LANCZOS_G + 0.5
    return (
        0.5 * math.log(2.0 * math.pi)
        + (shifted + 0.5) * cmath.log(scale)
        - scale
        + cmath.log(series)
    )


def riemann_zeta_euler_maclaurin(
    value: complex,
    cutoff: int,
    term_count: int,
) -> complex:
    """Evaluate zeta by its Euler--Maclaurin continuation away from s=1."""

    if abs(value - 1.0) < 1.0e-14:
        raise ValueError("the Euler--Maclaurin zeta evaluator excludes s=1")
    total = sum(cmath.exp(-value * math.log(index)) for index in range(1, cutoff))
    log_cutoff = math.log(cutoff)
    total += cmath.exp((1.0 - value) * log_cutoff) / (value - 1.0)
    total += 0.5 * cmath.exp(-value * log_cutoff)
    rising = complex(value)
    for order in range(1, term_count + 1):
        if order > 1:
            rising *= value + (2 * order - 3)
            rising *= value + (2 * order - 2)
        numerator, denominator = BERNOULLI_EVEN[order - 1]
        coefficient = (numerator / denominator) / math.factorial(2 * order)
        total += (
            coefficient
            * rising
            * cmath.exp(-(value + 2 * order - 1) * log_cutoff)
        )
    return total


def completed_xi(value: complex, settings: CoefficientSettings) -> complex:
    """The standard xi(s) = s(s-1) pi^(-s/2) Gamma(s/2) zeta(s) / 2."""

    zeta = riemann_zeta_euler_maclaurin(
        value,
        settings.zeta_cutoff,
        settings.zeta_terms,
    )
    gamma_factor = cmath.exp(
        complex_log_gamma(value / 2.0) - 0.5 * value * math.log(math.pi)
    )
    return 0.5 * value * (value - 1.0) * gamma_factor * zeta


def unwrap_phases(raw_phases: Sequence[float]) -> tuple[list[float], float, float]:
    phases = [raw_phases[0]]
    maximum_step = 0.0
    for raw_phase in raw_phases[1:]:
        phase = raw_phase
        while phase - phases[-1] > math.pi:
            phase -= 2.0 * math.pi
        while phase - phases[-1] < -math.pi:
            phase += 2.0 * math.pi
        maximum_step = max(maximum_step, abs(phase - phases[-1]))
        phases.append(phase)
    endpoint = raw_phases[0]
    while endpoint - phases[-1] > math.pi:
        endpoint -= 2.0 * math.pi
    while endpoint - phases[-1] < -math.pi:
        endpoint += 2.0 * math.pi
    maximum_step = max(maximum_step, abs(endpoint - phases[-1]))
    return phases, abs(endpoint - phases[0]), maximum_step


def keiper_li_coefficients(
    maximum_index: int,
    settings: CoefficientSettings,
) -> CoefficientResult:
    """Extract lambda_0 through lambda_maximum_index by a trapezoidal Cauchy sum."""

    raw_values: list[complex] = []
    raw_phases: list[float] = []
    for sample in range(settings.contour_samples):
        angle = 2.0 * math.pi * sample / settings.contour_samples
        z = settings.radius * cmath.exp(1j * angle)
        s = 1.0 / (1.0 - z)
        value = 2.0 * completed_xi(s, settings)
        raw_values.append(value)
        raw_phases.append(cmath.phase(value))
    phases, closure_error, maximum_phase_step = unwrap_phases(raw_phases)
    logarithms = [
        complex(math.log(abs(value)), phase)
        for value, phase in zip(raw_values, phases)
    ]
    coefficients = [0.0]
    maximum_imaginary_leakage = 0.0
    for index in range(1, maximum_index + 1):
        fourier_coefficient = sum(
            logarithm
            * cmath.exp(
                -2j * math.pi * index * sample / settings.contour_samples
            )
            for sample, logarithm in enumerate(logarithms)
        ) / settings.contour_samples
        li_value = index * fourier_coefficient / (settings.radius**index)
        coefficients.append(li_value.real)
        maximum_imaginary_leakage = max(
            maximum_imaginary_leakage,
            abs(li_value.imag),
        )
    return CoefficientResult(
        coefficients=coefficients,
        maximum_imaginary_leakage=maximum_imaginary_leakage,
        logarithm_closure_error=closure_error,
        maximum_logarithm_phase_step=maximum_phase_step,
    )


def li_basis_gram(coefficients: Sequence[float], dimension: int) -> list[list[float]]:
    return [
        [
            coefficients[row + 1]
            + coefficients[column + 1]
            - coefficients[abs(row - column)]
            for column in range(dimension)
        ]
        for row in range(dimension)
    ]


def jacobi_eigensystem(
    matrix: Sequence[Sequence[float]],
    tolerance: float,
    maximum_sweeps: int,
) -> tuple[list[float], list[list[float]], int, float]:
    """Symmetric cyclic Jacobi eigensolver, returning ascending eigenpairs."""

    dimension = len(matrix)
    values = [list(row) for row in matrix]
    vectors = [
        [1.0 if row == column else 0.0 for column in range(dimension)]
        for row in range(dimension)
    ]
    scale = max(1.0, max(abs(value) for row in values for value in row))
    residual = math.inf
    completed_sweeps = 0
    for sweep in range(1, maximum_sweeps + 1):
        residual = max(
            (abs(values[row][column]) for row in range(dimension)
             for column in range(row + 1, dimension)),
            default=0.0,
        )
        completed_sweeps = sweep
        if residual <= tolerance * scale:
            break
        for row in range(dimension):
            for column in range(row + 1, dimension):
                cross = values[row][column]
                if abs(cross) <= tolerance * scale:
                    continue
                diagonal_delta = values[column][column] - values[row][row]
                if diagonal_delta == 0.0:
                    tangent = 1.0
                else:
                    ratio = diagonal_delta / (2.0 * cross)
                    tangent = math.copysign(
                        1.0 / (abs(ratio) + math.sqrt(1.0 + ratio * ratio)),
                        ratio,
                    )
                cosine = 1.0 / math.sqrt(1.0 + tangent * tangent)
                sine = tangent * cosine
                row_diagonal = values[row][row]
                column_diagonal = values[column][column]
                values[row][row] = row_diagonal - tangent * cross
                values[column][column] = column_diagonal + tangent * cross
                values[row][column] = 0.0
                values[column][row] = 0.0
                for index in range(dimension):
                    if index == row or index == column:
                        continue
                    row_value = values[index][row]
                    column_value = values[index][column]
                    values[index][row] = cosine * row_value - sine * column_value
                    values[row][index] = values[index][row]
                    values[index][column] = sine * row_value + cosine * column_value
                    values[column][index] = values[index][column]
                for index in range(dimension):
                    row_vector = vectors[index][row]
                    column_vector = vectors[index][column]
                    vectors[index][row] = cosine * row_vector - sine * column_vector
                    vectors[index][column] = sine * row_vector + cosine * column_vector
    eigenpairs = sorted(
        (
            values[index][index],
            [vectors[row][index] for row in range(dimension)],
        )
        for index in range(dimension)
    )
    return (
        [pair[0] for pair in eigenpairs],
        [pair[1] for pair in eigenpairs],
        completed_sweeps,
        residual,
    )


def evaluate_section(
    coefficients: Sequence[float],
    dimension: int,
    eigen_tolerance: float,
    maximum_sweeps: int,
) -> GramSectionResult:
    eigenvalues, eigenvectors, sweeps, residual = jacobi_eigensystem(
        li_basis_gram(coefficients, dimension),
        eigen_tolerance,
        maximum_sweeps,
    )
    minimum = eigenvalues[0]
    maximum = eigenvalues[-1]
    condition = maximum / minimum if minimum > 0.0 else math.inf
    return GramSectionResult(
        dimension=dimension,
        minimum_eigenvalue=minimum,
        maximum_eigenvalue=maximum,
        condition_estimate=condition,
        jacobi_sweeps=sweeps,
        jacobi_residual=residual,
        minimum_direction=eigenvectors[0],
    )


def synthetic_off_line_coefficients(maximum_index: int) -> list[float]:
    """The X00 beta=0.9, gamma=0.1 symmetry quartet as an adversarial audit."""

    representatives = (complex(0.9, 0.1), complex(0.1, 0.1))
    coefficients = [0.0]
    for index in range(1, maximum_index + 1):
        coefficients.append(
            sum(
                2.0 * (1.0 - (1.0 - 1.0 / rho) ** index).real
                for rho in representatives
            )
        )
    return coefficients


def relative_difference(left: float, right: float) -> float:
    return abs(left - right) / max(1.0, abs(left), abs(right))


def complex_relative_difference(left: complex, right: complex) -> float:
    return abs(left - right) / max(1.0, abs(left), abs(right))


def leading_direction(direction: Sequence[float], limit: int = 8) -> list[dict[str, float | int]]:
    ordered = sorted(
        enumerate(direction, start=1),
        key=lambda item: abs(item[1]),
        reverse=True,
    )
    return [
        {"basis_index": index, "coefficient": coefficient}
        for index, coefficient in ordered[:limit]
    ]


def numerical_audit(settings: CoefficientSettings) -> dict[str, float]:
    zeta_two = riemann_zeta_euler_maclaurin(
        2.0 + 0.0j,
        settings.zeta_cutoff,
        settings.zeta_terms,
    )
    zeta_zero = riemann_zeta_euler_maclaurin(
        0.0 + 0.0j,
        settings.zeta_cutoff,
        settings.zeta_terms,
    )
    symmetry_points = (complex(0.37, 2.1), complex(1.3, 0.7))
    symmetry_error = max(
        complex_relative_difference(
            completed_xi(point, settings),
            completed_xi(1.0 - point, settings),
        )
        for point in symmetry_points
    )
    return {
        "zeta_two_error": abs(zeta_two - math.pi * math.pi / 6.0),
        "zeta_zero_error": abs(zeta_zero + 0.5),
        "xi_functional_symmetry_error": symmetry_error,
    }


def run_probe(args: argparse.Namespace) -> dict[str, object]:
    maximum_dimension = max(args.dimensions)
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
    baseline_coefficients = keiper_li_coefficients(maximum_dimension, baseline_settings)
    refined_coefficients = keiper_li_coefficients(maximum_dimension, refined_settings)
    exact_lambda_one = 1.0 + 0.5 * EULER_GAMMA - 0.5 * math.log(4.0 * math.pi)
    coefficient_differences = [
        relative_difference(left, right)
        for left, right in zip(
            baseline_coefficients.coefficients[1:],
            refined_coefficients.coefficients[1:],
        )
    ]
    baseline_sections = [
        evaluate_section(
            baseline_coefficients.coefficients,
            dimension,
            args.eigen_tolerance,
            args.maximum_jacobi_sweeps,
        )
        for dimension in args.dimensions
    ]
    refined_sections = [
        evaluate_section(
            refined_coefficients.coefficients,
            dimension,
            args.eigen_tolerance,
            args.maximum_jacobi_sweeps,
        )
        for dimension in args.dimensions
    ]
    section_comparison = []
    for baseline, refined in zip(baseline_sections, refined_sections):
        overlap = abs(sum(
            left * right
            for left, right in zip(
                baseline.minimum_direction,
                refined.minimum_direction,
            )
        ))
        section_comparison.append({
            "dimension": refined.dimension,
            "baseline_minimum_eigenvalue": baseline.minimum_eigenvalue,
            "refined_minimum_eigenvalue": refined.minimum_eigenvalue,
            "minimum_eigenvalue_relative_delta": relative_difference(
                baseline.minimum_eigenvalue,
                refined.minimum_eigenvalue,
            ),
            "minimum_direction_overlap": overlap,
            "minimum_eigenvalue_sign_stable": (
                (baseline.minimum_eigenvalue < -args.negative_tolerance)
                == (refined.minimum_eigenvalue < -args.negative_tolerance)
            ),
        })
    synthetic_coefficients = synthetic_off_line_coefficients(maximum_dimension)
    synthetic_section = evaluate_section(
        synthetic_coefficients,
        min(8, maximum_dimension),
        args.eigen_tolerance,
        args.maximum_jacobi_sweeps,
    )
    refined_audit = numerical_audit(refined_settings)
    stable_negative_sections = [
        comparison
        for comparison in section_comparison
        if comparison["baseline_minimum_eigenvalue"] < -args.negative_tolerance
        and comparison["refined_minimum_eigenvalue"] < -args.negative_tolerance
    ]
    audits_passed = (
        abs(refined_coefficients.coefficients[1] - exact_lambda_one)
        <= args.lambda_one_tolerance
        and max(coefficient_differences) <= args.coefficient_tolerance
        and refined_coefficients.maximum_imaginary_leakage
        <= args.imaginary_tolerance
        and refined_coefficients.logarithm_closure_error
        <= args.logarithm_closure_tolerance
        and refined_audit["zeta_two_error"] <= args.special_value_tolerance
        and refined_audit["zeta_zero_error"] <= args.special_value_tolerance
        and refined_audit["xi_functional_symmetry_error"]
        <= args.functional_symmetry_tolerance
        and synthetic_section.minimum_eigenvalue < -args.negative_tolerance
    )
    most_delicate = min(
        refined_sections,
        key=lambda section: section.minimum_eigenvalue,
    )
    return {
        "id": "M100-X03",
        "status": "INCONCLUSIVE",
        "hardness": "RH_HARD",
        "arithmetic": "Python float64",
        "coefficient_identity": (
            "log(2*xi(1/(1-z))) = sum(lambda_n*z^n/n, n>=1)"
        ),
        "gram_identity": "K(n,m)=lambda_n+lambda_m-lambda_|n-m|",
        "baseline_settings": asdict(baseline_settings),
        "refined_settings": asdict(refined_settings),
        "dimensions": args.dimensions,
        "exact_lambda_one": exact_lambda_one,
        "baseline_coefficient_result": asdict(baseline_coefficients),
        "refined_coefficient_result": asdict(refined_coefficients),
        "maximum_coefficient_relative_delta": max(coefficient_differences),
        "maximum_coefficient_delta_index": coefficient_differences.index(
            max(coefficient_differences)
        ) + 1,
        "numerical_audit": refined_audit,
        "baseline_sections": [asdict(section) for section in baseline_sections],
        "refined_sections": [asdict(section) for section in refined_sections],
        "section_comparison": section_comparison,
        "stable_negative_sections": stable_negative_sections,
        "most_delicate_section": {
            **asdict(most_delicate),
            "leading_minimum_direction": leading_direction(
                most_delicate.minimum_direction
            ),
        },
        "synthetic_off_line_audit": {
            **asdict(synthetic_section),
            "leading_minimum_direction": leading_direction(
                synthetic_section.minimum_direction
            ),
        },
        "passed": audits_passed,
        "decision": (
            "escalate any stable negative actual-zeta section to certified "
            "arithmetic; otherwise treat finite PSD as diagnostic only and "
            "move to exact arithmetic-side kernel structure"
        ),
    }


def format_number(value: float) -> str:
    if math.isinf(value):
        return "inf"
    return f"{value:.12e}"


def print_text_report(result: dict[str, object]) -> None:
    baseline = result["baseline_settings"]
    refined = result["refined_settings"]
    coefficients = result["refined_coefficient_result"]
    audit = result["numerical_audit"]
    print("M100-X03 actual-zeta Li-basis Gram probe")
    print("warning: float64 finite-section diagnostic; complete PSD is RH-hard")
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
        "  lambda_1="
        f"{format_number(coefficients['coefficients'][1])} "
        f"exact={format_number(result['exact_lambda_one'])}"
    )
    print(
        "  max baseline/refined coefficient delta="
        f"{format_number(result['maximum_coefficient_relative_delta'])} "
        f"at n={result['maximum_coefficient_delta_index']}"
    )
    print(
        "  max imaginary leakage="
        f"{format_number(coefficients['maximum_imaginary_leakage'])}"
    )
    print(
        "  logarithm closure error="
        f"{format_number(coefficients['logarithm_closure_error'])}"
    )
    print(
        "  zeta(2) error="
        f"{format_number(audit['zeta_two_error'])} "
        f"zeta(0) error={format_number(audit['zeta_zero_error'])}"
    )
    print(
        "  xi functional-symmetry error="
        f"{format_number(audit['xi_functional_symmetry_error'])}"
    )
    print()
    print("finite sections")
    for section, comparison in zip(
        result["refined_sections"],
        result["section_comparison"],
    ):
        print(
            f"  dimension={section['dimension']:2d} "
            f"min={format_number(section['minimum_eigenvalue'])} "
            f"max={format_number(section['maximum_eigenvalue'])} "
            f"condition={format_number(section['condition_estimate'])} "
            f"refinement_delta="
            f"{format_number(comparison['minimum_eigenvalue_relative_delta'])} "
            f"direction_overlap={comparison['minimum_direction_overlap']:.9f}"
        )
    delicate = result["most_delicate_section"]
    print()
    print(
        "most delicate actual-zeta direction: "
        f"dimension={delicate['dimension']} "
        f"min={format_number(delicate['minimum_eigenvalue'])}"
    )
    for item in delicate["leading_minimum_direction"]:
        print(
            f"  G_{item['basis_index']} coefficient="
            f"{format_number(item['coefficient'])}"
        )
    synthetic = result["synthetic_off_line_audit"]
    print()
    print(
        "X00 off-line adversarial audit: "
        f"dimension={synthetic['dimension']} "
        f"min={format_number(synthetic['minimum_eigenvalue'])}"
    )
    print(f"stable negative actual-zeta sections={len(result['stable_negative_sections'])}")
    print(f"status={result['status']}")
    print(f"audit_status={'PASS' if result['passed'] else 'FAIL'}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--dimensions",
        type=parse_int_list,
        default=parse_int_list("4,8,12,16,20,24"),
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
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if any(dimension <= 0 for dimension in args.dimensions):
        raise SystemExit("every Gram dimension must be positive")
    if not 0.0 < args.baseline_radius < 0.9:
        raise SystemExit("--baseline-radius must lie in (0, 0.9)")
    if not 0.0 < args.refined_radius < 0.9:
        raise SystemExit("--refined-radius must lie in (0, 0.9)")
    if args.baseline_samples <= 2 * max(args.dimensions):
        raise SystemExit("--baseline-samples must exceed twice the maximum dimension")
    if args.refined_samples <= 2 * max(args.dimensions):
        raise SystemExit("--refined-samples must exceed twice the maximum dimension")
    if not 1 <= args.baseline_zeta_terms <= len(BERNOULLI_EVEN):
        raise SystemExit("--baseline-zeta-terms is outside the implemented range")
    if not 1 <= args.refined_zeta_terms <= len(BERNOULLI_EVEN):
        raise SystemExit("--refined-zeta-terms is outside the implemented range")
    if args.baseline_zeta_cutoff < 2 or args.refined_zeta_cutoff < 2:
        raise SystemExit("zeta cutoffs must be at least two")
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
