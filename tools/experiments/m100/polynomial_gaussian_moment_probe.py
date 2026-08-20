#!/usr/bin/env python3
"""M100-X06 polynomial-Gaussian Hankel moment probe.

For a critical-line zero ordinate gamma, the scaled monomial basis from the
Lean experiment contributes the positive moment atom

    2 * gamma^(2*k) * exp(-pi*gamma^2).

The script forms diagonally normalized finite Hankel windows in the log domain
and compares 20-zero and 40-zero truncations. It also applies the same exact
real-part formula to one synthetic off-line conjugate pair. The rounded zero
sample is a deterministic smoke-test dataset already used by
`tools/finite_rayleigh_probe.py`; neither the sample nor PSD of its finite
critical-line matrices is evidence for RH.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Sequence


DEFAULT_ZEROS = (
    14.134725141734693,
    21.022039638771556,
    25.01085758014569,
    30.424876125859512,
    32.93506158773919,
    37.586178158825675,
    40.9187190121475,
    43.327073280915,
    48.00515088116716,
    49.7738324776723,
    52.97032147771446,
    56.44624769706339,
    59.34704400260235,
    60.83177852460981,
    65.11254404808161,
    67.07981052949417,
    69.54640171117398,
    72.06715767448191,
    75.70469069908393,
    77.1448400688748,
    79.33737502024937,
    82.91038085408603,
    84.73549298051705,
    87.42527461312523,
    88.80911120763447,
    92.49189927055848,
    94.65134404051989,
    95.87063422824531,
    98.83119421819369,
    101.31785100573139,
    103.72553804047834,
    105.44662305232609,
    107.1686111842764,
    111.02953554316967,
    111.87465917699264,
    114.32022091545271,
    116.22668032085755,
    118.79078286597622,
    121.37012500242065,
    122.94682929355259,
)


@dataclass(frozen=True)
class WindowResult:
    start_degree: int
    dimension: int
    zero_count: int
    minimum_eigenvalue: float
    maximum_eigenvalue: float
    condition_estimate: float | None
    numerical_rank: int
    jacobi_sweeps: int
    jacobi_residual: float
    minimum_direction: list[float]


@dataclass(frozen=True)
class SyntheticResult:
    ordinate: float
    horizontal_offset: float
    start_degree: int
    dimension: int
    minimum_eigenvalue: float
    maximum_eigenvalue: float
    negative_count: int
    minimum_direction: list[float]


def parse_int_list(text: str) -> list[int]:
    values = [int(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise argparse.ArgumentTypeError("expected a nonempty comma-separated list")
    return values


def parse_float_list(text: str) -> list[float]:
    values = [float(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise argparse.ArgumentTypeError("expected a nonempty comma-separated list")
    return values


def log_critical_moment(order: int, zeroes: Sequence[float]) -> float:
    exponents = [
        2.0 * order * math.log(gamma) - math.pi * gamma * gamma
        for gamma in zeroes
    ]
    maximum = max(exponents)
    return math.log(2.0) + maximum + math.log(
        sum(math.exp(value - maximum) for value in exponents)
    )


def normalized_critical_hankel(
    start_degree: int,
    dimension: int,
    zeroes: Sequence[float],
) -> list[list[float]]:
    needed_orders = range(2 * start_degree, 2 * (start_degree + dimension - 1) + 1)
    moments = {order: log_critical_moment(order, zeroes) for order in needed_orders}
    return [
        [
            math.exp(
                moments[2 * start_degree + row + column]
                - 0.5
                * (
                    moments[2 * (start_degree + row)]
                    + moments[2 * (start_degree + column)]
                )
            )
            for column in range(dimension)
        ]
        for row in range(dimension)
    ]


def synthetic_off_line_hankel(
    ordinate: float,
    horizontal_offset: float,
    start_degree: int,
    dimension: int,
) -> list[list[float]]:
    """Scale the real-part moment matrix by one common positive factor."""

    radius = math.hypot(ordinate, horizontal_offset)
    angle = math.atan2(horizontal_offset, ordinate)
    base_phase = -2.0 * math.pi * ordinate * horizontal_offset
    entries: dict[int, tuple[float, float]] = {}
    maximum_log_absolute = -math.inf
    for order in range(
        2 * start_degree,
        2 * (start_degree + dimension - 1) + 1,
    ):
        cosine = math.cos(base_phase + 2.0 * order * angle)
        if cosine == 0.0:
            entries[order] = (0.0, -math.inf)
            continue
        log_absolute = 2.0 * order * math.log(radius) + math.log(abs(cosine))
        entries[order] = (math.copysign(1.0, cosine), log_absolute)
        maximum_log_absolute = max(maximum_log_absolute, log_absolute)
    return [
        [
            sign * math.exp(log_absolute - maximum_log_absolute)
            if sign != 0.0
            else 0.0
            for column in range(dimension)
            for sign, log_absolute in [
                entries[2 * start_degree + row + column]
            ]
        ]
        for row in range(dimension)
    ]


def jacobi_eigensystem(
    matrix: Sequence[Sequence[float]],
    tolerance: float,
    maximum_sweeps: int,
) -> tuple[list[float], list[list[float]], int, float]:
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
            (
                abs(values[row][column])
                for row in range(dimension)
                for column in range(row + 1, dimension)
            ),
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
                delta = values[column][column] - values[row][row]
                if delta == 0.0:
                    tangent = 1.0
                else:
                    ratio = delta / (2.0 * cross)
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


def evaluate_window(
    start_degree: int,
    dimension: int,
    zero_count: int,
    tolerance: float,
    maximum_sweeps: int,
    rank_tolerance: float,
) -> tuple[WindowResult, list[list[float]]]:
    matrix = normalized_critical_hankel(
        start_degree,
        dimension,
        DEFAULT_ZEROS[:zero_count],
    )
    eigenvalues, eigenvectors, sweeps, residual = jacobi_eigensystem(
        matrix,
        tolerance,
        maximum_sweeps,
    )
    minimum = eigenvalues[0]
    maximum = eigenvalues[-1]
    condition = maximum / minimum if minimum > 0.0 else None
    rank = sum(value > rank_tolerance * maximum for value in eigenvalues)
    return (
        WindowResult(
            start_degree=start_degree,
            dimension=dimension,
            zero_count=zero_count,
            minimum_eigenvalue=minimum,
            maximum_eigenvalue=maximum,
            condition_estimate=condition,
            numerical_rank=rank,
            jacobi_sweeps=sweeps,
            jacobi_residual=residual,
            minimum_direction=eigenvectors[0],
        ),
        matrix,
    )


def maximum_matrix_delta(
    left: Sequence[Sequence[float]],
    right: Sequence[Sequence[float]],
) -> float:
    return max(
        abs(left[row][column] - right[row][column])
        for row in range(len(left))
        for column in range(len(left))
    )


def run_probe(args: argparse.Namespace) -> dict[str, object]:
    baseline_results: list[WindowResult] = []
    refined_results: list[WindowResult] = []
    deltas: list[dict[str, float | int]] = []
    for start in args.start_degrees:
        baseline, baseline_matrix = evaluate_window(
            start,
            args.dimension,
            args.baseline_zero_count,
            args.eigen_tolerance,
            args.maximum_sweeps,
            args.rank_tolerance,
        )
        refined, refined_matrix = evaluate_window(
            start,
            args.dimension,
            args.refined_zero_count,
            args.eigen_tolerance,
            args.maximum_sweeps,
            args.rank_tolerance,
        )
        baseline_results.append(baseline)
        refined_results.append(refined)
        deltas.append(
            {
                "start_degree": start,
                "maximum_normalized_entry_delta": maximum_matrix_delta(
                    baseline_matrix,
                    refined_matrix,
                ),
                "minimum_eigenvalue_delta": abs(
                    baseline.minimum_eigenvalue - refined.minimum_eigenvalue
                ),
            }
        )

    synthetic_results: list[SyntheticResult] = []
    for offset in args.synthetic_offsets:
        for start in args.synthetic_start_degrees:
            matrix = synthetic_off_line_hankel(
                args.synthetic_ordinate,
                offset,
                start,
                args.synthetic_dimension,
            )
            eigenvalues, eigenvectors, _sweeps, _residual = jacobi_eigensystem(
                matrix,
                args.eigen_tolerance,
                args.maximum_sweeps,
            )
            synthetic_results.append(
                SyntheticResult(
                    ordinate=args.synthetic_ordinate,
                    horizontal_offset=offset,
                    start_degree=start,
                    dimension=args.synthetic_dimension,
                    minimum_eigenvalue=eigenvalues[0],
                    maximum_eigenvalue=eigenvalues[-1],
                    negative_count=sum(
                        value < -args.negative_tolerance for value in eigenvalues
                    ),
                    minimum_direction=eigenvectors[0],
                )
            )

    stable_critical_negatives = [
        refined
        for baseline, refined in zip(baseline_results, refined_results)
        if baseline.minimum_eigenvalue < -args.negative_tolerance
        and refined.minimum_eigenvalue < -args.negative_tolerance
    ]
    synthetic_negatives = [
        result for result in synthetic_results if result.negative_count > 0
    ]
    audits_passed = (
        max(delta["maximum_normalized_entry_delta"] for delta in deltas)
        <= args.refinement_tolerance
        and not stable_critical_negatives
        and bool(synthetic_negatives)
    )
    return {
        "id": "M100-X06",
        "status": "PROMOTABLE" if audits_passed else "INCONCLUSIVE",
        "arithmetic": "Python float64 log-domain moments",
        "warning": (
            "finite rounded critical-line zero samples assume the tested zeros "
            "are on the line and are not evidence for RH"
        ),
        "basis": "z^(2*n) * exp(-pi*z^2/2)",
        "dimension": args.dimension,
        "baseline_zero_count": args.baseline_zero_count,
        "refined_zero_count": args.refined_zero_count,
        "critical_line_windows_baseline": [
            asdict(result) for result in baseline_results
        ],
        "critical_line_windows_refined": [
            asdict(result) for result in refined_results
        ],
        "refinement_audit": deltas,
        "stable_critical_negative_count": len(stable_critical_negatives),
        "synthetic_off_line_results": [
            asdict(result) for result in synthetic_results
        ],
        "synthetic_negative_count": len(synthetic_negatives),
        "decision": (
            "retain the exact finite Hankel characterization, but reject "
            "critical-line sample PSD as an unconditional positivity mechanism"
        ),
        "passed": audits_passed,
    }


def format_number(value: float | None) -> str:
    if value is None:
        return "unresolved"
    if math.isinf(value):
        return "inf"
    return f"{value:.12e}"


def print_text_report(result: dict[str, object]) -> None:
    print("M100-X06 polynomial-Gaussian Hankel moment probe")
    print(f"warning: {result['warning']}")
    print(f"basis={result['basis']}")
    print(
        f"dimension={result['dimension']} "
        f"zero_counts={result['baseline_zero_count']}/{result['refined_zero_count']}"
    )
    print()
    print("critical-line normalized Hankel windows")
    for item in result["critical_line_windows_refined"]:
        print(
            f"  start={item['start_degree']:4d} "
            f"min={format_number(item['minimum_eigenvalue'])} "
            f"max={format_number(item['maximum_eigenvalue'])} "
            f"rank={item['numerical_rank']}/{item['dimension']} "
            f"condition={format_number(item['condition_estimate'])}"
        )
    maximum_entry_delta = max(
        item["maximum_normalized_entry_delta"]
        for item in result["refinement_audit"]
    )
    print(
        "  maximum 20/40-zero normalized entry delta="
        f"{format_number(maximum_entry_delta)}"
    )
    print(
        "  stable negative windows="
        f"{result['stable_critical_negative_count']}"
    )
    print()
    print("synthetic off-line real-part Hankel controls")
    for item in result["synthetic_off_line_results"]:
        print(
            f"  offset={item['horizontal_offset']:g} "
            f"start={item['start_degree']:4d} "
            f"min={format_number(item['minimum_eigenvalue'])} "
            f"negative_count={item['negative_count']}"
        )
    print()
    print(f"status={result['status']}")
    print(f"audit_status={'PASS' if result['passed'] else 'FAIL'}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--start-degrees",
        type=parse_int_list,
        default=parse_int_list("0,479,830,1203,1576,1950,2419"),
    )
    parser.add_argument("--dimension", type=int, default=8)
    parser.add_argument("--baseline-zero-count", type=int, default=20)
    parser.add_argument("--refined-zero-count", type=int, default=40)
    parser.add_argument("--rank-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--eigen-tolerance", type=float, default=1.0e-14)
    parser.add_argument("--maximum-sweeps", type=int, default=200)
    parser.add_argument("--negative-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--refinement-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--synthetic-ordinate", type=float, default=14.134725141734693)
    parser.add_argument(
        "--synthetic-offsets",
        type=parse_float_list,
        default=parse_float_list("0.05,0.1,0.25,0.5"),
    )
    parser.add_argument(
        "--synthetic-start-degrees",
        type=parse_int_list,
        default=parse_int_list("0,64,256"),
    )
    parser.add_argument("--synthetic-dimension", type=int, default=4)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if args.dimension < 2 or args.synthetic_dimension < 2:
        raise SystemExit("matrix dimensions must be at least two")
    if any(start < 0 for start in args.start_degrees + args.synthetic_start_degrees):
        raise SystemExit("start degrees must be nonnegative")
    if not 1 <= args.baseline_zero_count <= len(DEFAULT_ZEROS):
        raise SystemExit("baseline zero count is outside the built-in sample")
    if not args.baseline_zero_count <= args.refined_zero_count <= len(DEFAULT_ZEROS):
        raise SystemExit("refined zero count is outside the built-in sample")
    if any(offset <= 0.0 for offset in args.synthetic_offsets):
        raise SystemExit("synthetic offsets must be positive")
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
