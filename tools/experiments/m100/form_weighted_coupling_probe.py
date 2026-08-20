#!/usr/bin/env python3
"""M100-X22 complete-form matrix-weighted coupling audit.

The probe reuses X21's interval evaluator at the hard right endpoint and
assembles the low block ``A``, the next-mode block ``D``, and their cross block
``B`` in one fixed Yoshida basis.  It never inverts an interval matrix.
Instead, for exact rational ``q`` it uses

    theta^2 < q  iff  [[q*A, B], [B^*, D]] is positive definite,

where ``theta = ||A^(-1/2) B D^(-1/2)||`` and the equivalence is applied only
after both diagonal blocks have been certified positive definite.  Midpoint
eigenvalues plus an interval row-sum perturbation bound give rigorous signs.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import json
import sys

try:
    import flint
    from flint import arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "form_weighted_coupling_probe.py requires python-flint==0.8.0"
    ) from error

from coupled_first_prime_band_probe import (
    interval_text,
    lowest_eigenvalue_record,
    matrix_entry_components,
)


@dataclass(frozen=True)
class Settings:
    cutoff: int
    windows: tuple[int, ...]
    parities: tuple[str, ...]
    series_terms: int
    precision_bits: int
    bisection_steps: int


def parse_windows(text: str) -> tuple[int, ...]:
    windows = tuple(sorted({int(item) for item in text.split(",")}))
    if not windows or windows[0] < 1:
        raise argparse.ArgumentTypeError("windows must be positive integers")
    return windows


def parse_parities(text: str) -> tuple[str, ...]:
    requested = set(text.split(","))
    parities = tuple(p for p in ("even", "odd") if p in requested)
    if not parities or requested != set(parities):
        raise argparse.ArgumentTypeError(
            "parities must be even, odd, or even,odd"
        )
    return parities


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cutoff", type=int, default=36)
    parser.add_argument(
        "--windows",
        type=parse_windows,
        default=(1, 2, 4, 8),
    )
    parser.add_argument(
        "--parities",
        type=parse_parities,
        default=("even",),
    )
    parser.add_argument("--series-terms", type=int, default=16384)
    parser.add_argument("--precision-bits", type=int, default=192)
    parser.add_argument("--bisection-steps", type=int, default=12)
    parser.add_argument("--summary-only", action="store_true")
    return parser.parse_args()


def validate_settings(settings: Settings) -> None:
    if settings.cutoff < 1:
        raise ValueError("cutoff must be positive")
    if settings.series_terms < 128:
        raise ValueError("series-terms must be at least 128")
    if settings.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")
    if settings.bisection_steps < 0 or settings.bisection_steps > 40:
        raise ValueError("bisection-steps must lie in [0, 40]")


def right_band_endpoint(log_two: arb) -> arb:
    return (
        log_two
        + (
            log_two * log_two
            + 4 * (-2 * arb(2).sqrt() * log_two).exp()
        ).sqrt()
    ) / 4


def fraction_text(value: Fraction) -> str:
    return (
        str(value.numerator)
        if value.denominator == 1
        else f"{value.numerator}/{value.denominator}"
    )


def fraction_arb(value: Fraction) -> arb:
    return arb(fmpq(value.numerator, value.denominator))


def extract_block(
    matrix: arb_mat,
    row_start: int,
    row_count: int,
    column_start: int,
    column_count: int,
) -> arb_mat:
    block = arb_mat(row_count, column_count)
    for row in range(row_count):
        for column in range(column_count):
            block[row, column] = matrix[
                row_start + row,
                column_start + column,
            ]
    return block


def threshold_matrix(
    low: arb_mat,
    cross: arb_mat,
    high: arb_mat,
    q: Fraction,
) -> arb_mat:
    low_dimension = low.nrows()
    high_dimension = high.nrows()
    if low.ncols() != low_dimension:
        raise ValueError("low block must be square")
    if high.ncols() != high_dimension:
        raise ValueError("high block must be square")
    if cross.nrows() != low_dimension or cross.ncols() != high_dimension:
        raise ValueError("cross block has incompatible dimensions")

    q_value = fraction_arb(q)
    result = arb_mat(low_dimension + high_dimension, low_dimension + high_dimension)
    for row in range(low_dimension):
        for column in range(low_dimension):
            result[row, column] = q_value * low[row, column]
        for column in range(high_dimension):
            value = cross[row, column]
            result[row, low_dimension + column] = value
            result[low_dimension + column, row] = value
    for row in range(high_dimension):
        for column in range(high_dimension):
            result[
                low_dimension + row,
                low_dimension + column,
            ] = high[row, column]
    return result


def threshold_record(
    low: arb_mat,
    cross: arb_mat,
    high: arb_mat,
    q: Fraction,
) -> dict[str, object]:
    record = lowest_eigenvalue_record(
        threshold_matrix(low, cross, high, q)
    )
    return {
        "q": fraction_text(q),
        "lowest_eigenvalue": record,
    }


def enclosure_loss_fraction(record: dict[str, object]) -> arb:
    perturbation = arb(record["entry_perturbation_row_sum_bound"])
    midpoint = abs(arb(record["midpoint_eigenvalue"]))
    if midpoint.lower() <= 0:
        raise ArithmeticError("midpoint eigenvalue does not avoid zero")
    return perturbation / midpoint


def theta_squared_bracket(
    low: arb_mat,
    cross: arb_mat,
    high: arb_mat,
    steps: int,
) -> dict[str, object]:
    """Bracket theta^2 by certified signs of the exact threshold blocks."""

    trace: list[dict[str, object]] = []
    lower = Fraction(0)
    # theta^2 >= 0 is exact.  Do not eigensolve the q=0 threshold block: its
    # repeated zero eigenvalues are artificial and need not be isolated.
    lower_record: dict[str, object] | None = None

    upper = Fraction(1)
    upper_record = threshold_record(low, cross, high, upper)
    trace.append(upper_record)
    while not upper_record["lowest_eigenvalue"][
        "certified_positive_finite_ritz"
    ]:
        if upper_record["lowest_eigenvalue"][
            "certified_negative_direction"
        ]:
            lower = upper
            lower_record = upper_record
            upper *= 2
            if upper > 64:
                return {
                    "certified_lower": fraction_text(lower),
                    "certified_upper": None,
                    "unresolved_reason": "no positive threshold through q=64",
                    "trace": trace,
                }
            upper_record = threshold_record(low, cross, high, upper)
            trace.append(upper_record)
            continue
        return {
            "certified_lower": fraction_text(lower),
            "certified_upper": None,
            "unresolved_reason": (
                f"q={fraction_text(upper)} sign unresolved"
            ),
            "trace": trace,
        }

    unresolved_q: Fraction | None = None
    for _ in range(steps):
        midpoint = (lower + upper) / 2
        midpoint_record = threshold_record(low, cross, high, midpoint)
        trace.append(midpoint_record)
        eigenvalue = midpoint_record["lowest_eigenvalue"]
        if eigenvalue["certified_positive_finite_ritz"]:
            upper = midpoint
            upper_record = midpoint_record
        elif eigenvalue["certified_negative_direction"]:
            lower = midpoint
            lower_record = midpoint_record
        else:
            unresolved_q = midpoint
            break

    return {
        "certified_lower": fraction_text(lower),
        "certified_upper": fraction_text(upper),
        "unresolved_q": (
            fraction_text(unresolved_q) if unresolved_q is not None else None
        ),
        "lower_witness": lower_record,
        "upper_witness": upper_record,
        "trace": trace,
    }


def midpoint_trial_vector(low: arb_mat) -> arb_mat:
    """Return a normalized real trial vector from the midpoint eigensystem."""

    eigenvalues, right = low.mid().eig(
        right=True,
        algorithm="approx",
    )
    lowest_index = min(
        range(len(eigenvalues)),
        key=lambda index: float(eigenvalues[index].real.mid()),
    )
    vector = arb_mat(low.nrows(), 1)
    for row in range(low.nrows()):
        vector[row, 0] = right[row, lowest_index].real.mid()

    norm_squared = (vector.transpose() * vector)[0, 0]
    if norm_squared.lower() <= 0:
        raise ArithmeticError("midpoint trial vector has uncertified norm")
    norm = norm_squared.sqrt()
    for row in range(low.nrows()):
        vector[row, 0] = vector[row, 0] / norm

    pivot = max(
        range(low.nrows()),
        key=lambda row: float(abs(vector[row, 0]).mid()),
    )
    if vector[pivot, 0].mid() < 0:
        for row in range(low.nrows()):
            vector[row, 0] = -vector[row, 0]
    return vector


def trial_vector_record(
    low: arb_mat,
    cross: arb_mat,
    high: arb_mat,
    steps: int,
) -> dict[str, object]:
    vector = midpoint_trial_vector(low)
    rayleigh = (vector.transpose() * low * vector)[0, 0]
    coupling = cross.transpose() * vector
    coupling_norm_squared = arb(0)
    for row in range(coupling.nrows()):
        coupling_norm_squared += coupling[row, 0] * coupling[row, 0]

    scalar_low = arb_mat(1, 1)
    scalar_low[0, 0] = rayleigh
    scalar_cross = coupling.transpose()
    return {
        "construction": (
            "normalized real part of the approximate lowest midpoint "
            "eigenvector; all reported evaluations use the interval matrix"
        ),
        "coefficients": [
            interval_text(vector[row, 0]) for row in range(vector.nrows())
        ],
        "rayleigh_interval": interval_text(rayleigh),
        "coupling_euclidean_norm_squared": interval_text(
            coupling_norm_squared
        ),
        "fixed_vector_theta_squared": theta_squared_bracket(
            scalar_low,
            scalar_cross,
            high,
            steps,
        ),
    }


def build_complete_matrix(
    parity: str,
    cutoff: int,
    max_window: int,
    a: arb,
    series_terms: int,
    log_two: arb,
    pi: arb,
) -> tuple[arb_mat, int]:
    low_dimension = cutoff + 1 if parity == "even" else cutoff
    full_dimension = low_dimension + max_window
    matrix = arb_mat(full_dimension, full_dimension)
    for left in range(full_dimension):
        print(
            f"[{parity}] assembling row {left + 1}/{full_dimension}",
            file=sys.stderr,
            flush=True,
        )
        for right in range(left, full_dimension):
            value = matrix_entry_components(
                "yoshida",
                parity,
                left,
                right,
                a,
                1,
                series_terms,
                log_two,
                pi,
            )["total"]
            matrix[left, right] = value
            matrix[right, left] = value
    return matrix, low_dimension


def window_record(
    full: arb_mat,
    low_dimension: int,
    window: int,
    bisection_steps: int,
) -> dict[str, object]:
    low = extract_block(full, 0, low_dimension, 0, low_dimension)
    cross = extract_block(full, 0, low_dimension, low_dimension, window)
    high = extract_block(
        full,
        low_dimension,
        window,
        low_dimension,
        window,
    )

    low_eigenvalue = lowest_eigenvalue_record(low)
    high_eigenvalue = lowest_eigenvalue_record(high)
    half = threshold_record(low, cross, high, Fraction(1, 2))
    augmented = threshold_record(low, cross, high, Fraction(1))
    augmented_loss_fraction = enclosure_loss_fraction(
        augmented["lowest_eigenvalue"]
    )
    augmented_loss_below_quarter = (
        augmented_loss_fraction.upper() < arb(fmpq(1, 4))
    )
    diagonal_blocks_positive = bool(
        low_eigenvalue["certified_positive_finite_ritz"]
        and high_eigenvalue["certified_positive_finite_ritz"]
    )

    if not diagonal_blocks_positive:
        gate = "DIAGONAL_BLOCK_NOT_CERTIFIED"
    elif augmented["lowest_eigenvalue"]["certified_negative_direction"]:
        gate = "NEGATIVE_DIRECTION_REPRODUCTION_REQUIRED"
    elif not augmented["lowest_eigenvalue"][
        "certified_positive_finite_ritz"
    ]:
        gate = "AUGMENTED_SIGN_UNRESOLVED"
    elif half["lowest_eigenvalue"]["certified_positive_finite_ritz"]:
        gate = (
            "FINITE_GATE_PASSES_WITH_HALF_RESERVE"
            if augmented_loss_below_quarter
            else "FINITE_GATE_NEEDS_ENCLOSURE_REFINEMENT"
        )
    elif half["lowest_eigenvalue"]["certified_negative_direction"]:
        gate = "FINITE_POSITIVE_BUT_HALF_RESERVE_FAILS"
    else:
        gate = "HALF_RESERVE_UNRESOLVED"

    return {
        "high_window": window,
        "augmented_dimension": low_dimension + window,
        "low_block_lowest": low_eigenvalue,
        "high_block_lowest": high_eigenvalue,
        "q_half_threshold": half,
        "full_augmented": augmented,
        "augmented_enclosure_loss_fraction": interval_text(
            augmented_loss_fraction
        ),
        "augmented_enclosure_loss_below_quarter": (
            augmented_loss_below_quarter
        ),
        "theta_squared_bracket": (
            theta_squared_bracket(
                low,
                cross,
                high,
                bisection_steps,
            )
            if diagonal_blocks_positive
            else None
        ),
        "near_minimizing_low_trial": (
            trial_vector_record(
                low,
                cross,
                high,
                bisection_steps,
            )
            if diagonal_blocks_positive
            else None
        ),
        "finite_gate": gate,
    }


def compact_bracket(record: dict[str, object] | None) -> object:
    if record is None:
        return None
    return {
        "certified_lower": record.get("certified_lower"),
        "certified_upper": record.get("certified_upper"),
        "unresolved_q": record.get("unresolved_q"),
        "unresolved_reason": record.get("unresolved_reason"),
    }


def summary_payload(payload: dict[str, object]) -> dict[str, object]:
    parities = []
    for parity in payload["parities"]:
        windows = []
        for record in parity["windows"]:
            trial = record["near_minimizing_low_trial"]
            windows.append(
                {
                    "high_window": record["high_window"],
                    "augmented_dimension": record["augmented_dimension"],
                    "low_block_lowest": record["low_block_lowest"],
                    "high_block_lowest": record["high_block_lowest"],
                    "q_half_threshold": record["q_half_threshold"],
                    "full_augmented": record["full_augmented"],
                    "augmented_enclosure_loss_fraction": record[
                        "augmented_enclosure_loss_fraction"
                    ],
                    "augmented_enclosure_loss_below_quarter": record[
                        "augmented_enclosure_loss_below_quarter"
                    ],
                    "theta_squared_bracket": compact_bracket(
                        record["theta_squared_bracket"]
                    ),
                    "near_minimizing_low_trial": (
                        {
                            "rayleigh_interval": trial["rayleigh_interval"],
                            "coupling_euclidean_norm_squared": trial[
                                "coupling_euclidean_norm_squared"
                            ],
                            "fixed_vector_theta_squared": compact_bracket(
                                trial["fixed_vector_theta_squared"]
                            ),
                        }
                        if trial is not None
                        else None
                    ),
                    "finite_gate": record["finite_gate"],
                }
            )
        parities.append(
            {
                "parity": parity["parity"],
                "low_dimension": parity["low_dimension"],
                "high_mode_indices": parity["high_mode_indices"],
                "windows": windows,
            }
        )
    return {
        key: value
        for key, value in payload.items()
        if key != "parities"
    } | {"parities": parities}


def main() -> int:
    args = parse_args()
    settings = Settings(
        cutoff=args.cutoff,
        windows=args.windows,
        parities=args.parities,
        series_terms=args.series_terms,
        precision_bits=args.precision_bits,
        bisection_steps=args.bisection_steps,
    )
    validate_settings(settings)
    ctx.prec = settings.precision_bits

    log_two = arb.const_log2()
    pi = arb.pi()
    a = right_band_endpoint(log_two)
    parity_records = []
    for parity in settings.parities:
        full, low_dimension = build_complete_matrix(
            parity,
            settings.cutoff,
            max(settings.windows),
            a,
            settings.series_terms,
            log_two,
            pi,
        )
        windows = [
            window_record(
                full,
                low_dimension,
                window,
                settings.bisection_steps,
            )
            for window in settings.windows
        ]
        parity_records.append(
            {
                "parity": parity,
                "low_dimension": low_dimension,
                "high_mode_indices": [
                    low_dimension,
                    low_dimension + max(settings.windows) - 1,
                ],
                "windows": windows,
            }
        )

    finite_gates = [
        record["finite_gate"]
        for parity in parity_records
        for record in parity["windows"]
    ]
    if any(
        gate == "NEGATIVE_DIRECTION_REPRODUCTION_REQUIRED"
        for gate in finite_gates
    ):
        summary = "NEGATIVE_DIRECTION_REPRODUCTION_REQUIRED"
    elif all(
        gate == "FINITE_GATE_PASSES_WITH_HALF_RESERVE"
        for gate in finite_gates
    ):
        summary = "DECLARED_FINITE_GATES_PASS"
    elif any(
        gate == "FINITE_POSITIVE_BUT_HALF_RESERVE_FAILS"
        for gate in finite_gates
    ):
        summary = "DECLARED_HALF_RESERVE_GATE_FAILS"
    elif any(
        gate == "FINITE_GATE_NEEDS_ENCLOSURE_REFINEMENT"
        for gate in finite_gates
    ):
        summary = "DECLARED_ENCLOSURE_GATE_UNRESOLVED"
    else:
        summary = "FINITE_GATE_UNRESOLVED"

    payload = {
        "experiment": "M100-X22",
        "artifact": "complete-form-weighted-schur-window",
        "dependency": f"python-flint=={flint.__version__}",
        "settings": {
            "cutoff": settings.cutoff,
            "windows": list(settings.windows),
            "parities": list(settings.parities),
            "series_terms": settings.series_terms,
            "precision_bits": settings.precision_bits,
            "bisection_steps": settings.bisection_steps,
        },
        "band_right_endpoint": interval_text(a),
        "certificate": (
            "theta^2<q iff [[qA,B],[B^*,D]] is positive definite; "
            "each sign uses midpoint eigenvalues plus the maximum "
            "interval perturbation row sum"
        ),
        "parities": parity_records,
        "finite_gate_summary": summary,
        "scope": (
            "Fixed-endpoint finite-window complete-form evidence. "
            "It is not an infinite-tail or parameter-continuum "
            "coercivity theorem."
        ),
    }
    if args.summary_only:
        payload = summary_payload(payload)
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
