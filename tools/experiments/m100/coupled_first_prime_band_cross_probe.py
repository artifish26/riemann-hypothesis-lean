#!/usr/bin/env python3
"""M100-X21 finite-window low/high cross-coupling scout.

The probe uses the complete-form entry evaluator from the X21 low-block scout
and assembles only the rectangular block between Yoshida modes ``|n| <= N``
and the first requested modes in ``|n| > N``.  It reports a certified singular
value enclosure for that finite window and compares it with the current Schur
threshold.  The finite window is discovery evidence: an upper bound for it is
not an upper bound for the full infinite high block, while a certified lower
bound above the Schur threshold is a genuine route obstruction.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json

try:
    from flint import arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "coupled_first_prime_band_cross_probe.py requires python-flint==0.8.0"
    ) from error

from coupled_first_prime_band_probe import (
    interval_text,
    matrix_entry_components,
)


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
    parser.add_argument("--high-window", type=int, default=1)
    parser.add_argument(
        "--parities",
        type=parse_parities,
        default=("even", "odd"),
    )
    parser.add_argument("--series-terms", type=int, default=8192)
    parser.add_argument("--precision-bits", type=int, default=192)
    return parser.parse_args()


def singular_value_enclosure(matrix: arb_mat) -> dict[str, object]:
    midpoint = matrix.mid()
    gram = midpoint.transpose() * midpoint
    eigenvalues = gram.eig(algorithm="rump")
    largest = max(eigenvalues, key=lambda value: float(value.real.mid()))
    if not largest.imag.contains(arb(0)):
        raise ArithmeticError("cross Gram eigenvalue missed the real axis")
    midpoint_norm = largest.real.sqrt()

    radius_frobenius = arb(0)
    for row in range(matrix.nrows()):
        for column in range(matrix.ncols()):
            radius = matrix[row, column].rad()
            radius_frobenius += radius * radius
    radius_frobenius = radius_frobenius.sqrt()
    enclosure = midpoint_norm + arb(0, radius_frobenius.upper())
    return {
        "midpoint_operator_norm": interval_text(midpoint_norm),
        "entry_radius_frobenius": interval_text(radius_frobenius),
        "operator_norm_interval": interval_text(enclosure),
        "operator_norm_lower": enclosure.lower().str(30, more=True),
        "operator_norm_upper": enclosure.upper().str(30, more=True),
    }


def main() -> None:
    args = parse_args()
    if args.cutoff < 1 or args.high_window < 1:
        raise ValueError("cutoff and high-window must be positive")
    if args.series_terms < 128:
        raise ValueError("series-terms must be at least 128")
    if args.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")
    ctx.prec = args.precision_bits

    log_two = arb.const_log2()
    pi = arb.pi()
    a = (
        log_two
        + (
            log_two * log_two
            + 4 * (-2 * arb(2).sqrt() * log_two).exp()
        ).sqrt()
    ) / 4
    high_margin = arb("0.00914732877973216")
    low_margins = {
        "even": arb("0.0000412111710357158"),
        "odd": arb("0.00587854548998113"),
    }
    low_eigenvalue_uppers = {
        "even": arb("0.0000576049288536388"),
        "odd": arb("0.00600690453974896"),
    }

    records = []
    for parity in args.parities:
        low_dimension = args.cutoff + 1 if parity == "even" else args.cutoff
        high_start = args.cutoff + 1 if parity == "even" else args.cutoff
        cross = arb_mat(low_dimension, args.high_window)
        largest_entry = arb(0)
        largest_indices = (0, high_start)
        for low_index in range(low_dimension):
            for high_offset in range(args.high_window):
                high_index = high_start + high_offset
                entry = matrix_entry_components(
                    "yoshida",
                    parity,
                    low_index,
                    high_index,
                    a,
                    1,
                    args.series_terms,
                    log_two,
                    pi,
                )["total"]
                cross[low_index, high_offset] = entry
                entry_magnitude = abs(entry).upper()
                if entry_magnitude > largest_entry:
                    largest_entry = entry_magnitude
                    largest_indices = (low_index, high_index)

        norm_record = singular_value_enclosure(cross)
        threshold = (
            low_margins[parity] * high_margin / 2
        ).sqrt()
        first_high_rayleigh = matrix_entry_components(
            "yoshida",
            parity,
            high_start,
            high_start,
            a,
            1,
            args.series_terms,
            log_two,
            pi,
        )["total"]
        absolute_threshold_ceiling = (
            low_eigenvalue_uppers[parity]
            * first_high_rayleigh.upper()
            / 2
        ).sqrt()
        records.append(
            {
                "parity": parity,
                "low_dimension": low_dimension,
                "high_mode_indices": [
                    high_start,
                    high_start + args.high_window - 1,
                ],
                "largest_entry_upper": interval_text(largest_entry),
                "largest_entry_indices": list(largest_indices),
                "current_schur_threshold": interval_text(threshold),
                "first_high_mode_rayleigh": interval_text(
                    first_high_rayleigh
                ),
                "absolute_schur_threshold_ceiling": interval_text(
                    absolute_threshold_ceiling
                ),
                "finite_window": norm_record,
                "finite_window_certified_above_threshold": (
                    arb(norm_record["operator_norm_lower"]) > threshold
                ),
                "finite_window_certified_above_absolute_ceiling": (
                    arb(norm_record["operator_norm_lower"])
                    > absolute_threshold_ceiling
                ),
            }
        )

    print(
        json.dumps(
            {
                "experiment": "M100-X21",
                "artifact": "finite-low-high-cross-window",
                "scope": (
                    "Complete-form finite-window cross evidence at the right "
                    "band endpoint; not an infinite-tail upper bound."
                ),
                "settings": {
                    "cutoff": args.cutoff,
                    "high_window": args.high_window,
                    "parities": list(args.parities),
                    "series_terms": args.series_terms,
                    "precision_bits": args.precision_bits,
                },
                "band_right_endpoint": interval_text(a),
                "high_margin": interval_text(high_margin),
                "records": records,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
