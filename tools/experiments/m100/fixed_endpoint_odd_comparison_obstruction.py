#!/usr/bin/env python3
"""M100-FT4 Arb obstruction to the frozen odd comparison reserve.

The desired FT4 inequality implies

    C_A E_A^(-1) C_A^* <= (19/1000) K

for every finite far Galerkin space A.  This script uses odd Yoshida modes
1 through 44 for K and the declared first far window beginning at mode 45.
It certifies a negative direction in the displayed finite target, which
refutes this comparison-energy route without making a claim about the actual
complete-form inverse or global positivity.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json

try:
    from flint import arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "fixed_endpoint_odd_comparison_obstruction.py requires "
        "python-flint==0.8.0"
    ) from error

from coupled_first_prime_band_probe import (
    interval_text,
    lowest_eigenvalue_record,
    matrix_entry_components,
)
from fixed_endpoint_even_comparison_certificate import (
    alternating,
    comparison_sine_transform,
    complete_sine_transform,
)
from form_weighted_coupling_probe import right_band_endpoint


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--boundary", type=int, default=44)
    parser.add_argument("--far-window", type=int, default=32)
    parser.add_argument("--series-terms", type=int, default=16384)
    parser.add_argument("--arch-tail-terms", type=int, default=128)
    parser.add_argument("--precision-bits", type=int, default=192)
    return parser.parse_args()


def odd_convolution_off_diagonal(
    transforms: list[arb],
    left_mode: int,
    right_mode: int,
    pi: arb,
) -> arb:
    """Odd sine-basis convolution entry for distinct positive modes."""

    if left_mode <= 0 or right_mode <= 0:
        raise ValueError("odd physical modes must be positive")
    if left_mode == right_mode:
        raise ValueError("off-diagonal reconstruction requires distinct modes")
    difference = left_mode - right_mode
    total = left_mode + right_mode
    difference_sign = alternating(abs(difference))
    total_sign = alternating(total)
    return 1 / (2 * pi) * (
        arb(difference_sign)
        * (transforms[left_mode] - transforms[right_mode])
        / difference
        - arb(total_sign)
        * (transforms[left_mode] + transforms[right_mode])
        / total
    )


def odd_comparison_diagonal(mode: int, a: arb, pi: arb) -> arb:
    point = 2 * arb(mode) * pi
    return (
        (arb(mode) * pi / a).log()
        + arb.const_euler()
        - point.ci()
        - point.si() / point
    )


def complete_odd_low_diagonal(
    boundary: int,
    a: arb,
    series_terms: int,
    log_two: arb,
    pi: arb,
) -> list[arb]:
    diagonal = []
    for index in range(boundary):
        components = matrix_entry_components(
            "yoshida",
            "odd",
            index,
            index,
            a,
            1,
            series_terms,
            log_two,
            pi,
        )
        diagonal.append(components["total"])
    return diagonal


def build_complete_low(
    boundary: int,
    diagonal: list[arb],
    transforms: list[arb],
    pi: arb,
) -> arb_mat:
    matrix = arb_mat(boundary, boundary)
    for row, left_mode in enumerate(range(1, boundary + 1)):
        matrix[row, row] = diagonal[row]
        for column, right_mode in enumerate(
            range(left_mode + 1, boundary + 1),
            start=row + 1,
        ):
            value = odd_convolution_off_diagonal(
                transforms,
                left_mode,
                right_mode,
                pi,
            )
            matrix[row, column] = value
            matrix[column, row] = value
    return matrix


def build_complete_cross(
    boundary: int,
    last_mode: int,
    transforms: list[arb],
    pi: arb,
) -> arb_mat:
    matrix = arb_mat(boundary, last_mode - boundary)
    for row, left_mode in enumerate(range(1, boundary + 1)):
        for column, right_mode in enumerate(range(boundary + 1, last_mode + 1)):
            matrix[row, column] = odd_convolution_off_diagonal(
                transforms,
                left_mode,
                right_mode,
                pi,
            )
    return matrix


def build_comparison_far(
    boundary: int,
    last_mode: int,
    transforms: list[arb],
    a: arb,
    pi: arb,
) -> arb_mat:
    size = last_mode - boundary
    matrix = arb_mat(size, size)
    for row, left_mode in enumerate(range(boundary + 1, last_mode + 1)):
        matrix[row, row] = odd_comparison_diagonal(left_mode, a, pi)
        for column, right_mode in enumerate(
            range(left_mode + 1, last_mode + 1),
            start=row + 1,
        ):
            value = odd_convolution_off_diagonal(
                transforms,
                left_mode,
                right_mode,
                pi,
            )
            matrix[row, column] = value
            matrix[column, row] = value
    return matrix


def main() -> int:
    args = parse_args()
    if args.boundary != 44:
        raise ValueError("FT4 keeps the frozen odd boundary equal to 44")
    if args.far_window <= 0:
        raise ValueError("far-window must be positive")
    if args.series_terms < 128:
        raise ValueError("series-terms must be at least 128")
    if args.arch_tail_terms < 16:
        raise ValueError("arch-tail-terms must be at least 16")
    if args.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")

    ctx.prec = args.precision_bits
    log_two = arb.const_log2()
    pi = arb.pi()
    a = right_band_endpoint(log_two)
    last_mode = args.boundary + args.far_window
    complete_transforms = [arb(0)]
    comparison_transforms = [arb(0)]
    for mode in range(1, last_mode + 1):
        complete_transforms.append(
            complete_sine_transform(
                mode,
                a,
                log_two,
                pi,
                args.arch_tail_terms,
            )
        )
        comparison_transforms.append(comparison_sine_transform(mode, pi))

    low_diagonal = complete_odd_low_diagonal(
        args.boundary,
        a,
        args.series_terms,
        log_two,
        pi,
    )
    low = build_complete_low(
        args.boundary,
        low_diagonal,
        complete_transforms,
        pi,
    )
    cross = build_complete_cross(
        args.boundary,
        last_mode,
        complete_transforms,
        pi,
    )
    comparison = build_comparison_far(
        args.boundary,
        last_mode,
        comparison_transforms,
        a,
        pi,
    )
    solution = comparison.solve(cross.transpose())
    finite_schur = cross * solution
    target = arb(fmpq(19, 1000)) * low - finite_schur
    target_record = lowest_eigenvalue_record(target)
    obstruction = bool(target_record["certified_negative_direction"])

    payload = {
        "experiment": "M100-FT4",
        "artifact": "fixed-endpoint-odd-comparison-finite-obstruction",
        "certification": (
            "ARB_FINITE_GALERKIN_OBSTRUCTION"
            if obstruction
            else "ARB_FINITE_GALERKIN_INCONCLUSIVE"
        ),
        "scope": (
            "The frozen odd cutoff-44 comparison-energy route only; this is "
            "not a complete-form inverse or global-positivity claim."
        ),
        "settings": {
            "boundary": args.boundary,
            "low_modes": [1, args.boundary],
            "far_modes": [args.boundary + 1, last_mode],
            "far_window": args.far_window,
            "series_terms": args.series_terms,
            "arch_tail_terms": args.arch_tail_terms,
            "precision_bits": args.precision_bits,
            "endpoint": interval_text(a),
        },
        "signed_identity": "F = E - s*I + P_2 - R",
        "low_complete_lowest": lowest_eigenvalue_record(low),
        "comparison_lowest": lowest_eigenvalue_record(comparison),
        "target_19_over_1000_lowest": target_record,
        "finite_galerkin_obstruction": obstruction,
        "conclusion": (
            "The desired FT4 comparison-energy reserve is impossible for "
            "the frozen projection because its finite Galerkin lower "
            "contribution already exceeds (19/1000) K in one direction."
            if obstruction
            else "The declared finite window does not decide the FT4 route."
        ),
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
