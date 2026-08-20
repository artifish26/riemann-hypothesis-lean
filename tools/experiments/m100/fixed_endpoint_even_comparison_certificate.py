#!/usr/bin/env python3
"""M100-FT3 Arb finite comparison-energy compression certificate.

The frozen low-plus-boundary block contains even Yoshida modes 0 through 44.
For each declared far window this script constructs:

* the complete low block K from certified diagonal entries and the exact
  convolution reconstruction;
* the complete coupling C from a closed first-row digamma formula; and
* Suzuki's local comparison-energy block E from exact Si/Ci formulas.

It then certifies positivity of (19/1000) K - C E^{-1} C^*, including an
explicit Galerkin residual prefix and a closed analytic upper matrix for the
remaining residual tail.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json

try:
    from flint import acb, arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "fixed_endpoint_even_comparison_certificate.py requires "
        "python-flint==0.8.0"
    ) from error

from coupled_first_prime_band_probe import (
    interval_text,
    lowest_eigenvalue_record,
    matrix_entry_components,
)
from form_weighted_coupling_probe import right_band_endpoint


def parse_ints(text: str) -> tuple[int, ...]:
    values = tuple(sorted({int(part) for part in text.split(",")}))
    if not values or values[0] <= 0:
        raise argparse.ArgumentTypeError("values must be positive integers")
    return values


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--boundary", type=int, default=44)
    parser.add_argument(
        "--far-windows",
        type=parse_ints,
        default=(32, 64, 128, 256),
    )
    parser.add_argument("--series-terms", type=int, default=65536)
    parser.add_argument("--arch-tail-terms", type=int, default=128)
    parser.add_argument("--precision-bits", type=int, default=192)
    parser.add_argument(
        "--residual-end",
        type=int,
        default=600,
        help="last residual mode summed explicitly before the analytic tail",
    )
    parser.add_argument(
        "--oscillatory-sum-end",
        type=int,
        default=20000,
    )
    return parser.parse_args()


def alternating(mode: int) -> int:
    return 1 if mode % 2 else -1


def complete_sine_transform(
    mode: int,
    a: arb,
    log_two: arb,
    pi: arb,
    tail_terms: int,
) -> arb:
    """Integral transform J_n whose convolution pairing gives F off diagonal."""

    wave_number = arb(mode) * pi / a
    quarter = arb(fmpq(1, 4))
    full_archimedean = acb(quarter, wave_number / 2).digamma().imag
    tail = arb(0)
    for index in range(tail_terms):
        decay = arb(2 * index) + arb(fmpq(1, 2))
        tail += (
            2
            * wave_number
            * (-2 * a * decay).exp()
            / (decay * decay + wave_number * wave_number)
        )
    first_omitted = arb(2 * tail_terms) + arb(fmpq(1, 2))
    tail_bound = (
        2
        * wave_number
        * (-2 * a * first_omitted).exp()
        / (first_omitted * first_omitted)
        / (1 - (-4 * a).exp())
    )
    archimedean_integral = full_archimedean - (
        tail + arb(0, tail_bound.upper())
    )
    pole_integral = (
        4
        * wave_number
        * (1 - a.cosh())
        / (wave_number * wave_number + arb(fmpq(1, 4)))
    )
    prime_integral = (
        -arb(2).sqrt()
        * log_two
        * (arb(mode) * pi * log_two / a).sin()
    )
    return pole_integral - archimedean_integral + prime_integral


def comparison_sine_transform(mode: int, pi: arb) -> arb:
    return -(2 * arb(mode) * pi).si()


def convolution_off_diagonal(
    transforms: list[arb],
    left: int,
    right: int,
    pi: arb,
) -> arb:
    if left == right:
        raise ValueError("off-diagonal reconstruction requires distinct modes")
    difference = left - right
    total = left + right
    left_scale = 1 / arb(2).sqrt() if left == 0 else arb(1)
    right_scale = 1 / arb(2).sqrt() if right == 0 else arb(1)
    difference_sign = alternating(abs(difference))
    total_sign = alternating(total)
    return left_scale * right_scale / (2 * pi) * (
        arb(difference_sign)
        * (transforms[left] - transforms[right])
        / arb(difference)
        + arb(total_sign)
        * (transforms[left] + transforms[right])
        / arb(total)
    )


def comparison_diagonal(mode: int, a: arb, pi: arb) -> arb:
    if mode == 0:
        return 1 - (2 * a).log()
    point = 2 * arb(mode) * pi
    return (
        (arb(mode) * pi / a).log()
        + arb.const_euler()
        - point.ci()
        + point.si() / point
    )


def complete_low_diagonal(
    boundary: int,
    a: arb,
    series_terms: int,
    log_two: arb,
    pi: arb,
) -> list[arb]:
    diagonal = []
    for mode in range(boundary + 1):
        components = matrix_entry_components(
            "yoshida",
            "even",
            mode,
            mode,
            a,
            1,
            series_terms,
            log_two,
            pi,
        )
        diagonal.append(components["total"])
    return diagonal


def build_low(
    boundary: int,
    diagonal: list[arb],
    transforms: list[arb],
    pi: arb,
) -> arb_mat:
    size = boundary + 1
    matrix = arb_mat(size, size)
    for left in range(size):
        matrix[left, left] = diagonal[left]
        for right in range(left + 1, size):
            value = convolution_off_diagonal(
                transforms,
                left,
                right,
                pi,
            )
            matrix[left, right] = value
            matrix[right, left] = value
    return matrix


def build_cross(
    boundary: int,
    last_mode: int,
    transforms: list[arb],
    pi: arb,
) -> arb_mat:
    low_size = boundary + 1
    far_size = last_mode - boundary
    matrix = arb_mat(low_size, far_size)
    for left in range(low_size):
        for column, right in enumerate(range(boundary + 1, last_mode + 1)):
            matrix[left, column] = convolution_off_diagonal(
                transforms,
                left,
                right,
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
    for row, left in enumerate(range(boundary + 1, last_mode + 1)):
        matrix[row, row] = comparison_diagonal(left, a, pi)
        for column, right in enumerate(
            range(left + 1, last_mode + 1),
            start=row + 1,
        ):
            value = convolution_off_diagonal(
                transforms,
                left,
                right,
                pi,
            )
            matrix[row, column] = value
            matrix[column, row] = value
    return matrix


def column_between_ranges(
    row_modes: range,
    column_mode: int,
    transforms: list[arb],
    pi: arb,
) -> arb_mat:
    column = arb_mat(len(row_modes), 1)
    for row, mode in enumerate(row_modes):
        column[row, 0] = convolution_off_diagonal(
            transforms,
            mode,
            column_mode,
            pi,
        )
    return column


def endpoint_vector(modes: range) -> arb_mat:
    vector = arb_mat(len(modes), 1)
    for row, mode in enumerate(modes):
        scale = 1 / arb(2).sqrt() if mode == 0 else arb(1)
        vector[row, 0] = arb(-1 if mode % 2 else 1) * scale
    return vector


def abs_upper(value: arb) -> arb:
    return abs(value).upper()


def oscillatory_inverse_square_tail(
    angle: arb,
    start: int,
    sum_end: int,
    *,
    cosine: bool,
) -> arb:
    if sum_end < start:
        raise ValueError("oscillatory-sum-end must not precede the tail start")
    total = arb(0)
    for mode in range(start, sum_end + 1):
        phase = arb(mode) * angle
        value = phase.cos() if cosine else phase.sin()
        total += value / (mode * mode)
    denominator = abs((angle / 2).sin())
    radius = 1 / (denominator * (sum_end + 1) ** 2)
    return total + arb(0, radius.upper())


def residual_tail_bound(
    low: arb_mat,
    finite_schur: arb_mat,
    solution: arb_mat,
    boundary: int,
    galerkin_last: int,
    residual_end: int,
    oscillatory_sum_end: int,
    complete_transforms: list[arb],
    comparison_transforms: list[arb],
    a: arb,
    log_two: arb,
    pi: arb,
    strict_target_sink: list[arb_mat] | None = None,
) -> dict[str, object]:
    low_modes = range(0, boundary + 1)
    band_modes = range(boundary + 1, galerkin_last + 1)
    if residual_end <= galerkin_last:
        raise ValueError("residual-end must exceed the Galerkin last mode")

    observed_gram = arb_mat(boundary + 1, boundary + 1)
    for mode in range(galerkin_last + 1, residual_end + 1):
        complete_column = column_between_ranges(
            low_modes,
            mode,
            complete_transforms,
            pi,
        )
        comparison_column = column_between_ranges(
            band_modes,
            mode,
            comparison_transforms,
            pi,
        )
        residual = complete_column - solution.transpose() * comparison_column
        observed_gram += residual * residual.transpose()

    low_endpoint = endpoint_vector(low_modes)
    band_endpoint = endpoint_vector(band_modes)
    endpoint_residual = low_endpoint - solution.transpose() * band_endpoint

    inverse_square_tail = arb.pi() * arb.pi() / 6
    for mode in range(1, residual_end + 1):
        inverse_square_tail -= arb(1) / (mode * mode)
    theta = pi * log_two / a
    sine_tail = oscillatory_inverse_square_tail(
        theta,
        residual_end + 1,
        oscillatory_sum_end,
        cosine=False,
    )
    cosine_double_tail = oscillatory_inverse_square_tail(
        2 * theta,
        residual_end + 1,
        oscillatory_sum_end,
        cosine=True,
    )
    sine_square_tail = (inverse_square_tail - cosine_double_tail) / 2
    prime_amplitude = arb(2).sqrt() * log_two
    main_tail = 1 / (pi * pi) * (
        (pi * pi / 4)
        * inverse_square_tail
        * (endpoint_residual * endpoint_residual.transpose())
        + prime_amplitude
        * prime_amplitude
        * sine_square_tail
        * (low_endpoint * low_endpoint.transpose())
        + (pi * prime_amplitude / 2)
        * sine_tail
        * (
            endpoint_residual * low_endpoint.transpose()
            + low_endpoint * endpoint_residual.transpose()
        )
    )

    variation = arb("0.450832848941026")
    remainder_transform_bound = 2 * variation * a / pi
    first_tail_mode = arb(residual_end + 1)
    comparison_bound = pi / 2 + 1 / (pi * first_tail_mode)
    complete_bound = (
        comparison_bound
        + prime_amplitude
        + remainder_transform_bound / first_tail_mode
    )

    moment_order = 4
    comparison_error_bound = 1 / pi
    delta_transform_bound = (
        prime_amplitude + remainder_transform_bound / first_tail_mode
    )
    structured_tail = arb_mat(boundary + 1, boundary + 1)
    low_last_moment = None
    band_last_moment = None
    for order in range(moment_order + 1):
        low_moment = arb_mat(boundary + 1, 1)
        band_moment = arb_mat(len(band_modes), 1)
        low_fixed_moment = arb_mat(boundary + 1, 1)
        band_fixed_moment = arb_mat(len(band_modes), 1)
        for row, mode in enumerate(low_modes):
            moment = arb(mode ** (2 * order))
            low_moment[row, 0] = low_endpoint[row, 0] * moment
            low_fixed_moment[row, 0] = (
                low_endpoint[row, 0]
                * arb(mode ** (2 * order + 1))
                * complete_transforms[mode]
            )
        for row, mode in enumerate(band_modes):
            moment = arb(mode ** (2 * order))
            band_moment[row, 0] = band_endpoint[row, 0] * moment
            band_fixed_moment[row, 0] = (
                band_endpoint[row, 0]
                * arb(mode ** (2 * order + 1))
                * comparison_transforms[mode]
            )
        moment_residual = low_moment - solution.transpose() * band_moment
        fixed_moment_residual = (
            low_fixed_moment - solution.transpose() * band_fixed_moment
        )
        if order == 0:
            inverse_fourth_tail = arb(1) / (3 * residual_end**3)
            structured_tail += inverse_fourth_tail / (pi * pi) * (
                comparison_error_bound
                * comparison_error_bound
                * (moment_residual * moment_residual.transpose())
                + remainder_transform_bound
                * remainder_transform_bound
                * (low_moment * low_moment.transpose())
                + fixed_moment_residual
                * fixed_moment_residual.transpose()
            )
        else:
            odd_square_tail = arb(1) / (
                (4 * order + 1) * residual_end ** (4 * order + 1)
            )
            even_square_tail = arb(1) / (
                (4 * order + 3) * residual_end ** (4 * order + 3)
            )
            structured_tail += 1 / (pi * pi) * (
                comparison_bound
                * comparison_bound
                * odd_square_tail
                * (moment_residual * moment_residual.transpose())
                + delta_transform_bound
                * delta_transform_bound
                * odd_square_tail
                * (low_moment * low_moment.transpose())
                + even_square_tail
                * (
                    fixed_moment_residual
                    * fixed_moment_residual.transpose()
                )
            )
        low_last_moment = low_moment
        band_last_moment = band_moment
    structured_tail *= 3 * (moment_order + 1)

    if low_last_moment is None or band_last_moment is None:
        raise ArithmeticError("missing terminal moment vectors")
    geometric_power = 2 * (moment_order + 1)
    low_geometric_envelope = arb_mat(boundary + 1, 1)
    for row, mode in enumerate(low_modes):
        endpoint_abs = abs_upper(low_endpoint[row, 0])
        fixed_transform = abs_upper(complete_transforms[mode])
        denominator_factor = 1 - arb(fmpq(mode * mode, (residual_end + 1) ** 2))
        low_geometric_envelope[row, 0] = (
            endpoint_abs
            * arb(mode**geometric_power)
            * (
                complete_bound
                + arb(mode) * fixed_transform / first_tail_mode
            )
            / denominator_factor
            / pi
        )

    band_geometric_envelope = arb_mat(len(band_modes), 1)
    for row, mode in enumerate(band_modes):
        endpoint_abs = abs_upper(band_endpoint[row, 0])
        fixed_transform = abs_upper(comparison_transforms[mode])
        denominator_factor = 1 - arb(fmpq(mode * mode, (residual_end + 1) ** 2))
        band_geometric_envelope[row, 0] = (
            endpoint_abs
            * arb(mode**geometric_power)
            * (
                comparison_bound
                + arb(mode) * fixed_transform / first_tail_mode
            )
            / denominator_factor
            / pi
        )

    geometric_envelope = arb_mat(boundary + 1, 1)
    for row in range(boundary + 1):
        value = low_geometric_envelope[row, 0]
        for band_row in range(len(band_modes)):
            value += (
                abs_upper(solution[band_row, row])
                * band_geometric_envelope[band_row, 0]
            )
        geometric_envelope[row, 0] = value

    geometric_envelope_sum = arb(0)
    geometric_diagonal_envelope = arb_mat(boundary + 1, boundary + 1)
    for row in range(boundary + 1):
        geometric_envelope_sum += geometric_envelope[row, 0]
        geometric_diagonal_envelope[row, row] = geometric_envelope[row, 0]
    geometric_square_power = 2 * (2 * moment_order + 3)
    geometric_tail_bound = arb(1) / (
        (geometric_square_power - 1)
        * residual_end ** (geometric_square_power - 1)
    )
    geometric_tail = (
        geometric_envelope_sum
        * geometric_tail_bound
        * geometric_diagonal_envelope
    )

    secondary_alpha = arb(fmpq(1, 10))
    remainder_tail = (
        (1 + secondary_alpha) * structured_tail
        + (1 + 1 / secondary_alpha) * geometric_tail
    )
    main_alpha = arb(fmpq(1, 20))
    analytic_tail = (
        (1 + main_alpha) * main_tail
        + (1 + 1 / main_alpha) * remainder_tail
    )
    full_upper = (
        finite_schur
        + arb(fmpq(1, 5)) * observed_gram
        + arb(fmpq(1, 5)) * analytic_tail
    )
    target = arb(fmpq(19, 1000)) * low - full_upper
    target_record = lowest_eigenvalue_record(target)
    eta_even = fmpq(1, 1_000_000_000)
    strict_target = (
        arb(fmpq(19, 1000)) * (1 - arb(eta_even)) * low - full_upper
    )
    if strict_target_sink is not None:
        strict_target_sink.append(strict_target)
    strict_target_record = lowest_eigenvalue_record(strict_target)
    return {
        "galerkin_last_mode": galerkin_last,
        "explicit_residual_modes": [galerkin_last + 1, residual_end],
        "main_tail_alpha": "1/20",
        "structured_tail_alpha": "1/10",
        "moment_order": moment_order,
        "oscillatory_sum_end": oscillatory_sum_end,
        "inverse_square_tail": interval_text(inverse_square_tail),
        "sine_tail": interval_text(sine_tail),
        "sine_square_tail": interval_text(sine_square_tail),
        "geometric_envelope_sum": interval_text(geometric_envelope_sum),
        "full_target_19_over_1000_lowest": target_record,
        "eta_even": "1/1000000000",
        "strict_target_lowest": strict_target_record,
        "full_residual_certificate_pass": bool(
            strict_target_record["certified_positive_finite_ritz"]
        ),
    }


def main() -> int:
    args = parse_args()
    if args.boundary != 44:
        raise ValueError("FT3 keeps the frozen boundary equal to 44")
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
    galerkin_last = args.boundary + max(args.far_windows)
    if args.residual_end <= galerkin_last:
        raise ValueError("residual-end must exceed the largest finite window")
    if args.oscillatory_sum_end <= args.residual_end:
        raise ValueError("oscillatory-sum-end must exceed residual-end")
    last_mode = max(galerkin_last, args.residual_end)

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

    low_diagonal = complete_low_diagonal(
        args.boundary,
        a,
        args.series_terms,
        log_two,
        pi,
    )
    low = build_low(
        args.boundary,
        low_diagonal,
        complete_transforms,
        pi,
    )
    low_record = lowest_eigenvalue_record(low)
    records = []
    final_solution = None
    final_schur = None
    for window in args.far_windows:
        window_last_mode = args.boundary + window
        cross = build_cross(
            args.boundary,
            window_last_mode,
            complete_transforms,
            pi,
        )
        comparison = build_comparison_far(
            args.boundary,
            window_last_mode,
            comparison_transforms,
            a,
            pi,
        )
        comparison_record = lowest_eigenvalue_record(comparison)
        solution = comparison.solve(cross.transpose())
        finite_schur = cross * solution
        if window == max(args.far_windows):
            final_solution = solution
            final_schur = finite_schur
        target = arb(fmpq(19, 1000)) * low - finite_schur
        target_record = lowest_eigenvalue_record(target)
        records.append(
            {
                "far_window": window,
                "last_mode": window_last_mode,
                "comparison_lowest": comparison_record,
                "target_19_over_1000_lowest": target_record,
                "finite_compression_pass": bool(
                    target_record["certified_positive_finite_ritz"]
                ),
            }
        )

    if final_solution is None or final_schur is None:
        raise ArithmeticError("missing final Galerkin system")
    tail_record = residual_tail_bound(
        low,
        final_schur,
        final_solution,
        args.boundary,
        galerkin_last,
        args.residual_end,
        args.oscillatory_sum_end,
        complete_transforms,
        comparison_transforms,
        a,
        log_two,
        pi,
    )
    full_pass = bool(tail_record["full_residual_certificate_pass"])

    payload = {
        "experiment": "M100-FT3",
        "artifact": "fixed-endpoint-even-comparison-residual-certificate",
        "certification": (
            "ARB_FULL_RESIDUAL_CERTIFICATE"
            if full_pass
            else "ARB_FULL_RESIDUAL_INCONCLUSIVE"
        ),
        "scope": (
            "One fixed endpoint, the frozen cutoff-44 even Yoshida block, "
            "and its complete infinite far complement."
        ),
        "settings": {
            "boundary": args.boundary,
            "far_windows": args.far_windows,
            "series_terms": args.series_terms,
            "arch_tail_terms": args.arch_tail_terms,
            "precision_bits": args.precision_bits,
            "residual_end": args.residual_end,
            "oscillatory_sum_end": args.oscillatory_sum_end,
            "endpoint": interval_text(a),
        },
        "signed_identity": "F = E - s*I + P_2 - R",
        "low_complete_lowest": low_record,
        "windows": records,
        "residual_tail": tail_record,
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
