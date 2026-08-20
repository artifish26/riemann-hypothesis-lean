#!/usr/bin/env python3
"""M100-DF1 Arb complete odd sharp-comparison certificate.

The frozen low block contains odd Yoshida modes 1 through 44.  This script
constructs the complete low block K, its coupling to odd far modes, and
Suzuki's comparison energy E.  It then certifies the complete infinite-tail
bound at the DF0 coefficient 2/5, using modes 45 through 300, the explicit
residual prefix 301 through 600, and an analytic tail from mode 601 onward.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

try:
    from flint import arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "fixed_endpoint_odd_sharp_comparison_certificate.py requires "
        "python-flint==0.8.0"
    ) from error

from coupled_first_prime_band_probe import (
    interval_text,
    lowest_eigenvalue_record,
)
from fixed_endpoint_even_comparison_certificate import (
    abs_upper,
    comparison_sine_transform,
    complete_sine_transform,
    parse_ints,
)
from fixed_endpoint_odd_comparison_obstruction import (
    build_comparison_far,
    build_complete_cross,
    build_complete_low,
    complete_odd_low_diagonal,
    odd_convolution_off_diagonal,
)
from form_weighted_coupling_probe import right_band_endpoint


def parse_fraction(text: str) -> Fraction:
    try:
        value = Fraction(text)
    except ValueError as error:
        raise argparse.ArgumentTypeError("expected a rational number") from error
    if value <= 0:
        raise argparse.ArgumentTypeError("rational values must be positive")
    return value


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--boundary", type=int, default=44)
    parser.add_argument(
        "--far-windows",
        type=parse_ints,
        default=(32, 64, 128, 256),
    )
    parser.add_argument("--series-terms", type=int, default=16384)
    parser.add_argument("--arch-tail-terms", type=int, default=128)
    parser.add_argument("--precision-bits", type=int, default=192)
    parser.add_argument("--residual-end", type=int, default=600)
    parser.add_argument("--oscillatory-sum-end", type=int, default=20000)
    parser.add_argument(
        "--comparison-coefficient",
        type=parse_fraction,
        default=Fraction(2, 5),
    )
    parser.add_argument(
        "--eta",
        type=parse_fraction,
        default=Fraction(1, 1_000_000_000),
    )
    return parser.parse_args()


def arb_fraction(value: Fraction) -> arb:
    return arb(fmpq(value.numerator, value.denominator))


def odd_column_between_ranges(
    row_modes: range,
    column_mode: int,
    transforms: list[arb],
    pi: arb,
) -> arb_mat:
    column = arb_mat(len(row_modes), 1)
    for row, mode in enumerate(row_modes):
        column[row, 0] = odd_convolution_off_diagonal(
            transforms,
            mode,
            column_mode,
            pi,
        )
    return column


def odd_sign(mode: int) -> arb:
    return arb(-1 if mode % 2 else 1)


def odd_truncated_tail_column(
    row_modes: range,
    column_mode: int,
    transforms: list[arb],
    pi: arb,
    moment_order: int,
) -> arb_mat:
    """Order-four geometric expansion of an odd off-diagonal column."""

    column = arb_mat(len(row_modes), 1)
    column_sign = arb(1 if column_mode % 2 else -1)
    n = arb(column_mode)
    column_transform = transforms[column_mode]
    for row, mode in enumerate(row_modes):
        sign = column_sign * odd_sign(mode)
        value = arb(0)
        for order in range(moment_order + 1):
            value += sign / pi * (
                -arb(mode ** (2 * order))
                * transforms[mode]
                / n ** (2 * order + 1)
                + arb(mode ** (2 * order + 1))
                * column_transform
                / n ** (2 * order + 2)
            )
        column[row, 0] = value
    return column


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
    comparison_coefficient: Fraction,
    eta: Fraction,
    strict_target_sink: list[arb_mat] | None = None,
) -> dict[str, object]:
    """Certify the odd residual prefix and its complete analytic tail.

    For a fixed positive odd mode m<n, the product-to-sum identity is

      A(m,n) = d_n*(-1)^m/pi *
        (m*J_n/(n^2-m^2) - n*J_m/(n^2-m^2)),

    where |d_n|=1.  Expanding (1-m^2/n^2)^(-1) through order four gives one
    exact inverse-square leading vector, fourteen higher structured vectors,
    and an n^(-11) geometric remainder.  The signs d_n disappear in each
    Gram upper bound.
    """

    low_modes = range(1, boundary + 1)
    band_modes = range(boundary + 1, galerkin_last + 1)
    low_size = len(low_modes)
    if residual_end <= galerkin_last:
        raise ValueError("residual-end must exceed the Galerkin last mode")
    if oscillatory_sum_end <= residual_end:
        raise ValueError("oscillatory-sum-end must exceed residual-end")

    observed_gram = arb_mat(low_size, low_size)
    for mode in range(galerkin_last + 1, residual_end + 1):
        complete_column = odd_column_between_ranges(
            low_modes,
            mode,
            complete_transforms,
            pi,
        )
        comparison_column = odd_column_between_ranges(
            band_modes,
            mode,
            comparison_transforms,
            pi,
        )
        residual = complete_column - solution.transpose() * comparison_column
        observed_gram += residual * residual.transpose()

    inverse_square_tail = arb.pi() * arb.pi() / 6
    for mode in range(1, residual_end + 1):
        inverse_square_tail -= arb(1) / (mode * mode)

    first_tail_mode = arb(residual_end + 1)
    prime_amplitude = arb(2).sqrt() * log_two
    variation = arb("0.450832848941026")
    remainder_transform_bound = 2 * variation * a / pi
    comparison_bound = pi / 2 + 1 / (pi * first_tail_mode)
    delta_transform_bound = (
        prime_amplitude + remainder_transform_bound / first_tail_mode
    )
    complete_bound = comparison_bound + delta_transform_bound

    moment_order = 4
    main_tail = arb_mat(low_size, low_size)
    structured_tail = arb_mat(low_size, low_size)
    for order in range(moment_order + 1):
        low_fixed = arb_mat(low_size, 1)
        band_fixed = arb_mat(len(band_modes), 1)
        low_moment = arb_mat(low_size, 1)
        band_moment = arb_mat(len(band_modes), 1)

        for row, mode in enumerate(low_modes):
            sign = odd_sign(mode)
            low_fixed[row, 0] = (
                sign * arb(mode ** (2 * order)) * complete_transforms[mode]
            )
            low_moment[row, 0] = sign * arb(mode ** (2 * order + 1))
        for row, mode in enumerate(band_modes):
            sign = odd_sign(mode)
            band_fixed[row, 0] = (
                sign
                * arb(mode ** (2 * order))
                * comparison_transforms[mode]
            )
            band_moment[row, 0] = sign * arb(mode ** (2 * order + 1))

        fixed_residual = low_fixed - solution.transpose() * band_fixed
        moment_residual = low_moment - solution.transpose() * band_moment

        if order == 0:
            main_tail = inverse_square_tail / (pi * pi) * (
                fixed_residual * fixed_residual.transpose()
            )
        else:
            fixed_square_tail = arb(1) / (
                (4 * order + 1) * residual_end ** (4 * order + 1)
            )
            structured_tail += fixed_square_tail * (
                fixed_residual * fixed_residual.transpose()
            ) / (pi * pi)

        moment_square_tail = arb(1) / (
            (4 * order + 3) * residual_end ** (4 * order + 3)
        )
        structured_tail += moment_square_tail / (pi * pi) * (
            comparison_bound
            * comparison_bound
            * (moment_residual * moment_residual.transpose())
            + delta_transform_bound
            * delta_transform_bound
            * (low_moment * low_moment.transpose())
        )

    structured_component_count = 3 * (moment_order + 1) - 1
    structured_tail *= structured_component_count

    geometric_power = 2 * (moment_order + 1)
    low_geometric_envelope = arb_mat(low_size, 1)
    for row, mode in enumerate(low_modes):
        denominator_factor = 1 - arb(
            fmpq(mode * mode, (residual_end + 1) ** 2)
        )
        low_geometric_envelope[row, 0] = (
            arb(mode**geometric_power)
            * (
                abs_upper(complete_transforms[mode])
                + arb(mode) * complete_bound / first_tail_mode
            )
            / denominator_factor
            / pi
        )

    band_geometric_envelope = arb_mat(len(band_modes), 1)
    for row, mode in enumerate(band_modes):
        denominator_factor = 1 - arb(
            fmpq(mode * mode, (residual_end + 1) ** 2)
        )
        band_geometric_envelope[row, 0] = (
            arb(mode**geometric_power)
            * (
                abs_upper(comparison_transforms[mode])
                + arb(mode) * comparison_bound / first_tail_mode
            )
            / denominator_factor
            / pi
        )

    geometric_envelope = arb_mat(low_size, 1)
    for row in range(low_size):
        value = low_geometric_envelope[row, 0]
        for band_row in range(len(band_modes)):
            value += (
                abs_upper(solution[band_row, row])
                * band_geometric_envelope[band_row, 0]
            )
        geometric_envelope[row, 0] = value

    geometric_envelope_sum = arb(0)
    geometric_diagonal_envelope = arb_mat(low_size, low_size)
    for row in range(low_size):
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

    tail_remainder_checks = []
    for mode in (residual_end + 1, residual_end + 2):
        exact_complete = odd_column_between_ranges(
            low_modes,
            mode,
            complete_transforms,
            pi,
        )
        exact_comparison = odd_column_between_ranges(
            band_modes,
            mode,
            comparison_transforms,
            pi,
        )
        exact_residual = (
            exact_complete - solution.transpose() * exact_comparison
        )
        truncated_complete = odd_truncated_tail_column(
            low_modes,
            mode,
            complete_transforms,
            pi,
            moment_order,
        )
        truncated_comparison = odd_truncated_tail_column(
            band_modes,
            mode,
            comparison_transforms,
            pi,
            moment_order,
        )
        truncated_residual = (
            truncated_complete
            - solution.transpose() * truncated_comparison
        )
        maximum_ratio = arb(0)
        for row in range(low_size):
            remainder = abs(
                exact_residual[row, 0] - truncated_residual[row, 0]
            ).upper()
            bound = (
                geometric_envelope[row, 0] / arb(mode**geometric_power)
                / mode
            ).lower()
            if not remainder < bound:
                raise ArithmeticError(
                    "odd analytic-tail remainder check failed at "
                    f"mode {mode}, row {row}"
                )
            ratio = remainder / bound
            if ratio > maximum_ratio:
                maximum_ratio = ratio
        tail_remainder_checks.append(
            {
                "mode": mode,
                "certified": True,
                "maximum_bound_ratio": interval_text(maximum_ratio),
            }
        )

    structured_alpha = arb(fmpq(1, 10))
    remainder_tail = (
        (1 + structured_alpha) * structured_tail
        + (1 + 1 / structured_alpha) * geometric_tail
    )
    main_alpha = arb(fmpq(1, 20))
    analytic_tail = (
        (1 + main_alpha) * main_tail
        + (1 + 1 / main_alpha) * remainder_tail
    )

    energy_inverse_bound = arb(fmpq(1, 5))
    full_upper = (
        finite_schur
        + energy_inverse_bound * observed_gram
        + energy_inverse_bound * analytic_tail
    )
    coefficient = arb_fraction(comparison_coefficient)
    target = coefficient * low - full_upper
    target_record = lowest_eigenvalue_record(target)
    strict_target = coefficient * (1 - arb_fraction(eta)) * low - full_upper
    if strict_target_sink is not None:
        strict_target_sink.append(strict_target)
    strict_target_record = lowest_eigenvalue_record(strict_target)

    return {
        "galerkin_last_mode": galerkin_last,
        "explicit_residual_modes": [galerkin_last + 1, residual_end],
        "analytic_tail_modes": [residual_end + 1, "infinity"],
        "odd_tail_identity": (
            "A(m,n)=d_n*(-1)^m/pi*"
            "(m*J_n/(n^2-m^2)-n*J_m/(n^2-m^2))"
        ),
        "main_tail_alpha": "1/20",
        "structured_tail_alpha": "1/10",
        "structured_component_count": structured_component_count,
        "moment_order": moment_order,
        "oscillatory_sum_end": oscillatory_sum_end,
        "inverse_square_tail": interval_text(inverse_square_tail),
        "geometric_envelope_sum": interval_text(geometric_envelope_sum),
        "tail_remainder_checks": tail_remainder_checks,
        "comparison_coefficient": str(comparison_coefficient),
        "full_target_lowest": target_record,
        "eta_odd": str(eta),
        "strict_target_lowest": strict_target_record,
        "full_residual_certificate_pass": bool(
            strict_target_record["certified_positive_finite_ritz"]
        ),
    }


def main() -> int:
    args = parse_args()
    if args.boundary != 44:
        raise ValueError("DF1 keeps the frozen odd boundary equal to 44")
    if args.comparison_coefficient != Fraction(2, 5):
        raise ValueError("DF1 freezes comparison-coefficient at 2/5")
    if args.eta != Fraction(1, 1_000_000_000):
        raise ValueError("DF1 freezes eta at 1/1000000000")
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
    last_mode = args.residual_end + 2

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
    low_record = lowest_eigenvalue_record(low)

    records = []
    final_solution = None
    final_schur = None
    coefficient = arb_fraction(args.comparison_coefficient)
    for window in args.far_windows:
        window_last_mode = args.boundary + window
        cross = build_complete_cross(
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
        target = coefficient * low - finite_schur
        target_record = lowest_eigenvalue_record(target)
        records.append(
            {
                "far_window": window,
                "last_mode": window_last_mode,
                "comparison_lowest": comparison_record,
                "target_lowest": target_record,
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
        args.comparison_coefficient,
        args.eta,
    )
    full_pass = bool(tail_record["full_residual_certificate_pass"])

    payload = {
        "experiment": "M100-DF1",
        "artifact": "fixed-endpoint-odd-sharp-comparison-residual-certificate",
        "certification": (
            "ARB_FULL_RESIDUAL_CERTIFICATE"
            if full_pass
            else "ARB_FULL_RESIDUAL_INCONCLUSIVE"
        ),
        "scope": (
            "One fixed endpoint, the frozen cutoff-44 odd Yoshida block, "
            "and its complete infinite far complement."
        ),
        "settings": {
            "boundary": args.boundary,
            "low_modes": [1, args.boundary],
            "far_windows": args.far_windows,
            "series_terms": args.series_terms,
            "arch_tail_terms": args.arch_tail_terms,
            "precision_bits": args.precision_bits,
            "residual_end": args.residual_end,
            "oscillatory_sum_end": args.oscillatory_sum_end,
            "comparison_coefficient": str(args.comparison_coefficient),
            "eta": str(args.eta),
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
