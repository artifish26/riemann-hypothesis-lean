#!/usr/bin/env python3
"""M100-DF5A Arb endpoint full-form coercivity certificate.

This artifact rebuilds only the frozen cutoff-44 low matrices at the endpoint
``a_star``.  It certifies the rational matrix bounds required by DF5A and then
performs the remaining coercivity assembly with exact rational arithmetic.
The already closed FT3 and DF1 complete-tail certificates are inputs; this
script neither reruns nor enlarges either infinite-tail calculation.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

try:
    import flint
    from flint import arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "df5a_endpoint_coercivity_certificate.py requires "
        "python-flint==0.8.0"
    ) from error

from coupled_first_prime_band_probe import interval_text, lowest_eigenvalue_record
from fixed_endpoint_even_comparison_certificate import (
    build_low,
    complete_low_diagonal,
    complete_sine_transform,
)
from fixed_endpoint_odd_comparison_obstruction import (
    build_complete_low,
    complete_odd_low_diagonal,
)
from form_weighted_coupling_probe import right_band_endpoint


BOUNDARY = 44
SERIES_TERMS = 16_384
ARCH_TAIL_TERMS = 128
ALLOWED_PRECISIONS = (192, 256)

EVEN_K_LOWER = Fraction(1, 25_000)
ODD_K_LOWER = Fraction(1, 200)
ODD_K_UPPER = Fraction(5, 1)

FT3_COMPARISON_COEFFICIENT = Fraction(19, 1_000)
DF0_INVERSE_ORDER_COEFFICIENT = Fraction(5, 2)
DF0_FAR_L2_LOWER = Fraction(2, 1)
DF1_ETA = Fraction(1, 1_000_000_000)
DF1_STRICT_TARGET_LOWER = Fraction(1, 500)

EVEN_RHO = Fraction(1, 20)
ODD_RHO = Fraction(999, 1_000)
EVEN_SQRT_WEAKENING = Fraction(3, 4)
ODD_SQRT_WEAKENING = Fraction(1, 2_000)
COMMON_ENDPOINT_COERCIVITY = Fraction(1, 400_000)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--precision-bits",
        type=int,
        choices=ALLOWED_PRECISIONS,
        required=True,
    )
    return parser.parse_args()


def arb_fraction(value: Fraction) -> arb:
    return arb(fmpq(value.numerator, value.denominator))


def fraction_text(value: Fraction) -> str:
    return str(value)


def shift_from_identity(
    matrix: arb_mat,
    identity_coefficient: Fraction,
    matrix_coefficient: int,
) -> arb_mat:
    """Return ``identity_coefficient*I + matrix_coefficient*matrix``."""

    if matrix.nrows() != matrix.ncols():
        raise ValueError("shift requires a square matrix")
    if matrix_coefficient not in (-1, 1):
        raise ValueError("matrix coefficient must be -1 or 1")
    size = matrix.nrows()
    result = arb_mat(size, size)
    identity_value = arb_fraction(identity_coefficient)
    for row in range(size):
        for column in range(size):
            value = matrix_coefficient * matrix[row, column]
            if row == column:
                value += identity_value
            result[row, column] = value
    return result


def build_endpoint_matrices() -> tuple[arb, arb_mat, arb_mat]:
    log_two = arb.const_log2()
    pi = arb.pi()
    endpoint = right_band_endpoint(log_two)

    complete_transforms = [arb(0)]
    for mode in range(1, BOUNDARY + 1):
        complete_transforms.append(
            complete_sine_transform(
                mode,
                endpoint,
                log_two,
                pi,
                ARCH_TAIL_TERMS,
            )
        )

    even_diagonal = complete_low_diagonal(
        BOUNDARY,
        endpoint,
        SERIES_TERMS,
        log_two,
        pi,
    )
    even_matrix = build_low(
        BOUNDARY,
        even_diagonal,
        complete_transforms,
        pi,
    )

    odd_diagonal = complete_odd_low_diagonal(
        BOUNDARY,
        endpoint,
        SERIES_TERMS,
        log_two,
        pi,
    )
    odd_matrix = build_complete_low(
        BOUNDARY,
        odd_diagonal,
        complete_transforms,
        pi,
    )
    return endpoint, even_matrix, odd_matrix


def finite_matrix_records(
    even_matrix: arb_mat,
    odd_matrix: arb_mat,
) -> dict[str, object]:
    even_lower_record = lowest_eigenvalue_record(
        shift_from_identity(even_matrix, -EVEN_K_LOWER, 1)
    )
    odd_lower_record = lowest_eigenvalue_record(
        shift_from_identity(odd_matrix, -ODD_K_LOWER, 1)
    )
    odd_upper_record = lowest_eigenvalue_record(
        shift_from_identity(odd_matrix, ODD_K_UPPER, -1)
    )
    certified = all(
        bool(record["certified_positive_finite_ritz"])
        for record in (even_lower_record, odd_lower_record, odd_upper_record)
    )
    return {
        "even_K_minus_1_over_25000_I_lowest": even_lower_record,
        "odd_K_minus_1_over_200_I_lowest": odd_lower_record,
        "five_I_minus_odd_K_lowest": odd_upper_record,
        "rational_finite_block_bounds_pass": certified,
    }


def exact_assembly_record() -> dict[str, object]:
    even_actual_coefficient = (
        DF0_INVERSE_ORDER_COEFFICIENT * FT3_COMPARISON_COEFFICIENT
    )
    odd_excess_over_target = (1 - DF1_ETA) - ODD_RHO
    odd_conversion_margin = (
        DF0_INVERSE_ORDER_COEFFICIENT * DF1_STRICT_TARGET_LOWER
        - ODD_K_UPPER * odd_excess_over_target
    )

    even_square_margin = (1 - EVEN_SQRT_WEAKENING) ** 2 - EVEN_RHO
    odd_square_margin = (1 - ODD_SQRT_WEAKENING) ** 2 - ODD_RHO
    even_coercivity = EVEN_SQRT_WEAKENING * EVEN_K_LOWER
    odd_coercivity = ODD_SQRT_WEAKENING * ODD_K_LOWER

    checks = {
        "even_actual_form_weakened_to_rho": even_actual_coefficient < EVEN_RHO,
        "odd_actual_form_weakened_to_rho": odd_conversion_margin > 0,
        "even_sqrt_weakened_exactly": even_square_margin > 0,
        "odd_sqrt_weakened_exactly": odd_square_margin > 0,
        "even_far_term_not_limiting": (
            EVEN_SQRT_WEAKENING * DF0_FAR_L2_LOWER >= even_coercivity
        ),
        "odd_far_term_not_limiting": (
            ODD_SQRT_WEAKENING * DF0_FAR_L2_LOWER >= odd_coercivity
        ),
        "common_constant_below_even": (
            COMMON_ENDPOINT_COERCIVITY <= even_coercivity
        ),
        "common_constant_equals_odd": (
            COMMON_ENDPOINT_COERCIVITY == odd_coercivity
        ),
    }
    return {
        "closed_inputs": {
            "FT3_even_comparison_coefficient": fraction_text(
                FT3_COMPARISON_COEFFICIENT
            ),
            "DF0_inverse_order_coefficient": fraction_text(
                DF0_INVERSE_ORDER_COEFFICIENT
            ),
            "DF0_far_L2_lower": fraction_text(DF0_FAR_L2_LOWER),
            "DF1_eta": fraction_text(DF1_ETA),
            "DF1_strict_target_exact_rational_lower": fraction_text(
                DF1_STRICT_TARGET_LOWER
            ),
        },
        "even_actual_coefficient": fraction_text(even_actual_coefficient),
        "even_rho": fraction_text(EVEN_RHO),
        "odd_excess_over_target": fraction_text(odd_excess_over_target),
        "odd_conversion_margin": fraction_text(odd_conversion_margin),
        "odd_rho": fraction_text(ODD_RHO),
        "even_sqrt_square_margin": fraction_text(even_square_margin),
        "odd_sqrt_square_margin": fraction_text(odd_square_margin),
        "even_full_form_coercivity": fraction_text(even_coercivity),
        "odd_full_form_coercivity": fraction_text(odd_coercivity),
        "common_endpoint_coercivity": fraction_text(
            COMMON_ENDPOINT_COERCIVITY
        ),
        "checks": checks,
        "exact_assembly_pass": all(checks.values()),
    }


def main() -> int:
    args = parse_args()
    if flint.__version__ != "0.8.0":
        raise RuntimeError("DF5A freezes python-flint at version 0.8.0")
    ctx.prec = args.precision_bits

    endpoint, even_matrix, odd_matrix = build_endpoint_matrices()
    matrix_records = finite_matrix_records(even_matrix, odd_matrix)
    assembly = exact_assembly_record()
    certified = bool(matrix_records["rational_finite_block_bounds_pass"]) and bool(
        assembly["exact_assembly_pass"]
    )

    payload = {
        "experiment": "M100-DF5A",
        "artifact": "endpoint-full-form-coercivity-certificate",
        "certification": (
            "ARB_DF5A_ENDPOINT_COERCIVITY_CERTIFICATE"
            if certified
            else "ARB_DF5A_ENDPOINT_COERCIVITY_INCONCLUSIVE"
        ),
        "scope": (
            "The frozen endpoint a_star and cutoff-44 even and odd low blocks; "
            "closed FT3 and DF1 complete-tail certificates are not rerun."
        ),
        "settings": {
            "boundary": BOUNDARY,
            "series_terms": SERIES_TERMS,
            "arch_tail_terms": ARCH_TAIL_TERMS,
            "precision_bits": args.precision_bits,
            "python_flint_version": flint.__version__,
            "endpoint": interval_text(endpoint),
        },
        "finite_matrix_certificates": matrix_records,
        "exact_full_form_assembly": assembly,
        "endpoint_coercivity_certificate_pass": certified,
    }
    print(json.dumps(payload, indent=2))
    return 0 if certified else 1


if __name__ == "__main__":
    raise SystemExit(main())
