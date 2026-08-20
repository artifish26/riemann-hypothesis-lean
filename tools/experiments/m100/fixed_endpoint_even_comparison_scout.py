#!/usr/bin/env python3
"""M100-FT3 frozen even comparison-energy compression scout.

This script is deliberately midpoint-only.  It evaluates the complete form
and Suzuki local comparison energy in the fixed even Yoshida basis by
Gauss-Legendre quadrature, then reports finite-compression generalized Schur
ratios.  It never treats a finite far window as an infinite-tail certificate.

The signed prime convention is the X20 convention:

    P_2 = -(log(2)/sqrt(2)) * (S_log(2) + S_log(2)^*).

Suzuki equation (2.5) therefore reads F = E - s*I + P_2 - R, so the
comparison-energy matrix is reconstructed as E = F + s*I - P_2 + R.
"""

from __future__ import annotations

import argparse
import json
import math

import numpy as np


EULER_GAMMA = 0.577215664901532860606512090082402431


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
        default=(1, 2, 4, 8, 16, 32),
    )
    parser.add_argument(
        "--quadrature-orders",
        type=parse_ints,
        default=(256, 512, 1024),
    )
    parser.add_argument(
        "--galerkin-window",
        type=int,
        default=0,
        help=(
            "optional first far-window size whose Galerkin residual is "
            "measured on the remaining assembled modes"
        ),
    )
    return parser.parse_args()


def right_band_endpoint() -> float:
    log_two = math.log(2.0)
    return (
        log_two
        + math.sqrt(log_two * log_two + 4.0 * math.exp(-2.0 * math.sqrt(2.0) * log_two))
    ) / 4.0


def _cosine_integral_matrix(
    wave_number: np.ndarray,
    phase: np.ndarray,
    displacement: float,
    zero_mask: np.ndarray,
) -> np.ndarray:
    lower = -1.0
    upper = 1.0 - displacement
    safe_wave_number = np.where(zero_mask, 1.0, wave_number)
    ordinary = (
        np.sin(wave_number * upper + phase)
        - np.sin(wave_number * lower + phase)
    ) / safe_wave_number
    zero_value = np.cos(phase) * (upper - lower)
    return np.where(zero_mask, zero_value, ordinary)


def symmetric_correlation_matrix(
    mode_count: int,
    displacement: float,
) -> np.ndarray:
    """Return the even Yoshida symmetric correlation at 0 <= d <= 2."""

    frequency = np.arange(mode_count, dtype=float) * math.pi
    left = frequency[:, None]
    right = frequency[None, :]
    phase = left * displacement
    difference = left - right
    total = left + right
    diagonal = np.eye(mode_count, dtype=bool)
    zero_total = np.zeros((mode_count, mode_count), dtype=bool)
    zero_total[0, 0] = True
    difference_term = _cosine_integral_matrix(
        difference,
        phase,
        displacement,
        diagonal,
    )
    total_term = _cosine_integral_matrix(
        total,
        phase,
        displacement,
        zero_total,
    )
    scale = np.ones(mode_count)
    scale[0] = 1.0 / math.sqrt(2.0)
    one_sided = (
        scale[:, None]
        * scale[None, :]
        * (difference_term + total_term)
        / 2.0
    )
    return (one_sided + one_sided.T) / 2.0


def remainder_second_derivative(t: float) -> float:
    if t < 1.0e-4:
        return -7.0 / 4.0 - t / 48.0 - 9.0 * t * t / 32.0
    return (
        -2.0 * math.cosh(t / 2.0)
        + math.exp(t / 2.0) / (2.0 * math.sinh(t))
        - 1.0 / (2.0 * t)
    )


def build_matrices(mode_count: int, quadrature_order: int) -> tuple[np.ndarray, ...]:
    a = right_band_endpoint()
    nodes, weights = np.polynomial.legendre.leggauss(quadrature_order)
    points = a * (nodes + 1.0)
    weights = a * weights
    identity = np.eye(mode_count)
    complete_integral = np.zeros((mode_count, mode_count))
    remainder = np.zeros((mode_count, mode_count))

    for t, weight in zip(points, weights, strict=True):
        correlation = symmetric_correlation_matrix(mode_count, t / a)
        gamma_numerator = math.exp(t / 2.0) * correlation - identity
        complete_integrand = (
            4.0 * math.cosh(t / 2.0) * correlation
            - gamma_numerator / math.sinh(t)
        )
        complete_integral += weight * complete_integrand
        remainder += (
            weight
            * 2.0
            * remainder_second_derivative(t)
            * correlation
        )

    log_two = math.log(2.0)
    prime = (
        -math.sqrt(2.0)
        * log_two
        * symmetric_correlation_matrix(mode_count, log_two / a)
    )
    diagonal_constant = -(
        math.log(4.0 * math.pi)
        + EULER_GAMMA
        + math.log(math.tanh(a))
    )
    complete = complete_integral + prime + diagonal_constant * identity
    scalar = math.log(2.0 * math.pi) + EULER_GAMMA
    comparison = complete + scalar * identity - prime + remainder
    return complete, comparison, prime, remainder


def symmetric_generalized_max(numerator: np.ndarray, denominator: np.ndarray) -> float:
    cholesky = np.linalg.cholesky(denominator)
    first = np.linalg.solve(cholesky, numerator)
    normalized = np.linalg.solve(cholesky, first.T).T
    normalized = (normalized + normalized.T) / 2.0
    return float(np.linalg.eigvalsh(normalized)[-1])


def reconstruct_convolution_matrix(matrix: np.ndarray) -> np.ndarray:
    """Reconstruct a symmetric convolution pairing from row zero and its diagonal."""

    mode_count = matrix.shape[0]
    sine_transform = np.zeros(mode_count)
    for mode in range(1, mode_count):
        alternating = 1.0 if mode % 2 else -1.0
        sine_transform[mode] = (
            matrix[0, mode]
            * math.sqrt(2.0)
            * math.pi
            * mode
            / alternating
        )
    scale = np.ones(mode_count)
    scale[0] = 1.0 / math.sqrt(2.0)
    reconstructed = np.diag(np.diag(matrix))
    for left in range(mode_count):
        for right in range(left + 1, mode_count):
            difference = left - right
            total = left + right
            difference_sign = 1.0 if abs(difference) % 2 else -1.0
            total_sign = 1.0 if total % 2 else -1.0
            value = scale[left] * scale[right] / (2.0 * math.pi) * (
                difference_sign
                * (sine_transform[left] - sine_transform[right])
                / difference
                + total_sign
                * (sine_transform[left] + sine_transform[right])
                / total
            )
            reconstructed[left, right] = value
            reconstructed[right, left] = value
    return reconstructed


def compression_records(
    complete: np.ndarray,
    comparison: np.ndarray,
    boundary: int,
    far_windows: tuple[int, ...],
) -> list[dict[str, float | int]]:
    low_count = boundary + 1
    low = complete[:low_count, :low_count]
    records = []
    for window in far_windows:
        stop = low_count + window
        cross = complete[:low_count, low_count:stop]
        far_comparison = comparison[low_count:stop, low_count:stop]
        far_complete = complete[low_count:stop, low_count:stop]
        comparison_schur = cross @ np.linalg.solve(far_comparison, cross.T)
        complete_schur = cross @ np.linalg.solve(far_complete, cross.T)
        scalar_schur = (1.0 / 5.0) * (cross @ cross.T)
        rho_comparison = symmetric_generalized_max(comparison_schur, low)
        rho_complete = symmetric_generalized_max(complete_schur, low)
        rho_scalar = symmetric_generalized_max(scalar_schur, low)
        records.append(
            {
                "far_window": window,
                "last_mode": boundary + window,
                "far_comparison_minimum": float(
                    np.linalg.eigvalsh(far_comparison)[0]
                ),
                "far_complete_minimum": float(
                    np.linalg.eigvalsh(far_complete)[0]
                ),
                "rho_comparison_finite": rho_comparison,
                "ratio_to_19_over_1000": rho_comparison / 0.019,
                "rho_complete_finite": rho_complete,
                "rho_scalar_finite": rho_scalar,
                "scalar_ratio_to_19_over_1000": rho_scalar / 0.019,
            }
        )
    return records


def galerkin_residual_record(
    complete: np.ndarray,
    comparison: np.ndarray,
    boundary: int,
    galerkin_window: int,
) -> dict[str, object]:
    low_count = boundary + 1
    split = low_count + galerkin_window
    if galerkin_window <= 0 or split >= complete.shape[0]:
        raise ValueError(
            "galerkin-window must be positive and leave assembled residual modes"
        )
    low = complete[:low_count, :low_count]
    cross_band = complete[:low_count, low_count:split]
    energy_band = comparison[low_count:split, low_count:split]
    galerkin_coefficients = np.linalg.solve(energy_band, cross_band.T)
    low_modes = np.arange(low_count)
    band_modes = np.arange(low_count, split)
    low_endpoint_vector = (-1.0) ** low_modes
    low_endpoint_vector[0] /= math.sqrt(2.0)
    band_endpoint_vector = (-1.0) ** band_modes
    projected_endpoint_vector = (
        galerkin_coefficients.T @ band_endpoint_vector
    )
    endpoint_residual_vector = (
        low_endpoint_vector - projected_endpoint_vector
    )
    cross_tail = complete[:low_count, split:]
    energy_band_tail = comparison[low_count:split, split:]
    residual = cross_tail - galerkin_coefficients.T @ energy_band_tail
    finite_schur = cross_band @ galerkin_coefficients
    observed_residual_gram = residual @ residual.T
    # This is a diagnostic use of the already proved E >= 5*I.  Because only
    # an assembled prefix of the residual is present, it is not an upper bound
    # for the complete Galerkin error.
    observed_correction = observed_residual_gram / 5.0
    inverse_square_tail = 1.0 / (boundary + galerkin_window)
    conservative_main_tail = (
        2.0
        / (math.pi * math.pi)
        * inverse_square_tail
        * (
            (math.pi * math.pi / 4.0)
            * np.outer(endpoint_residual_vector, endpoint_residual_vector)
            + 2.0
            * math.log(2.0) ** 2
            * np.outer(low_endpoint_vector, low_endpoint_vector)
        )
    )
    tail_modes = np.arange(
        boundary + galerkin_window + 1,
        1_000_001,
        dtype=float,
    )
    theta = math.pi * math.log(2.0) / right_band_endpoint()
    inverse_squares = 1.0 / (tail_modes * tail_modes)
    sine_values = np.sin(theta * tail_modes)
    sum_zero = float(np.sum(inverse_squares))
    sum_one = float(np.sum(sine_values * inverse_squares))
    sum_two = float(np.sum(sine_values * sine_values * inverse_squares))
    prime_amplitude = math.sqrt(2.0) * math.log(2.0)
    oscillatory_main_tail = 1.0 / (math.pi * math.pi) * (
        (math.pi * math.pi / 4.0)
        * sum_zero
        * np.outer(endpoint_residual_vector, endpoint_residual_vector)
        + prime_amplitude * prime_amplitude
        * sum_two
        * np.outer(low_endpoint_vector, low_endpoint_vector)
        + (math.pi * prime_amplitude / 2.0)
        * sum_one
        * (
            np.outer(endpoint_residual_vector, low_endpoint_vector)
            + np.outer(low_endpoint_vector, endpoint_residual_vector)
        )
    )
    column_norms = np.linalg.norm(residual, axis=0)
    return {
        "galerkin_window": galerkin_window,
        "galerkin_last_mode": boundary + galerkin_window,
        "observed_residual_first_mode": boundary + galerkin_window + 1,
        "observed_residual_last_mode": complete.shape[0] - 1,
        "finite_rho_comparison": symmetric_generalized_max(
            finite_schur,
            low,
        ),
        "observed_residual_frobenius_squared": float(
            np.sum(residual * residual)
        ),
        "observed_residual_max_column_norm": float(np.max(column_norms)),
        "observed_residual_first_column_norm": float(column_norms[0]),
        "observed_residual_last_column_norm": float(column_norms[-1]),
        "low_endpoint_vector_norm": float(
            np.linalg.norm(low_endpoint_vector)
        ),
        "projected_endpoint_vector_norm": float(
            np.linalg.norm(projected_endpoint_vector)
        ),
        "endpoint_residual_vector_norm": float(
            np.linalg.norm(endpoint_residual_vector)
        ),
        "heuristic_rho_with_observed_residual_over_5": (
            symmetric_generalized_max(
                finite_schur + observed_correction,
                low,
            )
        ),
        "conservative_main_tail_rho_over_5": (
            symmetric_generalized_max(
                finite_schur + conservative_main_tail / 5.0,
                low,
            )
        ),
        "oscillatory_main_tail_rho_over_5": (
            symmetric_generalized_max(
                finite_schur + oscillatory_main_tail / 5.0,
                low,
            )
        ),
        "oscillatory_main_tail_sum_truncation": 1_000_000,
        "warning": (
            "The observed residual correction omits all later modes and is "
            "not a certified upper bound."
        ),
    }


def main() -> int:
    args = parse_args()
    if args.boundary != 44:
        raise ValueError("FT3 keeps the frozen boundary equal to 44")
    if len(args.quadrature_orders) < 2:
        raise ValueError("at least two quadrature orders are required")
    maximum_window = max(args.far_windows)
    mode_count = args.boundary + 1 + maximum_window
    runs = []
    previous_complete = None
    previous_comparison = None
    for order in args.quadrature_orders:
        complete, comparison, prime, remainder = build_matrices(
            mode_count,
            order,
        )
        convergence = None
        if previous_complete is not None and previous_comparison is not None:
            convergence = {
                "complete_max_entry_change": float(
                    np.max(np.abs(complete - previous_complete))
                ),
                "comparison_max_entry_change": float(
                    np.max(np.abs(comparison - previous_comparison))
                ),
            }
        low_count = args.boundary + 1
        reconstructed_complete = reconstruct_convolution_matrix(complete)
        reconstructed_comparison = reconstruct_convolution_matrix(comparison)
        runs.append(
            {
                "quadrature_order": order,
                "convergence_from_previous": convergence,
                "low_complete_minimum": float(
                    np.linalg.eigvalsh(complete[:low_count, :low_count])[0]
                ),
                "prime_symmetry_error": float(np.max(np.abs(prime - prime.T))),
                "remainder_symmetry_error": float(
                    np.max(np.abs(remainder - remainder.T))
                ),
                "complete_convolution_reconstruction_error": float(
                    np.max(np.abs(complete - reconstructed_complete))
                ),
                "comparison_convolution_reconstruction_error": float(
                    np.max(np.abs(comparison - reconstructed_comparison))
                ),
                "compressions": compression_records(
                    complete,
                    comparison,
                    args.boundary,
                    args.far_windows,
                ),
                "galerkin_residual": (
                    galerkin_residual_record(
                        complete,
                        comparison,
                        args.boundary,
                        args.galerkin_window,
                    )
                    if args.galerkin_window
                    else None
                ),
            }
        )
        previous_complete = complete
        previous_comparison = comparison

    payload = {
        "experiment": "M100-FT3",
        "artifact": "fixed-endpoint-even-comparison-midpoint-scout",
        "certification": "MIDPOINT_ONLY",
        "warning": (
            "Finite compressions are lower route filters, not infinite-tail "
            "upper certificates. Any decision-producing inequality requires "
            "an independent Arb enclosure."
        ),
        "settings": {
            "boundary": args.boundary,
            "far_windows": args.far_windows,
            "quadrature_orders": args.quadrature_orders,
            "galerkin_window": args.galerkin_window,
            "endpoint": right_band_endpoint(),
        },
        "signed_identity": "F = E - s*I + P_2 - R",
        "runs": runs,
    }
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
