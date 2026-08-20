#!/usr/bin/env python3
"""M100-X21 complete-form first-prime-band feasibility scout.

The probe uses unitary pullbacks of fixed parity-separated bases on [-1, 1]
and evaluates the complete localized Weil form from Suzuki's displayed
explicit functional.  It supports both Dirichlet discovery bases and the
periodic Fourier projection in Yoshida's high-mode theorem.  On the
conservative first-prime band only n=2 enters.

The pole integral is evaluated exactly from the trigonometric
cross-correlation.  The complete Gamma term is evaluated as a convergent
exponential series with exact origin-value, origin-slope, and origin-curvature
corrections and an analytic tail bound.  Arb encloses every finite term and
every final matrix entry.

Positive finite Ritz values are feasibility evidence only.  They do not prove
positivity of the infinite-dimensional form.  A rigorously negative Ritz
value would instead give a genuine negative direction for the tested radius.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass

try:
    import flint
    from flint import acb, arb, arb_mat, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "coupled_first_prime_band_probe.py requires python-flint==0.8.0"
    ) from error


@dataclass(frozen=True)
class Settings:
    dimensions: tuple[int, ...]
    basis: str
    parities: tuple[str, ...]
    positions: str
    grid_intervals: int
    series_terms: int
    precision_bits: int


def parse_dimensions(text: str) -> tuple[int, ...]:
    dimensions = tuple(sorted({int(part) for part in text.split(",")}))
    if not dimensions or dimensions[0] <= 0:
        raise argparse.ArgumentTypeError("dimensions must be positive")
    return dimensions


def parse_parities(text: str) -> tuple[str, ...]:
    parities = tuple(
        parity for parity in ("even", "odd") if parity in text.split(",")
    )
    if not parities or set(text.split(",")) != set(parities):
        raise argparse.ArgumentTypeError(
            "parities must be even, odd, or even,odd"
        )
    return parities


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dimensions", type=parse_dimensions, default=(2, 4))
    parser.add_argument(
        "--basis",
        choices=("dirichlet", "yoshida"),
        default="dirichlet",
    )
    parser.add_argument(
        "--parities",
        type=parse_parities,
        default=("even", "odd"),
    )
    parser.add_argument(
        "--positions",
        choices=("all", "endpoints", "left", "right"),
        default="all",
    )
    parser.add_argument("--grid-intervals", type=int, default=4)
    parser.add_argument("--series-terms", type=int, default=8192)
    parser.add_argument("--precision-bits", type=int, default=160)
    parser.add_argument("--summary-only", action="store_true")
    return parser.parse_args()


def validate_settings(settings: Settings) -> None:
    if settings.grid_intervals <= 0:
        raise ValueError("grid-intervals must be positive")
    if settings.series_terms < 128:
        raise ValueError("series-terms must be at least 128")
    if settings.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")


def interval_text(value: arb) -> str:
    return value.str(30, more=True)


def endpoint_text(value: arb, *, upper: bool) -> str:
    endpoint = value.upper() if upper else value.lower()
    return endpoint.str(30, more=True)


def frequency(basis: str, parity: str, index: int, pi: arb) -> arb:
    if basis == "yoshida" and parity == "even":
        return arb(index) * pi
    if parity == "even":
        return (arb(index) + arb(fmpq(1, 2))) * pi
    if parity == "odd":
        return arb(index + 1) * pi
    raise ValueError(f"unknown parity: {parity}")


def basis_scale(basis: str, parity: str, index: int) -> arb:
    if basis == "yoshida" and parity == "even" and index == 0:
        return 1 / arb(2).sqrt()
    return arb(1)


def has_zero_total_frequency(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
) -> bool:
    return (
        basis == "yoshida"
        and parity == "even"
        and left_index == 0
        and right_index == 0
    )


def cosine_integral(
    wave_number: arb,
    phase: arb,
    lower: arb,
    upper: arb,
    *,
    zero_wave_number: bool,
) -> arb:
    if zero_wave_number:
        return phase.cos() * (upper - lower)
    return (
        (wave_number * upper + phase).sin()
        - (wave_number * lower + phase).sin()
    ) / wave_number


def one_sided_correlation(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    displacement: arb,
    pi: arb,
) -> arb:
    """Integral w_i(s+d) w_j(s) ds over -1 <= s <= 1-d."""

    left_frequency = frequency(basis, parity, left_index, pi)
    right_frequency = frequency(basis, parity, right_index, pi)
    lower = arb(-1)
    upper = arb(1) - displacement
    phase = left_frequency * displacement
    difference = left_frequency - right_frequency
    total = left_frequency + right_frequency
    difference_term = cosine_integral(
        difference,
        phase,
        lower,
        upper,
        zero_wave_number=left_index == right_index,
    )
    total_term = cosine_integral(
        total,
        phase,
        lower,
        upper,
        zero_wave_number=has_zero_total_frequency(
            basis,
            parity,
            left_index,
            right_index,
        ),
    )
    scale = (
        basis_scale(basis, parity, left_index)
        * basis_scale(basis, parity, right_index)
    )
    if parity == "even":
        return scale * (difference_term + total_term) / 2
    return scale * (difference_term - total_term) / 2


def symmetric_correlation(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    displacement: arb,
    pi: arb,
) -> arb:
    return (
        one_sided_correlation(
            basis,
            parity,
            left_index,
            right_index,
            displacement,
            pi,
        )
        + one_sided_correlation(
            basis,
            parity,
            right_index,
            left_index,
            displacement,
            pi,
        )
    ) / 2


def complex_weighted_integral(mu: arb, wave_number: arb, phase: arb) -> acb:
    """Integral of exp(-mu*d + i*(wave_number*d + phase)), 0 <= d <= 2."""

    exponent = acb(-mu, wave_number)
    phase_factor = acb(0, phase).exp()
    return phase_factor * ((2 * exponent).exp() - 1) / exponent


def weighted_sine_integral(
    mu: arb,
    wave_number: arb,
    phase: arb,
) -> arb:
    return complex_weighted_integral(mu, wave_number, phase).imag


def weighted_linear_cosine_integral(
    mu: arb,
    wave_number: arb,
    phase: arb,
) -> arb:
    """Integral of (2-d) exp(-mu*d) cos(wave_number*d+phase)."""

    exponent = acb(-mu, wave_number)
    phase_factor = acb(0, phase).exp()
    exponential_at_two = (2 * exponent).exp()
    integral_zero = phase_factor * (exponential_at_two - 1) / exponent
    integral_one = phase_factor * (
        (2 * exponent - 1) * exponential_at_two + 1
    ) / (exponent * exponent)
    return (2 * integral_zero - integral_one).real


def weighted_cosine_term_integral(
    left_frequency: arb,
    right_frequency: arb,
    mu: arb,
    *,
    equal_frequencies: bool,
) -> arb:
    """Weighted integral of one cosine-product term in the correlation."""

    wave_number = left_frequency - right_frequency
    if equal_frequencies:
        return weighted_linear_cosine_integral(
            mu,
            left_frequency,
            arb(0),
        )
    return (
        weighted_sine_integral(
            mu,
            left_frequency - wave_number,
            wave_number,
        )
        - weighted_sine_integral(
            mu,
            left_frequency,
            -wave_number,
        )
    ) / wave_number


def one_sided_weighted_correlation_integral(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    mu: arb,
    pi: arb,
) -> arb:
    """Integral of exp(-mu*d) C_ij^+(d) over 0 <= d <= 2."""

    left_frequency = frequency(basis, parity, left_index, pi)
    right_frequency = frequency(basis, parity, right_index, pi)
    difference_term = weighted_cosine_term_integral(
        left_frequency,
        right_frequency,
        mu,
        equal_frequencies=left_index == right_index,
    )
    total_term = weighted_cosine_term_integral(
        left_frequency,
        -right_frequency,
        mu,
        equal_frequencies=has_zero_total_frequency(
            basis,
            parity,
            left_index,
            right_index,
        ),
    )
    scale = (
        basis_scale(basis, parity, left_index)
        * basis_scale(basis, parity, right_index)
    )
    if parity == "even":
        return scale * (difference_term + total_term) / 2
    return scale * (difference_term - total_term) / 2


def symmetric_weighted_correlation_integral(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    mu: arb,
    pi: arb,
) -> arb:
    return (
        one_sided_weighted_correlation_integral(
            basis,
            parity,
            left_index,
            right_index,
            mu,
            pi,
        )
        + one_sided_weighted_correlation_integral(
            basis,
            parity,
            right_index,
            left_index,
            mu,
            pi,
        )
    ) / 2


def validate_correlation(
    basis: str,
    parity: str,
    dimension: int,
    pi: arb,
) -> None:
    for left_index in range(dimension):
        for right_index in range(dimension):
            at_zero = symmetric_correlation(
                basis,
                parity,
                left_index,
                right_index,
                arb(0),
                pi,
            )
            expected = arb(1 if left_index == right_index else 0)
            if not at_zero.contains(expected):
                raise ArithmeticError(
                    f"{parity} correlation normalization failed at zero"
                )
            at_two = symmetric_correlation(
                basis,
                parity,
                left_index,
                right_index,
                arb(2),
                pi,
            )
            if not at_two.contains(arb(0)):
                raise ArithmeticError(
                    f"{parity} correlation support failed at displacement two"
                )


def correlation_origin_slope(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    a: arb,
) -> arb:
    """Right derivative at t=0 of the physical symmetrized correlation."""

    if basis != "yoshida" or parity != "even":
        return arb(0)
    left_sign = -1 if left_index % 2 else 1
    right_sign = -1 if right_index % 2 else 1
    endpoint_product = (
        arb(left_sign * right_sign)
        * basis_scale(basis, parity, left_index)
        * basis_scale(basis, parity, right_index)
    )
    return -endpoint_product / a


def correlation_origin_second_derivative(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    a: arb,
    pi: arb,
) -> arb:
    """Right second derivative at t=0 of the physical correlation."""

    if left_index != right_index:
        return arb(0)
    basis_frequency = frequency(basis, parity, left_index, pi)
    return -(basis_frequency * basis_frequency) / (a * a)


def correlation_third_derivative_bound(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    a: arb,
    pi: arb,
) -> arb:
    """Uniform bound for the physical correlation's third derivative."""

    left_frequency = frequency(basis, parity, left_index, pi)
    right_frequency = frequency(basis, parity, right_index, pi)
    return (
        left_frequency**3
        + right_frequency**3
        + left_frequency * left_frequency
        + right_frequency * right_frequency
        + left_frequency * right_frequency
    ) / (a**3)


def matrix_entry_components(
    basis: str,
    parity: str,
    left_index: int,
    right_index: int,
    a: arb,
    position_index: int,
    series_terms: int,
    log_two: arb,
    pi: arb,
) -> dict[str, arb]:
    diagonal = left_index == right_index
    correlation_zero = arb(1 if diagonal else 0)

    pole_integral_negative = symmetric_weighted_correlation_integral(
        basis,
        parity,
        left_index,
        right_index,
        -a / 2,
        pi,
    )
    pole_integral_positive = symmetric_weighted_correlation_integral(
        basis,
        parity,
        left_index,
        right_index,
        a / 2,
        pi,
    )
    pole_term = 2 * a * (
        pole_integral_negative + pole_integral_positive
    )

    origin_slope = correlation_origin_slope(
        basis,
        parity,
        left_index,
        right_index,
        a,
    )
    origin_second_derivative = correlation_origin_second_derivative(
        basis,
        parity,
        left_index,
        right_index,
        a,
        pi,
    )
    gamma_series = arb(0)
    for series_index in range(series_terms):
        decay = arb(2 * series_index) + arb(fmpq(1, 2))
        weighted_correlation = a * symmetric_weighted_correlation_integral(
            basis,
            parity,
            left_index,
            right_index,
            a * decay,
            pi,
        )
        gamma_series += (
            weighted_correlation
            - correlation_zero / decay
            - origin_slope / (decay * decay)
            - origin_second_derivative / (decay**3)
        )

    if diagonal:
        gamma_series += pi / 4 + log_two / 2
    gamma_series += origin_slope * (
        pi * pi / 4 + 2 * arb.const_catalan()
    )
    gamma_series += origin_second_derivative * (
        pi**3 / 8 + arb(fmpq(7, 2)) * arb(3).zeta()
    )

    first_omitted_decay = (
        arb(2 * series_terms) + arb(fmpq(1, 2))
    )
    gamma_tail_bound = correlation_third_derivative_bound(
        basis,
        parity,
        left_index,
        right_index,
        a,
        pi,
    ) * (
        1 / first_omitted_decay**4
        + 1 / (6 * first_omitted_decay**3)
    )
    if diagonal:
        gamma_tail_bound += (
            (-2 * a * first_omitted_decay).exp()
            / (
                first_omitted_decay
                * (1 - (-4 * a).exp())
            )
        )
    if origin_slope != 0:
        support_endpoint = 2 * a
        geometric_denominator = 1 - (-4 * a).exp()
        gamma_tail_bound += (
            abs(origin_slope)
            * (-support_endpoint * first_omitted_decay).exp()
            * (
                support_endpoint / first_omitted_decay
                + 1 / (first_omitted_decay * first_omitted_decay)
            )
            / geometric_denominator
        )
    if origin_second_derivative != 0:
        support_endpoint = 2 * a
        geometric_denominator = 1 - (-4 * a).exp()
        gamma_tail_bound += (
            abs(origin_second_derivative)
            * (-support_endpoint * first_omitted_decay).exp()
            * (
                support_endpoint**2 / (2 * first_omitted_decay)
                + support_endpoint / first_omitted_decay**2
                + 1 / first_omitted_decay**3
            )
            / geometric_denominator
        )
    gamma_complete_term = -2 * (
        gamma_series + arb(0, gamma_tail_bound.upper())
    )

    constant_term = (
        -((4 * pi).log() + arb.const_euler()) * correlation_zero
    )

    if position_index == 0:
        prime_term = arb(0)
    else:
        prime_displacement = log_two / a
        prime_correlation = symmetric_correlation(
            basis,
            parity,
            left_index,
            right_index,
            prime_displacement,
            pi,
        )
        prime_term = -arb(2).sqrt() * log_two * prime_correlation

    total = (
        pole_term
        + prime_term
        + constant_term
        + gamma_complete_term
    )
    return {
        "pole": pole_term,
        "prime_two": prime_term,
        "constant": constant_term,
        "gamma_complete": gamma_complete_term,
        "total": total,
    }


def lowest_eigenvalue_record(matrix: arb_mat) -> dict[str, object]:
    midpoint = matrix.mid()
    eigenvalues = midpoint.eig(algorithm="rump")
    ordered = sorted(eigenvalues, key=lambda value: float(value.real.mid()))
    lowest_midpoint = ordered[0]
    if not lowest_midpoint.imag.contains(arb(0)):
        raise ArithmeticError("symmetric matrix eigenvalue missed the real axis")

    # Every exact symmetric matrix represented by the entry balls differs
    # from the midpoint matrix by an operator whose spectral norm is at most
    # its maximum absolute row sum. Weyl's inequality then gives a certified
    # enclosure for the lowest eigenvalue without asking Arb to isolate the
    # eigenvalues of a wide interval matrix directly.
    perturbation_bound = arb(0)
    for row in range(matrix.nrows()):
        row_bound = arb(0)
        for column in range(matrix.ncols()):
            row_bound += abs(matrix[row, column] - midpoint[row, column]).upper()
        if row_bound > perturbation_bound:
            perturbation_bound = row_bound

    lowest = lowest_midpoint.real + arb(0, perturbation_bound.upper())
    lower = lowest.lower()
    upper = lowest.upper()
    return {
        "interval": interval_text(lowest),
        "lower": lower.str(30, more=True),
        "upper": upper.str(30, more=True),
        "midpoint_eigenvalue": interval_text(lowest_midpoint.real),
        "entry_perturbation_row_sum_bound": interval_text(
            perturbation_bound
        ),
        "certified_positive_finite_ritz": lower > 0,
        "certified_negative_direction": upper < 0,
    }


def run_probe(settings: Settings) -> dict[str, object]:
    validate_settings(settings)
    ctx.prec = settings.precision_bits

    log_two = arb.const_log2()
    pi = arb.pi()
    a_two = log_two / 2
    a_half = (
        log_two
        + (
            log_two * log_two
            + 4 * (-2 * arb(2).sqrt() * log_two).exp()
        ).sqrt()
    ) / 4

    results: list[dict[str, object]] = []
    any_negative_direction = False
    all_finite_ritz_positive = True

    if settings.positions == "all":
        position_indices = tuple(range(settings.grid_intervals + 1))
    elif settings.positions == "endpoints":
        position_indices = (0, settings.grid_intervals)
    elif settings.positions == "left":
        position_indices = (0,)
    else:
        position_indices = (settings.grid_intervals,)

    for dimension in settings.dimensions:
        for parity in settings.parities:
            validate_correlation(settings.basis, parity, dimension, pi)

            for position_index in position_indices:
                position = arb(fmpq(position_index, settings.grid_intervals))
                a = a_two + position * (a_half - a_two)
                matrix = arb_mat(dimension, dimension)
                first_diagonal: dict[str, arb] | None = None

                for left_index in range(dimension):
                    for right_index in range(left_index, dimension):
                        components = matrix_entry_components(
                            settings.basis,
                            parity,
                            left_index,
                            right_index,
                            a,
                            position_index,
                            settings.series_terms,
                            log_two,
                            pi,
                        )
                        matrix[left_index, right_index] = components["total"]
                        matrix[right_index, left_index] = components["total"]
                        if left_index == 0 and right_index == 0:
                            first_diagonal = components

                eigenvalue = lowest_eigenvalue_record(matrix)
                any_negative_direction = (
                    any_negative_direction
                    or bool(eigenvalue["certified_negative_direction"])
                )
                all_finite_ritz_positive = (
                    all_finite_ritz_positive
                    and bool(eigenvalue["certified_positive_finite_ritz"])
                )
                assert first_diagonal is not None
                results.append(
                    {
                        "dimension": dimension,
                        "parity": parity,
                        "position": f"{position_index}/{settings.grid_intervals}",
                        "a": interval_text(a),
                        "lowest_ritz": eigenvalue,
                        "first_basis_components": {
                            name: interval_text(value)
                            for name, value in first_diagonal.items()
                        },
                    }
                )

    endpoint_even = next(
        (
            item
            for item in results
            if item["dimension"] == settings.dimensions[0]
            and item["parity"] == "even"
            and item["position"] == f"0/{settings.grid_intervals}"
        ),
        None,
    )
    endpoint_trial = (
        endpoint_even["first_basis_components"]["total"]
        if endpoint_even is not None
        else None
    )

    return {
        "experiment": "M100-X21",
        "dependency": f"python-flint=={flint.__version__}",
        "settings": asdict(settings),
        "band": {
            "a_2": interval_text(a_two),
            "A_(1/2)": interval_text(a_half),
        },
        "basis": (
            {
                "family": "dirichlet",
                "even": "cos((k+1/2)*pi*s)",
                "odd": "sin((k+1)*pi*s)",
                "scaling": "v(x)=w(x/a)/sqrt(a)",
            }
            if settings.basis == "dirichlet"
            else {
                "family": "yoshida",
                "even": "1/sqrt(2), then cos(k*pi*s) for k>=1",
                "odd": "sin((k+1)*pi*s)",
                "scaling": "v(x)=w(x/a)/sqrt(a)",
            }
        ),
        "endpoint_even_first_basis_total": endpoint_trial,
        "all_tested_finite_ritz_certified_positive": all_finite_ritz_positive,
        "any_certified_negative_direction": any_negative_direction,
        "results": results,
        "scope": (
            "Finite parity-separated Ritz evidence for the complete actual "
            "form at a discrete parameter grid. Positive values do not prove "
            "coercivity; a high-mode theorem, continuum enclosure, and cross "
            "estimate remain mandatory."
        ),
    }


def main() -> int:
    args = parse_args()
    settings = Settings(
        dimensions=args.dimensions,
        basis=args.basis,
        parities=args.parities,
        positions=args.positions,
        grid_intervals=args.grid_intervals,
        series_terms=args.series_terms,
        precision_bits=args.precision_bits,
    )
    result = run_probe(settings)
    if args.summary_only:
        result = {
            "experiment": result["experiment"],
            "dependency": result["dependency"],
            "settings": result["settings"],
            "band": result["band"],
            "endpoint_even_first_basis_total": result[
                "endpoint_even_first_basis_total"
            ],
            "all_tested_finite_ritz_certified_positive": result[
                "all_tested_finite_ritz_certified_positive"
            ],
            "any_certified_negative_direction": result[
                "any_certified_negative_direction"
            ],
            "lowest_ritz_summary": [
                {
                    "dimension": item["dimension"],
                    "parity": item["parity"],
                    "position": item["position"],
                    "a": item["a"],
                    "lowest_ritz": item["lowest_ritz"],
                }
                for item in result["results"]
            ],
            "scope": result["scope"],
        }
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
