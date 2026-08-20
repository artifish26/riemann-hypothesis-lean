#!/usr/bin/env python3
"""M100-X21 Yoshida high-mode local-energy certificate probe.

For a periodic restriction whose Fourier coefficients vanish on ``|n| <= N``,
the zero-extended Fourier transform satisfies an exact cardinal-sine leakage
bound.  This probe encloses the resulting lower bound for Suzuki's local
energy on the first-prime band and combines it with X20's ``kappa <= 1/2``
estimate and the smooth ``r''`` remainder.

The remainder reduction uses the elementary fact that Suzuki's ``r''(t)`` is
decreasing for ``0 < t <= 2*A_half``.  The equivalent scalar inequality and
the power-series tail estimate proving it on ``0 < t <= 1`` are printed in
the report so the non-numerical step remains visible.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction

try:
    from flint import arb, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "high_mode_local_energy_probe.py requires python-flint==0.8.0"
    ) from error


@dataclass(frozen=True)
class Case:
    cutoff: int
    scaled_threshold: Fraction


@dataclass(frozen=True)
class Settings:
    cases: tuple[Case, ...]
    precision_bits: int


def parse_cases(text: str) -> tuple[Case, ...]:
    cases: list[Case] = []
    for item in text.split(","):
        cutoff_text, threshold_text = item.split(":", maxsplit=1)
        cutoff = int(cutoff_text)
        threshold = Fraction(threshold_text)
        if cutoff < 1:
            raise argparse.ArgumentTypeError("cutoffs must be positive")
        if threshold <= 0 or threshold >= cutoff + 1:
            raise argparse.ArgumentTypeError(
                "each scaled threshold must lie in (0, cutoff + 1)"
            )
        cases.append(Case(cutoff, threshold))
    if not cases:
        raise argparse.ArgumentTypeError("at least one case is required")
    return tuple(cases)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cases",
        type=parse_cases,
        default=parse_cases("8:21/4,35:77/4,36:81/4,48:105/4"),
        help="comma-separated cutoff:scaled-threshold pairs",
    )
    parser.add_argument("--precision-bits", type=int, default=192)
    return parser.parse_args()


def interval_text(value: arb) -> str:
    return value.str(30, more=True)


def endpoint_text(value: arb, *, upper: bool) -> str:
    endpoint = value.upper() if upper else value.lower()
    return endpoint.str(30, more=True)


def arb_fraction(value: Fraction) -> arb:
    return arb(fmpq(value.numerator, value.denominator))


def sinc_square_antiderivative(value: arb, pi: arb) -> arb:
    """Odd primitive of (sin(pi*x)/(pi*x))^2, normalized to zero at 0."""

    if value == 0:
        return arb(0)
    return (2 * pi * value).si() / pi + (
        (2 * pi * value).cos() - 1
    ) / (2 * pi * pi * value)


def leakage_fraction(cutoff: int, threshold: arb, pi: arb) -> arb:
    """Enclose the low-frequency mass fraction rho_N(U)."""

    low_mode_mass = arb(0)
    for mode in range(-cutoff, cutoff + 1):
        low_mode_mass += sinc_square_antiderivative(
            threshold - mode,
            pi,
        ) - sinc_square_antiderivative(arb(-mode), pi)
    return 2 * (threshold - low_mode_mass)


def right_band_endpoint() -> arb:
    log_two = arb(2).log()
    return (
        log_two
        + (
            log_two * log_two
            + 4 * (-2 * arb(2).sqrt() * log_two).exp()
        ).sqrt()
    ) / 4


def remainder_second_derivative_at_two_a(a: arb) -> arb:
    """Suzuki's r''(2*a), using the removable-term closed form."""

    return (
        -2 * a.cosh()
        + (-a).exp() / (1 - (-4 * a).exp())
        - 1 / (4 * a)
    )


def evaluate_case(case: Case, a_max: arb, pi: arb, euler: arb) -> dict:
    cutoff = case.cutoff
    threshold = arb_fraction(case.scaled_threshold)
    rho = leakage_fraction(cutoff, threshold, pi)

    zero_crossing = a_max * (-euler).exp() / pi
    negative_weight_loss = 4 * zero_crossing**3 / (
        9
        * cutoff
        * (1 - zero_crossing / (cutoff + 1)) ** 2
    )
    high_weight = (pi * threshold / a_max).log() + euler
    local_energy_lower = high_weight * (1 - rho) - negative_weight_loss

    remainder_variation = 2 * (
        arb(fmpq(-7, 4)) - remainder_second_derivative_at_two_a(a_max)
    )
    primitive_norm = a_max / pi * (
        arb(fmpq(1, (cutoff + 1) ** 2)) + arb(fmpq(2, cutoff))
    ).sqrt()
    remainder_norm = remainder_variation * primitive_norm

    suzuki_scalar = (2 * pi).log() + euler
    complete_high_mode_margin = (
        local_energy_lower / 2 - suzuki_scalar - remainder_norm
    )

    return {
        "cutoff": cutoff,
        "scaled_threshold": str(case.scaled_threshold),
        "leakage_fraction": interval_text(rho),
        "leakage_fraction_upper": endpoint_text(rho, upper=True),
        "negative_log_weight_loss": interval_text(negative_weight_loss),
        "local_energy_lower": interval_text(local_energy_lower),
        "local_energy_certified_lower": endpoint_text(
            local_energy_lower,
            upper=False,
        ),
        "primitive_norm_factor": interval_text(primitive_norm),
        "remainder_norm_upper": endpoint_text(remainder_norm, upper=True),
        "complete_high_mode_margin": interval_text(
            complete_high_mode_margin
        ),
        "complete_high_mode_certified_lower": endpoint_text(
            complete_high_mode_margin,
            upper=False,
        ),
    }


def main() -> None:
    args = parse_args()
    settings = Settings(args.cases, args.precision_bits)
    if settings.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")
    ctx.prec = settings.precision_bits

    pi = arb.pi()
    euler = arb.const_euler()
    a_max = right_band_endpoint()
    remainder_variation = 2 * (
        arb(fmpq(-7, 4)) - remainder_second_derivative_at_two_a(a_max)
    )

    payload = {
        "experiment": "M100-X21",
        "artifact": "yoshida-high-mode-local-energy",
        "settings": {
            "cases": [
                {
                    "cutoff": case.cutoff,
                    "scaled_threshold": str(case.scaled_threshold),
                }
                for case in settings.cases
            ],
            "precision_bits": settings.precision_bits,
        },
        "band_right_endpoint": interval_text(a_max),
        "suzuki_scalar": interval_text((2 * pi).log() + euler),
        "remainder_total_variation": interval_text(remainder_variation),
        "remainder_monotonicity_lemma": (
            "For 0<t<=1, H(t)="
            "t^2*exp(t/2)*(2*cosh(t)-sinh(t))-2*sinh(t)^2 "
            ">= t^4/12-(2*t)^12*91/(12!*89)>0; "
            "hence r_1'''(t)<0 on the frozen band."
        ),
        "cases": [
            evaluate_case(case, a_max, pi, euler)
            for case in settings.cases
        ],
    }
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
