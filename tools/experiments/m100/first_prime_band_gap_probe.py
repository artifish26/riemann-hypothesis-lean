#!/usr/bin/env python3
"""M100-X18 certified first-prime-band separate-gap route filter.

At the first prime threshold

    L = log(2),  a_2 = L / 2,

use the real Dirichlet trial

    v(x) = cos(pi*x/(2*a_2)),  |x| <= a_2.

Its squared L2 norm is a_2 and its autocorrelation on [0, L] is

    C(t) = (L-t)/2*cos(pi*t/L) + L/(2*pi)*sin(pi*t/L).

At a_2 the n=2 overlap has measure zero. The explicit formula therefore
expresses the nonprime Rayleigh quotient using two compact integrals and one
closed-form tail. This script encloses those integrals with Arb interval-box
Riemann sums. The removable singularity in the Gamma integral is handled on
[0, delta] by an analytic derivative bound.

The result is a rigorous upper bound on the nonprime spectral gap at a_2. If
that upper bound is below log(2)/sqrt(2), the separate-domination certificate
in the X18 plan is impossible. This does not refute a coupled coercivity
argument and does not prove a sign for the full first-prime-band form.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass

try:
    import flint
    from flint import arb, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "first_prime_band_gap_probe.py requires python-flint==0.8.0"
    ) from error


@dataclass(frozen=True)
class Settings:
    panels: int
    head_divisor: int
    precision_bits: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--panels", type=int, default=65536)
    parser.add_argument("--head-divisor", type=int, default=1024)
    parser.add_argument("--precision-bits", type=int, default=160)
    return parser.parse_args()


def validate_settings(settings: Settings) -> None:
    if settings.panels <= 0:
        raise ValueError("panels must be positive")
    if settings.head_divisor <= 0:
        raise ValueError("head-divisor must be positive")
    if settings.panels % settings.head_divisor != 0:
        raise ValueError("panels must be divisible by head-divisor")
    if settings.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")


def interval_text(value: arb) -> str:
    return value.str(30, more=True)


def endpoint_text(value: arb, *, upper: bool) -> str:
    endpoint = value.upper() if upper else value.lower()
    return endpoint.str(30, more=True)


def run_probe(settings: Settings) -> dict[str, object]:
    validate_settings(settings)
    ctx.prec = settings.precision_bits

    log_two = arb.const_log2()
    pi = arb.pi()
    a_two = log_two / 2
    panel_width = log_two / settings.panels
    head_start = settings.panels // settings.head_divisor

    def correlation(t: arb) -> arb:
        phase = pi * t / log_two
        return (
            (log_two - t) / 2 * phase.cos()
            + log_two / (2 * pi) * phase.sin()
        )

    pole_integral = arb(0)
    gamma_integral_tail = arb(0)

    for index in range(settings.panels):
        scaled_panel = arb(
            fmpq(2 * index + 1, 2 * settings.panels),
            fmpq(1, 2 * settings.panels),
        )
        t = log_two * scaled_panel
        correlation_value = correlation(t)

        pole_integral += (
            correlation_value * (t / 2).cosh() * panel_width
        )

        if index >= head_start:
            gamma_integrand = (
                ((t / 2).exp() * correlation_value - a_two)
                / (t.exp() - (-t).exp())
            )
            gamma_integral_tail += gamma_integrand * panel_width

    delta = log_two / settings.head_divisor

    # Let N(t) = exp(t/2) C(t) - a_2. Since N(0) = 0,
    # |C(t)| <= a_2, |C'(t)| <= pi/2, and 2*sinh(t) >= 2*t,
    # the absolute value of the removable Gamma integrand on [0, delta]
    # is bounded by the following quantity.
    gamma_head_integrand_bound = (
        (delta / 2).exp() * (pi / 2 + a_two / 2) / 2
    )
    gamma_integral_head = arb(
        0,
        delta * gamma_head_integrand_bound,
    )

    pole_term = 4 * pole_integral
    constant_term = -((4 * pi).log() + arb.const_euler()) * a_two
    gamma_near_term = -2 * (gamma_integral_head + gamma_integral_tail)
    gamma_tail_term = -a_two * (log_two / 2).tanh().log()

    nonprime_value = (
        pole_term + constant_term + gamma_near_term + gamma_tail_term
    )
    trial_rayleigh = nonprime_value / a_two
    prime_operator_norm = log_two / arb(2).sqrt()
    certified_separation = trial_rayleigh.upper() < prime_operator_norm.lower()

    return {
        "experiment": "M100-X18",
        "dependency": f"python-flint=={flint.__version__}",
        "settings": asdict(settings),
        "trial": "cos(pi*x/(2*a_2)) on [-a_2,a_2]",
        "a_2": interval_text(a_two),
        "nonprime_trial_rayleigh": interval_text(trial_rayleigh),
        "nonprime_trial_rayleigh_lower": endpoint_text(
            trial_rayleigh,
            upper=False,
        ),
        "nonprime_trial_rayleigh_upper": endpoint_text(
            trial_rayleigh,
            upper=True,
        ),
        "prime_operator_norm": interval_text(prime_operator_norm),
        "prime_operator_norm_lower": endpoint_text(
            prime_operator_norm,
            upper=False,
        ),
        "certified_separate_domination_failure": certified_separation,
        "scope": (
            "Refutes only a certificate that lower-bounds the nonprime form "
            "by a uniform constant exceeding log(2)/sqrt(2); coupled "
            "first-prime-band coercivity remains open."
        ),
        "component_enclosures": {
            "pole_term": interval_text(pole_term),
            "constant_term": interval_text(constant_term),
            "gamma_near_term": interval_text(gamma_near_term),
            "gamma_tail_term": interval_text(gamma_tail_term),
            "gamma_head_integrand_abs_bound": interval_text(
                gamma_head_integrand_bound
            ),
        },
    }


def main() -> int:
    args = parse_args()
    settings = Settings(
        panels=args.panels,
        head_divisor=args.head_divisor,
        precision_bits=args.precision_bits,
    )
    result = run_probe(settings)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["certified_separate_domination_failure"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
