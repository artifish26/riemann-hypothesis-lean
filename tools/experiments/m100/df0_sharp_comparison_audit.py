#!/usr/bin/env python3
"""M100-DF0 Arb audit of the cutoff-44 sharp comparison constant.

This is a source-constant audit, not a DF1 or DF2 decision-producing run.  It
recomputes the X21/FT1 local-energy and smooth-remainder bounds at the frozen
endpoint and combines them with X18's exact first-prime L2 norm.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction

try:
    from flint import arb, ctx, fmpq
except ImportError as error:
    raise SystemExit(
        "df0_sharp_comparison_audit.py requires python-flint==0.8.0"
    ) from error

from high_mode_local_energy_probe import (
    arb_fraction,
    endpoint_text,
    interval_text,
    leakage_fraction,
    remainder_second_derivative_at_two_a,
    right_band_endpoint,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision-bits", type=int, default=192)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.precision_bits < 80:
        raise ValueError("precision-bits must be at least 80")
    ctx.prec = args.precision_bits

    cutoff = 44
    threshold = arb_fraction(Fraction(97, 4))
    pi = arb.pi()
    euler = arb.const_euler()
    log_two = arb(2).log()
    a_star = right_band_endpoint()

    rho = leakage_fraction(cutoff, threshold, pi)
    zero_crossing = a_star * (-euler).exp() / pi
    negative_weight_loss = 4 * zero_crossing**3 / (
        9 * cutoff * (1 - zero_crossing / (cutoff + 1)) ** 2
    )
    high_weight = (pi * threshold / a_star).log() + euler
    ell = high_weight * (1 - rho) - negative_weight_loss

    remainder_variation = 2 * (
        arb(fmpq(-7, 4)) - remainder_second_derivative_at_two_a(a_star)
    )
    primitive_norm = a_star / pi * (
        arb(fmpq(1, (cutoff + 1) ** 2)) + arb(fmpq(2, cutoff))
    ).sqrt()
    delta = remainder_variation * primitive_norm

    suzuki_scalar = (2 * pi).log() + euler
    prime_l2_norm = log_two / arb(2).sqrt()
    norm_penalty = suzuki_scalar + prime_l2_norm + delta
    alpha = 1 - norm_penalty / ell
    two_fifths_norm_margin = arb(fmpq(3, 5)) * ell - norm_penalty

    payload = {
        "experiment": "M100-DF0",
        "artifact": "sharp-comparison-source-constant-audit",
        "decision_producing_df1_or_df2_run": False,
        "settings": {
            "endpoint": "A_(1/2)",
            "cutoff": cutoff,
            "scaled_threshold": "97/4",
            "precision_bits": args.precision_bits,
        },
        "a_star": interval_text(a_star),
        "ell_44": interval_text(ell),
        "ell_44_certified_lower": endpoint_text(ell, upper=False),
        "delta_44": interval_text(delta),
        "delta_44_certified_upper": endpoint_text(delta, upper=True),
        "suzuki_scalar": interval_text(suzuki_scalar),
        "prime_l2_norm": interval_text(prime_l2_norm),
        "alpha_L2": interval_text(alpha),
        "alpha_L2_certified_lower": endpoint_text(alpha, upper=False),
        "two_fifths_norm_margin": interval_text(two_fifths_norm_margin),
        "two_fifths_norm_margin_certified_lower": endpoint_text(
            two_fifths_norm_margin,
            upper=False,
        ),
        "certified_F_ge_two_fifths_E": bool(
            two_fifths_norm_margin > 0
        ),
        "certified_two_fifths_E_ge_two_I": bool(ell > 5),
    }
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
