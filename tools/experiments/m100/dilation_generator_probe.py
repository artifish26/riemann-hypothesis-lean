#!/usr/bin/env python3
"""M100-X11 Gaussian dilation-generator route filter.

For the L2-normalized dilation

    D_a g(x) = exp(a/2) g(exp(a) x)

and the self-Fourier Gaussian ``g(x) = exp(-pi*x^2)``, the entire
autocorrelation source at ``z`` is, up to the fixed positive Gaussian norm,

    exp(-a) * exp(-2*pi*exp(-2*a)*z^2).

This probe evaluates the exact analytic value and its parameter derivative on
the X00 symmetry-preserving critical-line pair and off-line quartet.  These
are synthetic zero models, not zeta zero data.  A sign change rejects generic
dilation monotonicity; it says nothing about RH or the sign of the actual zeta
residual.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class SyntheticOrbit:
    name: str
    beta: float
    gamma: float

    @property
    def displacement(self) -> float:
        return self.beta - 0.5

    @property
    def paired_factor(self) -> float:
        return 2.0 if self.displacement == 0.0 else 4.0


@dataclass(frozen=True)
class OrbitAudit:
    name: str
    beta: float
    gamma: float
    minimum_value: float
    maximum_value: float
    minimum_generator: float
    maximum_generator: float
    generator_sign_change_intervals: tuple[tuple[float, float], ...]
    maximum_finite_difference_error: float
    has_both_generator_signs: bool


def gaussian_orbit_value(orbit: SyntheticOrbit, parameter: float) -> float:
    """Paired Gaussian zero-side value, up to one fixed positive factor."""

    delta = orbit.displacement
    scale = math.exp(-2.0 * parameter)
    decay = 2.0 * math.pi * (orbit.gamma**2 - delta**2) * scale
    phase = 4.0 * math.pi * orbit.gamma * delta * scale
    return (
        orbit.paired_factor
        * math.exp(-parameter)
        * math.exp(-decay)
        * math.cos(phase)
    )


def gaussian_orbit_generator(orbit: SyntheticOrbit, parameter: float) -> float:
    """Exact derivative with respect to the logarithmic dilation parameter."""

    delta = orbit.displacement
    scale = math.exp(-2.0 * parameter)
    decay = 2.0 * math.pi * (orbit.gamma**2 - delta**2) * scale
    phase = 4.0 * math.pi * orbit.gamma * delta * scale
    prefactor = orbit.paired_factor * math.exp(-parameter) * math.exp(-decay)
    return prefactor * (
        (-1.0 + 2.0 * decay) * math.cos(phase)
        + 2.0 * phase * math.sin(phase)
    )


def parameter_grid(start: float, stop: float, step: float) -> list[float]:
    count = int(round((stop - start) / step))
    return [start + step * index for index in range(count + 1)]


def sign_change_intervals(
    parameters: list[float], values: list[float]
) -> tuple[tuple[float, float], ...]:
    intervals: list[tuple[float, float]] = []
    for left_parameter, right_parameter, left, right in zip(
        parameters, parameters[1:], values, values[1:]
    ):
        if left == 0.0 or right == 0.0 or (left < 0.0 < right) or (right < 0.0 < left):
            intervals.append((left_parameter, right_parameter))
    return tuple(intervals)


def audit_orbit(
    orbit: SyntheticOrbit, parameters: list[float], finite_difference_step: float
) -> OrbitAudit:
    values = [gaussian_orbit_value(orbit, parameter) for parameter in parameters]
    generators = [
        gaussian_orbit_generator(orbit, parameter) for parameter in parameters
    ]
    finite_difference_errors = []
    for parameter, generator in zip(parameters, generators):
        finite_difference = (
            gaussian_orbit_value(orbit, parameter + finite_difference_step)
            - gaussian_orbit_value(orbit, parameter - finite_difference_step)
        ) / (2.0 * finite_difference_step)
        scale = max(1.0e-300, abs(generator), abs(finite_difference))
        finite_difference_errors.append(abs(generator - finite_difference) / scale)
    return OrbitAudit(
        name=orbit.name,
        beta=orbit.beta,
        gamma=orbit.gamma,
        minimum_value=min(values),
        maximum_value=max(values),
        minimum_generator=min(generators),
        maximum_generator=max(generators),
        generator_sign_change_intervals=sign_change_intervals(parameters, generators),
        maximum_finite_difference_error=max(finite_difference_errors),
        has_both_generator_signs=min(generators) < 0.0 < max(generators),
    )


def run_probe(args: argparse.Namespace) -> dict[str, object]:
    parameters = parameter_grid(args.parameter_start, args.parameter_stop, args.step)
    orbits = (
        SyntheticOrbit("critical_line_pair", 0.5, 5.0),
        SyntheticOrbit("x00_off_line_quartet", 0.7, 5.0),
        SyntheticOrbit("x00_exact_rational_quartet", 0.9, 0.001),
    )
    audits = [
        audit_orbit(orbit, parameters, args.finite_difference_step)
        for orbit in orbits
    ]
    return {
        "experiment": "M100-X11",
        "model": "L2-normalized dilation of the degree-zero pi-Gaussian",
        "parameter_range": [args.parameter_start, args.parameter_stop],
        "parameter_step": args.step,
        "finite_difference_step": args.finite_difference_step,
        "audits": [asdict(audit) for audit in audits],
        "decision": (
            "reject generic one-sided dilation monotonicity"
            if any(audit.has_both_generator_signs for audit in audits)
            else "inconclusive"
        ),
        "scope": (
            "synthetic zero route filter only; not actual zeta sign evidence"
        ),
    }


def print_report(result: dict[str, object]) -> None:
    print("M100-X11 Gaussian dilation-generator probe")
    print(f"parameter range: {result['parameter_range']}")
    print(f"parameter step: {result['parameter_step']}")
    for audit in result["audits"]:
        print(f"  {audit['name']}")
        print(
            "    value range: "
            f"[{audit['minimum_value']:.12e}, {audit['maximum_value']:.12e}]"
        )
        print(
            "    generator range: "
            f"[{audit['minimum_generator']:.12e}, "
            f"{audit['maximum_generator']:.12e}]"
        )
        print(
            "    generator sign-change intervals: "
            f"{audit['generator_sign_change_intervals']}"
        )
        print(
            "    maximum relative finite-difference error: "
            f"{audit['maximum_finite_difference_error']:.3e}"
        )
    print(f"decision: {result['decision']}")
    print(f"scope: {result['scope']}")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--parameter-start", type=float, default=0.0)
    parser.add_argument("--parameter-stop", type=float, default=8.0)
    parser.add_argument("--step", type=float, default=0.002)
    parser.add_argument("--finite-difference-step", type=float, default=1.0e-6)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.parameter_stop <= args.parameter_start:
        raise SystemExit("parameter stop must exceed parameter start")
    if args.step <= 0.0 or args.finite_difference_step <= 0.0:
        raise SystemExit("steps must be positive")
    return args


def main() -> None:
    args = parse_args()
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print_report(result)


if __name__ == "__main__":
    main()
