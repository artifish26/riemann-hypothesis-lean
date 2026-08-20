#!/usr/bin/env python3
"""M100-X08 many-translate probe for Burnol's spectral quadratic form.

The base profile is the L2-normalized smooth bump from M100-X02.  For each
case this script forms `N` overlapping translates, with center spacing
`kappa * half_width`, and chooses cosine coefficients whose finite Fourier
sum is concentrated near a frequency where Burnol's coefficient is negative.

All integrals use deterministic float64 midpoint quadrature and are repeated
at a strictly finer resolution and cutoff.  This is a route filter, not an
interval-certified proof of a sign or of the candidate Burnol radius.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from typing import Sequence

from two_block_burnol_probe import (
    QuadratureSettings,
    burnol_local_coefficient,
    cosine_correction_audit,
    digamma_audit,
    normalized_base_fourier_values,
)


@dataclass(frozen=True)
class ProbeCase:
    half_width: float
    block_count: int


@dataclass(frozen=True)
class WitnessResult:
    half_width: float
    block_count: int
    separation_ratio: float
    center_separation: float
    individual_support_radius: float
    joint_support_radius: float
    target_frequency: float
    diagonal: float
    coefficient_norm_square: float
    quadratic_value: float
    rayleigh_quotient: float


def parse_cases(text: str) -> list[ProbeCase]:
    cases: list[ProbeCase] = []
    for item in text.split(","):
        stripped = item.strip()
        if not stripped:
            continue
        try:
            width_text, count_text = stripped.split(":", maxsplit=1)
            cases.append(ProbeCase(float(width_text), int(count_text)))
        except ValueError as error:
            raise argparse.ArgumentTypeError(
                "cases must have the comma-separated form half_width:block_count"
            ) from error
    if not cases:
        raise argparse.ArgumentTypeError("expected at least one probe case")
    return cases


def geometric_sum(angle: float, count: int) -> complex:
    """Return sum(exp(-i*j*angle), j=0..count-1) stably."""

    reduced = math.remainder(angle, 2.0 * math.pi)
    denominator = math.sin(0.5 * reduced)
    if abs(denominator) <= 1.0e-12:
        return complex(float(count), 0.0)
    amplitude = math.sin(0.5 * count * reduced) / denominator
    phase = -0.5 * (count - 1) * reduced
    return amplitude * complex(math.cos(phase), math.sin(phase))


def cosine_coefficient_fourier_sum(
    scaled_frequency: float,
    half_width: float,
    block_count: int,
    separation_ratio: float,
    target_frequency: float,
) -> complex:
    """Finite translate multiplier, up to an irrelevant unit center phase."""

    spatial_phase = 2.0 * math.pi * separation_ratio * scaled_frequency
    coefficient_phase = (
        2.0
        * math.pi
        * separation_ratio
        * half_width
        * target_frequency
    )
    return 0.5 * (
        geometric_sum(spatial_phase - coefficient_phase, block_count)
        + geometric_sum(spatial_phase + coefficient_phase, block_count)
    )


def coefficient_norm_square(
    half_width: float,
    block_count: int,
    separation_ratio: float,
    target_frequency: float,
) -> float:
    phase = (
        2.0
        * math.pi
        * separation_ratio
        * half_width
        * target_frequency
    )
    return sum(math.cos(index * phase) ** 2 for index in range(block_count))


def evaluate_cases(
    cases: Sequence[ProbeCase],
    separation_ratio: float,
    target_frequency: float,
    settings: QuadratureSettings,
    samples_per_cycle: int,
) -> list[WitnessResult]:
    table_count = settings.outer_nodes
    table_step = settings.scaled_cutoff / table_count
    table_nodes = [index * table_step for index in range(table_count + 1)]
    base_fourier_table = normalized_base_fourier_values(
        table_nodes,
        settings.inner_nodes,
    )
    maximum_span = max(
        separation_ratio * case.half_width * case.block_count
        for case in cases
    )
    frequency_step = 1.0 / (samples_per_cycle * maximum_span)
    maximum_frequency = max(
        settings.scaled_cutoff / case.half_width for case in cases
    )
    sample_count = math.ceil(maximum_frequency / frequency_step)
    diagonal_sums = [0.0 for _case in cases]
    quadratic_sums = [0.0 for _case in cases]

    def interpolate_base_fourier(scaled_frequency: float) -> float:
        coordinate = scaled_frequency / table_step
        left = min(int(coordinate), table_count - 1)
        fraction = coordinate - left
        return (
            (1.0 - fraction) * base_fourier_table[left]
            + fraction * base_fourier_table[left + 1]
        )

    for sample_index in range(sample_count):
        frequency = (sample_index + 0.5) * frequency_step
        coefficient = burnol_local_coefficient(frequency, settings)
        for case_index, case in enumerate(cases):
            scaled = case.half_width * frequency
            if scaled >= settings.scaled_cutoff:
                continue
            transform = interpolate_base_fourier(scaled)
            weight = (
                2.0
                * frequency_step
                * case.half_width
                * coefficient
                * transform
                * transform
            )
            diagonal_sums[case_index] += weight
            multiplier = cosine_coefficient_fourier_sum(
                scaled,
                case.half_width,
                case.block_count,
                separation_ratio,
                target_frequency,
            )
            quadratic_sums[case_index] += weight * abs(multiplier) ** 2

    results: list[WitnessResult] = []
    for case_index, case in enumerate(cases):
        norm_square = coefficient_norm_square(
            case.half_width,
            case.block_count,
            separation_ratio,
            target_frequency,
        )
        quadratic_value = quadratic_sums[case_index]
        separation = separation_ratio * case.half_width
        results.append(
            WitnessResult(
                half_width=case.half_width,
                block_count=case.block_count,
                separation_ratio=separation_ratio,
                center_separation=separation,
                individual_support_radius=case.half_width,
                joint_support_radius=(
                    case.half_width
                    + 0.5 * (case.block_count - 1) * separation
                ),
                target_frequency=target_frequency,
                diagonal=diagonal_sums[case_index],
                coefficient_norm_square=norm_square,
                quadratic_value=quadratic_value,
                rayleigh_quotient=quadratic_value / norm_square,
            )
        )
    return results


def relative_difference(left: float, right: float) -> float:
    return abs(left - right) / max(1.0, abs(left), abs(right))


def compare_results(
    baseline: Sequence[WitnessResult],
    refined: Sequence[WitnessResult],
) -> dict[str, float | bool]:
    if len(baseline) != len(refined):
        raise ValueError("baseline and refined runs have different case counts")
    max_diagonal_delta = 0.0
    max_rayleigh_delta = 0.0
    signs_stable = True
    for first, second in zip(baseline, refined):
        max_diagonal_delta = max(
            max_diagonal_delta,
            relative_difference(first.diagonal, second.diagonal),
        )
        max_rayleigh_delta = max(
            max_rayleigh_delta,
            relative_difference(first.rayleigh_quotient, second.rayleigh_quotient),
        )
        if (first.rayleigh_quotient < 0.0) != (second.rayleigh_quotient < 0.0):
            signs_stable = False
    return {
        "max_relative_diagonal_delta": max_diagonal_delta,
        "max_relative_rayleigh_delta": max_rayleigh_delta,
        "rayleigh_signs_stable": signs_stable,
    }


def run_probe(args: argparse.Namespace) -> dict[str, object]:
    baseline_settings = QuadratureSettings(
        inner_nodes=args.inner_nodes,
        outer_nodes=args.outer_nodes,
        scaled_cutoff=args.scaled_cutoff,
        digamma_shift=args.digamma_shift,
        digamma_terms=args.digamma_terms,
    )
    refined_settings = QuadratureSettings(
        inner_nodes=args.refined_inner_nodes,
        outer_nodes=args.refined_outer_nodes,
        scaled_cutoff=args.refined_scaled_cutoff,
        digamma_shift=args.refined_digamma_shift,
        digamma_terms=args.refined_digamma_terms,
    )
    baseline = evaluate_cases(
        args.cases,
        args.separation_ratio,
        args.target_frequency,
        baseline_settings,
        args.samples_per_cycle,
    )
    refined = evaluate_cases(
        args.cases,
        args.separation_ratio,
        args.target_frequency,
        refined_settings,
        args.refined_samples_per_cycle,
    )
    refinement = compare_results(baseline, refined)
    digamma = digamma_audit()
    support = cosine_correction_audit(
        args.support_epsilon,
        args.support_audit_maximum_frequency,
        args.support_audit_frequency_step,
        refined_settings,
    )
    candidate_radius = float(support["candidate_support_radius"])
    target_coefficient = burnol_local_coefficient(
        args.target_frequency,
        refined_settings,
    )
    negative = [
        result
        for result in refined
        if result.rayleigh_quotient < -args.negative_tolerance
    ]
    distinct_negative_widths = sorted({result.half_width for result in negative})
    audits_passed = (
        digamma["coefficient_shift_term_delta"] <= args.digamma_tolerance
        and digamma["known_real_value_delta"] <= args.digamma_tolerance
        and bool(support["grid_feasible"])
        and float(support["minimum_corrected_value"])
        >= -args.support_audit_tolerance
        and target_coefficient < 0.0
        and all(result.diagonal > args.negative_tolerance for result in refined)
        and all(result.half_width <= candidate_radius for result in refined)
        and refinement["max_relative_rayleigh_delta"]
        <= args.refinement_tolerance
        and refinement["rayleigh_signs_stable"]
    )
    return {
        "id": "M100-X08",
        "status": "INCONCLUSIVE",
        "arithmetic": "Python float64",
        "fourier_convention": "exp(-2*pi*i*x*t)",
        "profile": "L2-normalized C-infinity bump exp(-1/(1-u^2)) on |u|<1",
        "baseline_settings": asdict(baseline_settings),
        "refined_settings": asdict(refined_settings),
        "baseline_samples_per_cycle": args.samples_per_cycle,
        "refined_samples_per_cycle": args.refined_samples_per_cycle,
        "separation_ratio": args.separation_ratio,
        "support_geometry": "overlapping translated intervals",
        "target_frequency": args.target_frequency,
        "target_coefficient": target_coefficient,
        "digamma_audit": digamma,
        "cosine_correction_support_audit": support,
        "refinement_audit": refinement,
        "negative_tolerance": args.negative_tolerance,
        "negative_case_count": len(negative),
        "distinct_negative_half_widths": distinct_negative_widths,
        "baseline_results": [asdict(result) for result in baseline],
        "refined_results": [asdict(result) for result in refined],
        "decision": (
            "reject diagonal or pairwise translated-block positivity as a "
            "finite-to-global mechanism; require a zeta-specific complete "
            "Gram estimate before revisiting support continuation"
        ),
        "passed": audits_passed,
    }


def format_number(value: float) -> str:
    return f"{value:.12e}"


def print_text_report(result: dict[str, object]) -> None:
    baseline = result["baseline_settings"]
    refined = result["refined_settings"]
    digamma = result["digamma_audit"]
    support = result["cosine_correction_support_audit"]
    audit = result["refinement_audit"]
    print("M100-X08 finite translated-block Burnol probe")
    print("warning: float64 discovery calculation; this is not a proof of a sign")
    print(f"profile={result['profile']}")
    print(f"fourier={result['fourier_convention']}")
    print(
        "baseline="
        f"inner:{baseline['inner_nodes']} outer:{baseline['outer_nodes']} "
        f"scaled_cutoff:{baseline['scaled_cutoff']:g} "
        f"samples_per_cycle:{result['baseline_samples_per_cycle']}"
    )
    print(
        "refined="
        f"inner:{refined['inner_nodes']} outer:{refined['outer_nodes']} "
        f"scaled_cutoff:{refined['scaled_cutoff']:g} "
        f"samples_per_cycle:{result['refined_samples_per_cycle']}"
    )
    print(
        f"spacing_ratio={result['separation_ratio']:g} "
        f"geometry={result['support_geometry']}"
    )
    print(
        f"target_frequency={result['target_frequency']:g} "
        f"coefficient={format_number(result['target_coefficient'])}"
    )
    print()
    print("audits")
    print(
        "  digamma coefficient delta="
        f"{format_number(digamma['coefficient_shift_term_delta'])}"
    )
    print(
        "  digamma known-value delta="
        f"{format_number(digamma['known_real_value_delta'])}"
    )
    print(
        "  candidate individual support radius="
        f"{format_number(support['candidate_support_radius'])}"
    )
    print(
        "  cosine-correction grid="
        f"{'FEASIBLE' if support['grid_feasible'] else 'INFEASIBLE'} "
        f"minimum={format_number(support['minimum_corrected_value'])}"
    )
    print(
        "  max relative diagonal delta="
        f"{format_number(audit['max_relative_diagonal_delta'])}"
    )
    print(
        "  max relative Rayleigh delta="
        f"{format_number(audit['max_relative_rayleigh_delta'])}"
    )
    print(
        "  Rayleigh signs="
        f"{'STABLE' if audit['rayleigh_signs_stable'] else 'UNSTABLE'}"
    )
    print()
    print("refined cosine witnesses")
    for item in result["refined_results"]:
        print(
            f"  width={item['half_width']:g} N={item['block_count']} "
            f"joint_radius={item['joint_support_radius']:.6g} "
            f"diagonal={format_number(item['diagonal'])} "
            f"Q/norm2={format_number(item['rayleigh_quotient'])}"
        )
    print()
    print(
        f"negative_cases={result['negative_case_count']} "
        f"distinct_widths={result['distinct_negative_half_widths']}"
    )
    print(f"status={result['status']}")
    print(f"audit_status={'PASS' if result['passed'] else 'FAIL'}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cases",
        type=parse_cases,
        default=parse_cases(
            "0.001:20000,0.002:10000,0.004:5000,0.005:4000"
        ),
    )
    parser.add_argument("--separation-ratio", type=float, default=0.1)
    parser.add_argument("--target-frequency", type=float, default=2.07)
    parser.add_argument("--inner-nodes", type=int, default=400)
    parser.add_argument("--outer-nodes", type=int, default=2560)
    parser.add_argument("--scaled-cutoff", type=float, default=25.0)
    parser.add_argument("--digamma-shift", type=float, default=24.0)
    parser.add_argument("--digamma-terms", type=int, default=8)
    parser.add_argument("--refined-inner-nodes", type=int, default=560)
    parser.add_argument("--refined-outer-nodes", type=int, default=5120)
    parser.add_argument("--refined-scaled-cutoff", type=float, default=32.0)
    parser.add_argument("--refined-digamma-shift", type=float, default=32.0)
    parser.add_argument("--refined-digamma-terms", type=int, default=8)
    parser.add_argument("--samples-per-cycle", type=int, default=12)
    parser.add_argument("--refined-samples-per-cycle", type=int, default=24)
    parser.add_argument("--negative-tolerance", type=float, default=1.0e-8)
    parser.add_argument("--digamma-tolerance", type=float, default=5.0e-13)
    parser.add_argument("--refinement-tolerance", type=float, default=2.0e-4)
    parser.add_argument("--support-epsilon", type=float, default=0.15)
    parser.add_argument(
        "--support-audit-maximum-frequency",
        type=float,
        default=200.0,
    )
    parser.add_argument("--support-audit-frequency-step", type=float, default=0.01)
    parser.add_argument("--support-audit-tolerance", type=float, default=1.0e-10)
    parser.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_argument_parser().parse_args(argv)
    if any(case.half_width <= 0.0 for case in args.cases):
        raise SystemExit("every half-width must be positive")
    if any(case.block_count < 2 for case in args.cases):
        raise SystemExit("every block count must be at least two")
    if args.separation_ratio <= 0.0:
        raise SystemExit("separation ratio must be positive")
    if args.samples_per_cycle < 4 or args.refined_samples_per_cycle < 4:
        raise SystemExit("samples per cycle must be at least four")
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True, allow_nan=False))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
