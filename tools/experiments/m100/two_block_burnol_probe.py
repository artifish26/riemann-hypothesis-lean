#!/usr/bin/env python3
"""M100-X02 two-block probe for Burnol's checked spectral coefficient.

The base profile is the standard smooth bump on [-1, 1]. Two translated,
L2-normalized copies have disjoint support when their center separation is
greater than twice their half-width. Under the project's Fourier convention,
their symmetric cross term is

    integral alpha(t) * |Phi_r(t)|^2 * cos(2*pi*d*t) dt,

where alpha is exactly the coefficient used by `burnolLocalCoefficient`.

This is a float64 discovery probe with convergence audits. It is not an
interval-certified positivity or negativity proof.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from dataclasses import asdict, dataclass
from typing import Sequence


ASYMPTOTIC_DIGAMMA_COEFFICIENTS = (
    -1.0 / 12.0,
    1.0 / 120.0,
    -1.0 / 252.0,
    1.0 / 240.0,
    -1.0 / 132.0,
    691.0 / 32760.0,
    -1.0 / 12.0,
    3617.0 / 8160.0,
)


@dataclass(frozen=True)
class QuadratureSettings:
    inner_nodes: int
    outer_nodes: int
    scaled_cutoff: float
    digamma_shift: float
    digamma_terms: int


@dataclass(frozen=True)
class GramResult:
    half_width: float
    separation_ratio: float
    center_separation: float
    joint_support_radius: float
    diagonal: float
    cross_term: float
    eigenvalue_symmetric: float
    eigenvalue_antisymmetric: float
    minimum_eigenvalue: float
    minimum_direction: str


def parse_float_list(text: str) -> list[float]:
    values = [float(item.strip()) for item in text.split(",") if item.strip()]
    if not values:
        raise argparse.ArgumentTypeError("expected a nonempty comma-separated list")
    return values


def gauss_legendre_nodes_weights(
    count: int,
    lower: float,
    upper: float,
) -> tuple[list[float], list[float]]:
    """Compute Gauss-Legendre nodes and weights without external packages."""

    if count < 2:
        raise ValueError("Gauss-Legendre quadrature requires at least two nodes")
    midpoint = 0.5 * (lower + upper)
    half_length = 0.5 * (upper - lower)
    nodes = [0.0] * count
    weights = [0.0] * count
    half_count = (count + 1) // 2
    for index in range(half_count):
        root = math.cos(math.pi * (index + 0.75) / (count + 0.5))
        derivative = 0.0
        for _iteration in range(100):
            previous = 1.0
            current = root
            for degree in range(2, count + 1):
                next_value = (
                    (2 * degree - 1) * root * current
                    - (degree - 1) * previous
                ) / degree
                previous, current = current, next_value
            derivative = count * (root * current - previous) / (root * root - 1.0)
            updated = root - current / derivative
            if abs(updated - root) <= 2.0e-16:
                root = updated
                break
            root = updated
        else:
            raise RuntimeError("Gauss-Legendre root iteration did not converge")
        weight = 2.0 / ((1.0 - root * root) * derivative * derivative)
        left_index = index
        right_index = count - 1 - index
        nodes[left_index] = midpoint - half_length * root
        nodes[right_index] = midpoint + half_length * root
        weights[left_index] = half_length * weight
        weights[right_index] = half_length * weight
    return nodes, weights


def smooth_bump(unit_coordinate: float) -> float:
    square = unit_coordinate * unit_coordinate
    if square >= 1.0:
        return 0.0
    return math.exp(-1.0 / (1.0 - square))


def complex_digamma(
    value: complex,
    shift_threshold: float,
    term_count: int,
) -> complex:
    """Recurrence plus the standard Bernoulli asymptotic expansion."""

    shifted = value
    correction = 0.0j
    while shifted.real < shift_threshold:
        correction -= 1.0 / shifted
        shifted += 1.0
    result = cmath.log(shifted) - 0.5 / shifted
    inverse_square = 1.0 / (shifted * shifted)
    inverse_power = inverse_square
    for coefficient in ASYMPTOTIC_DIGAMMA_COEFFICIENTS[:term_count]:
        result += coefficient * inverse_power
        inverse_power *= inverse_square
    return result + correction


def burnol_local_coefficient(
    frequency: float,
    settings: QuadratureSettings,
) -> float:
    gamma_line = complex(0.25, frequency / 2.0)
    oscillatory = (
        8.0
        * math.sqrt(2.0)
        * math.cos(math.log(2.0) * frequency)
        / (1.0 + 4.0 * frequency * frequency)
    )
    return (
        oscillatory
        - math.log(math.pi)
        + complex_digamma(
            gamma_line,
            settings.digamma_shift,
            settings.digamma_terms,
        ).real
    )


def normalized_base_fourier_values(
    scaled_frequencies: Sequence[float],
    inner_nodes: int,
) -> list[float]:
    nodes, weights = gauss_legendre_nodes_weights(inner_nodes, 0.0, 1.0)
    bump_values = [smooth_bump(node) for node in nodes]
    norm_square = 2.0 * sum(
        weight * value * value
        for weight, value in zip(weights, bump_values)
    )
    normalization = 1.0 / math.sqrt(norm_square)
    return [
        2.0
        * normalization
        * sum(
            weight * value * math.cos(2.0 * math.pi * node * frequency)
            for node, weight, value in zip(nodes, weights, bump_values)
        )
        for frequency in scaled_frequencies
    ]


def evaluate_sweep(
    half_widths: Sequence[float],
    separation_ratios: Sequence[float],
    settings: QuadratureSettings,
) -> list[GramResult]:
    scaled_nodes, scaled_weights = gauss_legendre_nodes_weights(
        settings.outer_nodes,
        0.0,
        settings.scaled_cutoff,
    )
    base_fourier = normalized_base_fourier_values(
        scaled_nodes,
        settings.inner_nodes,
    )
    results: list[GramResult] = []
    for half_width in half_widths:
        weighted_spectrum = [
            2.0
            * weight
            * burnol_local_coefficient(scaled / half_width, settings)
            * transform
            * transform
            for scaled, weight, transform in zip(
                scaled_nodes,
                scaled_weights,
                base_fourier,
            )
        ]
        diagonal = sum(weighted_spectrum)
        for ratio in separation_ratios:
            center_separation = ratio * half_width
            joint_support_radius = half_width + 0.5 * center_separation
            cross_term = sum(
                weight
                * math.cos(2.0 * math.pi * ratio * scaled)
                for weight, scaled in zip(weighted_spectrum, scaled_nodes)
            )
            symmetric = diagonal + cross_term
            antisymmetric = diagonal - cross_term
            if symmetric <= antisymmetric:
                minimum = symmetric
                direction = "(1,1)/sqrt(2)"
            else:
                minimum = antisymmetric
                direction = "(1,-1)/sqrt(2)"
            results.append(
                GramResult(
                    half_width=half_width,
                    separation_ratio=ratio,
                    center_separation=center_separation,
                    joint_support_radius=joint_support_radius,
                    diagonal=diagonal,
                    cross_term=cross_term,
                    eigenvalue_symmetric=symmetric,
                    eigenvalue_antisymmetric=antisymmetric,
                    minimum_eigenvalue=minimum,
                    minimum_direction=direction,
                )
            )
    return results


def digamma_audit() -> dict[str, float]:
    reference = QuadratureSettings(2, 2, 1.0, 24.0, 8)
    baseline = QuadratureSettings(2, 2, 1.0, 16.0, 7)
    sample_frequencies = (0.0, 0.5, 1.0, 5.0, 20.0, 100.0)
    coefficient_delta = max(
        abs(
            burnol_local_coefficient(frequency, baseline)
            - burnol_local_coefficient(frequency, reference)
        )
        for frequency in sample_frequencies
    )
    psi_one = complex_digamma(1.0 + 0.0j, 16.0, 7).real
    psi_half = complex_digamma(0.5 + 0.0j, 16.0, 7).real
    euler_gamma = 0.5772156649015328606
    known_value_delta = max(
        abs(psi_one + euler_gamma),
        abs(psi_half + euler_gamma + 2.0 * math.log(2.0)),
    )
    return {
        "coefficient_shift_term_delta": coefficient_delta,
        "known_real_value_delta": known_value_delta,
    }


def cosine_correction_audit(
    epsilon: float,
    maximum_frequency: float,
    frequency_step: float,
    settings: QuadratureSettings,
) -> dict[str, float | int | bool]:
    """Find the feasible A interval on a deterministic frequency grid."""

    lower_bound = 0.0
    upper_bound = math.inf
    samples: list[tuple[float, float, float]] = []
    impossible_samples = 0
    sample_count = int(round(maximum_frequency / frequency_step)) + 1
    for index in range(sample_count):
        frequency = index * frequency_step
        coefficient = burnol_local_coefficient(frequency, settings)
        cosine = math.cos(epsilon * frequency)
        samples.append((frequency, coefficient, cosine))
        if cosine > 1.0e-12:
            lower_bound = max(lower_bound, -coefficient / cosine)
        elif cosine < -1.0e-12:
            upper_bound = min(upper_bound, coefficient / (-cosine))
        elif coefficient < 0.0:
            impossible_samples += 1
    feasible = (
        impossible_samples == 0
        and lower_bound >= 0.0
        and lower_bound <= upper_bound
    )
    if feasible:
        amplitude = (
            0.5 * (lower_bound + upper_bound)
            if math.isfinite(upper_bound)
            else lower_bound + 1.0
        )
        minimum_corrected = min(
            coefficient + amplitude * cosine
            for _frequency, coefficient, cosine in samples
        )
    else:
        amplitude = math.nan
        minimum_corrected = math.nan
    return {
        "epsilon": epsilon,
        "candidate_support_radius": epsilon / (8.0 * math.pi),
        "maximum_frequency": maximum_frequency,
        "frequency_step": frequency_step,
        "sample_count": sample_count,
        "amplitude_lower_bound": lower_bound,
        "amplitude_upper_bound": upper_bound,
        "selected_amplitude": amplitude,
        "minimum_corrected_value": minimum_corrected,
        "impossible_samples": impossible_samples,
        "grid_feasible": feasible,
    }


def relative_difference(left: float, right: float) -> float:
    return abs(left - right) / max(1.0, abs(left), abs(right))


def compare_refinement(
    baseline: Sequence[GramResult],
    refined: Sequence[GramResult],
) -> dict[str, float | bool]:
    if len(baseline) != len(refined):
        raise ValueError("baseline and refined sweeps have different sizes")
    max_diagonal_delta = 0.0
    max_cross_delta = 0.0
    max_eigenvalue_delta = 0.0
    sign_stable = True
    for first, second in zip(baseline, refined):
        max_diagonal_delta = max(
            max_diagonal_delta,
            relative_difference(first.diagonal, second.diagonal),
        )
        max_cross_delta = max(
            max_cross_delta,
            relative_difference(first.cross_term, second.cross_term),
        )
        max_eigenvalue_delta = max(
            max_eigenvalue_delta,
            relative_difference(first.minimum_eigenvalue, second.minimum_eigenvalue),
        )
        if (first.minimum_eigenvalue < 0.0) != (second.minimum_eigenvalue < 0.0):
            sign_stable = False
    return {
        "max_relative_diagonal_delta": max_diagonal_delta,
        "max_relative_cross_delta": max_cross_delta,
        "max_relative_minimum_eigenvalue_delta": max_eigenvalue_delta,
        "minimum_eigenvalue_sign_stable": sign_stable,
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
        inner_nodes=args.inner_nodes + args.refinement_nodes,
        outer_nodes=args.outer_nodes + args.refinement_nodes,
        scaled_cutoff=args.scaled_cutoff * args.refinement_cutoff_factor,
        digamma_shift=args.digamma_shift + 8.0,
        digamma_terms=min(8, args.digamma_terms + 1),
    )
    baseline = evaluate_sweep(args.half_widths, args.separation_ratios, baseline_settings)
    refined = evaluate_sweep(args.half_widths, args.separation_ratios, refined_settings)
    refinement = compare_refinement(baseline, refined)
    digamma = digamma_audit()

    support_audit = cosine_correction_audit(
        args.support_epsilon,
        args.support_audit_maximum_frequency,
        args.support_audit_frequency_step,
        refined_settings,
    )
    candidate_radius = support_audit["candidate_support_radius"]

    locally_positive = [result for result in refined if result.diagonal > args.negative_tolerance]
    negative = [
        result
        for result in locally_positive
        if result.minimum_eigenvalue < -args.negative_tolerance
    ]
    within_candidate_joint_support = [
        result
        for result in refined
        if result.joint_support_radius <= candidate_radius
    ]
    negative_within_candidate_joint_support = [
        result
        for result in negative
        if result.joint_support_radius <= candidate_radius
    ]
    negative_outside_candidate_joint_support = [
        result
        for result in negative
        if result.joint_support_radius > candidate_radius
    ]
    minimum = min(refined, key=lambda result: result.minimum_eigenvalue)
    minimum_within_joint_support = min(
        within_candidate_joint_support,
        key=lambda result: result.minimum_eigenvalue,
    )
    audits_passed = (
        digamma["coefficient_shift_term_delta"] <= args.digamma_tolerance
        and digamma["known_real_value_delta"] <= args.digamma_tolerance
        and support_audit["grid_feasible"]
        and support_audit["minimum_corrected_value"]
        >= -args.support_audit_tolerance
        and refinement["max_relative_minimum_eigenvalue_delta"]
        <= args.refinement_tolerance
        and refinement["minimum_eigenvalue_sign_stable"]
    )
    if audits_passed and negative_within_candidate_joint_support:
        status = "REFUTED"
        decision = (
            "reject two-block PSD inside the numerically audited candidate "
            "Burnol joint support envelope"
        )
    elif negative_within_candidate_joint_support:
        status = "INCONCLUSIVE"
        decision = (
            "repeat the support-radius calculation with certified error bounds; "
            "a negative direction was detected inside the candidate joint "
            "support envelope, "
            "but the numerical audits did not pass"
        )
    elif negative_outside_candidate_joint_support:
        status = "INCONCLUSIVE"
        decision = (
            "retain the support-certified two-block lane; negative directions "
            "were found only outside the numerically audited candidate joint "
            "support envelope"
        )
    else:
        status = "INCONCLUSIVE"
        decision = (
            "retain the support-certified two-block lane; no stable negative "
            "direction was found in the tested family"
        )

    return {
        "id": "M100-X02",
        "status": status,
        "arithmetic": "Python float64",
        "fourier_convention": "exp(-2*pi*i*x*t)",
        "profile": "L2-normalized C-infinity bump exp(-1/(1-u^2)) on |u|<1",
        "baseline_settings": asdict(baseline_settings),
        "refined_settings": asdict(refined_settings),
        "half_widths": args.half_widths,
        "separation_ratios": args.separation_ratios,
        "strictly_disjoint": all(ratio > 2.0 for ratio in args.separation_ratios),
        "digamma_audit": digamma,
        "cosine_correction_support_audit": support_audit,
        "refinement_audit": refinement,
        "minimum_result": asdict(minimum),
        "minimum_within_candidate_joint_support_result": asdict(
            minimum_within_joint_support
        ),
        "negative_locally_positive_results": [asdict(result) for result in negative],
        "negative_within_candidate_joint_support_results": [
            asdict(result) for result in negative_within_candidate_joint_support
        ],
        "negative_outside_candidate_joint_support_results": [
            asdict(result) for result in negative_outside_candidate_joint_support
        ],
        "results": [asdict(result) for result in refined],
        "decision": decision,
        "passed": audits_passed,
    }


def format_number(value: float) -> str:
    return f"{value:.12e}"


def print_text_report(result: dict[str, object]) -> None:
    baseline = result["baseline_settings"]
    refined = result["refined_settings"]
    digamma = result["digamma_audit"]
    audit = result["refinement_audit"]
    minimum = result["minimum_result"]
    support = result["cosine_correction_support_audit"]
    support_minimum = result["minimum_within_candidate_joint_support_result"]
    negatives = result["negative_locally_positive_results"]
    negative_inside = result["negative_within_candidate_joint_support_results"]
    negative_outside = result["negative_outside_candidate_joint_support_results"]

    print("M100-X02 two-block Burnol spectral Gram probe")
    print("warning: float64 discovery calculation; this is not a proof of a sign")
    print(f"profile={result['profile']}")
    print(f"fourier={result['fourier_convention']}")
    print(
        "baseline="
        f"inner:{baseline['inner_nodes']} outer:{baseline['outer_nodes']} "
        f"scaled_cutoff:{baseline['scaled_cutoff']:g}"
    )
    print(
        "refined="
        f"inner:{refined['inner_nodes']} outer:{refined['outer_nodes']} "
        f"scaled_cutoff:{refined['scaled_cutoff']:g}"
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
        "  max relative diagonal delta="
        f"{format_number(audit['max_relative_diagonal_delta'])}"
    )
    print(
        "  max relative cross delta="
        f"{format_number(audit['max_relative_cross_delta'])}"
    )
    print(
        "  max relative minimum-eigenvalue delta="
        f"{format_number(audit['max_relative_minimum_eigenvalue_delta'])}"
    )
    print(
        "  minimum-eigenvalue signs="
        f"{'STABLE' if audit['minimum_eigenvalue_sign_stable'] else 'UNSTABLE'}"
    )
    print(
        "  cosine-correction grid="
        f"{'FEASIBLE' if support['grid_feasible'] else 'INFEASIBLE'} "
        f"epsilon={support['epsilon']:g} A={support['selected_amplitude']:.12e}"
    )
    print(
        "  candidate support radius="
        f"{support['candidate_support_radius']:.12e} "
        f"minimum corrected={support['minimum_corrected_value']:.12e}"
    )
    print()
    print("minimum tested Gram direction")
    print(
        f"  half_width={minimum['half_width']:g} "
        f"separation_ratio={minimum['separation_ratio']:g} "
        f"center_separation={minimum['center_separation']:g} "
        f"joint_support_radius={minimum['joint_support_radius']:g}"
    )
    print(
        f"  diagonal={format_number(minimum['diagonal'])} "
        f"cross={format_number(minimum['cross_term'])}"
    )
    print(
        f"  eigen_symmetric={format_number(minimum['eigenvalue_symmetric'])} "
        f"eigen_antisymmetric={format_number(minimum['eigenvalue_antisymmetric'])}"
    )
    print(f"  witness={minimum['minimum_direction']}")
    print()
    print("minimum inside candidate joint support envelope")
    print(
        f"  half_width={support_minimum['half_width']:g} "
        f"separation_ratio={support_minimum['separation_ratio']:g} "
        f"joint_support_radius={support_minimum['joint_support_radius']:g} "
        f"diagonal={format_number(support_minimum['diagonal'])} "
        f"cross={format_number(support_minimum['cross_term'])} "
        f"min={format_number(support_minimum['minimum_eigenvalue'])}"
    )
    print()
    print(
        f"stable negative locally-positive cases={len(negatives)} "
        f"inside_candidate_joint_support={len(negative_inside)} "
        f"outside_candidate_joint_support={len(negative_outside)}"
    )
    for item in negatives[:10]:
        print(
            f"  width={item['half_width']:g} ratio={item['separation_ratio']:g} "
            f"joint_radius={item['joint_support_radius']:g} "
            f"diag={format_number(item['diagonal'])} "
            f"cross={format_number(item['cross_term'])} "
            f"min={format_number(item['minimum_eigenvalue'])} "
            f"witness={item['minimum_direction']}"
        )
    print()
    print(f"status={result['status']}")
    print(f"audit_status={'PASS' if result['passed'] else 'FAIL'}")
    print(f"decision={result['decision']}")


def build_argument_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--half-widths",
        type=parse_float_list,
        default=parse_float_list("0.001,0.002,0.004,0.005,0.02,0.05,0.1,0.2"),
        help="comma-separated support half-widths",
    )
    parser.add_argument(
        "--separation-ratios",
        type=parse_float_list,
        default=parse_float_list("2.05,2.25,2.5,3,4,6,8,12"),
        help="center separation divided by support half-width; every value must exceed 2",
    )
    parser.add_argument("--inner-nodes", type=int, default=240)
    parser.add_argument("--outer-nodes", type=int, default=480)
    parser.add_argument("--scaled-cutoff", type=float, default=20.0)
    parser.add_argument("--digamma-shift", type=float, default=16.0)
    parser.add_argument("--digamma-terms", type=int, default=7)
    parser.add_argument("--refinement-nodes", type=int, default=160)
    parser.add_argument("--refinement-cutoff-factor", type=float, default=1.25)
    parser.add_argument("--negative-tolerance", type=float, default=1.0e-8)
    parser.add_argument("--digamma-tolerance", type=float, default=5.0e-13)
    parser.add_argument("--refinement-tolerance", type=float, default=5.0e-5)
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
    if any(width <= 0.0 for width in args.half_widths):
        raise SystemExit("every half-width must be positive")
    if any(ratio <= 2.0 for ratio in args.separation_ratios):
        raise SystemExit("every separation ratio must exceed 2 for disjoint support")
    if not any(
        width * (1.0 + 0.5 * ratio)
        <= args.support_epsilon / (8.0 * math.pi)
        for width in args.half_widths
        for ratio in args.separation_ratios
    ):
        raise SystemExit(
            "at least one joint support envelope must lie inside the candidate radius"
        )
    if not 1 <= args.digamma_terms <= len(ASYMPTOTIC_DIGAMMA_COEFFICIENTS):
        raise SystemExit("--digamma-terms is outside the implemented range")
    result = run_probe(args)
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print_text_report(result)
    return 0 if result["passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
