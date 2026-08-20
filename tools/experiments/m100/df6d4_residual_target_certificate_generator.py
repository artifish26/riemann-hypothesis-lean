#!/usr/bin/env python3
"""Generate exact rational certificates for the final DF6D4 targets.

The input intervals are exported by Lean from the live even and odd residual
certificate target grids.  Python constructs rational Gram factors, but Lean
rechecks the interval data, the factor residuals, and the bridge back to the
live grids before either certificate is consumed.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from decimal import Decimal, localcontext
from fractions import Fraction
from math import ceil, floor
from pathlib import Path
from typing import Iterable

# The whole-grid even diagonal bridge consumes about 1.4e-8 more exact
# residual margin than the former row-12-only policy.  Recenter the generated
# Gram factor with 5e-8 of residual slack, staying below FT3's strict
# 5.5827684091e-8 even target spectral lower bound.  The generator and Lean
# still reject the artifact unless the resulting exact residual checks pass.
EVEN_RESIDUAL_SLACK = Fraction(1, 20_000_000)
ODD_RESIDUAL_SLACK = Fraction(1, 10_000)
FACTOR_BITS = 180
DECIMAL_PRECISION = 150
ARB_PRECISION_BITS = 192
ARB_ENTRY_GRID_DENOMINATOR = 10**14
# Preserve the installed 3.5e-10 off-diagonal bridge allowance.  Stage-2 row
# 12 showed that only the even diagonal lower endpoint needed more room, so the
# final candidate policy widens diagonal entries independently rather than
# perturbing already-admitted off-diagonal entries.  A live fixed-grid scan of
# all 45 diagonals found the worst additional requirement at row 44:
# 2214297381 / 200000000000000000 beyond the former 1e-9 allowance.  The 1.5e-8
# policy therefore retains about 2.93e-9 of whole-grid containment headroom.
EVEN_ARB_LEAN_BRIDGE_PADDING = Fraction(7, 20_000_000_000)
EVEN_ARB_LEAN_DIAGONAL_BRIDGE_PADDING = Fraction(3, 200_000_000)
# The materialized dependency-aware odd (0,0) enclosure extends about
# 2.86e-10 beyond the direct Arb entry grid.  Use a conservative 1e-9 bridge
# allowance only for the initial odd probe.  A subsequent live scan of all 44
# diagonals found the worst additional requirement at row 43:
# 1023053223 / 1000000000000000000 beyond that allowance.  Freeze 3e-9 for the
# whole odd grid; Lean still rechecks both certificate margins exactly.
ODD_ARB_LEAN_BRIDGE_PADDING = Fraction(3, 1_000_000_000)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        required=True,
        help="generated Lean certificate-data module",
    )
    parser.add_argument(
        "--lake",
        type=Path,
        default=Path.home() / ".elan" / "bin" / "lake.exe",
        help="Lake executable used to run the checked Lean grid exporter",
    )
    parser.add_argument(
        "--source",
        choices=("arb", "lean"),
        default="arb",
        help="matrix source; Arb is fast, while Lean exports the live grid",
    )
    parser.add_argument(
        "--python-flint-path",
        type=Path,
        help="directory containing the pinned python-flint 0.8.0 package",
    )
    return parser.parse_args()


def decimal_from_fraction(value: Fraction) -> Decimal:
    return Decimal(value.numerator) / Decimal(value.denominator)


def round_to_dyadic(value: Decimal, bits: int) -> Fraction:
    exact = Fraction(value)
    denominator = 1 << bits
    scaled_numerator = exact.numerator * denominator
    divisor = exact.denominator
    sign = -1 if scaled_numerator < 0 else 1
    quotient, remainder = divmod(abs(scaled_numerator), divisor)
    if 2 * remainder >= divisor:
        quotient += 1
    return Fraction(sign * quotient, denominator)


def rational_cholesky_factor(
    intervals: list[list[tuple[Fraction, Fraction]]],
    slack: Fraction,
) -> list[list[Fraction]]:
    size = len(intervals)
    with localcontext() as decimal_context:
        decimal_context.prec = DECIMAL_PRECISION
        midpoint = [
            [
                decimal_from_fraction((lower + upper) / 2)
                - (decimal_from_fraction(slack) if row == column else Decimal(0))
                for column, (lower, upper) in enumerate(intervals[row])
            ]
            for row in range(size)
        ]
        lower_factor = [[Decimal(0) for _ in range(size)] for _ in range(size)]
        for row in range(size):
            for column in range(row + 1):
                residual = midpoint[row][column] - sum(
                    lower_factor[row][k] * lower_factor[column][k]
                    for k in range(column)
                )
                if row == column:
                    if residual <= 0:
                        raise ArithmeticError(
                            f"nonpositive Cholesky pivot at row {row}: {residual}"
                        )
                    lower_factor[row][column] = residual.sqrt()
                else:
                    lower_factor[row][column] = (
                        residual / lower_factor[column][column]
                    )
        return [
            [
                round_to_dyadic(lower_factor[column][row], FACTOR_BITS)
                if row <= column
                else Fraction(0)
                for column in range(size)
            ]
            for row in range(size)
        ]


def gram_entry(factor: list[list[Fraction]], row: int, column: int) -> Fraction:
    return sum(
        factor[index][row] * factor[index][column]
        for index in range(len(factor))
    )


def certificate_margin(
    intervals: list[list[tuple[Fraction, Fraction]]],
    factor: list[list[Fraction]],
) -> tuple[Fraction, list[Fraction]]:
    margins = []
    for row in range(len(intervals)):
        diagonal_lower = intervals[row][row][0] - gram_entry(factor, row, row)
        off_diagonal_sum = Fraction(0)
        for column in range(len(intervals)):
            if row == column:
                continue
            entry_gram = gram_entry(factor, row, column)
            lower, upper = intervals[row][column]
            off_diagonal_sum += max(
                abs(lower - entry_gram),
                abs(upper - entry_gram),
            )
        margins.append(diagonal_lower - off_diagonal_sum)
    return min(margins), margins


def fraction_lean(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"({value.numerator} / {value.denominator} : Rat)"


def wrapped_array(entries: Iterable[str], *, indent: str = "  ") -> str:
    values = list(entries)
    lines = []
    for start in range(0, len(values), 4):
        lines.append(indent + ", ".join(values[start : start + 4]))
    return "#[\n" + ",\n".join(lines) + "\n]"


def interval_array_lean(
    intervals: list[list[tuple[Fraction, Fraction]]],
) -> str:
    return wrapped_array(
        "{ lower := " + fraction_lean(lower) + ", upper := "
        + fraction_lean(upper) + " }"
        for row in intervals
        for lower, upper in row
    )


def factor_array_lean(factor: list[list[Fraction]]) -> str:
    return wrapped_array(
        fraction_lean(value)
        for row in factor
        for value in row
    )


def emit_certificate(
    name: str,
    intervals: list[list[tuple[Fraction, Fraction]]],
    factor: list[list[Fraction]],
) -> str:
    size = len(intervals)
    entry_name = f"{name}EntryData"
    factor_name = f"{name}FactorData"
    certificate_name = f"{name}Certificate"
    return f"""
/-- Outward-rounded exact rational intervals for the strict target matrix. -/
def {entry_name} : Array RationalInterval :=
{interval_array_lean(intervals)}

/-- Rational Gram factor for the exact residual checker. -/
def {factor_name} : Array Rat :=
{factor_array_lean(factor)}

theorem {entry_name}_length :
    RationalMatrixCertificate.HasExpectedLength (n := {size}) {entry_name} := by
  unfold RationalMatrixCertificate.HasExpectedLength
  native_decide

theorem {factor_name}_length :
    RationalMatrixCertificate.HasExpectedLength (n := {size}) {factor_name} := by
  unfold RationalMatrixCertificate.HasExpectedLength
  native_decide

def {certificate_name} : RationalMatrixCertificate {size} where
  entry := RationalMatrixCertificate.matrixOfArray {entry_name}
  gramFactor := RationalMatrixCertificate.matrixOfArray {factor_name}

theorem {certificate_name}_valid : {certificate_name}.Valid := by
  unfold RationalMatrixCertificate.Valid
  native_decide
"""


def fraction_from_fmpq(value: object) -> Fraction:
    return Fraction(str(value))


def arb_interval(
    value: object, bridge_padding: Fraction
) -> tuple[Fraction, Fraction]:
    lower = fraction_from_fmpq(value.lower().fmpq())
    upper = fraction_from_fmpq(value.upper().fmpq())
    rounded = (
        Fraction(
            floor(lower * ARB_ENTRY_GRID_DENOMINATOR),
            ARB_ENTRY_GRID_DENOMINATOR,
        ),
        Fraction(
            ceil(upper * ARB_ENTRY_GRID_DENOMINATOR),
            ARB_ENTRY_GRID_DENOMINATOR,
        ),
    )
    return (
        rounded[0] - bridge_padding,
        rounded[1] + bridge_padding,
    )


def arb_matrix_intervals(
    matrix: object,
    bridge_padding: Fraction,
    diagonal_bridge_padding: Fraction | None = None,
):
    if diagonal_bridge_padding is None:
        diagonal_bridge_padding = bridge_padding
    return [
        [
            arb_interval(
                matrix[row, column],
                diagonal_bridge_padding if row == column else bridge_padding,
            )
            for column in range(matrix.ncols())
        ]
        for row in range(matrix.nrows())
    ]


def build_arb_target_grids(
    python_flint_path: Path | None,
) -> dict[str, list[list[tuple[Fraction, Fraction]]]]:
    if python_flint_path is not None:
        sys.path.insert(0, str(python_flint_path))
    import flint
    from flint import arb, ctx
    import fixed_endpoint_even_comparison_certificate as even
    import fixed_endpoint_odd_sharp_comparison_certificate as odd
    from form_weighted_coupling_probe import right_band_endpoint

    if flint.__version__ != "0.8.0":
        raise RuntimeError("DF6D4 freezes python-flint at version 0.8.0")
    ctx.prec = ARB_PRECISION_BITS
    boundary = 44
    galerkin_last = 300
    residual_end = 600
    oscillatory_sum_end = 20000
    log_two = arb.const_log2()
    pi = arb.pi()
    a = right_band_endpoint(log_two)

    complete_transforms = [arb(0)]
    comparison_transforms = [arb(0)]
    for mode in range(1, residual_end + 3):
        complete_transforms.append(
            even.complete_sine_transform(mode, a, log_two, pi, 128)
        )
        comparison_transforms.append(even.comparison_sine_transform(mode, pi))

    even_low_diagonal = even.complete_low_diagonal(
        boundary, a, 65536, log_two, pi
    )
    even_low = even.build_low(
        boundary, even_low_diagonal, complete_transforms, pi
    )
    even_cross = even.build_cross(
        boundary, galerkin_last, complete_transforms, pi
    )
    even_comparison = even.build_comparison_far(
        boundary, galerkin_last, comparison_transforms, a, pi
    )
    even_solution = even_comparison.solve(even_cross.transpose())
    even_schur = even_cross * even_solution
    even_sink = []
    even.residual_tail_bound(
        even_low,
        even_schur,
        even_solution,
        boundary,
        galerkin_last,
        residual_end,
        oscillatory_sum_end,
        complete_transforms,
        comparison_transforms,
        a,
        log_two,
        pi,
        strict_target_sink=even_sink,
    )

    odd_low_diagonal = odd.complete_odd_low_diagonal(
        boundary, a, 16384, log_two, pi
    )
    odd_low = odd.build_complete_low(
        boundary, odd_low_diagonal, complete_transforms, pi
    )
    odd_cross = odd.build_complete_cross(
        boundary, galerkin_last, complete_transforms, pi
    )
    odd_comparison = odd.build_comparison_far(
        boundary, galerkin_last, comparison_transforms, a, pi
    )
    odd_solution = odd_comparison.solve(odd_cross.transpose())
    odd_schur = odd_cross * odd_solution
    odd_sink = []
    odd.residual_tail_bound(
        odd_low,
        odd_schur,
        odd_solution,
        boundary,
        galerkin_last,
        residual_end,
        oscillatory_sum_end,
        complete_transforms,
        comparison_transforms,
        a,
        log_two,
        pi,
        Fraction(2, 5),
        Fraction(1, 1_000_000_000),
        strict_target_sink=odd_sink,
    )
    if len(even_sink) != 1 or len(odd_sink) != 1:
        raise ArithmeticError("strict Arb target capture failed")
    return {
        "suzukiDF6D4EvenResidualTarget": arb_matrix_intervals(
            even_sink[0],
            EVEN_ARB_LEAN_BRIDGE_PADDING,
            EVEN_ARB_LEAN_DIAGONAL_BRIDGE_PADDING,
        ),
        "suzukiDF6D4OddResidualTarget": arb_matrix_intervals(
            odd_sink[0], ODD_ARB_LEAN_BRIDGE_PADDING
        ),
    }


def parse_grid_output(
    output: str,
) -> dict[str, list[list[tuple[Fraction, Fraction]]]]:
    records: dict[str, list[list[tuple[Fraction, Fraction]]]] = {}
    current_name: str | None = None
    current_size = 0
    current_entries: list[tuple[Fraction, Fraction]] = []
    for raw_line in output.splitlines():
        line = raw_line.strip()
        if line.startswith("BEGIN "):
            _, current_name, size_text = line.split()
            current_size = int(size_text)
            current_entries = []
        elif line.startswith("END "):
            _, end_name = line.split()
            if current_name != end_name:
                raise ValueError(f"mismatched grid terminator: {line}")
            if len(current_entries) != current_size * current_size:
                raise ValueError(
                    f"{current_name} exported {len(current_entries)} entries; "
                    f"expected {current_size * current_size}"
                )
            records[current_name] = [
                current_entries[start : start + current_size]
                for start in range(0, len(current_entries), current_size)
            ]
            current_name = None
        elif current_name is not None:
            lower, upper = line.split("\t")
            current_entries.append((Fraction(lower), Fraction(upper)))
    if current_name is not None:
        raise ValueError(f"unterminated grid: {current_name}")
    return records


def export_live_grids(
    repo_root: Path, lake: Path
) -> dict[str, list[list[tuple[Fraction, Fraction]]]]:
    exporter = (
        repo_root
        / "tools"
        / "experiments"
        / "m100"
        / "df6d4_residual_target_grid_export.lean"
    )
    result = subprocess.run(
        [str(lake), "env", "lean", "--run", str(exporter)],
        cwd=repo_root,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    if result.returncode != 0:
        raise RuntimeError(
            "Lean target-grid export failed:\n"
            + result.stderr
            + "\n"
            + result.stdout[-4000:]
        )
    return parse_grid_output(result.stdout)


def lean_module(
    records: list[
        tuple[
            str,
            list[list[tuple[Fraction, Fraction]]],
            list[list[Fraction]],
        ]
    ],
) -> str:
    body = "".join(emit_certificate(*record) for record in records)
    return f"""import RiemannHypothesisProject.Experiments.M100.RationalMatrixCertificate

/-!
# Generated rational data for the final M100-DF6D4 residual targets

This file is generated by
`tools/experiments/m100/df6d4_residual_target_certificate_generator.py`.
The factors and entry intervals are untrusted generated data: Lean checks
their exact Gram/residual conditions, and a separate consumer checks that the
live analytic target entries lie in the generated intervals.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalMatrixCertificate

set_option maxRecDepth 100000
{body}
end RiemannHypothesisProject.Experiments.M100
"""


def main() -> int:
    args = parse_args()
    repo_root = Path(__file__).resolve().parents[3]
    if args.source == "lean":
        grids = export_live_grids(repo_root, args.lake)
    else:
        grids = build_arb_target_grids(args.python_flint_path)
    specs = [
        (
            "suzukiDF6D4EvenResidualTarget",
            EVEN_RESIDUAL_SLACK,
        ),
        (
            "suzukiDF6D4OddResidualTarget",
            ODD_RESIDUAL_SLACK,
        ),
    ]
    records = []
    summaries = []
    for name, slack in specs:
        intervals = grids[name]
        factor = rational_cholesky_factor(intervals, slack)
        minimum_margin, row_margins = certificate_margin(intervals, factor)
        if minimum_margin < 0:
            raise ArithmeticError(
                f"rational residual checker failed for {name}: "
                f"{minimum_margin}"
            )
        records.append((name, intervals, factor))
        summaries.append(
            {
                "name": name,
                "dimension": len(intervals),
                "slack": str(slack),
                "minimum_exact_rational_row_margin": str(minimum_margin),
                "maximum_exact_rational_row_margin": str(max(row_margins)),
            }
        )

    output = args.output
    if not output.is_absolute():
        output = repo_root / output
    output.write_text(lean_module(records), encoding="utf-8", newline="\r\n")
    print(
        json.dumps(
            {
                "experiment": "M100-DF6D4",
                "artifact": "lean-rational-residual-target-certificates",
                "input": (
                    "live Lean rational target grids"
                    if args.source == "lean"
                    else "pinned 192-bit Arb strict target matrices"
                ),
                "source": args.source,
                "output": str(output),
                "certificates": summaries,
                "rational_certificate_generation_pass": True,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
