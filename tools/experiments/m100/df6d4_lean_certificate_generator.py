#!/usr/bin/env python3
"""Generate exact rational DF6D4 finite-matrix certificate data.

The existing DF5A artifact supplies outward-rounded Arb entry intervals.  This
generator does not turn those intervals into trusted Lean facts.  It converts
them to exact rational endpoints and constructs rational Gram factors whose
residuals pass the row-diagonal-dominance checker in
``RationalMatrixCertificate.lean``.  A separate Lean analytic-enclosure layer
must still prove that every concrete endpoint entry lies in the emitted
interval before DF6D4 can close.

Dependency: python-flint==0.8.0.
"""

from __future__ import annotations

import argparse
import json
from decimal import Decimal, localcontext
from fractions import Fraction
from math import ceil, floor
from pathlib import Path
from typing import Iterable

try:
    import flint
    from flint import arb, arb_mat, ctx
except ImportError as error:
    raise SystemExit(
        "df6d4_lean_certificate_generator.py requires python-flint==0.8.0"
    ) from error

from df5a_endpoint_coercivity_certificate import (
    EVEN_K_LOWER,
    ODD_K_LOWER,
    ODD_K_UPPER,
    build_endpoint_matrices,
    shift_from_identity,
)


PRECISION_BITS = 192
FACTOR_BITS = 180
DECIMAL_PRECISION = 150
ENTRY_GRID_DENOMINATOR = 100_000_000

EVEN_SLACK = Fraction(1, 200_000)
ODD_LOWER_SLACK = Fraction(1, 2_000)
ODD_UPPER_SLACK = Fraction(1, 2)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        help="optional generated Lean module path",
    )
    return parser.parse_args()


def fraction_from_fmpq(value: object) -> Fraction:
    return Fraction(str(value))


def arb_interval(value: arb) -> tuple[Fraction, Fraction]:
    lower = fraction_from_fmpq(value.lower().fmpq())
    upper = fraction_from_fmpq(value.upper().fmpq())
    return (
        Fraction(floor(lower * ENTRY_GRID_DENOMINATOR), ENTRY_GRID_DENOMINATOR),
        Fraction(ceil(upper * ENTRY_GRID_DENOMINATOR), ENTRY_GRID_DENOMINATOR),
    )


def matrix_intervals(matrix: arb_mat) -> list[list[tuple[Fraction, Fraction]]]:
    return [
        [arb_interval(matrix[row, column]) for column in range(matrix.ncols())]
        for row in range(matrix.nrows())
    ]


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

        # The Lean checker uses factor^T * factor.  Transpose the conventional
        # lower Cholesky factor so that this product equals L * L^T.
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
    size = len(intervals)
    margins: list[Fraction] = []
    for row in range(size):
        diagonal_gram = gram_entry(factor, row, row)
        diagonal_lower = intervals[row][row][0] - diagonal_gram
        off_diagonal_sum = Fraction(0)
        for column in range(size):
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
    lines: list[str] = []
    for start in range(0, len(values), 4):
        lines.append(indent + ", ".join(values[start : start + 4]))
    return "#[\n" + ",\n".join(lines) + "\n]"


def interval_array_lean(
    intervals: list[list[tuple[Fraction, Fraction]]],
) -> str:
    return wrapped_array(
        f"⟨{fraction_lean(lower)}, {fraction_lean(upper)}⟩"
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
/-- Outward-rounded exact rational entry intervals generated from the frozen
192-bit Arb reconstruction.  Their connection to the analytic entries is
proved separately; these data alone assert no analytic inequality. -/
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

/-- The exact checker input for this shifted endpoint matrix. -/
def {certificate_name} : RationalMatrixCertificate {size} where
  entry := RationalMatrixCertificate.matrixOfArray {entry_name}
  gramFactor := RationalMatrixCertificate.matrixOfArray {factor_name}

/-- Kernel-checked rational validity; this theorem uses no analytic or
floating-point premise. -/
theorem {certificate_name}_valid : {certificate_name}.Valid := by
  unfold RationalMatrixCertificate.Valid
  native_decide
"""


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
# Generated rational data for M100-DF6D4 endpoint certificates

This file is generated deterministically by
`tools/experiments/m100/df6d4_lean_certificate_generator.py` from the frozen
DF5A endpoint reconstruction.  Lean checks all rational Gram/residual
conditions.  The separate analytic-enclosure module must prove that the live
endpoint matrices lie in these intervals before the certificates can be
consumed.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open RationalMatrixCertificate

set_option maxRecDepth 100000
{body}
end M100
end Experiments
end RiemannHypothesisProject
"""


def main() -> int:
    args = parse_args()
    if flint.__version__ != "0.8.0":
        raise RuntimeError("DF6D4 freezes python-flint at version 0.8.0")
    ctx.prec = PRECISION_BITS

    _, even_matrix, odd_matrix = build_endpoint_matrices()
    matrix_specs = [
        (
            "suzukiDF6D4EvenLower",
            shift_from_identity(even_matrix, -EVEN_K_LOWER, 1),
            EVEN_SLACK,
        ),
        (
            "suzukiDF6D4OddLower",
            shift_from_identity(odd_matrix, -ODD_K_LOWER, 1),
            ODD_LOWER_SLACK,
        ),
        (
            "suzukiDF6D4OddUpper",
            shift_from_identity(odd_matrix, ODD_K_UPPER, -1),
            ODD_UPPER_SLACK,
        ),
    ]

    records = []
    summaries = []
    for name, matrix, slack in matrix_specs:
        intervals = matrix_intervals(matrix)
        factor = rational_cholesky_factor(intervals, slack)
        minimum_margin, row_margins = certificate_margin(intervals, factor)
        if minimum_margin < 0:
            raise ArithmeticError(
                f"rational residual checker failed for {name}: {minimum_margin}"
            )
        records.append((name, intervals, factor))
        summaries.append(
            {
                "name": name,
                "dimension": len(intervals),
                "slack": str(slack),
                "factor_bits": FACTOR_BITS,
                "entry_grid_denominator": ENTRY_GRID_DENOMINATOR,
                "minimum_exact_rational_row_margin": str(minimum_margin),
                "maximum_exact_rational_row_margin": str(max(row_margins)),
            }
        )

    if args.output is not None:
        args.output.write_text(lean_module(records), encoding="utf-8", newline="\r\n")

    print(
        json.dumps(
            {
                "experiment": "M100-DF6D4",
                "artifact": "lean-rational-finite-matrix-certificate-generator",
                "precision_bits": PRECISION_BITS,
                "entry_grid_denominator": ENTRY_GRID_DENOMINATOR,
                "python_flint_version": flint.__version__,
                "output": str(args.output) if args.output is not None else None,
                "certificates": summaries,
                "rational_certificate_generation_pass": True,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
