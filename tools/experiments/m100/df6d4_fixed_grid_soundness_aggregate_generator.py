#!/usr/bin/env python3
"""Generate the DF6D4 whole-grid literal-cache soundness aggregate."""

from __future__ import annotations

from pathlib import Path


MODULE = "SuzukiEndpointGalerkinResidualFixedGridSoundnessAggregate"


def solve_data(index: int, parity: str) -> str:
    parity_prefix = "Odd" if parity == "Odd" else ""
    if index < 2:
        return (
            f"suzukiDF6D4FixedGrid{parity_prefix}Stage1SolveRow{index:02d}Data"
        )
    return f"suzukiDF6D4FixedGridShard{index:03d}{parity}SolveData"


def solve_theorem(index: int, parity: str) -> str:
    parity_prefix = "Odd" if parity == "Odd" else ""
    if index < 2:
        return (
            f"suzukiDF6D4FixedGrid{parity_prefix}Stage1SolveRow"
            f"{index:02d}Data_contains"
        )
    return f"suzukiDF6D4FixedGridShard{index:03d}{parity}SolveData_contains"


def residual_data(index: int, parity: str) -> str:
    parity_prefix = "Odd" if parity == "Odd" else ""
    mode = 301 + index
    if index < 2:
        return (
            f"suzukiDF6D4FixedGrid{parity_prefix}Stage1ResidualRow{mode}Data"
        )
    return f"suzukiDF6D4FixedGridShard{index:03d}{parity}ResidualData"


def residual_theorem(index: int, parity: str) -> str:
    parity_prefix = "Odd" if parity == "Odd" else ""
    mode = 301 + index
    if index < 2:
        return (
            f"suzukiDF6D4FixedGrid{parity_prefix}Stage1ResidualRow"
            f"{mode}Data_contains"
        )
    return f"suzukiDF6D4FixedGridShard{index:03d}{parity}ResidualData_contains"


def balanced_dispatch(entries: list[str], start: int, indent: str) -> list[str]:
    if len(entries) == 1:
        return [f"{indent}{entries[0]}"]
    left_size = len(entries) // 2
    midpoint = start + left_size
    lines = [f"{indent}if k.val < {midpoint} then"]
    lines.extend(balanced_dispatch(entries[:left_size], start, indent + "  "))
    lines.append(f"{indent}else")
    lines.extend(
        balanced_dispatch(entries[left_size:], midpoint, indent + "  ")
    )
    return lines


def dispatch(name: str, size: int, entries: list[str]) -> list[str]:
    lines = [
        f"def {name}",
        f"    (k : Fin {size}) : Array FixedGridInterval :=",
    ]
    lines.extend(balanced_dispatch(entries, 0, "  "))
    return lines


def proof_cases(
    dispatcher: str, theorem_names: list[str], extra_simp: str = ""
) -> list[str]:
    lines = ["  fin_cases k"]
    for theorem_name in theorem_names:
        simp_terms = dispatcher + extra_simp
        lines.extend(
            [
                f"  · simpa [{simp_terms}] using",
                f"      {theorem_name} i",
            ]
        )
    return lines


def render() -> str:
    lines: list[str] = []
    for index in range(300):
        lines.append(
            "import RiemannHypothesisProject.Experiments.M100."
            f"SuzukiEndpointGalerkinResidualFixedGridShard{index:03d}Soundness"
        )
    lines.extend(
        [
            "",
            "/-!",
            "# Whole-grid soundness for the DF6D4 literal fixed-grid caches",
            "",
            "This generated module dispatches the 256 solve rows and 300 residual",
            "rows to their independently checked shard adapters. It performs no",
            "numerical evaluation.",
            "-/",
            "",
            "namespace RiemannHypothesisProject.Experiments.M100",
            "",
            "set_option maxRecDepth 100000",
            "",
        ]
    )

    for parity in ("Even", "Odd"):
        lines.extend(
            dispatch(
                f"suzukiDF6D4FixedGridLiteral{parity}SolveRow",
                256,
                [solve_data(index, parity) for index in range(256)],
            )
        )
        lines.append("")
    for parity in ("Even", "Odd"):
        lines.extend(
            dispatch(
                f"suzukiDF6D4FixedGridLiteral{parity}ResidualRow",
                300,
                [residual_data(index, parity) for index in range(300)],
            )
        )
        lines.append("")

    for parity, dimension in (("Even", 45), ("Odd", 44)):
        dispatcher = f"suzukiDF6D4FixedGridLiteral{parity}SolveRow"
        lines.extend(
            [
                f"theorem {dispatcher}_contains",
                f"    (k : Fin 256) (i : Fin {dimension}) :",
                "    (FixedGridInterval.toRationalInterval",
                "      suzukiDF6D4FixedGridDenominator",
                f"      (({dispatcher} k)[i.val]!)).Contains",
                f"        (suzukiDF6D4{parity}GalerkinSolveResidual k i) := by",
            ]
        )
        lines.extend(
            proof_cases(
                dispatcher,
                [solve_theorem(index, parity) for index in range(256)],
            )
        )
        lines.append("")

    for parity, dimension in (("Even", 45), ("Odd", 44)):
        dispatcher = f"suzukiDF6D4FixedGridLiteral{parity}ResidualRow"
        lines.extend(
            [
                f"theorem {dispatcher}_contains",
                f"    (r : Fin 300) (i : Fin {dimension}) :",
                "    (FixedGridInterval.toRationalInterval",
                "      suzukiDF6D4FixedGridDenominator",
                f"      (({dispatcher} r)[i.val]!)).Contains",
                f"        (suzukiDF6D4{parity}ResidualColumn (301 + r.val) i) := by",
                "  fin_cases r",
            ]
        )
        for index in range(300):
            lines.extend(
                [
                    f"  · simpa [{dispatcher}] using",
                    f"      {residual_theorem(index, parity)} i",
                ]
            )
        lines.append("")

    lines.extend(
        [
            "end RiemannHypothesisProject.Experiments.M100",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    target = (
        root
        / "RiemannHypothesisProject/Experiments/M100"
        / f"{MODULE}.lean"
    )
    target.write_text(render(), encoding="utf-8")
    print(target.relative_to(root))


if __name__ == "__main__":
    main()
