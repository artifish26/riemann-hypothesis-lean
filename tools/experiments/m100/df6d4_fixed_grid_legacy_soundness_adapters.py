#!/usr/bin/env python3
"""Render the legacy DF6D4 fixed-grid soundness adapters for shards 000/001."""

from __future__ import annotations

import re
from pathlib import Path


def render(template: str, index: int) -> str:
    if index not in (0, 1):
        raise ValueError("legacy adapter index must be 0 or 1")

    row = f"{index:02d}"
    residual_mode = 301 + index
    text = template.replace(
        "SuzukiEndpointGalerkinResidualFixedGridShard002Stage0Check",
        "SuzukiEndpointGalerkinResidualFixedGridStage0Check",
    ).replace(
        "SuzukiEndpointGalerkinResidualFixedGridShard002Stage1Check",
        "SuzukiEndpointGalerkinResidualFixedGridStage1Check",
    )
    text = text.replace("Shard002", f"Shard{index:03d}")

    replacements = {
        f"suzukiDF6D4FixedGridShard{index:03d}EvenComparisonData":
            f"suzukiDF6D4FixedGridStage0ComparisonRow{row}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}EvenCrossData":
            f"suzukiDF6D4FixedGridStage0SolveCrossRow{row}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}EvenSolveData":
            f"suzukiDF6D4FixedGridStage1SolveRow{row}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}OddComparisonData":
            f"suzukiDF6D4FixedGridOddStage0ComparisonRow{row}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}OddCrossData":
            f"suzukiDF6D4FixedGridOddStage0SolveCrossRow{row}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}OddSolveData":
            f"suzukiDF6D4FixedGridOddStage1SolveRow{row}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}EvenResidualComparisonData":
            f"suzukiDF6D4FixedGridStage0ComparisonPrefixRow{residual_mode}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}EvenFullData":
            f"suzukiDF6D4FixedGridStage0FullPrefixRow{residual_mode}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}EvenResidualData":
            f"suzukiDF6D4FixedGridStage1ResidualRow{residual_mode}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}OddResidualComparisonData":
            f"suzukiDF6D4FixedGridOddStage0ComparisonPrefixRow{residual_mode}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}OddFullData":
            f"suzukiDF6D4FixedGridOddStage0FullPrefixRow{residual_mode}Data",
        f"suzukiDF6D4FixedGridShard{index:03d}OddResidualData":
            f"suzukiDF6D4FixedGridOddStage1ResidualRow{residual_mode}Data",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)

    stage0 = f"suzukiDF6D4FixedGridShard{index:03d}Stage0_valid"
    stage1 = f"suzukiDF6D4FixedGridShard{index:03d}Stage1_valid"
    if index == 0:
        accessors = {
            f"{stage0}.1.1": "suzukiDF6D4FixedGridStage0BoundedBlock_valid.1",
            f"{stage0}.1.2.1": "suzukiDF6D4FixedGridStage0BoundedBlock_valid.2.1",
            f"{stage0}.1.2.2.1": "suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.1",
            f"{stage0}.1.2.2.2": "suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.2.1",
            f"{stage0}.2.1": "suzukiDF6D4FixedGridStage0BoundedBlock_valid.2.2.1",
            f"{stage0}.2.2.1": "suzukiDF6D4FixedGridStage0BoundedBlock_valid.2.2.2.1",
            f"{stage0}.2.2.2.1": "suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.2.2.1",
            f"{stage0}.2.2.2.2": "suzukiDF6D4FixedGridOddStage0BoundedBlock_valid.2.2.2.1",
            f"{stage1}.1.1": "suzukiDF6D4FixedGridStage1BoundedBlock_valid.1",
            f"{stage1}.1.2": "suzukiDF6D4FixedGridOddStage1BoundedBlock_valid.1",
            f"{stage1}.2.1": "suzukiDF6D4FixedGridStage1BoundedBlock_valid.2",
            f"{stage1}.2.2": "suzukiDF6D4FixedGridOddStage1BoundedBlock_valid.2",
        }
    else:
        accessors = {
            f"{stage0}.1.1": "suzukiDF6D4FixedGridStage0Shard01_valid.1",
            f"{stage0}.1.2.1": "suzukiDF6D4FixedGridStage0Shard01_valid.2.1",
            f"{stage0}.1.2.2.1": "suzukiDF6D4FixedGridOddStage0Shard01_valid.1",
            f"{stage0}.1.2.2.2": "suzukiDF6D4FixedGridOddStage0Shard01_valid.2.1",
            f"{stage0}.2.1": "suzukiDF6D4FixedGridStage0Shard01_valid.2.2.1",
            f"{stage0}.2.2.1": "suzukiDF6D4FixedGridStage0Shard01_valid.2.2.2",
            f"{stage0}.2.2.2.1": "suzukiDF6D4FixedGridOddStage0Shard01_valid.2.2.1",
            f"{stage0}.2.2.2.2": "suzukiDF6D4FixedGridOddStage0Shard01_valid.2.2.2",
            f"{stage1}.1.1": "suzukiDF6D4FixedGridStage1Shard01_valid.1",
            f"{stage1}.1.2": "suzukiDF6D4FixedGridOddStage1Shard01_valid.1",
            f"{stage1}.2.1": "suzukiDF6D4FixedGridStage1Shard01_valid.2",
            f"{stage1}.2.2": "suzukiDF6D4FixedGridOddStage1Shard01_valid.2",
        }
    placeholders: dict[str, str] = {}
    for number, (old, new) in enumerate(accessors.items()):
        marker = f"LEGACY_ACCESSOR_{number:03d}"
        text = text.replace(old, marker)
        placeholders[marker] = new
    text = re.sub(r"\b303\b", str(residual_mode), text)
    text = re.sub(r"\b2\b", str(index), text)
    for marker, replacement in placeholders.items():
        text = text.replace(marker, replacement)
    return text


def main() -> None:
    root = Path(__file__).resolve().parents[3]
    module_dir = root / "RiemannHypothesisProject/Experiments/M100"
    template = (
        module_dir
        / "SuzukiEndpointGalerkinResidualFixedGridShard002Soundness.lean"
    ).read_text(encoding="utf-8")
    for index in (0, 1):
        target = module_dir / (
            f"SuzukiEndpointGalerkinResidualFixedGridShard{index:03d}Soundness.lean"
        )
        target.write_text(render(template, index), encoding="utf-8")
        print(target.relative_to(root))


if __name__ == "__main__":
    main()
