#!/usr/bin/env python3
"""Generate and verify bounded DF6D4 fixed-grid Stage-2 target-row batches."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path


MODULE_PREFIX = "SuzukiEndpointGalerkinResidualFixedGridStage2"
COMMON_PREFIX = f"{MODULE_PREFIX}Common"
MANIFEST = "EXPERIMENTS/M100_DF6D4_STAGE2_ROW_MANIFEST.json"
FINGERPRINT_SCHEMA = 3


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", required=True, type=Path)
    parser.add_argument("--parity", required=True, choices=("even", "odd"))
    parser.add_argument("--start", required=True, type=int)
    parser.add_argument("--stop", required=True, type=int)
    parser.add_argument("--max-seconds", type=float, default=3600.0)
    parser.add_argument(
        "--migrate-from-fingerprint",
        help="migrate a complete verified parity from an older fingerprint",
    )
    parser.add_argument(
        "--expected-certificate-section-sha256",
        help="required parity-certificate hash guarding a fingerprint migration",
    )
    return parser.parse_args()


def timestamp() -> str:
    return datetime.now(timezone.utc).isoformat()


def load_manifest(path: Path) -> dict:
    if path.exists():
        return json.loads(path.read_text(encoding="utf-8"))
    return {
        "schema": 1,
        "track": "M100-DF6D4-fixed-grid-stage2-rows",
        "entries": {},
        "last_stop": None,
    }


def save_manifest(path: Path, manifest: dict) -> None:
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    os.replace(temporary, path)


def write_if_changed(path: Path, content: str) -> bool:
    if path.exists() and path.read_text(encoding="utf-8") == content:
        return False
    path.write_text(content, encoding="utf-8")
    return True


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def certificate_parity_content(path: Path, parity: str) -> str:
    text = path.read_text(encoding="utf-8")
    even_marker = "def suzukiDF6D4EvenResidualTargetEntryData"
    odd_marker = "def suzukiDF6D4OddResidualTargetEntryData"
    if parity == "even":
        start = text.index(even_marker)
        stop = text.index(odd_marker)
        return text[start:stop]
    start = text.index(odd_marker)
    return text[start:]


def shared_evaluator_content(path: Path, parity: str) -> str:
    family = parity.capitalize()
    text = path.read_text(encoding="utf-8")
    start = text.index(
        f"def suzukiDF6D4FixedGrid{family}Stage2Denominator"
    )
    marker = "/-! ## Live fixed-grid target soundness -/"
    stop = (
        text.index(marker)
        if marker in text
        else text.rindex(
            "end RiemannHypothesisProject.Experiments.M100"
        )
    )
    return text[start:stop]


def verification_fingerprint(
    root: Path, shared_source: Path, parity: str
) -> str:
    module_dir = root / "RiemannHypothesisProject/Experiments/M100"
    paths = [
        module_dir / "SuzukiEndpointGalerkinResidualFixedGridStageData.lean",
    ]
    paths.extend(
        module_dir
        / f"SuzukiEndpointGalerkinResidualFixedGridShard{index:03d}Data.lean"
        for index in range(2, 300)
    )
    digest = hashlib.sha256()
    digest.update(
        f"stage2-row-schema={FINGERPRINT_SCHEMA};parity={parity}\n".encode()
    )
    digest.update(render_thin_module(parity, 0).encode())
    digest.update(b"\nshared-evaluator-content\0")
    digest.update(shared_evaluator_content(shared_source, parity).encode())
    digest.update(b"\ncertificate-parity-content\0")
    digest.update(
        certificate_parity_content(
            module_dir
            / "SuzukiEndpointGalerkinResidualCertificateData.lean",
            parity,
        ).encode()
    )
    digest.update(b"\n")
    for path in paths:
        digest.update(str(path.relative_to(root)).encode())
        digest.update(b"\0")
        digest.update(sha256(path).encode())
        digest.update(b"\n")
    return digest.hexdigest()


def shard_import(index: int) -> str:
    return (
        "import RiemannHypothesisProject.Experiments.M100."
        "SuzukiEndpointGalerkinResidualFixedGridShard"
        f"{index:03d}Data"
    )


def data_name(parity: str, kind: str, index: int) -> str:
    marker = "Odd" if parity == "odd" else ""
    if index == 0:
        suffix = "SolveRow00" if kind == "solve" else "ResidualRow301"
        return f"suzukiDF6D4FixedGrid{marker}Stage1{suffix}Data"
    if index == 1:
        suffix = "SolveRow01" if kind == "solve" else "ResidualRow302"
        return f"suzukiDF6D4FixedGrid{marker}Stage1{suffix}Data"
    family = "Odd" if parity == "odd" else "Even"
    suffix = "SolveData" if kind == "solve" else "ResidualData"
    return f"suzukiDF6D4FixedGridShard{index:03d}{family}{suffix}"


def match_body(parity: str, kind: str, count: int) -> str:
    cases = "\n".join(
        f"    | {index} => {data_name(parity, kind, index)}[column.val]!"
        for index in range(count)
    )
    return cases + "\n    | _ => default"


def module_stem(parity: str, row: int) -> str:
    return f"{MODULE_PREFIX}{parity.capitalize()}Row{row:02d}Check"


def common_stem(parity: str) -> str:
    return f"{COMMON_PREFIX}{parity.capitalize()}"


def render_common_module(parity: str) -> str:
    odd = parity == "odd"
    dimension = 44 if odd else 45
    family = "Odd" if odd else "Even"
    coefficient = "2 / 5" if odd else "19 / 1000"
    imports = "\n".join(shard_import(index) for index in range(2, 300))
    solve_cases = match_body(parity, "solve", 256)
    residual_cases = match_body(parity, "residual", 300)
    return f"""{imports}
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStageData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridSoundnessAggregate

/-!
# Shared materialized fixed-grid Stage-2 {parity} assembly

Generated by `df6d4_fixed_grid_stage2_row_batch.py`.  The large literal
dispatch and arithmetic definitions are compiled once here; row admission
modules are deliberately thin consumers.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def suzukiDF6D4FixedGrid{family}Stage2Denominator : Nat :=
  1000000000000000000

private def coefficientDenominator : Nat := 1000000000000000000000000

private def coefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4{family}GalerkinApproximantData[
    k * {dimension} + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def solveEntry (row : Fin 256) (column : Fin {dimension}) :
    FixedGridInterval :=
  match row.val with
{solve_cases}

private def residualEntry (row : Fin 300) (column : Fin {dimension}) :
    FixedGridInterval :=
  match row.val with
{residual_cases}

private def dotForColumn
    (i : Nat) (entries : Fin 256 -> FixedGridInterval) :
    FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => coefficientNumerator k i) entries

private def galerkinBaseEntry
    (row j : Fin {dimension}) : FixedGridInterval :=
  (dotForColumn j.val fun k : Fin 256 =>
    FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (suzukiDF6D4{family}CompleteCrossEntryInterval row k)).add
  (dotForColumn row.val fun k : Fin 256 => solveEntry k j)

private def finiteResidualGramEntry
    (row j : Fin {dimension}) : FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum
    suzukiDF6D4FixedGrid{family}Stage2Denominator
    (fun k : Fin 256 => solveEntry k row)
    (fun k : Fin 256 => solveEntry k j)).add
  (FixedGridInterval.mulCenteredFinSum
    suzukiDF6D4FixedGrid{family}Stage2Denominator
    (fun r : Fin 300 => residualEntry r row)
    (fun r : Fin 300 => residualEntry r j))

def suzukiDF6D4FixedGrid{family}Stage2TargetEntry
    (row j : Fin {dimension}) : FixedGridInterval :=
  (FixedGridInterval.scale
    ({coefficient} * (1 - 1 / 1000000000) : Rat)
    (FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (suzukiDF6D4{family}EndpointEntryInterval row j))).sub
  (((galerkinBaseEntry row j).add
    (FixedGridInterval.scale (1 / 5 : Rat)
      (finiteResidualGramEntry row j))).add
    (FixedGridInterval.scale (1 / 5 : Rat)
      (FixedGridInterval.ofRationalInterval
        suzukiDF6D4FixedGrid{family}Stage2Denominator
        (suzukiDF6D4{family}AnalyticTailEntryInterval row j))))

/-! ## Live fixed-grid target soundness -/

private theorem solveEntry_eq_literal
    (k : Fin 256) (i : Fin {dimension}) :
    solveEntry k i =
      ((suzukiDF6D4FixedGridLiteral{family}SolveRow k)[i.val]!) := by
  native_decide +revert

private theorem residualEntry_eq_literal
    (r : Fin 300) (i : Fin {dimension}) :
    residualEntry r i =
      ((suzukiDF6D4FixedGridLiteral{family}ResidualRow r)[i.val]!) := by
  native_decide +revert

private theorem solveEntry_contains
    (k : Fin 256) (i : Fin {dimension}) :
    (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (solveEntry k i)).Contains
        (suzukiDF6D4{family}GalerkinSolveResidual k i) := by
  rw [solveEntry_eq_literal]
  exact suzukiDF6D4FixedGridLiteral{family}SolveRow_contains k i

private theorem residualEntry_contains
    (r : Fin 300) (i : Fin {dimension}) :
    (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (residualEntry r i)).Contains
        (suzukiDF6D4{family}ResidualColumn (301 + r.val) i) := by
  rw [residualEntry_eq_literal]
  exact suzukiDF6D4FixedGridLiteral{family}ResidualRow_contains r i

private theorem dotForColumn_contains
    (i : Fin {dimension}) (entries : Fin 256 -> FixedGridInterval)
    (x : Fin 256 -> Real)
    (hx : forall k, (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (entries k)).Contains (x k)) :
    (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (dotForColumn i.val entries)).Contains
        (Finset.univ.sum fun k : Fin 256 =>
          ((suzukiDF6D4{family}GalerkinApproximant k i : Rat) : Real) *
            x k) := by
  have hdot := FixedGridInterval.contains_dotCommonDenominator
    (n := 256)
    (D := suzukiDF6D4FixedGrid{family}Stage2Denominator)
    (Q := coefficientDenominator)
    (q := fun k => coefficientNumerator k i.val)
    (I := entries) (x := x)
    (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator]) hx
  unfold dotForColumn
  convert hdot using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← suzukiDF6D4FixedGrid{family}Coefficient_real k i]
  simp only [coefficientDenominator, coefficientNumerator,
    suzukiDF6D4FixedGridSoundnessCoefficientDenominator,
    suzukiDF6D4FixedGridSoundness{family}Numerator]
  ring

private theorem galerkinBaseEntry_contains
    (row j : Fin {dimension}) :
    (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (galerkinBaseEntry row j)).Contains
        (suzukiDF6D4{family}GalerkinBaseEntry row j) := by
  have hcross := dotForColumn_contains j
    (fun k : Fin 256 => FixedGridInterval.ofRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (suzukiDF6D4{family}CompleteCrossEntryInterval row k))
    (fun k : Fin 256 => suzukiDF6D4{family}CompleteCrossEntry row k)
    (fun k => FixedGridInterval.contains_ofRationalInterval
      (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
      (suzukiDF6D4{family}CompleteCrossEntryInterval_contains row k))
  have hsolve := dotForColumn_contains row
    (fun k : Fin 256 => solveEntry k j)
    (fun k : Fin 256 => suzukiDF6D4{family}GalerkinSolveResidual k j)
    (fun k => solveEntry_contains k j)
  unfold galerkinBaseEntry suzukiDF6D4{family}GalerkinBaseEntry
  simpa only [Finset.sum_add_distrib, mul_comm] using
    FixedGridInterval.contains_add hcross hsolve

private theorem finiteResidualGramEntry_contains
    (row j : Fin {dimension}) :
    (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (finiteResidualGramEntry row j)).Contains
        (suzukiDF6D4{family}FiniteResidualGramEntry row j) := by
  have hsolve := FixedGridInterval.contains_mulCenteredFinSum
    (D := suzukiDF6D4FixedGrid{family}Stage2Denominator)
    (I := fun k : Fin 256 => solveEntry k row)
    (J := fun k : Fin 256 => solveEntry k j)
    (x := fun k : Fin 256 =>
      suzukiDF6D4{family}GalerkinSolveResidual k row)
    (y := fun k : Fin 256 =>
      suzukiDF6D4{family}GalerkinSolveResidual k j)
    (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
    (fun k => solveEntry_contains k row)
    (fun k => solveEntry_contains k j)
  have hresidual := FixedGridInterval.contains_mulCenteredFinSum
    (D := suzukiDF6D4FixedGrid{family}Stage2Denominator)
    (I := fun r : Fin 300 => residualEntry r row)
    (J := fun r : Fin 300 => residualEntry r j)
    (x := fun r : Fin 300 =>
      suzukiDF6D4{family}ResidualColumn (301 + r.val) row)
    (y := fun r : Fin 300 =>
      suzukiDF6D4{family}ResidualColumn (301 + r.val) j)
    (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
    (fun r => residualEntry_contains r row)
    (fun r => residualEntry_contains r j)
  unfold finiteResidualGramEntry
    suzukiDF6D4{family}FiniteResidualGramEntry
  exact FixedGridInterval.contains_add hsolve hresidual

theorem suzukiDF6D4FixedGrid{family}Stage2TargetEntry_contains
    (row j : Fin {dimension}) :
    (FixedGridInterval.toRationalInterval
      suzukiDF6D4FixedGrid{family}Stage2Denominator
      (suzukiDF6D4FixedGrid{family}Stage2TargetEntry row j)).Contains
        (suzukiDF6D4{family}ResidualCertificateTargetMatrix row j) := by
  have hcoupling := FixedGridInterval.contains_add
    (FixedGridInterval.contains_add
      (galerkinBaseEntry_contains row j)
      (FixedGridInterval.contains_scale (q := (1 / 5 : Rat))
        (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
        (finiteResidualGramEntry_contains row j)))
    (FixedGridInterval.contains_scale (q := (1 / 5 : Rat))
      (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
      (FixedGridInterval.contains_ofRationalInterval
        (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
        (suzukiDF6D4{family}AnalyticTailEntryInterval_contains row j)))
  have h := FixedGridInterval.contains_sub
    (FixedGridInterval.contains_scale
      (q := suzukiDF6D4{family}StrictComparisonCoefficient)
      (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
      (FixedGridInterval.contains_ofRationalInterval
        (by norm_num [suzukiDF6D4FixedGrid{family}Stage2Denominator])
        (suzukiDF6D4{family}EndpointEntryInterval_contains row j)))
    hcoupling
  unfold suzukiDF6D4FixedGrid{family}Stage2TargetEntry
  unfold suzukiDF6D4{family}ResidualCertificateTargetMatrix
    suzukiDF6D4{family}CouplingUpperMatrix
    suzukiDF6D4{family}GalerkinBaseMatrix
    suzukiDF6D4{family}FiniteResidualGramMatrix
  simpa only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, suzukiDF6D4{family}StrictComparisonCoefficient,
    suzukiDF6D4{family}ComparisonCoefficient,
    suzukiDF6D4StrictReserve] using h

end RiemannHypothesisProject.Experiments.M100
"""


def render_thin_module(parity: str, row: int) -> str:
    odd = parity == "odd"
    dimension = 44 if odd else 45
    family = "Odd" if odd else "Even"
    theorem_row = f"{row:02d}"
    return f"""import RiemannHypothesisProject.Experiments.M100.{common_stem(parity)}
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Materialized fixed-grid Stage-2 {parity} row {row}

Generated by `df6d4_fixed_grid_stage2_row_batch.py`.  The shared assembly is
compiled in `{common_stem(parity)}`; this module checks only one upper-triangle
certificate-admission row.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem suzukiDF6D4FixedGrid{family}Stage2Row{theorem_row}_admitted :
    forall j : Fin {dimension},
      {row} <= j.val ->
      (suzukiDF6D4{family}ResidualTargetCertificate.entry {row} j).lower <=
          (FixedGridInterval.toRationalInterval
            suzukiDF6D4FixedGrid{family}Stage2Denominator
            (suzukiDF6D4FixedGrid{family}Stage2TargetEntry {row} j)).lower /\\
        (FixedGridInterval.toRationalInterval
          suzukiDF6D4FixedGrid{family}Stage2Denominator
          (suzukiDF6D4FixedGrid{family}Stage2TargetEntry {row} j)).upper <=
          (suzukiDF6D4{family}ResidualTargetCertificate.entry {row} j).upper := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
"""


def render_module(parity: str, row: int) -> str:
    odd = parity == "odd"
    dimension = 44 if odd else 45
    family = "Odd" if odd else "Even"
    marker = "Odd" if odd else ""
    coefficient = "2 / 5" if odd else "19 / 1000"
    low_mode = f"suzukiDF6D4{family}LowMode"
    imports = "\n".join(shard_import(index) for index in range(2, 300))
    solve_cases = match_body(parity, "solve", 256)
    residual_cases = match_body(parity, "residual", 300)
    theorem_row = f"{row:02d}"
    return f"""{imports}
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualFixedGridStageData
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Materialized fixed-grid Stage-2 {parity} row {row}

Generated by `df6d4_fixed_grid_stage2_row_batch.py`.  This module assembles
one complete target row from previously materialized Stage-1 shard literals.
-/

namespace RiemannHypothesisProject.Experiments.M100

set_option maxHeartbeats 0
set_option maxRecDepth 100000

private def fixedGridDenominator : Nat := 1000000000000000000
private def coefficientDenominator : Nat := 1000000000000000000000000

private def coefficientNumerator (k i : Nat) : Int :=
  let q := suzukiDF6D4{family}GalerkinApproximantData[
    k * {dimension} + i]!
  q.num * ((coefficientDenominator / q.den : Nat) : Int)

private def solveEntry (row : Fin 256) (column : Fin {dimension}) :
    FixedGridInterval :=
  match row.val with
{solve_cases}

private def residualEntry (row : Fin 300) (column : Fin {dimension}) :
    FixedGridInterval :=
  match row.val with
{residual_cases}

private def dotForColumn
    (i : Nat) (entries : Fin 256 -> FixedGridInterval) :
    FixedGridInterval :=
  FixedGridInterval.dotCommonDenominator coefficientDenominator
    (fun k : Fin 256 => coefficientNumerator k i) entries

private def galerkinBaseRow (j : Fin {dimension}) : FixedGridInterval :=
  (dotForColumn j.val fun k : Fin 256 =>
    FixedGridInterval.ofRationalInterval fixedGridDenominator
      (suzukiDF6D4{family}CompleteCrossEntryInterval {row} k)).add
  (dotForColumn {row} fun k : Fin 256 => solveEntry k j)

private def finiteResidualGramRow (j : Fin {dimension}) :
    FixedGridInterval :=
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun k : Fin 256 => solveEntry k {row})
    (fun k : Fin 256 => solveEntry k j)).add
  (FixedGridInterval.mulCenteredFinSum fixedGridDenominator
    (fun r : Fin 300 => residualEntry r {row})
    (fun r : Fin 300 => residualEntry r j))

private def targetRow (j : Fin {dimension}) : FixedGridInterval :=
  (FixedGridInterval.scale
    ({coefficient} * (1 - 1 / 1000000000) : Rat)
    (FixedGridInterval.ofRationalInterval fixedGridDenominator
      (suzukiDF6D4{family}EndpointEntryInterval {row} j))).sub
  (((galerkinBaseRow j).add
    (FixedGridInterval.scale (1 / 5 : Rat)
      (finiteResidualGramRow j))).add
    (FixedGridInterval.scale (1 / 5 : Rat)
      (FixedGridInterval.ofRationalInterval fixedGridDenominator
        (suzukiDF6D4{family}AnalyticTailEntryInterval {row} j))))

theorem suzukiDF6D4FixedGrid{family}Stage2Row{theorem_row}_admitted :
    forall j : Fin {dimension},
      {row} <= j.val ->
      (suzukiDF6D4{family}ResidualTargetCertificate.entry {row} j).lower <=
          (FixedGridInterval.toRationalInterval fixedGridDenominator
            (targetRow j)).lower /\\
        (FixedGridInterval.toRationalInterval fixedGridDenominator
          (targetRow j)).upper <=
          (suzukiDF6D4{family}ResidualTargetCertificate.entry {row} j).upper := by
  native_decide

end RiemannHypothesisProject.Experiments.M100
"""


def compile_module(
    root: Path, lake: Path, source: Path, stem: str
) -> None:
    relative = Path("RiemannHypothesisProject/Experiments/M100") / stem
    output = root / ".lake/build/lib/lean" / relative.with_suffix(".olean")
    interface = root / ".lake/build/lib/lean" / relative.with_suffix(".ilean")
    output.parent.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    environment["GIT_CONFIG_COUNT"] = "1"
    environment["GIT_CONFIG_KEY_0"] = "safe.directory"
    environment["GIT_CONFIG_VALUE_0"] = "*"
    subprocess.run(
        [
            str(lake),
            "env",
            "lean",
            str(source.relative_to(root)),
            "-o",
            str(output.relative_to(root)),
            "-i",
            str(interface.relative_to(root)),
        ],
        cwd=root,
        env=environment,
        check=True,
    )


def main() -> int:
    args = parse_args()
    upper = 44 if args.parity == "even" else 43
    if not 0 <= args.start <= args.stop <= upper:
        raise ValueError(f"{args.parity} rows must stay within 0..{upper}")
    if args.max_seconds < 0:
        raise ValueError("max-seconds must be nonnegative")

    root = Path(__file__).resolve().parents[3]
    module_dir = root / "RiemannHypothesisProject/Experiments/M100"
    manifest_path = root / MANIFEST
    manifest = load_manifest(manifest_path)
    manifest["schema"] = FINGERPRINT_SCHEMA
    started = time.monotonic()

    shared_stem = common_stem(args.parity)
    shared_source = module_dir / f"{shared_stem}.lean"
    write_if_changed(shared_source, render_common_module(args.parity))
    fingerprint = verification_fingerprint(
        root, shared_source, args.parity
    )
    if args.migrate_from_fingerprint is not None:
        if args.expected_certificate_section_sha256 is None:
            raise ValueError(
                "fingerprint migration requires "
                "--expected-certificate-section-sha256"
            )
        certificate_path = (
            module_dir
            / "SuzukiEndpointGalerkinResidualCertificateData.lean"
        )
        certificate_hash = hashlib.sha256(
            certificate_parity_content(
                certificate_path, args.parity
            ).encode()
        ).hexdigest()
        if certificate_hash != args.expected_certificate_section_sha256:
            raise ValueError(
                "certificate section changed: "
                f"expected {args.expected_certificate_section_sha256}, "
                f"found {certificate_hash}"
            )
        expected_rows = range(upper + 1)
        for row in expected_rows:
            key = f"{args.parity}/{row:02d}"
            entry = manifest["entries"].get(key, {})
            if not (
                entry.get("status") == "verified"
                and entry.get("fingerprint")
                == args.migrate_from_fingerprint
            ):
                raise ValueError(
                    f"cannot migrate incomplete or mismatched entry {key}"
                )
        for row in expected_rows:
            key = f"{args.parity}/{row:02d}"
            manifest["entries"][key]["fingerprint"] = fingerprint
        manifest.setdefault("fingerprints", {})[
            args.parity
        ] = fingerprint
        manifest.setdefault("migrations", []).append(
            {
                "parity": args.parity,
                "from": args.migrate_from_fingerprint,
                "to": fingerprint,
                "certificate_section_sha256": certificate_hash,
                "reason": (
                    "schema-3 parity-specific fingerprint migration; "
                    "verified evaluator semantics and parity certificate "
                    "content unchanged"
                ),
                "timestamp": timestamp(),
            }
        )
        save_manifest(manifest_path, manifest)
        print(
            f"migrated={args.parity}/00-{upper:02d} "
            f"fingerprint={fingerprint}",
            flush=True,
        )
        return 0
    shared_stamp = (
        root / ".lake/build/lib/lean"
        / Path("RiemannHypothesisProject/Experiments/M100")
        / f"{shared_stem}.df6d4-fingerprint"
    )
    if (
        shared_stamp.exists()
        and shared_stamp.read_text(encoding="utf-8").strip() == fingerprint
    ):
        print(f"reuse=common/{args.parity}", flush=True)
    else:
        print(f"start=common/{args.parity}", flush=True)
        shared_started = time.monotonic()
        compile_module(root, args.lake, shared_source, shared_stem)
        shared_stamp.write_text(fingerprint + "\n", encoding="utf-8")
        print(
            f"verified=common/{args.parity} "
            f"seconds={time.monotonic() - shared_started:.3f}",
            flush=True,
        )
    manifest.setdefault("fingerprints", {})[args.parity] = fingerprint
    save_manifest(manifest_path, manifest)

    for row in range(args.start, args.stop + 1):
        key = f"{args.parity}/{row:02d}"
        entry = manifest["entries"].get(key, {})
        if (
            entry.get("status") == "verified"
            and entry.get("fingerprint") == fingerprint
        ):
            print(f"skip={key}", flush=True)
            continue
        if time.monotonic() - started >= args.max_seconds:
            manifest["last_stop"] = {
                "reason": "time-budget",
                "next": key,
                "timestamp": timestamp(),
            }
            save_manifest(manifest_path, manifest)
            print(f"stop=time-budget next={key}", flush=True)
            return 0

        stem = module_stem(args.parity, row)
        source = module_dir / f"{stem}.lean"
        write_if_changed(source, render_thin_module(args.parity, row))
        print(f"start={key}", flush=True)
        row_started = time.monotonic()
        try:
            compile_module(root, args.lake, source, stem)
        except subprocess.CalledProcessError as error:
            manifest["entries"][key] = {
                "status": "failed",
                "returncode": error.returncode,
                "fingerprint": fingerprint,
                "timestamp": timestamp(),
            }
            manifest["last_stop"] = {
                "reason": "failure",
                "next": key,
                "timestamp": timestamp(),
            }
            save_manifest(manifest_path, manifest)
            raise
        elapsed = time.monotonic() - row_started
        manifest["entries"][key] = {
            "status": "verified",
            "elapsed_seconds": round(elapsed, 3),
            "fingerprint": fingerprint,
            "timestamp": timestamp(),
        }
        manifest["last_stop"] = {
            "reason": "checkpoint",
            "next": f"{args.parity}/{row + 1:02d}",
            "timestamp": timestamp(),
        }
        save_manifest(manifest_path, manifest)
        print(f"verified={key} seconds={elapsed:.3f}", flush=True)

    manifest["last_stop"] = {
        "reason": "complete-range",
        "next": None,
        "timestamp": timestamp(),
    }
    save_manifest(manifest_path, manifest)
    print(f"complete={args.parity}/{args.start:02d}-{args.stop:02d}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
