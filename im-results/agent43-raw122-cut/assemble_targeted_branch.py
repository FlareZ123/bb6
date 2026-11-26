#!/usr/bin/env python3
"""Assemble the source-preserving Raw122 branch-05 residual cover from CI shards."""
from __future__ import annotations

from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path.cwd()
HERE = Path(__file__).resolve().parent
BRANCH = 5
SOURCE_ARTIFACT = 15043765926
CORE_ARTIFACT = 15012394320
BOUND = 6766859


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run(args: list[str], *, cwd: Path = ROOT, env: dict[str, str] | None = None,
        capture: bool = False) -> str:
    print("$ " + " ".join(map(str, args)), flush=True)
    result = subprocess.run(
        list(map(str, args)), cwd=cwd, env=env, text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.STDOUT if capture else None,
        check=True,
    )
    if capture and result.stdout:
        print(result.stdout, end="" if result.stdout.endswith("\n") else "\n", flush=True)
    return result.stdout or "" if capture else ""


def unique_file(root: Path, name: str) -> Path:
    found = list(root.rglob(name))
    if len(found) != 1:
        raise RuntimeError(f"expected exactly one {name} below {root}, found {len(found)}")
    return found[0]


def copy_oleans(root: Path, out: Path, seen: dict[str, str], *, skip_raw122: bool = False) -> None:
    for src in root.rglob("*.olean"):
        name = src.name
        if skip_raw122 and name.startswith("Raw122") and name != "Raw122Base.olean":
            continue
        sha = digest(src)
        if name in seen and seen[name] != sha:
            raise RuntimeError(f"conflicting Lean object {name}: {seen[name]} != {sha} from {src}")
        if name not in seen:
            shutil.copy2(src, out / name)
            seen[name] = sha


def copy_sources(root: Path, out: Path, tracked_names: set[str]) -> None:
    for src in root.rglob("*.lean"):
        if src.name in tracked_names:
            continue
        dst = out / src.name
        if dst.exists() and digest(dst) != digest(src):
            raise RuntimeError(f"conflicting Lean source {src.name}: {src}")
        if not dst.exists():
            shutil.copy2(src, dst)


def main() -> None:
    branch = int(sys.argv[1])
    if branch != BRANCH:
        raise ValueError("this assembly target is specifically the 0LF (branch 05) witness roster")

    source_dir = Path("/tmp/a43-source")
    core_dir = Path("/tmp/a43-core")
    targets_dir = Path("/tmp/a43-targets")
    work = Path("/tmp/a43-work")
    factored = Path("/tmp/a43-factored-source")
    generated = Path("/tmp/a43-generated")
    final = Path("/tmp/a43-final")
    output = Path("/tmp/a43-output")
    for path in (source_dir, core_dir, targets_dir):
        if not path.is_dir():
            raise FileNotFoundError(path)
    for path in (work, factored, generated, final, output):
        if path.exists():
            shutil.rmtree(path)
        path.mkdir(parents=True)

    # Require the 24 sub-cylinder artifacts to form one exact, disjoint cover.
    coverage: dict[int, str] = {}
    target_dirs = sorted(p for p in targets_dir.iterdir() if p.is_dir())
    if not target_dirs:
        raise RuntimeError("no targeted-recovery artifacts were downloaded")
    artifact_records = []
    for directory in target_dirs:
        metadata_path = directory / "metadata.json"
        metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
        if metadata.get("source_artifact") != SOURCE_ARTIFACT:
            raise RuntimeError(f"wrong source artifact in {metadata_path}")
        if metadata.get("core_artifact") != CORE_ARTIFACT:
            raise RuntimeError(f"wrong core artifact in {metadata_path}")
        if metadata.get("branch") != branch:
            raise RuntimeError(f"wrong branch in {metadata_path}: {metadata.get('branch')}")
        first, end = int(metadata["first"]), int(metadata["end"])
        if not (0 <= first < end <= 24):
            raise RuntimeError(f"invalid sub-cylinder interval [{first},{end})")
        for j in range(first, end):
            if j in coverage:
                raise RuntimeError(f"overlapping target artifacts at kid {j}: {coverage[j]} and {directory.name}")
            coverage[j] = directory.name
        for filename, expected in metadata["files"].items():
            relative = Path(filename)
            if relative.is_absolute() or ".." in relative.parts or len(relative.parts) != 1:
                raise RuntimeError(f"unsafe artifact path {filename!r}")
            path = directory / relative
            if not path.is_file() or digest(path) != expected:
                raise RuntimeError(f"artifact SHA-256 mismatch: {path}")
        artifact_records.append({
            "name": directory.name,
            "first": first,
            "end": end,
            "modules": metadata.get("modules", []),
            "metadata_sha256": digest(metadata_path),
        })
    if set(coverage) != set(range(24)):
        missing = sorted(set(range(24)) - set(coverage))
        raise RuntimeError(f"target artifacts do not cover all 24 kid cylinders; missing {missing}")

    # Merge only byte-identical shared objects. The pinned source and core IDs
    # are the same ones used by the original Raw122 recovery workflow.
    seen_oleans: dict[str, str] = {}
    tracked_names = {Path(line).name for line in subprocess.check_output(
        ["git", "ls-files", "*.lean"], cwd=ROOT, text=True
    ).splitlines()}
    copy_oleans(core_dir, work, seen_oleans, skip_raw122=True)
    for directory in target_dirs:
        copy_oleans(directory, work, seen_oleans)
        copy_sources(directory, factored, tracked_names)

    branch_source = unique_file(source_dir, f"Raw122Branch{branch:02}.lean")
    shutil.copy2(branch_source, factored / branch_source.name)
    for j in range(24):
        name = f"Raw122Kid{branch:02}_{j:02}.lean"
        if not (factored / name).exists():
            shutil.copy2(unique_file(source_dir, name), factored / name)
        if not (work / f"Raw122Kid{branch:02}_{j:02}.olean").is_file():
            raise RuntimeError(f"missing compiled kid object Raw122Kid{branch:02}_{j:02}.olean")

    # The residual roster is extracted from the pinned, original, unpatched
    # source artifact, never from a grafted candidate tree.
    roster_output = run([
        sys.executable,
        HERE / "residual_roster.py",
        source_dir,
        generated,
        str(branch),
    ], capture=True)
    roster_tsv = generated / f"Raw122Roster{branch:02}.tsv"
    residual_rows = [line for line in roster_tsv.read_text(encoding="utf-8").splitlines() if line]
    if len(residual_rows) != 20:
        raise RuntimeError(f"expected the pinned 20-table residual roster, got {len(residual_rows)}")
    if f"Raw122Roster{branch:02} 20" not in roster_output:
        raise RuntimeError("residual_roster.py did not report the expected 20-table roster")

    # Reconstruct the 11 exact Agent29 indexed certificates and the packed
    # late-query proof used by the existing 20-table witness mapping.
    run([
        sys.executable,
        ROOT / "im-results/agent29-raw122-run/generate.py",
        generated,
        *[str(i) for i in range(50, 61)],
    ])
    run([
        sys.executable,
        ROOT / "im-results/agent29-raw122-run/late.py",
        generated,
        "0",
    ])

    # Compile the branch module against the merged original-source objects,
    # then freeze its exact import closure as a reusable precompiled manifest.
    env = os.environ.copy()
    env["LEAN_PATH"] = str(work.resolve())
    branch_log = run([
        "lean", "-o", work / f"Raw122Branch{branch:02}.olean", branch_source.name,
    ], cwd=factored, env=env, capture=True)
    manifest = Path("/tmp/a43-branch05-manifest.json")
    Path("/tmp/a43-manifest-work").mkdir(parents=True, exist_ok=True)
    closure_tool = ROOT / "tools/lean_compile_closure.py"
    run([
        sys.executable, closure_tool,
        "--workdir", "/tmp/a43-manifest-work",
        "--source-root", factored,
        "--manifest", manifest,
        "--manifest-only",
        "--artifact-dir", work,
        factored / branch_source.name,
    ])

    wrapper = generated / "Raw122Recovered05.lean"
    wrapper.write_text(
        """import Raw122Roster05Witnesses
import LateCheck0
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered05
open BB6Coverage
theorem cover05 (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨false,false,5⟩) m) :
    WeightedBound 6766859 m := by
  have hLate : BB6.Agent43Raw122ResidualCompose.Covered 6766859
      BB6.Agent43Raw122Roster.p05_007 :=
    BB6Coverage.Agent29PackedLate.M0.bound
  exact BB6.Agent43Raw122Roster.cover05 6766859 (by decide)
    (BB6.Agent43Raw122Roster.witnesses05 hLate) m hm

theorem residual_count : BB6.Agent43Raw122Roster.tables05.length = 20 := by decide
#print axioms cover05
#print axioms residual_count
end BB6.Agent43Raw122Recovered05
""",
        encoding="utf-8",
    )

    compile_log = run([
        sys.executable, closure_tool,
        "--workdir", final,
        "--source-root", factored,
        "--source-root", generated,
        "--jobs", "3",
        "--precompiled-manifest", manifest,
        "--precompiled-dir", work,
        "--manifest", final / "manifest.json",
        "--label", "Raw122 F1=0LF source-accepted child Cover",
        "--theorem", "BB6.Agent43Raw122Recovered05.cover05",
        "--parent-table", "Canonical124 raw122 parent with F1=0LF",
        "--weighted-bound", str(BOUND),
        "--artifact-name", "raw122-branch05-cover",
        wrapper,
    ], capture=True)
    for theorem in (
        "BB6.Agent43Raw122Recovered05.cover05",
        "BB6.Agent43Raw122Recovered05.residual_count",
    ):
        lines = [line for line in compile_log.splitlines()
                 if theorem in line and "depends on axioms:" in line]
        if len(lines) != 1:
            raise RuntimeError(f"missing unique axiom report for {theorem}")
        if any(token in lines[0] for token in ("sorryAx", "native_decide", "Lean.ofReduceBool")):
            raise RuntimeError(f"prohibited trust dependency in {theorem}: {lines[0]}")

    # Retain the proof source, exact roster, transitive module manifest and
    # root objects as a single reproducible CI artifact.
    for src in generated.iterdir():
        if src.is_file() and src.suffix in {".lean", ".tsv"} and (
            src.name.startswith(("Raw122Roster05", "Agent29Raw122Indexed", "PackedLate0"))
            or src.name in {"LateCheck0.lean", "Raw122Recovered05.lean"}
        ):
            shutil.copy2(src, output / src.name)
    shutil.copy2(factored / f"Raw122Branch{branch:02}.lean", output / f"Raw122Branch{branch:02}.lean")
    shutil.copy2(final / "manifest.json", output / "manifest.json")
    (output / "Lean-axioms.txt").write_text(compile_log, encoding="utf-8")
    shutil.copy2(final / "Raw122Recovered05.olean", output / "Raw122Recovered05.olean")
    shutil.copy2(work / f"Raw122Branch{branch:02}.olean", output / f"Raw122Branch{branch:02}.olean")
    proof_metadata = {
        "theorem": "BB6.Agent43Raw122Recovered05.cover05",
        "branch": "0LF",
        "branch_index": branch,
        "weighted_bound": BOUND,
        "residual_count": len(residual_rows),
        "source_artifact": SOURCE_ARTIFACT,
        "core_artifact": CORE_ARTIFACT,
        "workflow_run_id": os.environ.get("GITHUB_RUN_ID"),
        "target_artifacts": artifact_records,
        "target_coverage": sorted(coverage),
        "merged_olean_count": len(seen_oleans),
        "branch_compile_output": branch_log,
    }
    (output / "proof-metadata.json").write_text(
        json.dumps(proof_metadata, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(proof_metadata, indent=2, sort_keys=True), flush=True)
    print("SUCCESS: original Raw122 F1=0LF child Cover compiled at 6766859", flush=True)


if __name__ == "__main__":
    main()
