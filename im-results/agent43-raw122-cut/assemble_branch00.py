#!/usr/bin/env python3
"""Assemble the completed targeted Raw122 0LA shards and expose their exact residual roster."""
from __future__ import annotations
from pathlib import Path
import hashlib, json, os, shutil, subprocess

ROOT = Path.cwd()
HERE = Path(__file__).resolve().parent
BRANCH = 0
SOURCE_ARTIFACT = 15043765926
CORE_ARTIFACT = 15012394320
TARGET_RUNS = [45773448173, 45785487569]
BOUND = 6766859


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def run(args, *, cwd=ROOT, env=None, capture=False):
    args = list(map(str, args))
    print("$ " + " ".join(args), flush=True)
    r = subprocess.run(args, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE if capture else None,
                       stderr=subprocess.STDOUT if capture else None, check=True)
    if capture and r.stdout:
        print(r.stdout, end="" if r.stdout.endswith("\n") else "\n", flush=True)
    return r.stdout or "" if capture else ""


def copy_oleans(root: Path, out: Path, seen: dict[str, str], prefer_existing=False):
    for src in root.rglob("*.olean"):
        name = src.name
        h = sha(src)
        if name in seen:
            if prefer_existing:
                continue
            if seen[name] != h:
                raise RuntimeError(f"conflicting Lean object {name}: {seen[name]} != {h}")
        else:
            shutil.copy2(src, out / name)
            seen[name] = h


def main():
    source = Path("/tmp/a43-source")
    core = Path("/tmp/a43-core")
    targets = Path("/tmp/a43-targets")
    work = Path("/tmp/a43-work")
    factored = Path("/tmp/a43-factored-source")
    generated = Path("/tmp/a43-generated")
    final = Path("/tmp/a43-final")
    output = Path("/tmp/a43-output")
    for p in (source, core, targets):
        if not p.is_dir():
            raise FileNotFoundError(p)
    for p in (work, factored, generated, final, output):
        if p.exists():
            shutil.rmtree(p)
        p.mkdir(parents=True)

    tracked = {Path(x).name for x in subprocess.check_output(
        ["git", "ls-files", "*.lean"], cwd=ROOT, text=True).splitlines()}
    records, coverage, seen_olean = [], {}, {}
    metadata_paths = sorted(targets.rglob("metadata.json"))
    if len(metadata_paths) != 24:
        raise RuntimeError(f"expected 24 branch-00 shard artifacts, found {len(metadata_paths)}")
    run_counts = {rid: 0 for rid in TARGET_RUNS}
    for mp in metadata_paths:
        d = mp.parent
        matched_run = next((rid for rid in TARGET_RUNS if f"run{rid}" in str(mp)), None)
        if matched_run is None:
            raise RuntimeError(f"target artifact came from an unpinned run: {mp}")
        run_counts[matched_run] += 1
        m = json.loads(mp.read_text(encoding="utf-8"))
        if m.get("source_artifact") != SOURCE_ARTIFACT or m.get("core_artifact") != CORE_ARTIFACT:
            raise RuntimeError(f"source/core artifact mismatch in {mp}")
        if m.get("branch") != BRANCH:
            raise RuntimeError(f"wrong branch in {mp}: {m.get('branch')}")
        first, end = int(m["first"]), int(m["end"])
        if not 0 <= first < end <= 24:
            raise RuntimeError(f"unexpected branch-00 interval [{first},{end})")
        for kid_index in range(first, end):
            if kid_index in coverage:
                raise RuntimeError(f"overlapping branch-00 kid {kid_index}: {coverage[kid_index]} and {d}")
            coverage[kid_index] = str(d)
        for filename, expected in m["files"].items():
            rel = Path(filename)
            if rel.is_absolute() or ".." in rel.parts or len(rel.parts) != 1:
                raise RuntimeError(f"unsafe artifact path {filename!r}")
            f = d / rel
            if not f.is_file() or sha(f) != expected:
                raise RuntimeError(f"artifact SHA-256 mismatch: {f}")
        records.append({"name": d.name, "run_id": matched_run, "first": first, "end": end,
                        "modules": m.get("modules", []), "metadata_sha256": sha(mp)})
        for f in d.rglob("*.lean"):
            if f.name in tracked:
                continue
            dst = factored / f.name
            if dst.exists() and sha(dst) != sha(f):
                raise RuntimeError(f"conflicting target source {f.name}")
            if not dst.exists():
                shutil.copy2(f, dst)
        copy_oleans(d, work, seen_olean)
    if set(coverage) != set(range(24)):
        raise RuntimeError(f"branch-00 shard complement is {sorted(set(range(24))-set(coverage))}")
    if run_counts != {45773448173: 8, 45785487569: 16}:
        raise RuntimeError(f"unexpected target-run artifact distribution: {run_counts}")

    copy_oleans(core, work, seen_olean, prefer_existing=True)
    branch_srcs = list(source.rglob("Raw122Branch00.lean"))
    if len(branch_srcs) != 1:
        raise RuntimeError(f"expected one original Raw122Branch00.lean, got {len(branch_srcs)}")
    shutil.copy2(branch_srcs[0], factored / "Raw122Branch00.lean")
    for j in range(24):
        kid = f"Raw122Kid00_{j:02}.lean"
        if not (factored / kid).exists():
            original = list(source.rglob(kid))
            if len(original) != 1:
                raise RuntimeError(f"target artifacts and pinned source both omit {kid}")
            shutil.copy2(original[0], factored / kid)
        if not (work / f"Raw122Kid00_{j:02}.olean").is_file():
            raise RuntimeError(f"missing compiled object Raw122Kid00_{j:02}.olean")

    # Expand aliases introduced by checked prefix factoring or grouped shard
    # compilation; the roster is computed from the exact kid definitions that
    # the source-checked target artifacts compile.
    roster_log = run([os.sys.executable, HERE / "residual_roster.py", factored, generated, "0"], capture=True)
    tsv = generated / "Raw122Roster00.tsv"
    residual_rows = [x for x in tsv.read_text(encoding="utf-8").splitlines() if x]
    if f"Raw122Roster00 {len(residual_rows)}" not in roster_log:
        raise RuntimeError("residual roster generator count disagrees with its TSV")

    env = os.environ.copy()
    env["LEAN_PATH"] = str(work.resolve())
    branch_log = run(["lean", "-o", work / "Raw122Branch00.olean", "Raw122Branch00.lean"],
                     cwd=factored, env=env, capture=True)
    manifest = Path("/tmp/a43-branch00-manifest.json")
    Path("/tmp/a43-manifest-work").mkdir(parents=True, exist_ok=True)
    closure = ROOT / "tools/lean_compile_closure.py"
    run([os.sys.executable, closure, "--workdir", "/tmp/a43-manifest-work",
         "--source-root", ROOT, "--source-root", factored, "--manifest", manifest, "--manifest-only",
         "--artifact-dir", work, factored / "Raw122Branch00.lean"])

    wrapper = generated / "Raw122Recovered00.lean"
    body = f'''import Raw122Roster00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered00
open BB6Coverage
theorem residual_count : BB6.Agent43Raw122Roster.tables00.length = {len(residual_rows)} := by decide
'''
    if not residual_rows:
        body += '''theorem cover00 (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨false,false,0⟩) m) :
    WeightedBound 6766859 m := by
  exact BB6.Agent43Raw122Roster.cover00 6766859 (by decide)
    (by intro p hp; simp [BB6.Agent43Raw122Roster.tables00] at hp) m hm
#print axioms cover00
'''
    body += '''#print axioms residual_count
end BB6.Agent43Raw122Recovered00
'''
    wrapper.write_text(body, encoding="utf-8")

    theorem = ("BB6.Agent43Raw122Recovered00.cover00" if not residual_rows
               else "BB6.Agent43Raw122Recovered00.residual_count")
    args = [os.sys.executable, closure, "--workdir", final,
            "--source-root", ROOT, "--source-root", factored, "--source-root", generated, "--jobs", "3",
            "--precompiled-manifest", manifest, "--precompiled-dir", work,
            "--manifest", final / "manifest.json",
            "--label", "Raw122 F1=0LA exact residual roster",
            "--theorem", theorem,
            "--parent-table", "Canonical124 raw122 parent with F1=0LA",
            "--artifact-name", "raw122-branch00-cover" if not residual_rows else "raw122-branch00-roster",
            wrapper]
    if not residual_rows:
        args += ["--weighted-bound", str(BOUND)]
    log = run(args, capture=True)
    names = (["BB6.Agent43Raw122Recovered00.cover00", "BB6.Agent43Raw122Recovered00.residual_count"]
             if not residual_rows else ["BB6.Agent43Raw122Recovered00.residual_count"])
    for name in names:
        lines = [x for x in log.splitlines() if name in x and "depends on axioms:" in x]
        if len(lines) != 1 or any(t in lines[0] for t in ("sorryAx", "native_decide", "Lean.ofReduceBool")):
            raise RuntimeError(f"missing or untrusted axiom report for {name}: {lines}")

    for f in generated.iterdir():
        if f.is_file() and f.suffix in {".lean", ".tsv"} and f.name.startswith("Raw122Roster00"):
            shutil.copy2(f, output / f.name)
    shutil.copy2(wrapper, output / wrapper.name)
    shutil.copy2(factored / "Raw122Branch00.lean", output / "Raw122Branch00.lean")
    shutil.copy2(final / "manifest.json", output / "manifest.json")
    (output / "Lean-axioms.txt").write_text(log, encoding="utf-8")
    shutil.copy2(final / "Raw122Recovered00.olean", output / "Raw122Recovered00.olean")
    shutil.copy2(work / "Raw122Branch00.olean", output / "Raw122Branch00.olean")
    meta = {"branch": "0LA", "branch_index": 0, "residual_count": len(residual_rows),
            "weighted_bound": BOUND if not residual_rows else None,
            "source_artifact": SOURCE_ARTIFACT, "core_artifact": CORE_ARTIFACT,
            "target_runs": TARGET_RUNS, "target_artifacts": records,
            "target_coverage": sorted(coverage), "merged_olean_count": len(seen_olean),
            "theorem": theorem, "branch_compile_output": branch_log,
            "workflow_run_id": os.environ.get("GITHUB_RUN_ID")}
    (output / "proof-metadata.json").write_text(json.dumps(meta, indent=2, sort_keys=True)+"\n")
    print(json.dumps(meta, indent=2, sort_keys=True), flush=True)
    print(f"SUCCESS: branch 0LA source audit compiled; residual tables={len(residual_rows)}", flush=True)


if __name__ == "__main__":
    main()
