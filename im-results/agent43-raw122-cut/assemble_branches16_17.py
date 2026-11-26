#!/usr/bin/env python3
"""Assemble source-accepted Raw122 F1=1LE and F1=1LF child Covers."""
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
SOURCE_ARTIFACT = 15043765926
CORE_ARTIFACT = 15012394320
BRANCHES = (16, 17)
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
                       stderr=subprocess.STDOUT if capture else None, check=False)
    if capture and r.stdout:
        print(r.stdout, end="" if r.stdout.endswith("\n") else "\n", flush=True)
    if r.returncode != 0:
        raise subprocess.CalledProcessError(r.returncode, args, output=r.stdout)
    return r.stdout or "" if capture else ""

def copy_oleans(root: Path, out: Path, seen: dict[str, str], *, prefer_existing=False):
    for src in root.rglob("*.olean"):
        name = src.name
        h = sha(src)
        if name in seen:
            if prefer_existing:
                continue
            if seen[name] != h:
                raise RuntimeError(f"conflicting Lean object {name}: {seen[name]} != {h} from {src}")
            continue
        shutil.copy2(src, out / name)
        seen[name] = h

def main():
    source = Path("/tmp/a43-source")
    core = Path("/tmp/a43-core")
    targets = Path("/tmp/a43-targets")
    work = Path("/tmp/a43-work")
    factored = Path("/tmp/a43-factored-source")
    generated = Path("/tmp/a43-generated")
    manifest_work = Path("/tmp/a43-manifest-work")
    output = Path("/tmp/a43-output")
    for p in (source, core, targets):
        if not p.is_dir():
            raise FileNotFoundError(p)
    for p in (work, factored, generated, manifest_work, output):
        if p.exists():
            shutil.rmtree(p)
        p.mkdir(parents=True)

    tracked = {Path(x).name for x in subprocess.check_output(
        ["git", "ls-files", "*.lean"], cwd=ROOT, text=True).splitlines()}
    coverage = {b: set() for b in BRANCHES}
    records = {b: [] for b in BRANCHES}
    seen_oleans: dict[str, str] = {}
    seen_sources: dict[str, str] = {}
    metadata_paths = sorted(targets.rglob("metadata.json"))
    if len(metadata_paths) != 48:
        raise RuntimeError(f"expected 48 target shard artifacts for branches 16 and 17, found {len(metadata_paths)}")

    for mp in metadata_paths:
        d = mp.parent
        m = json.loads(mp.read_text(encoding="utf-8"))
        branch = int(m.get("branch", -1))
        if branch not in BRANCHES:
            raise RuntimeError(f"unexpected target branch in {mp}: {branch}")
        if m.get("source_artifact") != SOURCE_ARTIFACT or m.get("core_artifact") != CORE_ARTIFACT:
            raise RuntimeError(f"source/core artifact mismatch in {mp}")
        first, end = int(m["first"]), int(m["end"])
        if not 0 <= first < end <= 24:
            raise RuntimeError(f"invalid branch-{branch} interval [{first},{end})")
        for j in range(first, end):
            if j in coverage[branch]:
                raise RuntimeError(f"overlapping branch-{branch} target at kid {j}")
            coverage[branch].add(j)
        for filename, expected in m["files"].items():
            rel = Path(filename)
            if rel.is_absolute() or ".." in rel.parts or len(rel.parts) != 1:
                raise RuntimeError(f"unsafe artifact path {filename!r}")
            f = d / rel
            if not f.is_file() or sha(f) != expected:
                raise RuntimeError(f"target artifact SHA-256 mismatch: {f}")
        records[branch].append({
            "name": d.name, "first": first, "end": end,
            "modules": m.get("modules", []), "metadata_sha256": sha(mp),
        })
        for f in d.rglob("*.lean"):
            if f.name in tracked:
                continue
            h = sha(f)
            if f.name in seen_sources and seen_sources[f.name] != h:
                raise RuntimeError(f"conflicting target source {f.name}: {f}")
            if f.name not in seen_sources:
                shutil.copy2(f, factored / f.name)
                seen_sources[f.name] = h
        copy_oleans(d, work, seen_oleans)

    for b in BRANCHES:
        if coverage[b] != set(range(24)):
            raise RuntimeError(f"branch-{b} target complement: {sorted(set(range(24))-coverage[b])}")
        if len(records[b]) != 24:
            raise RuntimeError(f"expected 24 one-kid artifacts for branch {b}, got {len(records[b])}")

    # Preserve the target-shard objects and fill only missing common dependencies
    # from the pinned original core artifact.
    copy_oleans(core, work, seen_oleans, prefer_existing=True)

    # The branch source is pinned to the original generator artifact. Kid sources
    # come from the checked target shards where prefix factoring was applied.
    for b in BRANCHES:
        name = f"Raw122Branch{b:02}.lean"
        found = list(source.rglob(name))
        if len(found) != 1:
            raise RuntimeError(f"expected one pinned {name}, found {len(found)}")
        shutil.copy2(found[0], factored / name)
        for j in range(24):
            kid = f"Raw122Kid{b:02}_{j:02}.lean"
            if not (factored / kid).exists():
                matches = list(source.rglob(kid))
                if len(matches) != 1:
                    raise RuntimeError(f"missing unique original source for {kid}")
                shutil.copy2(matches[0], factored / kid)
            if not (work / f"Raw122Kid{b:02}_{j:02}.olean").is_file():
                raise RuntimeError(f"missing compiled target object Raw122Kid{b:02}_{j:02}.olean")

    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(work.resolve()), str(generated.resolve())])
    branch_logs = {}
    for b in BRANCHES:
        name = f"Raw122Branch{b:02}"
        branch_logs[b] = run(["lean", "-o", work / f"{name}.olean", f"{name}.lean"],
                             cwd=factored, env=env, capture=True)

    # The roster is derived from the exact prefix-factored source modules that
    # were compiled in the 48 source-checking target jobs.
    witness_info = {}
    for b in BRANCHES:
        roster_log = run([sys.executable, HERE / "residual_roster.py",
                          factored, generated, str(b)], capture=True)
        tsv = generated / f"Raw122Roster{b:02}.tsv"
        count = len([x for x in tsv.read_text(encoding="utf-8").splitlines() if x])
        expected = 13 if b == 16 else 24
        if count != expected or f"Raw122Roster{b:02} {count}" not in roster_log:
            raise RuntimeError(f"unexpected residual roster for branch {b}: {count}")
        witness_log = run([
            sys.executable, HERE / "roster_witnesses.py", str(b), tsv,
            ROOT / "im-results/agent29-raw122-run/hits.tsv",
            ROOT / "im-results/agent43-raw122-cut/direct_certificates.json",
            generated / f"Raw122Roster{b:02}Witnesses.lean",
        ], capture=True)
        witness_info[b] = json.loads(witness_log.splitlines()[-1])

    expected16 = {"indexed_ids": list(range(67, 78)), "direct_ids": [90], "specials": ["late1"]}
    expected17 = {"indexed_ids": list(range(78, 100)), "direct_ids": [104], "specials": ["counter17"]}
    for b, expected in ((16, expected16), (17, expected17)):
        for key, value in expected.items():
            if witness_info[b][key] != value:
                raise RuntimeError(f"branch {b} witness mapping changed for {key}: {witness_info[b][key]}")

    indexed_ids = sorted(set(witness_info[16]["indexed_ids"] + witness_info[17]["indexed_ids"]))
    direct_ids = sorted(set(witness_info[16]["direct_ids"] + witness_info[17]["direct_ids"]))
    run([sys.executable, ROOT / "im-results/agent29-raw122-run/generate.py",
         generated, *[str(i) for i in indexed_ids]])
    run([sys.executable, HERE / "direct_cert.py",
         ROOT / "im-results/agent43-raw122-cut/direct_certificates.json",
         generated, *[str(i) for i in direct_ids]], env=env)
    run([sys.executable, ROOT / "im-results/agent29-raw122-run/late.py", generated, "1"])

    run([sys.executable, ROOT / "im-results/agent13-coverage/unpack.py"])

    manifest = Path("/tmp/a43-branches16-17-manifest.json")
    run([sys.executable, ROOT / "tools/lean_compile_closure.py",
         "--workdir", manifest_work, "--source-root", ROOT, "--source-root", factored,
         "--manifest", manifest, "--manifest-only", "--artifact-dir", work,
         factored / "Raw122Branch16.lean", factored / "Raw122Branch17.lean"])

    for b in BRANCHES:
        tag = f"{b:02}"
        wrapper = generated / f"Raw122Recovered{tag}.lean"
        wrapper.write_text(f'''import BB6Coverage
import Raw122Base
import Raw122Roster{tag}
import Raw122Roster{tag}Witnesses
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw122Recovered{tag}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
theorem cover{tag} (m : Machine)
    (hm : compatible (BB6.Agent43Raw122.child ⟨true,false,{b-12}⟩) m) :
    WeightedBound 6766859 m := by
  exact BB6.Agent43Raw122Roster.cover{tag} 6766859 (by decide)
    BB6.Agent43Raw122Roster.witnesses{tag} m hm
theorem residual_count : BB6.Agent43Raw122Roster.tables{tag}.length = {13 if b==16 else 24} := by decide
#print axioms cover{tag}
#print axioms residual_count
end BB6.Agent43Raw122Recovered{tag}
''', encoding="utf-8")

        final = Path(f"/tmp/a43-final-{tag}")
        if final.exists():
            shutil.rmtree(final)
        final.mkdir(parents=True)
        theorem = f"BB6.Agent43Raw122Recovered{tag}.cover{tag}"
        log = run([
            sys.executable, ROOT / "tools/lean_compile_closure.py",
            "--workdir", final, "--source-root", ROOT, "--source-root", factored,
            "--source-root", generated, "--jobs", "3",
            "--precompiled-manifest", manifest, "--precompiled-dir", work,
            "--manifest", final / "manifest.json",
            "--label", f"Raw122 F1={'1LE' if b==16 else '1LF'} source-accepted child Cover",
            "--theorem", theorem,
            "--parent-table", f"Canonical124 raw122 parent with F1={'1LE' if b==16 else '1LF'}",
            "--weighted-bound", str(BOUND),
            "--artifact-name", f"raw122-branch{tag}-cover",
            *sum((["--override", f"{f.stem}={f}"] for f in generated.glob(f"Raw122Roster{tag}*.lean")), []),
            "--override", f"Raw122Recovered{tag}={wrapper}",
            wrapper,
        ], capture=True)
        for name in (theorem, f"BB6.Agent43Raw122Recovered{tag}.residual_count"):
            lines = [x for x in log.splitlines() if name in x and "depends on axioms:" in x]
            if len(lines) != 1 or any(t in lines[0] for t in ("sorryAx", "native_decide", "Lean.ofReduceBool")):
                raise RuntimeError(f"missing or untrusted axiom report for {name}: {lines}")

        out = output / f"branch{tag}-assembly"
        out.mkdir(parents=True)
        relevant = (
            f"Raw122Roster{tag}", "Agent29Raw122Indexed",
            f"Raw122D{90 if b==16 else 104}", f"Raw122Direct{90 if b==16 else 104}",
        )
        for f in generated.iterdir():
            if not f.is_file() or f.suffix not in {".lean", ".tsv"}:
                continue
            if f.name.startswith(relevant) or f.name == wrapper.name:
                if f.name.startswith("Agent29Raw122Indexed"):
                    idx = int(f.name.split("Indexed")[1][:3])
                    if idx not in witness_info[b]["indexed_ids"]:
                        continue
                shutil.copy2(f, out / f.name)
        if b == 16:
            for f in generated.iterdir():
                if f.is_file() and f.suffix == ".lean" and (
                    f.name == "LateCheck1.lean" or f.name.startswith("PackedLate1")
                ):
                    shutil.copy2(f, out / f.name)
        if b == 17:
            shutil.copy2(ROOT / "im-results/agent43-raw122-cut/Raw122Counter17.lean",
                         out / "Raw122Counter17.lean")
        shutil.copy2(factored / f"Raw122Branch{tag}.lean", out / f"Raw122Branch{tag}.lean")
        shutil.copy2(final / "manifest.json", out / "manifest.json")
        (out / "Lean-axioms.txt").write_text(log, encoding="utf-8")
        shutil.copy2(final / f"Raw122Recovered{tag}.olean", out / f"Raw122Recovered{tag}.olean")
        shutil.copy2(work / f"Raw122Branch{tag}.olean", out / f"Raw122Branch{tag}.olean")
        meta = {
            "branch": "1LE" if b == 16 else "1LF",
            "branch_index": b,
            "residual_count": witness_info[b]["residual_count"],
            "weighted_bound": BOUND,
            "source_artifact": SOURCE_ARTIFACT,
            "core_artifact": CORE_ARTIFACT,
            "target_artifacts": records[b],
            "target_coverage": sorted(coverage[b]),
            "merged_olean_count": len(seen_oleans),
            "witness_mapping": witness_info[b],
            "theorem": theorem,
            "branch_compile_output": branch_logs[b],
            "workflow_run_id": os.environ.get("GITHUB_RUN_ID"),
        }
        (out / "proof-metadata.json").write_text(json.dumps(meta, indent=2, sort_keys=True) + "\n")
        print(json.dumps(meta, indent=2, sort_keys=True), flush=True)

    print("SUCCESS: original Raw122 F1=1LE and F1=1LF child Covers compiled at 6766859", flush=True)

if __name__ == "__main__":
    main()
