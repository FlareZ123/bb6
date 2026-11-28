"""Compose the pinned accepted Raw36 proof objects, with no child search or replay.

Download the named ZIPs to --inputs or supply --download in an authenticated
GitHub Actions environment. Only the dependency closure of requested roots
is imported (the old pilot's Raw36Kid08 is deliberately not selected).
"""
import argparse, hashlib, json, os, re, subprocess, zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PINS = json.loads((ROOT / "accepted_pins.json").read_text())
AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
def sha(data): return hashlib.sha256(data).hexdigest()
def file_sha(p):
    with p.open("rb") as f: return hashlib.file_digest(f, "sha256").hexdigest()
def canonical(x): return json.dumps(x, sort_keys=True, separators=(",", ":")).encode()
def identity(entry, members):
    deps = [{"module": d, "identity": members[d]["module_identity_sha256"]}
            for d in sorted(entry["project_imports"])]
    imp = sha(canonical(deps))
    payload = {k: entry[k] for k in ("module", "source_sha256", "project_imports", "olean_sha256")}
    payload["import_closure_sha256"] = imp
    return imp, sha(canonical(payload))

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--inputs", type=Path, required=True)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--download", action="store_true")
    args = ap.parse_args()
    args.inputs.mkdir(parents=True, exist_ok=True)
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    compiler = Path(subprocess.check_output([args.lean, "--print-prefix"], text=True).strip()) / "bin/lean"
    compiler_sha = file_sha(compiler)
    assert compiler_sha == "db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00"
    members = {}
    for pin in PINS:
        archive = args.inputs / (pin["name"] + ".zip")
        if args.download and not archive.exists():
            with archive.open("wb") as f:
                subprocess.run(["gh", "api", f'repos/FlareZ123/bb6/actions/artifacts/{pin["artifact_id"]}/zip'], stdout=f, check=True)
        assert file_sha(archive) == pin["sha256"], archive
        with zipfile.ZipFile(archive) as z:
            m = json.loads(z.read("manifest.json"))
            assert m["schema_version"] == 1 and m["lean_version"] == version
            assert m["lean_binary"]["sha256"] == compiler_sha
            assert m["proof_source_revision"] == m["workflow"]["workflow_head_sha"] == pin["revision"]
            assert int(m["workflow"]["run_id"]) == pin["run_id"]
            assert m["claim"]["weighted_bound"] == pin["bound"]
            assert set(pin["roots"]) <= {r["module"] for r in m["roots"]}
            index = {e["module"]: e for e in m["modules"]}
            assert len(index) == m["module_count"] == len(m["modules"])
            visited = set()
            def visit(name):
                if name in visited: return
                assert re.fullmatch(r"[A-Za-z0-9_.]+", name)
                e = index[name]
                for d in e["project_imports"]: visit(d)
                imp, ident = identity(e, members)
                assert (imp, ident) == (e["import_closure_sha256"], e["module_identity_sha256"]), name
                if name in members:
                    assert members[name]["module_identity_sha256"] == ident, name
                else:
                    rel = Path(*name.split("."))
                    for ext, key in ((".lean", "source_sha256"), (".olean", "olean_sha256")):
                        p = rel.with_suffix(ext)
                        data = z.read(str(p))
                        assert sha(data) == e[key], (pin["name"], p)
                        dst = work / p
                        dst.parent.mkdir(parents=True, exist_ok=True)
                        dst.write_bytes(data)
                    members[name] = e
                visited.add(name)
            for r in pin["roots"]: visit(r)
        print("accepted", pin["name"], len(visited), flush=True)
    env = dict(os.environ, LEAN_PATH=str(work))
    roots = []
    output = []
    for name in ("Raw36Branch", "Raw36D1Complement", "Raw36ParentComplement", "Raw36ParentLive12"):
        src = ROOT / (name + ".lean")
        dst = work / src.name
        dst.write_bytes(src.read_bytes())
        p = subprocess.run([args.lean, "-o", name + ".olean", dst.name],
                           cwd=work, env=env, text=True, capture_output=True, check=True)
        print(p.stdout, end="", flush=True)
        assert not p.stderr, p.stderr
        output.append(p.stdout)
        axioms = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", p.stdout)
        expected = {"Raw36Branch": {"children_bound", "branch_bound", "branch_cover"},
                    "Raw36D1Complement": {"b1Complement_count", "b1Complement_nodup", "d1_bound_from_four", "d1_cover_from_four"},
                    "Raw36ParentComplement": {"remaining_explicit", "parentComplement_count", "parent_cover_from_thirteen"},
                    "Raw36ParentLive12": {"b101_identity", "b1Live_count", "parentLive12_count", "b101_cover_at", "d1_cover_from_three", "parent_cover_from_twelve"}}[name]
        assert {k.rsplit(".", 1)[-1] for k, _ in axioms} == expected, p.stdout
        assert all(set(x.strip() for x in a.split(",") if x.strip()) <= AXIOMS for _, a in axioms)
        entry = {"module": name, "source_path": "im-results/agent29-raw36/" + src.name,
                 "source_kind": "tracked", "source_sha256": file_sha(dst),
                 "project_imports": re.findall(r"^import ([A-Za-z0-9_.]+)$", dst.read_text(), re.M),
                 "olean_path": name + ".olean", "olean_sha256": file_sha(work / (name + ".olean"))}
        entry["import_closure_sha256"], entry["module_identity_sha256"] = identity(entry, members)
        members[name] = entry
        roots.append({k:entry[k] for k in ("module", "source_path", "source_sha256")})
    revision = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"], text=True).strip()
    result = {"schema_version": 1, "label": "raw36-d1-complement",
              "artifact_name": "raw36-d1-complement", "proof_source_revision": revision,
              "source_revisions": sorted({revision, *(p["revision"] for p in PINS)}),
              "workflow": {"run_id": os.environ.get("GITHUB_RUN_ID"), "workflow_head_sha": os.environ.get("GITHUB_SHA")},
              "lean_version": version, "lean_binary": {"path": str(compiler), "sha256": compiler_sha},
              "claim": {"theorem": "BB6.Agent29Raw36.parent_cover_from_twelve", "weighted_bound": 1022,
                        "parent_table": "1RB---_1RC---_0RD---_0LD---_------_------",
                        "conditional": True, "remaining_D1": ["0LA", "1LA", "0LB", "0LC", "1LC", "0LE", "0RE", "1LE", "1RE"], "remaining_B1": ["0LE", "1LE", "1RE"]},
              "roots": roots, "module_count": len(members),
              "modules": [members[k] for k in sorted(members)],
              "provenance_inputs": [{"path": "im-results/agent29-raw36/accepted_pins.json",
                                     "sha256": file_sha(ROOT / "accepted_pins.json")}],
              "precompiled_core": None}
    (work / "manifest.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    (work / "audit.log").write_text("".join(output))
    print("Accepted exact dependency closure:", len(members), "modules", flush=True)

if __name__ == "__main__":
    main()
