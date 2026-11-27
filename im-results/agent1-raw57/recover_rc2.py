#!/usr/bin/env python3
"""Recompile accepted Raw57 source certificates under pinned Lean rc2.

The original cut manifests used Lean 4.36.0 final. Their source is useful,
but their object headers are incompatible with the canonical rc2 interface.
Only the missing early source cut is regenerated; no new witness discovery.
"""
import argparse
import hashlib
import json
import re
from itertools import product
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE.parent / "agent2-raw63-shards"))
from repair_raw67 import fetch as fetch_core, split_children, MOVES
from shard import compile_roots, merge, schedule, digest, PARENTS

PARENTS["57"] = ("1RB---_1RC---_0RD---_1LD1RE_---0LA_------", "1500", "Agent31Raw57")
EARLY = ["RA", "RB0", "RC0", "RB1", "RC1", "RE1", "RE0", "RF0"]
MIDDLE = ["LB0", "LC0", "LD0", "RA1", "RF1", "LC1"]
RESIDUAL = ["LA1", "LB1", "LE1", "LF0", "LF1"]
CHILDREN = EARLY + MIDDLE + RESIDUAL
PINS = {
    "middle": (15161588755, "a83a27c85aa7586300f0e55e2bec2c5d62c5b811dcfe231a8f91beac733e6bfa"),
    "residual-a": (15164504491, "15f4c36af8a38b8ff4690083db1e3ad417da787c3bd1a991edd395a3ec14dfba"),
    "residual-b": (15162872297, "6870543400a502c9a49c7c3bc76e60a743c86029370b82bbd557e4430738818c"),
}
REPO = "FlareZ123/bb6"
ORIGINAL_RUN = 45912215362
ORIGINAL_REVISION = "68d9ea23b6c709c3bec6fa880d12c0e37161124b"
LIMIT = 30000


def run(path, *args):
    subprocess.run([sys.executable, str(ROOT/path), *args], cwd=ROOT, check=True)


def put(dest, data):
    if dest.exists():
        assert dest.read_bytes() == data, f"source collision: {dest.name}"
    else:
        dest.write_bytes(data)


def source_cut(group, generated):
    aid, expected = PINS[group]
    info = json.loads(subprocess.check_output(
        ["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}"], text=True))
    assert info["workflow_run"]["id"] == ORIGINAL_RUN
    assert info["name"] == "raw57-cut-" + group and not info["expired"]
    assert info["digest"] == "sha256:" + expected
    archive = generated.parent / f"{aid}.zip"
    with archive.open("wb") as f:
        subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{aid}/zip"], stdout=f, check=True)
    assert digest(archive) == expected
    with zipfile.ZipFile(archive) as z:
        m = json.loads(z.read("manifest.json"))
        assert m["proof_source_revision"] == ORIGINAL_REVISION
        assert m["artifact_name"] == info["name"]
        assert m["module_count"] == len(m["modules"])
        expected_roots = {
            "middle": MIDDLE, "residual-a": RESIDUAL[:3], "residual-b": RESIDUAL[3:]}[group]
        assert {x["module"] for x in m["roots"]} == {f"Raw57{x}Data" for x in expected_roots}
        for entry in m["modules"]:
            module = entry["module"]
            assert re.fullmatch(r"[A-Za-z0-9_]+",module), module
            data = z.read("precompiled/" + module + ".lean")
            assert hashlib.sha256(data).hexdigest() == entry["source_sha256"], module
            put(generated / (module + ".lean"), data)
    archive.unlink()
    print(f"Reused {group}: {m['module_count']} exact source modules from {m['lean_version']}",flush=True)


def factor(path):
    """Factor only a simple generated exact child check; existing factored modules stay unchanged."""
    source = path.read_text()
    m = re.fullmatch(r"(.*?)(?:def (kid\d\d) : Audit := )(.*?)\ntheorem (check\d\d) : zipCheck (\d+) (\(child ⟨[^⟩]+⟩\)) \2 = true := by decide\n\s*(end [^\n]+)\s*", source, re.S)
    if not m:
        return 0
    header, kid, tree, check, bound, parent, end = m.groups()
    header = "import ZipPrefixAudit\n" + header
    if len(tree) <= LIMIT:
        path.write_text(header + f"def {kid} : Audit := {tree}\ntheorem {check} : zipCheck {bound} {parent} {kid} = true := by\n  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]\n  decide\n\n" + end + "\n")
        return 0
    made = 0
    def emit(text, p, suffix):
        nonlocal made
        mod, k, c = path.stem + suffix, kid + suffix, check + suffix
        if len(text) <= LIMIT:
            imports = ""
            body = f"def {k} : Audit := {text}\ntheorem {c} : zipCheck {bound} {p} {k} = true := by\n  rw [← BB6.Agent48PrefixAudit.prefixCheck_eq]\n  decide\n"
        else:
            n, slot, children = split_children(text)
            names = [emit(t, f"(refine {p} {slot} (some {mv}))", suffix+f"P{i:02}")
                     for i,(t,mv) in enumerate(zip(children,MOVES))]
            imports = "".join(f"import {module}\n" for module,_,_ in names)
            branch = k + "Branches"
            body = f"def {branch} : Move → Audit := byMove [{','.join(x[1] for x in names)}]\n"
            body += f"theorem {branch}_checked (mv : Move) : zipCheck {bound} (refine {p} {slot} (some mv)) ({branch} mv) = true := by\n  rcases mv with ⟨w,r,q⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n"
            body += "\n".join(f"  · exact {names[12*w+6*r+q][2]}" for q,w,r in product(range(6),range(2),range(2)))+"\n"
            body += f"def {k} : Audit := .split {n} {slot} {branch}\n"
            body += f"theorem {c} : zipCheck {bound} {p} {k} = true := by\n  change (zipQueryOK {bound} {p} {n} {slot} && allMoves (fun mv => zipCheck {bound} (refine {p} {slot} (some mv)) ({branch} mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide, allMoves_of _ {branch}_checked⟩\n"
        target = path.with_name(mod + ".lean")
        assert target == path or not target.exists(), target
        target.write_text(imports + header + body + "\n" + end + "\n")
        made += bool(suffix)
        return mod,k,c
    emit(tree,parent,"")
    return made


def prepare(generated, core):
    generated.mkdir(parents=True,exist_ok=False)
    for group in PINS:
        source_cut(group, generated)
    run("im-results/agent13-coverage/unpack.py")
    run("im-results/agent31-three-hole-tnf/generate_sweeps.py")
    run("im-results/agent31-three-hole-tnf/generate_four_hole.py")
    run("im-results/agent6-raw57-ra/generate.py")
    for move in ("0RB","0RC","1RB","1RC","1RE","0RE","0RF"):
        run("im-results/agent6-raw57-ra/generate_sibling.py",move)
    early_dir = HERE.parent / "agent6-raw57-ra"
    # All generated early module families and unpacked custom proof dependencies.
    for path in sorted(early_dir.glob("*.lean")):
        if path.name.startswith(tuple("Raw57"+c for c in EARLY)) or not (generated/path.name).exists():
            put(generated/path.name,path.read_bytes())
    for name in ("Raw57ParentBridge","Raw57ParentConsumer","Raw57ParentConsumerWithLALE","Raw57ParentComplete"):
        put(generated/(name+".lean"),(HERE/(name+".lean")).read_bytes())
    put(generated/"Raw57ParentCover.lean",(HERE/"Raw57ParentCover.lean").read_bytes())
    n = sum(factor(path) for path in sorted(generated.glob("Raw57*Kid[0-9][0-9].lean")))
    print(f"Factored large exact child trees into {n} additional bounded checks",flush=True)
    groups = [[f"Raw57{x}Data"] for x in CHILDREN]
    assert all((generated/(name+".lean")).is_file() for group in groups for name in group)
    (generated/"schedule.json").write_text(json.dumps({
        "branch":"57","final":"Raw57ParentCover","groups":groups,
        "sources":{p.name:digest(p) for p in sorted(generated.glob("*.lean"))}},indent=2)+"\n")
    fetch_core("core",core)
    cm=json.loads((core/"manifest.json").read_text())
    assert "4.36.0-rc2" in cm["lean_version"]


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("action",choices=("prepare","shard","assemble"))
    ap.add_argument("--generated",required=True,type=Path)
    ap.add_argument("--core",type=Path)
    ap.add_argument("--work",type=Path)
    ap.add_argument("--shard",type=int)
    ap.add_argument("--inputs",type=Path)
    ap.add_argument("--merged",type=Path)
    a=ap.parse_args()
    if a.action=="prepare":
        prepare(a.generated,a.core)
    elif a.action=="shard":
        s=schedule(a.generated)
        compile_roots([a.generated/(x+".lean") for x in s["groups"][a.shard]],
                      a.generated,a.core,a.work,"57")
    else:
        merge(a.inputs,a.merged,a.generated,prefix="raw57-rc2")
        compile_roots([a.generated/"Raw57ParentCover.lean"],a.generated,a.merged,a.work,"57",final=True)

if __name__=="__main__":
    main()
