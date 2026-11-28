#!/usr/bin/env python3
"""Recover the two Raw56 pilot branches from successful shards of run 46064129990.

This is proof assembly, not discovery. Only E11LC cut shard 0 was cancelled.
All other certificate and cut shards are reused with their original module
names and frozen prepared source graph. Reject missing or conflicting objects.
"""
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

RUN = 46064129990
TAGS = ("E10RD", "E11LC")
SHARDS = set(range(4))
SPECIAL = ["RunStack", "M19569Data"] + [f"M19569Check{i}" for i in range(36)] + [
    "M19569Final", "Raw56LCM5334", "Raw56LCM20376", "Raw56PilotSpecial"
]

def read(p):
    return json.loads(p.read_text())

def digest(p):
    with p.open("rb") as f:
        return hashlib.file_digest(f, "sha256").hexdigest()

def module(root, name, suffix):
    return root / Path(*name.split(".")).with_suffix(suffix)

def merge_objects(src, dst):
    for p in sorted(src.rglob("*")):
        if not p.is_file() or not (p.name.endswith(".olean") or ".olean." in p.name):
            continue
        q = dst / p.relative_to(src)
        q.parent.mkdir(parents=True, exist_ok=True)
        if q.exists():
            if digest(p) != digest(q):
                raise ValueError(f"conflicting object: {p} and {q}")
        else:
            shutil.copy2(p, q)

def need(root, names):
    for name in names:
        if not module(root, name, ".olean").is_file():
            raise ValueError(f"missing object {name} in {root}")

def validate_certs(prep, tag, inputs, dest):
    meta = read(prep / tag / "accept-meta.json")
    found = set()
    for p in sorted(inputs.iterdir()):
        if not p.is_dir():
            continue
        m = read(p / "cert-meta.json")
        k = m["shard"]
        assert m["tag"] == tag and m["shards"] == 4 and k in SHARDS - found, m
        expected = meta["cert_modules"][k::4] + [
            name for name in meta["growth_modules"][k::4] if name != "Raw56PilotSpecial"
        ]
        assert m["modules"] == expected, (p, m)
        need(p, ["TwoSidedAutomata", *expected, *(SPECIAL if tag == "E11LC" and k == 0 else [])])
        merge_objects(p, dest)
        found.add(k)
    assert found == SHARDS, found

def validate_cut(prep, tag, src, dest, found):
    man = read(prep / tag / "manifest.json")
    deps = dict(man)
    base, final = man[0][0], man[-1][0]
    top = man[-1][1]
    m = read(src / "cut-meta.json")
    k = m["shard"]
    assert m["tag"] == tag and k in SHARDS - found, m
    roots = top[k::4]
    assert m["roots"] == roots, (src, m)
    closure = set()
    def visit(name):
        if name in closure or name not in deps or name in (base, final):
            return
        closure.add(name)
        for d in deps[name]:
            visit(d)
    for root in roots:
        visit(root)
    assert set(m["modules"]) == closure, (src, m)
    need(src, [f"{tag}.{name}" for name in [base, *sorted(closure)]])
    merge_objects(src, dest)
    found.add(k)

def check_base(base):
    m = read(base / "manifest.json")
    assert m["module_count"] == 747
    assert m["claim"]["theorem"] == "BB6.Agent1Raw56Root.sound19_closed"
    lean = Path(shutil.which("lean"))
    # elan shim is not the underlying compiler.
    if shutil.which("elan"):
        lean = Path(subprocess.check_output(["elan", "which", "lean"], text=True).strip())
    assert digest(lean) == m["lean_binary"]["sha256"] == "db7f559d05795e7af52e42bc966c90240a39dcb9712161c54c97afa546e20c00"
    for item in m["modules"]:
        assert digest(base / item["olean_path"]) == item["olean_sha256"], item
    return digest(base / "manifest.json")

def main():
    p = argparse.ArgumentParser()
    p.add_argument("mode", choices=["restore", "final"])
    p.add_argument("--tag", choices=TAGS, required=True)
    for name in ("prep", "base", "cert-inputs", "cut-inputs", "work", "out"):
        p.add_argument("--" + name, type=Path, required=True)
    p.add_argument("--new-cut", type=Path, required=True)
    p.add_argument("--compiler", type=Path, required=True)
    a = p.parse_args()
    certs, cuts = a.work / "certs", a.work / "cuts"
    certs.mkdir(parents=True, exist_ok=True)
    cuts.mkdir(parents=True, exist_ok=True)
    base_sha = check_base(a.base)
    validate_certs(a.prep, a.tag, a.cert_inputs, certs)
    found = set()
    for d in sorted(a.cut_inputs.iterdir()):
        if d.is_dir():
            validate_cut(a.prep, a.tag, d, cuts, found)
    if a.mode == "restore":
        expected = SHARDS if a.tag == "E10RD" else SHARDS - {0}
        assert found == expected, (a.tag, found)
        if a.tag == "E11LC":
            subprocess.run([sys.executable, str(a.compiler), "compile-cut",
                            "--prep", str(a.prep), "--base", str(a.base),
                            "--certs", str(certs), "--tag", a.tag,
                            "--shard", "0", "--shards", "4",
                            "--out", str(a.new_cut)], check=True)
        return
    if a.tag == "E11LC":
        validate_cut(a.prep, a.tag, a.new_cut, cuts, found)
    assert found == SHARDS, found
    subprocess.run([sys.executable, str(a.compiler), "compile-final",
                    "--prep", str(a.prep), "--base", str(a.base),
                    "--certs", str(certs), "--cuts", str(cuts),
                    "--tag", a.tag, "--out", str(a.out)], check=True)
    theorem = f"BB6.Agent1Raw56Pilot.{a.tag}.all_quotient"
    checker = a.compiler.parent.parent / "agent1-raw57" / "check_axioms.py"
    subprocess.run([sys.executable, str(checker),
                    str(a.out / f"{a.tag}-final.log"), "--require", theorem], check=True)
    data = {"prior_run": RUN, "tag": a.tag, "base_manifest_sha256": base_sha,
            "prepared_manifest_sha256": digest(a.prep / a.tag / "manifest.json"),
            "theorem": theorem,
            "objects": {kind: {str(f.relative_to(root)): digest(f)
                                for f in sorted(root.rglob("*.olean"))}
                        for kind, root in [("certs", certs), ("cuts", cuts)]}}
    (a.out / "recovery-inputs.json").write_text(json.dumps(data, indent=2) + "\n")

if __name__ == "__main__":
    main()
