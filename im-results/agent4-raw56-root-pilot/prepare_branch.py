#!/usr/bin/env python3
"""Materialize a frozen complete Raw56 branch candidate ledger as original Lean source.

Reconstruct the deterministic original canonical cut and cheap FAR-bank witnesses;
replay exactly the recorded finite-stack parameters and symbolic sweeps, without
searching a portfolio again. All generated source is subsequently kernel checked.
"""
import argparse
import base64
import gzip
import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

LEDGER_SHA = {
    "E10RB": "0a4eea4ca50a6089fae9916ff8c3298b961581cd0944762bef95682bea8b44dd",
}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def valid_far(code):
    n = (len(code) - 1) // 2
    return (len(code) >= 3 and len(code) % 2 == 1 and code[0] in "01"
            and n <= 10 and all("0" <= x <= "9" and int(x) < n for x in code[1:]))

def parse_table(s):
    t = s.replace("_", "")
    assert len(t) == 36
    return [t[j:j+3] for j in range(0, 36, 3)]

def run(args, cwd, **kw):
    return subprocess.run(args, cwd=cwd, check=True, **kw)

def emit_selective(source, target):
    # The original generator imports every finite proof into the root base.
    # Preserve its tree/proof semantics, importing only proofs used by each shard.
    s = source.read_text()
    replacements = [
        ("emit(MOD+'Base',['Raw40Nores']+AUTOS,base)",
         "emit(MOD+'Base',['Raw40Nores'],base)\nused=set()"),
        ("return f'.proven {PROVEN[s]}.table {PROVEN[s]}.never' if s in PROVEN else far(bank[i],p)",
         "if s in PROVEN:\n            mod,ns=PROVEN[s];used.add(mod)\n            return f'.proven {ns}.table {ns}.never'\n        return far(bank[i],p)"),
        ("if current_name:emit(current_name,[MOD+'Base'],current)",
         "if current_name:emit(current_name,[MOD+'Base']+sorted(used),current)\n    used.clear()"),
    ]
    for old, new in replacements:
        assert s.count(old) == 1, old
        s = s.replace(old, new)
    target.write_text(s)

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--ledger", type=Path, required=True)
    a = p.parse_args()
    raw = gzip.decompress(base64.b64decode(a.ledger.read_text().strip(), validate=True))
    data = json.loads(raw)
    tag, bound = data["tag"], data["bound"]
    assert hashlib.sha256(raw).hexdigest() == LEDGER_SHA[tag]
    src, out = a.source.resolve(), a.out.resolve()
    assert not out.exists(), out
    shutil.copytree(src, out)
    sys.path[:0] = [str(out), str(Path(__file__).resolve().parents[1] / "agent1-raw56")]
    from root_pilot_accept import patch_emitter
    from discover_siblings import method
    from minimize_cert import quotient, validate
    from emit_automata import emit as emit_finite
    from emit_symbolic import emit as emit_growth

    parent = f"1RB---_1RC---_0RD---_1LD1LE_---{tag[2:]}_------"
    stem = out / tag
    run(["g++", "-O3", "-std=c++20", "cut.cpp", "-o", "cut"], out)
    run(["g++", "-O3", "-std=c++20", "farbank.cpp", "-o", "farbank"], out)
    # One transferred code 101123241 had an out-of-range state; exclude all
    # invalid code shapes before they reach the historical C++ importer.
    codes = (out / "bank-candidates.txt").read_text().split()
    valid = [c for c in codes if valid_far(c)]
    (out / "valid-bank.txt").write_text("\n".join(valid) + "\n")
    print("bank rejected", [c for c in codes if not valid_far(c)], flush=True)
    run([str(out / "cut"), parent, "1000", "32", "7", str(stem)], out)
    assert sha(stem.with_suffix(".json")) == data["tree_sha256"]
    assert sha(stem.with_suffix(".open")) == data["open_sha256"]
    rows = stem.with_suffix(".open").read_text().splitlines()
    query = "".join(f"{i} {s.replace('_','')}\n" for i, s in enumerate(rows))
    with stem.with_suffix(".far").open("w") as f, stem.with_suffix(".far.log").open("w") as log:
        run([str(out / "farbank"), "4", str(out / "valid-bank.txt")], out,
            input=query, text=True, stdout=f, stderr=log)
    assert sha(stem.with_suffix(".far")) == data["far_sha256"]
    bank_rows = [(int(i), c) for i, c in (s.split() for s in stem.with_suffix(".far").read_text().splitlines())]
    bank = {i: c for i, c in bank_rows}
    assert len(bank) == len(bank_rows) and all(valid_far(c) for c in bank.values())
    finite = {i: (pid, n) for i, pid, n in data["finite"]}
    late = {i: (s, n, slot) for i, s, n, slot in data["late"]}
    growth = {r["index"]: r for r in data["growth"]}
    assert len(finite) == len(data["finite"]) and len(late) == len(data["late"]) and len(growth) == len(data["growth"])
    sets = [set(x) for x in (bank, finite, late, growth)]
    assert sum(map(len, sets)) == len(set.union(*sets)) == len(rows)
    assert set.union(*sets) == set(range(len(rows)))
    assert len(set(rows)) == len(rows)

    ns = f"BB6.Agent4Raw56BranchFinite.{tag}"
    fdir = out / "finite" / tag
    fdir.mkdir(parents=True, exist_ok=True)
    proven = {}
    certmods = []
    for i, (pid, n) in finite.items():
        kind, left, right = data["params"][pid]
        t = rows[i]
        tbl = parse_table(t)
        cert = method(tbl, kind, left, right, max(12000, n + 1))
        assert cert[0] and cert[1] == n, (i, cert[:2], n)
        cert = quotient(cert)
        validate(tbl, cert)
        mod = f"finite.{tag}.F{i}"
        (fdir / f"F{i}.lean").write_text(
            "import TwoSidedAutomata\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
            + f"namespace {ns}\nopen BB6Coverage\n"
            + emit_finite(i, tbl, cert) + f"\nend {ns}\n")
        certmods.append(mod)
        proven[t] = [mod, f"{ns}.M{i}"]
    gdir = out / "rootgrowth"
    gdir.mkdir(exist_ok=True)
    growthmods = []
    for i, r in growth.items():
        assert r["table"] == rows[i]
        name = f"{tag}M{i}"
        mod = f"rootgrowth.{name}"
        (gdir / (name + ".lean")).write_text(emit_growth(r, tag))
        growthmods.append(mod)
        proven[rows[i]] = [mod, f"BB6.Agent4Raw56Root{tag}.M{i}"]
    lrows = {}
    for i, (s, n, slot) in late.items():
        assert s == rows[i] and s.count("---") == 1 and parse_table(s)[slot] == "---"
        assert n + 7 <= bound
        lrows[s] = ["last", n, slot]
    od = out / tag
    od.mkdir(exist_ok=True)
    for name, value in (("proven", proven), ("late", lrows), ("automata_modules", certmods + growthmods)):
        (od / (name + ".json")).write_text(json.dumps(value))
    patch_emitter(out / "emit_cut.py", out / "emit_root_cut.py")
    emit_selective(out / "emit_root_cut.py", out / "emit_branch_cut.py")
    run([sys.executable, "emit_branch_cut.py", tag, str(bound)], out)
    man = json.loads((od / "manifest.json").read_text())
    meta = {"tag": tag, "bound": bound, "open": len(rows), "valid_far": len(bank),
            "finite": len(finite), "late": len(late), "proven": len(proven),
            "cert_modules": certmods, "growth_modules": growthmods,
            "cut_modules": len(man), "top_roots": man[-1][1], "final_module": man[-1][0],
            "ledger_sha256": LEDGER_SHA[tag]}
    (od / "accept-meta.json").write_text(json.dumps(meta, indent=2) + "\n")
    print({k: v for k, v in meta.items() if k not in ("cert_modules", "growth_modules", "top_roots")})

if __name__ == "__main__":
    main()
