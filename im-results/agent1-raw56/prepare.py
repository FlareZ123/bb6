#!/usr/bin/env python3
"""Replay the exact Raw56 E1=0RE candidate and emit sharded Lean audit modules.

The C++ and Python discovery code is untrusted. Only the final original-source
Lean check, including all split/last/cycle/FAR/pump/sparse leaves, is authoritative.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import hashlib
import json
import os
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
IM = HERE.parent
OUT = HERE / "generated"
OUT.mkdir(exist_ok=True)
spec = json.loads((HERE / "candidates.json").read_text())
sys.path[:0] = [str(IM / "agent31-three-hole-tnf"), str(IM / "agent47-raw111-cut")]
import generate_sweeps as pump
import emit_sparse

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def build(source, exe, std="c++20"):
    subprocess.run(["g++", "-O3", "-std=" + std, str(source), "-o", str(exe)], check=True)

def census(tree):
    c = Counter([tree[0]])
    if tree[0] == "split":
        assert len(tree[3]) == 24
        for child in tree[3]:
            c.update(census(child))
    return c

def run():
    with tempfile.TemporaryDirectory() as td:
        tmp = Path(td)
        build(IM / "agent7-raw49/cut.cpp", tmp / "cut")
        build(IM / "agent19-raw40-cut/farbank.cpp", tmp / "farbank")
        build(IM / "agent47-raw111-cut/ngram_sparse.cpp", tmp / "ngram", "c++17")
        subprocess.run([str(tmp / "cut"), spec["parent"], str(spec["cap"]),
                        str(spec["lookback"]), str(spec["depth"]), str(tmp / "raw")], check=True)
        assert digest(tmp / "raw.open") == spec["open_sha256"]
        assert digest(tmp / "raw.json") == spec["tree_sha256"]
        (tmp / "raw.open").rename(tmp / "open.txt")
        (tmp / "raw.json").rename(tmp / "tree.json")
        rows = (tmp / "open.txt").read_text().splitlines()
        tree = json.loads((tmp / "tree.json").read_text())
        assert census(tree) == Counter(spec["counts"])
        assert len(rows) == len(set(rows)) == spec["counts"]["open"]
        assert tree[:3] == ["split", 10, 8]
        input_rows = "".join(f"{i} {row.replace('_', '')}\n" for i, row in enumerate(rows))
        with (tmp / "far5.txt").open("w") as f, (tmp / "far5.log").open("w") as err:
            subprocess.run([str(tmp / "farbank"), "5"], input=input_rows, text=True,
                           stdout=f, stderr=err, check=True)
        assert digest(tmp / "far5.txt") == spec["far5_sha256"]
        far5 = {int(x.split()[0]) for x in (tmp / "far5.txt").read_text().splitlines()}
        assert len(far5) == spec["far5_count"]
        extra = {int(k): v for k, v in spec["far_extra"].items()}
        sparse = {int(k): v for k, v in spec["sparse"].items()}
        pumps = set(spec["pumps"])
        categories = [far5, set(extra), set(sparse), pumps]
        assert sum(map(len, categories)) == len(set.union(*categories)) == len(rows)
        assert set.union(*categories) == set(range(len(rows)))
        (tmp / "far_extra.txt").write_text("".join(f"{i} {code}\n" for i, code in extra.items()))
        imports, proven = [], {}
        # Generate fully quantified sweep equations with the shared exact zipper
        # semantics, not a finite trace extrapolation.
        pump.local = lru_cache(maxsize=50000)(pump.local)
        for i in sorted(pumps):
            p = pump.parse(rows[i])
            if i == 2006:
                # The growth adds twelve bits but the transferable block is 0101.
                # Using the entire growth word as the opaque block misses this case.
                c = next(c for t, _, c in pump.concrete_events(p) if t == 52)
                st = pump.C(0, 0, 0, pump.W(), pump.W("1", "0101", "0101010101"))
                ta = pump.C(0, -4, 0, pump.W(), pump.W("1010101010101", "0101", "0101010101"))
                res = pump.pump(p, st, ta)
                assert res is not None
                ans = (52, c, st, ta, res)
            else:
                ans = pump.candidate(p, pump.concrete_events(p))
                assert ans is not None, (i, rows[i])
            source, info = pump.generate(i, p, ans)
            if i == 2006:
                assert info == (52, 100, 16), info
            name = f"Raw56Sweep{i}"
            ns = f"BB6Coverage.Agent31Pump.{name}"
            (OUT / (name + ".lean")).write_text("\n\n".join([
                "import SweepPumping", "set_option maxRecDepth 100000",
                "set_option maxHeartbeats 0", "set_option linter.unusedVariables false",
                f"namespace {ns}", "open BB6Coverage", source, f"end {ns}"
            ]) + "\n")
            imports.append(name)
            proven[rows[i]] = f"{ns}.M{i}"
            print("SWEEP", i, info, flush=True)
        for i, (k, n, l, r) in sparse.items():
            result = subprocess.check_output([str(tmp / "ngram"), str(k)],
                                             input=f"{i} {rows[i]}\n", text=True)
            ident, data = result.strip().split(maxsplit=1)
            assert int(ident) == i
            name, ns = emit_sparse.emit(OUT, i, rows[i], data, width=k,
                                         module_name=f"Raw56Sparse{i}", expected=(n,l,r))
            imports.append(name)
            proven[rows[i]] = ns
        (tmp / "proven.txt").write_text("".join(f"{row} {ns}\n" for row, ns in proven.items()))
        # Reuse the shared modular canonical emitter unchanged except for
        # hexadecimal DFA labels and a distinct namespace. No checker semantics
        # are modified. The original helper assumes decimal-only DFA labels.
        helper = tmp / "helper"
        helper.mkdir()
        shared = IM / "agent19-raw40-cut"
        for name in ("certify_shards.py", "certify_canonical.py", "certify_modular.py"):
            text = (shared / name).read_text()
            if name == "certify_shards.py":
                assert "D=list(map(int,code[1:]))" in text
                text = text.replace("D=list(map(int,code[1:]))", "D=[int(x,16) for x in code[1:]]")
            text = text.replace("BB6.Agent19Raw40.{mod}", "BB6.Agent1Raw56.{mod}")
            (helper / name).write_text(text)
        env = os.environ.copy()
        env["RAW40_PROOF_IMPORTS"] = " ".join(imports)
        subprocess.run([sys.executable, str(helper / "certify_modular.py"),
                        str(tmp), str(OUT), spec["parent"], "7014",
                        "Raw56E1RE", "96", "600"], env=env, check=True)
        print("RAW56_E1_RE_CANDIDATE_COMPLETE", len(rows), "FAR", len(far5)+len(extra),
              "SWEEP", len(pumps), "SPARSE", len(sparse), flush=True)

if __name__ == "__main__":
    run()
