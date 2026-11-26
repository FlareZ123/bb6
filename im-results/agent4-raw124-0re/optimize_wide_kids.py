#!/usr/bin/env python3
"""Replace expensive wide FAR decisions with the accepted DirectFAR checker.

Input is the pinned source checkout after regenerate_subtree.py and the
unchanged subdivision directory. The final original weighted audit still
checks every refined transition table; no candidate is discarded.
"""
import base64
import hashlib
import json
import re
import shutil
import sys
import zlib
from pathlib import Path

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    if len(sys.argv) < 4:
        raise SystemExit("usage: optimize_wide_kids.py PINNED_ROOT REPAIR_DIR KID...")
    root, repair = map(lambda x: Path(x).resolve(), sys.argv[1:3])
    kids = sys.argv[3:]
    raw = root / "im-results/agent2-tnf-raw124"
    out = repair / "optimized"
    out.mkdir(exist_ok=True)
    split = json.loads((repair / "SPLIT_MANIFEST.json").read_text())
    assert split["branch"] == "0RE"
    sys.path.insert(0, str(raw))
    from generate_bundle import masks, parse, move
    bundle_path = raw / "complete-bundle-0RE-1LF-1LE.json.zlib.b64"
    assert digest(bundle_path) == split["input_sha256"][bundle_path.name]
    bundle = next(b for b in json.loads(zlib.decompress(base64.b64decode(bundle_path.read_text()))) if b["branch"] == "0RE")
    open_path = raw / "open.txt"
    assert digest(open_path) == bundle["hash"] == split["input_sha256"]["open.txt"]
    opens = open_path.read_text().splitlines()
    assert len(opens) == len(bundle["far"])
    entries = {}
    for i, j in enumerate(bundle["far"]):
        if j < 0:
            continue
        rev, dfa = bundle["pool"][j]
        if len(dfa) // 2 < 16:
            continue
        assert not rev, "This pinned 0RE wide set is unreflected."
        d, dd, m0, m1, z = masks(parse(opens[i]), rev, dfa)
        literal = f".far false {d} ⟨0,{dd},{m0},{m1},{z}⟩"
        assert literal not in entries
        entries[literal] = (i, d, dd, m0, m1, z)
    deps = ("WeakFAR", "SparseFAR", "DirectFAR")
    for name in deps:
        shutil.copy2(root / "im-results/agent3-tnf-raw120" / (name + ".lean"), out / (name + ".lean"))
    manifest = {}
    for kid in kids:
        name = "Raw124B0REKid" + kid
        source = repair / (name + ".lean")
        assert digest(source) == split["kids"][kid]["subdivided"]["sha256"]
        text = source.read_text()
        used = []
        for literal, (i, d, dd, m0, m1, z) in entries.items():
            if literal not in text:
                continue
            assert text.count(literal) == 1
            mod = f"Raw124B0REDirect{i}"
            table = "[" + ",".join("none" if a == "---" else "some (some " + move(a) + ")" for a in parse(opens[i])) + "]"
            def indices(m):
                return [k for k in range(m.bit_length()) if (m >> k) & 1]
            ss0, ss1 = [[indices(m) for m in ms] for ms in (m0, m1)]
            proof = f"""import Raw124B0REBase
import DirectFAR
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
namespace BB6.Agent2Raw124B0RE
open BB6Coverage BB6Coverage.FAR
def directTable{i} : PartialMachine := fromRows {table}
def directData{i} : FAR.Data {d} := ⟨0,{dd},{m0},{m1},{z}⟩
def directRows{i} : FAR.Sparse.Rows := ⟨{ss0},{ss1}⟩
theorem directCheck{i} : FAR.Direct.check directData{i} directRows{i} directTable{i} = true := by decide
theorem directNever{i} : ∀ m, compatible directTable{i} m → NeverHalts m :=
  FAR.Direct.sound directData{i} directRows{i} directTable{i} directCheck{i}
#print axioms directNever{i}
end BB6.Agent2Raw124B0RE
"""
            (out / (mod + ".lean")).write_text(proof)
            text = text.replace(literal, f".proven directTable{i} directNever{i}")
            used.append((i, mod))
        assert not re.search(r"\.far (?:true|false) (?:[2-9][0-9]|1[6-9]|[0-9]{3,}) ", text)
        # Separate the 24 immediate subtrees, preserving all declarations and
        # the root theorem. Add imports only where an external proof is used.
        start = text.index(f"abbrev p{kid} :")
        header = text[:start].split("\n", 1)[1]
        footer = "\nend BB6.Agent2Raw124B0RE\n"
        assert text.endswith(footer)
        positions = [m.start() for m in re.finditer(rf"(?m)^abbrev \w+ : PartialMachine := refine p{kid} ", text)]
        assert len(positions) == 24
        end = text.index(f"def kids{kid} :")
        chunks = [text[a:b] for a,b in zip(positions, positions[1:] + [end])]
        head = name + "Head"
        modules = []
        def emit(mod, imports, body):
            (out / (mod + ".lean")).write_text("".join(f"import {x}\n" for x in imports) + header + body + footer)
            modules.append(mod)
        emit(head, ["Raw124B0REBase"], text[start:positions[0]])
        part_names = []
        for n, chunk in enumerate(chunks):
            mod = f"{name}Part{n:02}"
            imports = [head] + [m for i,m in used if f"directNever{i}" in chunk]
            emit(mod, imports, chunk)
            part_names.append(mod)
        emit(name, part_names, text[end:-len(footer)])
        order = [*deps, *(m for _,m in used), *modules]
        assert all(statement in (out / (name + ".lean")).read_text() for statement in split["kids"][kid]["root_statements"].values())
        (out / (kid + ".order")).write_text("\n".join(order) + "\n")
        manifest[kid] = {"wide_leaf_ids": [i for i,_ in used], "modules": order,
                         "source_sha256": {m: digest(out / (m + ".lean")) for m in order}}
    (out / "OPTIMIZED_MANIFEST.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: v["wide_leaf_ids"] for k,v in manifest.items()}))

if __name__ == "__main__":
    main()
