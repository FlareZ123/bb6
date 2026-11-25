#!/usr/bin/env python3
"""Reconstruct and emit the source-auditable weighted parent proof for raw121.

The C++ producer and 84-code bank are deterministic witness producers only.
Every emitted cycle, last-hole, FAR, and symbolic leaf is checked by Lean.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
BUILD = ROOT / "_raw121_build"
THREE = ROOT.parent / "agent31-three-hole-tnf"
MULTI = ROOT.parent / "agent10-tnf-multipump"
PARENT = "1RB---_1RC---_0RD---_1LD1RE_---1RE_------"
OPEN_SHA = "30a72b502df5ea47f06886d114fb9ab8af7f918bfd3a1066a73b16634e3e07c9"
EXPECTED_STATS = {"cycle": 150577, "last": 39663, "open": 14277, "split": 8892}
BOUND = 4063

def read_specs():
    return json.loads((ROOT / "specs.json").read_text())

def run(cmd, **kwargs):
    print("+", " ".join(map(str, cmd)), flush=True)
    return subprocess.run(list(map(str, cmd)), check=True, **kwargs)

def count_tree(node, out):
    tag = node[0]
    out[tag] += 1
    if tag == "split":
        assert len(node[3]) == 24
        for child in node[3]:
            count_tree(child, out)

def expected_special(spec):
    return (
        set(map(int, spec["one"])) |
        set(map(int, spec["multi"])) |
        set(map(int, spec["quad"])) |
        set(map(int, spec["counter"])) |
        set(map(int, spec["long"])) |
        set(map(int, spec["quadExtra"])) |
        set(map(int, spec["binaryA"])) |
        set(map(int, spec["unresolved"])) |
        set(map(int, spec["late"]))
    )

def enumerate_parent():
    spec = read_specs()
    BUILD.mkdir(exist_ok=True)
    enum = BUILD / "fast_enum"
    bank = BUILD / "bank"
    run(["g++", "-std=c++17", "-O3", ROOT / "fast_enum.cpp", "-o", enum])
    res = run([enum, PARENT], cwd=BUILD, text=True, capture_output=True)
    print(res.stdout, flush=True)
    tree_path = BUILD / "tree.json"
    open_path = BUILD / "open.txt"
    tree = json.loads(tree_path.read_text())
    opens = open_path.read_text().splitlines()
    assert hashlib.sha256(open_path.read_bytes()).hexdigest() == OPEN_SHA
    assert len(opens) == len(set(opens)) == EXPECTED_STATS["open"]
    assert tree[:3] == ["split", 8, 8]
    counts = Counter()
    count_tree(tree, counts)
    assert dict(counts) == EXPECTED_STATS, (counts, EXPECTED_STATS)
    late_times = [int(value[0]) for value in spec["late"].values()]
    assert max(late_times) + 1 == BOUND, late_times

    run(["g++", "-std=c++20", "-O3", ROOT / "bank.cpp", "-o", bank])
    indexed = "".join(f"{i} {table}\n" for i, table in enumerate(opens))
    bank_result = run([bank, ROOT / "bank.txt"], cwd=BUILD, input=indexed,
                      text=True, capture_output=True)
    dfa = {}
    unmatched = {}
    for line in bank_result.stdout.splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0].isdigit():
            dfa[int(fields[0])] = fields[1]
    for line in bank_result.stderr.splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0].isdigit():
            unmatched[int(fields[0])] = fields[1]

    special = expected_special(spec)
    assert len(special) == 121, len(special)
    assert set(unmatched) == special, (len(unmatched), sorted(set(unmatched) ^ special)[:20])
    assert set(dfa) == set(range(len(opens))) - special
    assert len(dfa) == 14156 and len(set(dfa.values())) <= 84

    # The explicit symbolic tables are pinned to their open-list indices.
    for category in ("quad", "counter", "long", "quadExtra", "binaryA", "unresolved"):
        for i, table in spec[category].items():
            assert opens[int(i)].replace("_", "") == table.replace("_", ""), (category, i)
    for i, (_n, table) in spec["late"].items():
        assert opens[int(i)].replace("_", "") == table.replace("_", ""), ("late", i)

    (BUILD / "dfa_map.json").write_text(json.dumps({str(k): v for k, v in sorted(dfa.items())}, indent=2) + "\n")
    manifest = {
        "parent": PARENT,
        "first_query": {"ordinary_time": 8, "slot": "E0"},
        "weighted_bound": BOUND,
        "max_late_first_hole_time": max(late_times),
        "open_sha256": OPEN_SHA,
        "tree_sha256": hashlib.sha256(tree_path.read_bytes()).hexdigest(),
        "dfa_map_sha256": hashlib.sha256((BUILD / "dfa_map.json").read_bytes()).hexdigest(),
        "stats": EXPECTED_STATS,
        "open_leaves": len(opens),
        "far_leaves": len(dfa),
        "far_codes_used": len(set(dfa.values())),
        "symbolic_or_delayed_leaves": len(special),
        "enumerator_stdout": res.stdout.strip(),
    }
    (ROOT / "parent-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("raw121 enumeration and fixed-bank assignment accepted:", manifest, flush=True)

def setup_paths():
    sys.path.insert(0, str(THREE))
    sys.path.insert(0, str(MULTI))

def generate_pumps():
    setup_paths()
    import generate_sweeps as one
    import multi
    spec = read_specs()
    opens = (BUILD / "open.txt").read_text().splitlines()
    long_specs = json.loads((ROOT / "long.json").read_text())
    pieces = [
        "import SweepPumping",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "set_option linter.unusedVariables false",
        "namespace BB6.Agent11Raw121Pumps",
        "open BB6Coverage BB6Coverage.Agent31Pump",
    ]
    modules = {}

    for i in spec["one"]:
        p = one.parse(opens[i])
        ans = one.candidate(p, one.concrete_events(p, 6000))
        assert ans is not None, ("one-block", i, opens[i])
        code, info = one.generate(i, p, ans)
        pieces.append(code)
        modules[str(i)] = f"BB6.Agent11Raw121Pumps.M{i}"
        print("one-block", i, info, flush=True)

    for i in spec["multi"]:
        p = one.parse(opens[i])
        ans = multi.candidate(p, one.concrete_events(p, 6000))
        assert ans is not None, ("two-block", i, opens[i])
        code, info = multi.generate(i, p, ans)
        pieces.append(code)
        modules[str(i)] = f"BB6.Agent11Raw121Pumps.M{i}"
        print("two-block", i, info, flush=True)

    def parts(xs):
        return multi.clean(tuple((str(word), bool(repeated)) for word, repeated in xs))

    for i, entry, q, left0, right0, left1, right1 in long_specs:
        p = one.parse(opens[i])
        start = multi.C(int(q), parts(left0), parts(right0))
        target = multi.C(int(q), parts(left1), parts(right1))
        ans = multi.pump(p, start, target, 3000)
        assert ans is not None, ("long-explicit", i, opens[i])
        code, info = multi.generate(i, p, (int(entry), start, target, ans))
        pieces.append(code)
        modules[str(i)] = f"BB6.Agent11Raw121Pumps.M{i}"
        print("long-explicit", i, info, flush=True)

    pieces.append("end BB6.Agent11Raw121Pumps")
    (ROOT / "Raw121Pumps.lean").write_text("\n\n".join(pieces) + "\n")
    (BUILD / "pumps.json").write_text(json.dumps(modules, indent=2) + "\n")
    assert set(map(int, modules)) == set(spec["one"]) | set(spec["multi"]) | set(map(int, spec["long"]))
    print("generated arbitrary-tail pump proofs:", len(modules), flush=True)

def generate_quadratic():
    setup_paths()
    import generate_sweeps as one
    import quad
    import quad_codegen as codegen
    spec = read_specs()
    modules = []
    for i, table in spec["quad"].items():
        modules.append(codegen.generate(int(i), one.parse(table)))
        print("quadratic", i, flush=True)
    out = codegen.header + "\n\n" + "\n\n".join(modules) + "\nend BB6.Agent11Raw121Quadratic\n"
    (ROOT / "Raw121Quadratic.lean").write_text(out)

def generate_counter():
    setup_paths()
    import generate_sweeps as one
    import counter
    import counter_codegen as codegen
    spec = read_specs()
    modules = []
    for i, table in spec["counter"].items():
        modules.append(codegen.generate(int(i), one.parse(table)))
        print("counter", i, flush=True)
    out = codegen.header + "\n\n" + "\n\n".join(modules) + "\nend BB6.Agent11Raw121Counter\n"
    (ROOT / "Raw121Counter.lean").write_text(out)

def generate_quadratic_extra():
    setup_paths()
    import generate_sweeps as one
    import quad
    import quad_extra_codegen as codegen
    spec = read_specs()
    modules = []
    for i, table in spec["quadExtra"].items():
        modules.append(codegen.generate(int(i), one.parse(table)))
        print("quadratic-extra", i, flush=True)
    out = codegen.header + "\n\n" + "\n\n".join(modules) + "\nend BB6.Agent11Raw121QuadraticExtra\n"
    (ROOT / "Raw121QuadraticExtra.lean").write_text(out)

def generate_tree():
    setup_paths()
    import generate_sweeps as one
    from generate_four_hole import masks, slot, move
    spec = read_specs()
    tree = json.loads((BUILD / "tree.json").read_text())
    opens = (BUILD / "open.txt").read_text().splitlines()
    index = {table: i for i, table in enumerate(opens)}
    dfa = {int(k): v for k, v in json.loads((BUILD / "dfa_map.json").read_text()).items()}
    pumps = {int(k): v for k, v in json.loads((BUILD / "pumps.json").read_text()).items()}
    proofs = {}

    for i, module in pumps.items():
        proofs[i] = (f"{module}.table", f"(fun m hm => {module}.never m hm)")
    for i in map(int, spec["quad"]):
        module = f"BB6.Agent11Raw121Quadratic.M{i}"
        proofs[i] = (f"{module}.table", f"(fun m hm => {module}.never m hm)")
    for i in map(int, spec["counter"]):
        module = f"BB6.Agent11Raw121Counter.M{i}"
        proofs[i] = (f"{module}.table", f"(fun m hm => {module}.never m hm)")
    for i in map(int, spec["quadExtra"]):
        module = f"BB6.Agent11Raw121QuadraticExtra.M{i}"
        proofs[i] = (f"{module}.table", f"(fun m hm => {module}.never m hm)")

    binary_variants = {888: "plain", 10492: "pair", 10491: "triple", 13655: "extra"}
    for i, v in binary_variants.items():
        proofs[i] = (
            f"BB6.Agent11Raw121BinaryA.table .{v}",
            f"(fun m hm => BB6.Agent11Raw121BinaryA.never .{v} m hm)",
        )
    unresolved = {
        4749: (
            "BB6.Agent11Raw121BinarySweep.table .a",
            "(fun m hm => BB6.Agent11Raw121Exceptions.binary_never .a m hm)",
        ),
        10484: (
            "BB6.Agent11Raw121BinarySweep.table .f",
            "(fun m hm => BB6.Agent11Raw121Exceptions.binary_never .f m hm)",
        ),
        7080: (
            "BB6.Agent11Raw121TripleSweep.table",
            "(fun m hm => BB6.Agent11Raw121Exceptions.triple_never m hm)",
        ),
        11644: (
            "BB6.Agent11Raw121TripleCounter.table",
            "(fun m hm => BB6.Agent11Raw121Exceptions.counter_never m hm)",
        ),
    }
    proofs.update(unresolved)

    late = {}
    for i, (n, table) in spec["late"].items():
        parsed = one.parse(table)
        assert parsed.count("---") == 1
        late[int(i)] = (int(n), parsed.index("---"))

    special = expected_special(spec)
    assert set(proofs) | set(late) == special
    assert set(proofs).isdisjoint(late)
    assert set(dfa) == set(range(len(opens))) - special
    assert len(proofs) == 119 and len(late) == 2 and len(dfa) == 14156

    def build(node):
        tag, *values = node
        if tag == "cycle":
            e, k, right, boundary = values
            return f".cycle {e} {k} {str(bool(right)).lower()} ({boundary})"
        if tag == "last":
            n, s = values
            return f".last {n} {slot(s)}"
        if tag == "open":
            code = values[0]
            i = index[code]
            if i in proofs:
                p, safe = proofs[i]
                return f".proven ({p}) {safe}"
            if i in late:
                n, s = late[i]
                return f".last {n} {slot(s)}"
            a = dfa[i]
            rev = int(a[0])
            d, D, L, R, z = masks(one.parse(code), rev, [int(ch, 36) for ch in a[1:]])
            return f".far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩"
        assert tag == "split"
        n, s, kids = values
        assert len(kids) == 24
        return f".split {n} {slot(s)} (byMove [\n" + ",\n".join(build(k) for k in kids) + "])"

    counts = Counter()
    count_tree(tree, counts)
    assert dict(counts) == EXPECTED_STATS, (counts, EXPECTED_STATS)
    base_imports = [
        "ZipThreeHoleAudit",
        "Raw121Pumps",
        "Raw121Quadratic",
        "Raw121Counter",
        "Raw121QuadraticExtra",
        "Raw121BinaryA",
        "Raw121Exceptions",
    ]
    base_header = (
        "".join(f"import {name}\n" for name in base_imports) +
        "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" +
        "namespace BB6.Agent11Raw121\n" +
        "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath\n" +
        "open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit\n"
    )
    base_body = f"""
abbrev p121 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4, true) (some ⟨true, true, 4⟩)

theorem p121_root : p121 initialSlot = some (some ⟨true, true, 1⟩) := by decide

theorem p121_nohalt : weightedTNFNoAssignedHalt p121 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)

abbrev child121 (mv : Move) := refine p121 (4, false) (some mv)

theorem query121 : zipQueryOK {BOUND} p121 8 (4, false) = true := by decide
"""
    (ROOT / "Raw121Base.lean").write_text(base_header + base_body + "\nend BB6.Agent11Raw121\n")

    common = (
        "set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n" +
        "namespace BB6.Agent11Raw121\n" +
        "open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath\n" +
        "open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit\n"
    )
    moves = [w + d + q for w, d, q in product("01", "LR", "ABCDEF")]
    child_names = []
    for i, kid in enumerate(tree[3]):
        name = f"Raw121Kid{i:02}"
        child_names.append(name)
        body = (
            f"def kid{i:02} : Audit := {build(kid)}\n\n" +
            f"theorem check{i:02} : zipCheck {BOUND} (child121 {move(moves[i])}) kid{i:02} = true := by decide\n"
        )
        (ROOT / f"{name}.lean").write_text("import Raw121Base\n" + common + body + "\nend BB6.Agent11Raw121\n")

    cases = "\n".join(
        f"  · exact check{12*w + 6*r + q:02}"
        for q, w, r in product(range(6), range(2), range(2))
    )
    data_imports = "import Raw121Base\n" + "".join(f"import {name}\n" for name in child_names)
    data_body = f"""
def kids121 : Move → Audit := byMove [{",".join(f"kid{i:02}" for i in range(24))}]

theorem kids121_checked (mv : Move) :
    zipCheck {BOUND} (child121 mv) (kids121 mv) = true := by
  rcases mv with ⟨w, r, q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}

def tree121 : Audit := .split 8 (4, false) kids121

theorem tree121_checked : zipCheck {BOUND} p121 tree121 = true := by
  change (zipQueryOK {BOUND} p121 8 (4, false) &&
    allMoves (fun mv => zipCheck {BOUND} (child121 mv) (kids121 mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query121, allMoves_of _ kids121_checked⟩

noncomputable def certificate121 : WeightedTNFCertificate {BOUND} p121 6 :=
  certifiedZip {BOUND} p121 tree121 p121_root p121_nohalt tree121_checked

theorem all121 : ∀ m, compatible p121 m → WeightedBound {BOUND} m :=
  certificate121.sound

#print axioms tree121_checked
#print axioms all121
"""
    (ROOT / "Raw121Data.lean").write_text(data_imports + common + data_body + "\nend BB6.Agent11Raw121\n")

    manifest_path = ROOT / "parent-manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest.update({
        "proof_leaf_counts": {
            "arbitrary_tail_sweeps": 71,
            "two_block_sweeps": 12,
            "quadratic": 14,
            "recursive_counters": 6,
            "quadratic_extra": 4,
            "binary_fill": 4,
            "long_affine": 4,
            "delayed_last_holes": 2,
            "exceptional_returns": 4,
            "far": 14156,
        },
        "lean_parent_module": "Raw121Data",
        "child_modules": child_names,
    })
    manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    print("generated raw121 audit tree with", len(child_names), "top-level children", flush=True)

def all_modes():
    enumerate_parent()
    for mode in ("pumps", "quad", "counter", "quad-extra", "tree"):
        run([sys.executable, Path(__file__), mode])
    run([sys.executable, MULTI / "chunk_checks.py", ROOT, "Raw121", "--limit", "180"])
    print("raw121 Lean audit source generation complete", flush=True)

if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "all"
    if mode == "all":
        all_modes()
    elif mode == "enumerate":
        enumerate_parent()
    elif mode == "pumps":
        generate_pumps()
    elif mode == "quad":
        generate_quadratic()
    elif mode == "counter":
        generate_counter()
    elif mode == "quad-extra":
        generate_quadratic_extra()
    elif mode == "tree":
        generate_tree()
    else:
        raise SystemExit(f"unknown mode: {mode}")
