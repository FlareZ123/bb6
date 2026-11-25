"""Raw120/E0=0LA automatic sibling closure attempt.

This is deterministic discovery plus original-source Lean proof generation.
Finite event traces propose one-block and multi-block sweep witnesses; the
emitted Lean module checks every proposed witness against SweepPumping and
ZipThreeHoleAudit. If any open leaf remains unmatched, the script records
the exact indices/tables and exits without emitting a claimed certificate.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT.parent / "agent31-three-hole-tnf"))
from generate_four_hole import masks, slot, move, parse
import generate_sweeps as one
sys.path.insert(0, str(ROOT.parent / "agent10-tnf-multipump"))
import multi

MOVES = ["".join(x) for x in product("01", "LR", "ABCDEF")]
PARENT = "1RB---_1RC---_0RD---_1LD1RE_0LA1LE_------"
EXPECTED_OPEN = 4710
EXPECTED_SHA = "0ee9b27fbb87a275e6b4626d91ec537aef9d72283e4deed09d1face988e1043c"
EVENT_LIMIT = 20000
CHUNK = 240
FOLDER = ROOT / "la"
FOLDER.mkdir(exist_ok=True)

subprocess.run(
    ["g++", "-std=c++17", "-O3",
     str(ROOT.parent / "agent2-tnf-raw99" / "enumerate.cpp"),
     "-o", "enumerate"],
    cwd=FOLDER, check=True)
subprocess.run([str(FOLDER / "enumerate"), PARENT], cwd=FOLDER, check=True)

open_bytes = (FOLDER / "open.txt").read_bytes()
open_sha = hashlib.sha256(open_bytes).hexdigest()
opens = open_bytes.decode().splitlines()
assert len(opens) == len(set(opens)), "duplicate raw open-leaf encoding"
if len(opens) != EXPECTED_OPEN or open_sha != EXPECTED_SHA:
    raise RuntimeError(
        f"previous incarnation recorded {EXPECTED_OPEN} open leaves; "
        f"reproduced {len(opens)} (SHA256 {open_sha})")

subprocess.run(
    ["g++", "-std=c++17", "-O3",
     str(ROOT.parent / "agent8-tnf-six" / "bank.cpp"), "-o", "bank"],
    cwd=FOLDER, check=True)

# Use the union of the two already source-used FAR banks. A duplicate hit is
# harmless; keep the first exact mask so regeneration is deterministic.
certs = {}
bank_counts = {}
for bank_name in (
    "bank.txt", "rb-bank.txt", "la-discovery-bank.txt",
    "../agent8-tnf-six/raw115/bank.txt",
    "../agent8-tnf-six/raw119/bank.txt",
    "../agent11-raw121/bank.txt",
    "../agent47-raw114-cut/all-far-bank.txt",
    "../agent8-tnf-raw117/bank112.txt",
    "../agent8-tnf-raw117/bank112extra.txt",
    "../agent8-tnf-raw117/bank117.txt",
):
    hits = subprocess.check_output(
        [str(FOLDER / "bank"), str(ROOT / bank_name),
         str(FOLDER / "open.txt")], text=True)
    rows = 0
    for row in hits.splitlines():
        i, mask = row.split(":")
        certs.setdefault(opens[int(i)], mask)
        rows += 1
    bank_counts[bank_name] = rows

pumpns = "BB6.Agent3Raw120LAPumps"
pump_code = [
    "import SweepPumping",
    "set_option maxRecDepth 100000",
    "set_option maxHeartbeats 0",
    "set_option linter.unusedVariables false",
    f"namespace {pumpns}",
    "open BB6Coverage BB6Coverage.Agent31Pump",
]
# The fixed-point checker reconstructs every manifest certificate.
# This also replaces the former custom carry proof for open leaf 855.
sys.path.insert(0, str(ROOT.parent / "agent16-raw118"))
from bidfa_emit import emit as emit_bidfa
bns = "BB6.Agent3Raw120LABiDFA"
bcode = ["import BiDFA", "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         f"namespace {bns}", "open BB6Coverage BB6Coverage.Agent16BiDFA"]
pumps = {}
for row in (ROOT / "0LA-bidfa.txt").read_text().splitlines():
    idx, dl, dr, count, edges = row.split()
    i = int(idx)
    table = opens[i]
    code, n, e = emit_bidfa(i, table, [int(x,36) for x in dl], [int(x,36) for x in dr])
    assert (n,e) == (int(count),int(edges))
    bcode.append(code)
    pumps[table] = (f"{bns}.M{i}.table", f"{bns}.M{i}.never")
assert len(pumps) == 97
bcode.append(f"end {bns}")
(FOLDER / "Raw120LABiDFA.lean").write_text("\n".join(bcode)+"\n")
bidfa_count = len(pumps)
assert opens[855] == "1RB1LB_1RC0LF_0RD0RA_1LD1RE_0LA1LE_---1LD"
late = {
    opens[2311]: (1019, 10),
    opens[2313]: (1001, 10),
    opens[3898]: (13295, 10),
    opens[3916]: (18853, 10),
}
assert opens[2311] == "1RB1RA_1RC0LD_0RD0RF_1LD1RE_0LA1LE_---1RC"
assert opens[2313] == "1RB1RA_1RC0RE_0RD0RF_1LD1RE_0LA1LE_---1RC"
assert opens[3898] == "1RB1LF_1RC1RF_0RD1RB_1LD1RE_0LA1LE_---0LA"
assert opens[3916] == "1RB1LF_1RC1RF_0RD1RB_1LD1RE_0LA1LE_---0RE"
from make_la_shuttle import emit as emit_shuttles, machines as shuttle_machines
emit_shuttles(opens,FOLDER)
for i,code,*_ in shuttle_machines:
    pumps[code] = (f"BB6.Agent3LAFinal.M{i}.table", f"BB6.Agent3LAFinal.M{i}.never")
missing = []
one_count = 0
multi_count = 0
one.SIMP = one.SIMP if "List.append_nil" in one.SIMP else one.SIMP + ",List.append_nil"
multi.SIMP = multi.SIMP if "List.append_nil" in multi.SIMP else multi.SIMP + ",List.append_nil"

def extended_one_candidate(p, ev):
    # Same opaque-word simulation as generate_sweeps.candidate, with a longer
    # event separation. The emitted proof is still checked by Lean.
    for i, (t, s, c) in enumerate(ev[:60]):
        for j in range(i+1, min(i+48, len(ev))):
            _, s2, d = ev[j]
            if s != s2 or c.q != d.q:
                continue
            delta = d.h0-c.h0
            if s == "L" and c.l.pre == d.l.pre == "":
                a, b, side = c.r.pre, d.r.pre, "R"
            elif s == "R" and c.r.pre == d.r.pre == "":
                a, b, side = c.l.pre, d.l.pre, "L"
            else:
                continue
            diff = len(b)-len(a)
            if not 1 <= diff <= 16:
                continue
            for k in range(len(a)+1):
                if b[:k] != a[:k] or b[k+diff:] != a[k:]:
                    continue
                block = b[k:k+diff]
                pred = a[:k]+block*2+a[k:]
                if not any(e[1] == s and e[2].q == c.q and e[2].h0 == c.h0+2*delta
                           and (e[2].r.pre if side == "R" else e[2].l.pre) == pred
                           for e in ev[j+1:j+48]):
                    continue
                w = one.W(a[:k], block, a[k:])
                v = one.W(a[:k]+block, block, a[k:])
                start = one.C(c.q, 0, 0, one.W() if side == "R" else w, w if side == "R" else one.W())
                target = one.C(c.q, delta, 0, one.W() if side == "R" else v, v if side == "R" else one.W())
                res = one.pump(p, start, target)
                if res:
                    return t, c, start, target, res
    return None

# Only unmatched leaves incur concrete event simulation. Finite traces propose
# witnesses; one.generate / multi.generate emit inductive Lean proofs.
for i, code in enumerate(opens):
    if code in certs or code in pumps or code in late:
        continue
    p = one.parse(code)
    # These two families need carefully aligned repeated cuts.
    if i in (3911,4214):
        if i == 3911:
            assert code == "1RB0LF_1RC1RF_0RD1RB_1LD1RE_0LA1LE_---0RC"
            st = multi.C(4,(),multi.clean(multi.lit("1")+multi.rep("1"*18)+multi.lit("111")))
            target = multi.C(4,(),multi.clean(multi.rep("1"*18)+multi.lit("1"*22)))
            entry = 9
        else:
            assert code == "1RB1LF_1RC1RB_0RD1RF_1LD1RE_0LA1LE_---0RB"
            st = multi.C(1,multi.clean(multi.lit("011")+multi.rep("1")+multi.lit("0111")+multi.rep("01")),())
            target = multi.C(1,multi.clean(multi.lit("0111")+multi.rep("1")+multi.lit("011101")+multi.rep("01")),())
            entry = 16
        proof = multi.pump(p,st,target,500)
        assert proof is not None, (i,code)
        generated, info = multi.generate(i,p,(entry,st,target,proof))
        pump_code.append(generated)
        pumps[code] = (f"{pumpns}.M{i}.table", f"{pumpns}.M{i}.never")
        multi_count += 1
        print("targeted-multi",i,info)
        continue
    events = one.concrete_events(p, EVENT_LIMIT)
    ans = extended_one_candidate(p, events)
    if ans is not None:
        generated, info = one.generate(i, p, ans)
        pump_code.append(generated)
        pumps[code] = (f"{pumpns}.M{i}.table", f"{pumpns}.M{i}.never")
        one_count += 1
        print("one-block", i, info)
        continue
    ans = multi.candidate(p, events)
    if ans is not None:
        generated, info = multi.generate(i, p, ans)
        pump_code.append(generated)
        pumps[code] = (f"{pumpns}.M{i}.table", f"{pumpns}.M{i}.never")
        multi_count += 1
        print("multi-block", i, info)
        continue
    found = False
    # Three known long grouped-boundary candidates avoid a slow blind scan.
    preferred = {1651: ("L", 0, 12), 1652: ("L", 0, 4), 1660: ("L", 0, 5)}
    if i in preferred:
        side, q, period = preferred[i]
        ans = multi.long_candidate(p, events, side, q, period)
        if ans is not None:
            generated, info = multi.generate(i, p, ans)
            pump_code.append(generated)
            pumps[code] = (f"{pumpns}.M{i}.table", f"{pumpns}.M{i}.never")
            multi_count += 1
            print("long-multi-block", i, side, q, period, info)
            continue
    for side in ("L", "R"):
        for q in range(6):
            for period in range(1, 13):
                ans = multi.long_candidate(p, events, side, q, period)
                if ans is None:
                    continue
                generated, info = multi.generate(i, p, ans)
                pump_code.append(generated)
                pumps[code] = (f"{pumpns}.M{i}.table", f"{pumpns}.M{i}.never")
                multi_count += 1
                print("long-multi-block", i, side, q, period, info)
                found = True
                break
            if found:
                break
        if found:
            break
    if not found:
        missing.append((i, code))

tree = json.loads((FOLDER / "tree.json").read_text())
stats = Counter()
max_last = 0
max_query = 0

def inspect(t):
    global max_last, max_query
    tag, *v = t
    stats[tag] += 1
    if tag in ("split", "last"):
        max_query = max(max_query, v[0])
    if tag == "split":
        for child in v[2]:
            inspect(child)
    elif tag == "last":
        max_last = max(max_last, v[0])

inspect(tree)
B = max(max_query, *(n for n, _ in late.values())) + 6  # weighted safe bound
summary = {
    "parent": PARENT,
    "expected_open_count": EXPECTED_OPEN,
    "open_count": len(opens),
    "open_sha256": open_sha,
    "tree_stats": dict(stats),
    "max_last_time": max_last,
    "candidate_weighted_bound": B,
    "bank_hits": bank_counts,
    "far_union": len(certs),
    "one_block_pumps": one_count,
    "multi_block_pumps": multi_count,
    "late_leaves": len(late),
    "bidfa_leaves": bidfa_count,
    "nested_shuttle_leaves": len(shuttle_machines),
    "unresolved": len(missing),
    "unresolved_sample": [{"index": i, "table": code} for i, code in missing[:100]],
}
(FOLDER / "probe_summary.json").write_text(
    json.dumps(summary, indent=2, sort_keys=True) + "\n")
(FOLDER / "unresolved.txt").write_text(
    "".join(f"{i}: {code}\n" for i, code in missing))
print(json.dumps(summary, indent=2, sort_keys=True))

if missing:
    raise SystemExit(
        f"{len(missing)} open leaves still lack FAR or symbolic growth witnesses")

pump_code.append(f"end {pumpns}")
(FOLDER / "Raw120LASweeps.lean").write_text(
    "\n\n".join(pump_code) + "\n")

used = set()
def size(t):
    return 1 + sum(size(kid) for kid in t[3]) if t[0] == "split" else 1

def render(t):
    tag, *v = t
    if tag == "cycle":
        e, k, right, boundary = v
        return f".cycle {e} {k} {str(right).lower()} ({boundary})"
    if tag == "last":
        n, s = v
        return f".last {n} {slot(s)}"
    if tag == "open":
        code = v[0]
        assert code not in used
        used.add(code)
        if code in late:
            n, s = late[code]
            return f".last {n} {slot(s)}"
        if code in pumps:
            return ".proven " + " ".join(pumps[code])
        mask = certs[code]
        d, D, L, R, z = masks(
            parse(code), int(mask[0]), [int(x, 36) for x in mask[1:]])
        return f'.far {str(mask[0] == "1").lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
    assert tag == "split"
    n, s, kids = v
    assert len(kids) == 24
    return ".split " + str(n) + " " + slot(s) + " (byMove [\n" + \
        ",\n".join(render(kid) for kid in kids) + "])"

def compose(parent, name, t):
    if size(t) <= CHUNK:
        return (
            f"def t_{name} : Audit := {render(t)}\n"
            f"theorem c_{name} : zipCheck {B} {parent} t_{name} = true := by decide\n")
    assert t[0] == "split"
    _, n, s, kids = t
    out, names = [], []
    for i, kid in enumerate(kids):
        child_name = f"{name}_{i:02}"
        names.append(child_name)
        out.append(
            f"abbrev p_{child_name} := refine {parent} {slot(s)} "
            f"(some {move(MOVES[i])})\n")
        out.append(compose(f"p_{child_name}", child_name, kid))
    out.append(combine(parent, name, n, s, names))
    return "".join(out)

def combine(parent, name, n, s, names):
    cases = "\n".join(
        f"  · exact c_{names[12*w+6*r+q]}"
        for q, w, r in product(range(6), range(2), range(2)))
    return f"""
def k_{name} : Move → Audit := byMove [{','.join('t_'+x for x in names)}]
def t_{name} : Audit := .split {n} {slot(s)} k_{name}
theorem q_{name} : zipQueryOK {B} {parent} {n} {slot(s)} = true := by decide
theorem kcheck_{name} (mv : Move) :
    zipCheck {B} (refine {parent} {slot(s)} (some mv)) (k_{name} mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
theorem c_{name} : zipCheck {B} {parent} t_{name} = true :=
  split_checked {parent} {n} {slot(s)} k_{name} q_{name} kcheck_{name}
"""

prefix = "Raw120LA"
ns = "BB6.Agent3Raw120LA"
header = f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent3Raw120
"""

def emit(name, imports, body):
    (FOLDER / (name + ".lean")).write_text(
        "".join("import " + imp + "\n" for imp in imports) +
        header + body + f"\nend {ns}\n")

base = f"""
abbrev pLA : PartialMachine := refine p120 (4,false) (some ⟨false,false,0⟩)
theorem pLA_root : pLA initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pLA_nohalt : weightedTNFNoAssignedHalt pLA :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt))
theorem split_checked (p : PartialMachine) (n : Nat) (s : Slot)
    (kids : Move → Audit)
    (hq : zipQueryOK {B} p n s = true)
    (hk : ∀ mv, zipCheck {B} (refine p s (some mv)) (kids mv) = true) :
    zipCheck {B} p (.split n s kids) = true := by
  change (zipQueryOK {B} p n s &&
    allMoves (fun mv => zipCheck {B} (refine p s (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨hq, allMoves_of _ hk⟩
"""
emit(prefix + "Base", ["Raw120Late", "Raw120LABiDFA", "Raw120LAShuttles", prefix + "Sweeps"], base)

assert tree[0] == "split"
root_n, root_slot, root_kids = tree[1], tree[2], tree[3]
modules, names = [], []
for i, kid in enumerate(root_kids):
    name = f"kid{i:02}"
    names.append(name)
    module = f"{prefix}Kid{i:02}"
    modules.append(module)
    emit(module, [prefix + "Base"],
         f"abbrev p_{name} := refine pLA ( {slot(root_slot)} ) "
         f"(some {move(MOVES[i])})\n" +
         compose(f"p_{name}", name, kid))

body = combine("pLA", "root", root_n, root_slot, names) + f"""
noncomputable def certificateLA : WeightedTNFCertificate {B} pLA 6 :=
  certifiedZip {B} pLA t_root pLA_root pLA_nohalt c_root
theorem allLA : ∀ m, compatible pLA m → WeightedBound {B} m :=
  certificateLA.sound
#print axioms c_root
#print axioms allLA
"""
assert used == set(opens), (len(used), len(opens))
emit(prefix + "Data", modules, body)
print(f"all {len(opens)} E0=0LA completions covered at weighted bound {B}")
