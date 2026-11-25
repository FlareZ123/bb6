"""Raw120/E0=0RC complete candidate sibling audit.

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
import rc_nested

MOVES = ["".join(x) for x in product("01", "LR", "ABCDEF")]
PARENT = "1RB---_1RC---_0RD---_1LD1RE_0RC1LE_------"
EXPECTED_OPEN = 2214
EXPECTED_SHA = "01f82938bb361d4335146c22191f1fec517d993c76d71488fbc804910629e78f"
EVENT_LIMIT = 20000
CHUNK = 240
FOLDER = ROOT / "rc"
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

pumpns = "BB6.Agent3Raw120RCPumps"
pump_code = [
    "import SweepPumping",
    "set_option maxRecDepth 100000",
    "set_option maxHeartbeats 0",
    "set_option linter.unusedVariables false",
    f"namespace {pumpns}",
    "open BB6Coverage BB6Coverage.Agent31Pump",
]
# Two parameterised proof families cover the four nontrivial unmatched leaves.
assert opens[1370] == "1RB0LE_1RC0RF_0RD1RA_1LD1RE_0RC1LE_---0LA"
assert opens[1380] == "1RB0LE_1RC1RF_0RD1RA_1LD1RE_0RC1LE_---1RC"
assert opens[1633] == "1RB---_1RC0LF_0RD1RB_1LD1RE_0RC1LE_0LA1LB"
assert opens[1639] == "1RB---_1RC0LF_0RD1RB_1LD1RE_0RC1LE_1LA1LB"
pumps = {
    opens[1370]: ("(BB6.Agent3Raw120RCCounter.table false)", "(BB6.Agent3Raw120RCCounter.never false)"),
    opens[1380]: ("(BB6.Agent3Raw120RCCounter.table true)", "(BB6.Agent3Raw120RCCounter.never true)"),
}
for i in (1633, 1639):
    pump_code.append(rc_nested.generate_nested(i, one.parse(opens[i])))
    pumps[opens[i]] = (f"{pumpns}.M{i}.table", f"{pumpns}.M{i}.never")
late = {}
missing = []
one_count = 0
multi_count = 0
one.SIMP = one.SIMP if "List.append_nil" in one.SIMP else one.SIMP + ",List.append_nil"
multi.SIMP = multi.SIMP if "List.append_nil" in multi.SIMP else multi.SIMP + ",List.append_nil"

# Only unmatched leaves incur concrete event simulation. Finite traces propose
# witnesses; one.generate / multi.generate emit inductive Lean proofs.
for i, code in enumerate(opens):
    if code in certs or code in pumps or code in late:
        continue
    p = one.parse(code)
    events = one.concrete_events(p, EVENT_LIMIT)
    ans = one.candidate(p, events)
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
assert stats == Counter(split=934, cycle=15226, last=4043, open=2214), stats
B = max_query + 6  # weighted safe bound
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
    "custom_counter_and_nested_leaves": 4,
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
(FOLDER / "Raw120RCSweeps.lean").write_text(
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

prefix = "Raw120RC"
ns = "BB6.Agent3Raw120RC"
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
abbrev pRC : PartialMachine := refine p120 (4,false) (some ⟨false,true,2⟩)
theorem pRC_root : pRC initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pRC_nohalt : weightedTNFNoAssignedHalt pRC :=
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
emit(prefix + "Base", ["Raw120Late", "Raw120RCCounter", prefix + "Sweeps"], base)

assert tree[0] == "split"
root_n, root_slot, root_kids = tree[1], tree[2], tree[3]
modules, names = [], []
for i, kid in enumerate(root_kids):
    name = f"kid{i:02}"
    names.append(name)
    module = f"{prefix}Kid{i:02}"
    modules.append(module)
    emit(module, [prefix + "Base"],
         f"abbrev p_{name} := refine pRC ( {slot(root_slot)} ) "
         f"(some {move(MOVES[i])})\n" +
         compose(f"p_{name}", name, kid))

body = combine("pRC", "root", root_n, root_slot, names) + f"""
noncomputable def certificateRC : WeightedTNFCertificate {B} pRC 6 :=
  certifiedZip {B} pRC t_root pRC_root pRC_nohalt c_root
theorem allRC : ∀ m, compatible pRC m → WeightedBound {B} m :=
  certificateRC.sound
#print axioms c_root
#print axioms allRC
"""
assert used == set(opens), (len(used), len(opens))
emit(prefix + "Data", modules, body)
print(f"all {len(opens)} E0=0RC open leaves assigned certificates at weighted bound {B}")
