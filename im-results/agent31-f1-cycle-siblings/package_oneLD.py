#!/usr/bin/env python3
"""Package discovered F/1=1LD pump witnesses as Lean source."""

from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
GEN = ROOT / "im-results" / "agent48-raw139-f1-oneLA"
sys.path.insert(0, str(GEN))
from emitproof import emit

D = json.loads(Path("f1-14-600.json").read_text())
if D["unresolved"]:
    print("No complete proof package; unresolved open leaves:", D["unresolved"])
    raise SystemExit(0)

idx = {tuple(p): i for i, p in enumerate(D["open"])}

def b(x):
    return str(bool(x)).lower()

def node(t):
    k, *v = t
    if k == "cycle":
        a, n, direction, z = v
        return f".cycle {a} {n} {b(direction)} ({z})"
    if k == "last":
        n, s = v
        return f".last {n} ({s // 2},{b(s % 2)})"
    if k == "split":
        n, s, children = v
        return f".split {n} ({s // 2},{b(s % 2)}) (byMove [\n" + ",\n".join(map(node, children)) + "])"
    if k == "open":
        i = idx[tuple(v[0])]
        if not Path(f"pump-{i}.json").exists():
            raise RuntimeError(f"missing pump witness for open leaf {i}")
        return f".proven BB6.Agent31OneLD.H{i}.ctr BB6.Agent31OneLD.H{i}.never"
    if k == "far":
        direction, width, dfa, t0, t1, z = v
        return f".far {b(direction)} {width} ⟨0,{dfa},{t0},{t1},{z}⟩"
    raise ValueError(t)

head = """import SweepPumping
import F0SiblingCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent31OneLD
open BB6Coverage BB6Coverage.Agent31Pump
"""
parts = []
for path in sorted(Path(".").glob("pump-*.json")):
    s = emit(path)
    i = path.stem.split("-")[1]
    m = re.search(r"theorem growth \(n : Nat\) : run0 ctr \((\d+)\*n\+(\d+)\)", s)
    if not m:
        raise RuntimeError(f"could not read growth cost in {path}")
    a, b0 = map(int, m.groups())
    t = json.loads(path.read_text())["result"][0]
    suffix = (
        f"theorem never (m : Machine) (hm : compatible ctr m) : NeverHalts m :=\n"
        f"  never_of_growth ctr family {t} (fun n => {a}*n+{b0}) entry "
        f"(fun k => by omega) growth m hm\n"
        f"#print axioms growth\n#print axioms never\nend H{i}"
    )
    s = s.replace(f"#print axioms growth\nend H{i}", suffix)
    parts.append(s)
Path("ChampionF1OneLDHard.lean").write_text(head + "\n\n".join(parts) + "\nend BB6.Agent31OneLD\n")

parent = D["parent"]
bound = max(290, int(D["counts"].get("maxquery", 0)) + 1)
tree = node(D["tree"])
cover = f"""import FastThreeHoleAudit
import ChampionF1OneLDHard
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent31OneLD
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit

def parent : PartialMachine := fromCodes {parent}
def tree : Audit := {tree}
theorem checked : fastCheck {bound} parent tree = true := by decide
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({parent} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {bound} parent 6 :=
  certifiedFast {bound} parent tree root nohalt checked
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {bound} m := certificate.sound
#print axioms checked
#print axioms all_completions_weighted
end BB6.Agent31OneLD
"""
Path("ChampionF1OneLDCover.lean").write_text(cover)
print(f"packaged {len(parts)} growth lemmas; counts={D['counts']}")
