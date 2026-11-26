"""Re-use four complete candidate trees. Sharpen Raw95/105 and construct
attaining total completions from their enumerated maximal first-hole branches.
All numerical claims, including witness compatibility, halting time, incoming
blank delay, and the all-completions upper bound, are checked by Lean.
"""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent.parent
DIRS = {
    95: "agent3-tnf-raw95", 99: "agent2-tnf-raw99",
    103: "agent3-tnf-raw103", 105: "agent3-tnf-raw105",
}
BOUNDS = {95: 379, 99: 196, 103: 116, 105: 182}

def find_delay(table, state, seen, depth):
    if depth == 0:
        return []
    for q in range(6):
        if q in seen:
            continue
        a = table[2*q]
        if a != "---" and not (a[0] == "0" and a[2] == chr(65+state)):
            continue
        suffix = find_delay(table, q, seen | {q}, depth-1)
        if suffix is not None:
            return [(q, state), *suffix]
    return None

def literal(a):
    if a in ("---", "HHH"):
        return "none"
    return f"some ⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩"

def sharp(raw):
    folder = ROOT / "im-results" / DIRS[raw]
    result = subprocess.run([sys.executable, str(folder/"generate.py")],
                            cwd=ROOT, capture_output=True, text=True)
    print(result.stdout, end="")
    print(result.stderr, end="", file=sys.stderr)
    result.check_returncode()
    if raw in (99, 103):
        return
    match = re.search(r"maxscore=(\d+) n=(\d+) delay=(\d+) table=([A-Z01_\-]+)", result.stdout)
    assert match, "candidate maximum missing"
    score, n, d = map(int, match.groups()[:3])
    assert score == BOUNDS[raw] == n+1+d, (raw, score,n,d)
    code = match.group(4).replace("_","")
    assert len(code)==36
    table = [code[i:i+3] for i in range(0,36,3)]
    path = find_delay(table, 0, {0}, d)
    assert path is not None
    for q, state in path:
        if table[2*q] == "---":
            table[2*q] = "0L" + chr(65+state)
    table = ["HHH" if a == "---" else a for a in table]
    print("Attainment candidate:", score, n, d, "_".join("".join(table[i:i+2]) for i in range(0,12,2)))
    # Replace only the bound arguments; do not alter any numeric proof data.
    for p in folder.glob(f"Raw{raw}*.lean"):
        t = p.read_text()
        t = re.sub(r"\b(check|queryOK|WeightedTNFCertificate|certified|WeightedBound) 395\b",
                   lambda m: m[1]+" "+str(score), t)
        p.write_text(t)
    branches = "\n".join(f"  | {i//2}, {str(bool(i%2)).lower()} => {literal(a)}" for i,a in enumerate(table))
    source = f"""import Raw{raw}Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31SharpRaw{raw}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent3Raw{raw}

def witness : Machine := fun (q,b) =>
  match q.val,b with
{branches}
  | _, _ => none

theorem witness_compatible : compatible p{raw} witness := by
  have ha (s : Slot) : p{raw} s = none ∨ p{raw} s = some (witness s) := by
    rcases s with ⟨q,b⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide
  intro s t hs
  rcases ha s with h | h
  · rw [h] at hs
    contradiction
  · exact Option.some.inj (h.symm.trans hs)

theorem witness_halts : HaltsAfter witness {n} := by
  unfold HaltsAfter
  decide

theorem witness_delay : {d} ∈ delays (zeroNext witness) 0 := by decide

theorem exact{raw} (B : Nat) :
    (∀ m, compatible p{raw} m → WeightedBound B m) ↔ {score} ≤ B := by
  constructor
  · intro h
    have hb := h witness witness_compatible {n} {d} witness_halts witness_delay
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all{raw} m hm k d hk hd) hb

#print axioms witness_compatible
#print axioms witness_halts
#print axioms witness_delay
#print axioms exact{raw}
end BB6.Agent31SharpRaw{raw}
"""
    (folder/f"SharpRaw{raw}.lean").write_text(source)

if __name__ == "__main__":
    assert len(sys.argv)==2 and int(sys.argv[1]) in DIRS
    sharp(int(sys.argv[1]))
