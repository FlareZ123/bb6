"""Generate Lean-checked low-region visit ranks for the existing E3 certificate.

Generator and rank numbers are untrusted. Lean checks every edge inequality
of all 6,399 original abstract seam states and all 128 root rank bounds.
"""
from __future__ import annotations
from collections import defaultdict, deque
from pathlib import Path
import os
import tempfile
import sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent / "agent31-d-exceptional" / "ESeamClosedStates.txt"
BLOCK_SIZE = 32

# Literal D machine transitions (write, direction, next state).
TABLE = (
    ((1, 1, 1), (0, 1, 4)),
    ((1, -1, 2), (0, 1, 0)),
    ((1, -1, 0), (1, -1, 3)),
    ((1, -1, 2), (1, -1, 5)),
    ((0, -1, 2), (0, -1, 1)),
    ((1, -1, 4), (0, 0, 6)),
)

def successors(v: int) -> list[int]:
    state, off, bits = v % 8, (v // 8) % 32, v // 256
    bit = (bits >> off) & 1
    if off == 1 or (state == 5 and bit):
        return []
    if state == 5 and not bit and bits & ((1 << off) - 1) == 0:
        return []
    write, direction, next_state = TABLE[state][bit]
    next_bits = bits | (1 << off) if write else bits & ~(1 << off)
    next_off = off + direction
    if next_off == 18:
        return [256 * next_bits + 8 * 17 + s for s in range(6)]
    return [256 * next_bits + 8 * next_off + next_state]

def weight(v: int) -> int:
    return int((v // 8) % 32 <= 13)

def rank_states(states: list[int]) -> dict[int, int]:
    keys = set(states)
    pred: dict[int, list[int]] = defaultdict(list)
    succ: dict[int, list[int]] = {}
    for v in states:
        ns = successors(v)
        if not set(ns) <= keys:
            raise ValueError("Certificate is not successor-closed")
        succ[v] = ns
        for w in ns:
            pred[w].append(v)
    ranks = {v: weight(v) for v in states}
    queue = deque(v for v in states if ranks[v] > 0)
    enqueued = set(queue)
    while queue:
        v = queue.popleft()
        enqueued.discard(v)
        for p in pred[v]:
            candidate = weight(p) + max((ranks[w] for w in succ[p]), default=0)
            if candidate > ranks[p]:
                ranks[p] = candidate
                if ranks[p] > len(states):
                    raise ValueError("Positive-weight graph cycle")
                if p not in enqueued:
                    enqueued.add(p)
                    queue.append(p)
    if any(weight(v) + ranks[w] > ranks[v]
           for v in states for w in succ[v]):
        raise AssertionError("Unmet edge inequality")
    seeds = [256 * (171 + 2048*r) + 8*10 + 4 for r in range(128)]
    peak = max(ranks[v] for v in seeds)
    if len(states) != 6399 or sum(map(len, succ.values())) != 7306 or peak != 82:
        raise ValueError("Unexpected abstract graph or rank bound")
    print(f"states={len(states)} edges={sum(map(len,succ.values()))} seed_peak={peak}")
    return ranks

def tree(ns: list[int], rank: dict[int, int]) -> str:
    if len(ns) == 1:
        return f"(RankTree.leaf {ns[0]} {rank[ns[0]]})"
    mid = len(ns) // 2
    return (f"(RankTree.branch {ns[mid]} "
            f"{tree(ns[:mid], rank)} {tree(ns[mid:], rank)})")

def block_tree(blocks: list[list[int]], ids: list[int]) -> str:
    if len(ids) == 1:
        return f"rankBlock{ids[0]}"
    mid = len(ids) // 2
    return (f"(RankTree.branch {blocks[ids[mid]][0]} "
            f"{block_tree(blocks, ids[:mid])} {block_tree(blocks, ids[mid:])})")

def write_atomic(path: Path, data: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
        dir=path.parent, prefix=path.name+".", suffix=".tmp", delete=False) as out:
        out.write(data)
        out.flush()
        os.fsync(out.fileno())
        name = out.name
    os.replace(name, path)

BASE = r'''import ESeamTreeBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.ESeamRank
open BB6.TreeCert

inductive RankTree where
  | leaf : Nat → Nat → RankTree
  | branch : Nat → RankTree → RankTree → RankTree

def lookup : RankTree → Nat → Nat
  | .leaf k n, v => if k == v then n else 0
  | .branch pivot lo hi, v =>
      if v < pivot then lookup lo v else lookup hi v

__BLOCKS__

def rankRoot : RankTree := __ROOT__
def score (v : Nat) : Nat := lookup rankRoot v
def leftWeight (v : Nat) : Nat := if (v / 8) % 32 <= 13 then 1 else 0

def rankGood (v : Nat) : Bool :=
  (successors v).all (fun w => decide (leftWeight v + score w ≤ score v))

def allRankGood : Tree → Bool
  | .leaf v => rankGood v
  | .branch _ lo hi => allRankGood lo && allRankGood hi

theorem rank_member_of_all {t : Tree} (h : allRankGood t = true)
    {v : Nat} (hv : member t v = true) : rankGood v = true := by
  induction t with
  | leaf k =>
      simp only [allRankGood] at h
      simp only [member, beq_iff_eq] at hv
      cases hv
      exact h
  | branch pivot lo hi ihLo ihHi =>
      have hp : allRankGood lo = true ∧ allRankGood hi = true := by
        simpa only [allRankGood, Bool.and_eq_true] using h
      simp only [member] at hv
      split at hv
      · exact ihLo hp.1 hv
      · exact ihHi hp.2 hv

end BB6.ESeamRank
'''

MASTER = r'''import ESeamTreeMaster
__IMPORTS__
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.ESeamRank
open BB6.TreeCert

theorem all_rank_good : allRankGood root = true := by
  simp only [root, allRankGood]
  simp only [
__LEMMAS__
  ]
  decide

theorem rank_edge (v w : Nat) (hv : member root v = true)
    (hw : w ∈ successors v) :
    leftWeight v + score w ≤ score v := by
  have h : rankGood v = true := rank_member_of_all all_rank_good hv
  have hdec : decide (leftWeight v + score w ≤ score v) = true :=
    (List.all_eq_true.mp h) w hw
  exact of_decide_eq_true hdec

inductive CountPath (start : Nat) : Nat → Nat → Prop where
  | zero : CountPath start start 0
  | next {u v c : Nat} : CountPath start u c →
      v ∈ successors u → CountPath start v (c+leftWeight u)

theorem count_path_member {start u c : Nat} (hseed : member root start = true)
    (p : CountPath start u c) : member root u = true := by
  induction p with
  | zero => exact hseed
  | next hp he ih => exact successor_closed _ _ ih he

theorem count_path_bound {start u c : Nat} (hseed : member root start = true)
    (p : CountPath start u c) : c + score u ≤ score start := by
  induction p with
  | zero => omega
  | @next x y n hp he ih =>
      have hm : member root x = true := count_path_member hseed hp
      have hr := rank_edge x y hm he
      omega

private def allSeedBounds : Bool :=
  (List.range 128).all (fun r =>
    decide (score (encode 10 4 (171+2048*r)) ≤ 82))

theorem all_seed_bounds : allSeedBounds = true := by decide

theorem seed_score (r : Nat) (hr : r < 128) :
    score (encode 10 4 (171+2048*r)) ≤ 82 := by
  have h := (List.all_eq_true.mp all_seed_bounds) r (List.mem_range.mpr hr)
  exact of_decide_eq_true h

/-- Every finite E3 abstract path visits positions at most +3 at most
82 times, for any right suffix allowed by the closed overapproximation. -/
theorem all_e3_low_visits (r u c : Nat) (hr : r < 128)
    (p : CountPath (encode 10 4 (171+2048*r)) u c) : c ≤ 82 := by
  have hs := count_path_bound (seed_member r hr) p
  have hb := seed_score r hr
  omega

#print axioms all_rank_good
#print axioms rank_edge
#print axioms all_e3_low_visits
end BB6.ESeamRank
'''

def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("Usage: python make_e_seam_rank.py OUTPUT_DIRECTORY")
    states = [int(line) for line in SOURCE.read_text(encoding="utf-8").splitlines()
              if line.strip() and not line.lstrip().startswith("#")]
    if states != sorted(set(states)):
        raise ValueError("Source graph states must be sorted unique")
    ranks = rank_states(states)
    blocks = [states[i:i+BLOCK_SIZE] for i in range(0,len(states),BLOCK_SIZE)]
    output = Path(sys.argv[1])
    body = "\n".join(f"def rankBlock{i} : RankTree := {tree(bs,ranks)}"
                     for i,bs in enumerate(blocks))
    write_atomic(output/"ESeamRankBase.lean",
                 BASE.replace("__BLOCKS__",body).replace("__ROOT__",
                     block_tree(blocks,list(range(len(blocks))))))
    for i in range(len(blocks)):
        write_atomic(output/f"ESeamRankBlock{i}.lean",
                     f"""import ESeamRankBase
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.ESeamRank
theorem block{i}_rank_good : allRankGood BB6.TreeCert.block{i} = true := by decide
end BB6.ESeamRank
""")
    imports = "".join(f"import ESeamRankBlock{i}\n" for i in range(len(blocks)))
    lemmas = ",\n".join(f"    block{i}_rank_good" for i in range(len(blocks)))
    write_atomic(output/"ESeamRankMaster.lean",
                 MASTER.replace("__IMPORTS__",imports).replace("__LEMMAS__",lemmas))
    print(f"Generated {len(blocks)} kernel rank leaves")

if __name__ == "__main__":
    main()
