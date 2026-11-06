"""Generate kernel-checked original P1 dyadic gateway certificates for nine q seeds.

The generator is untrusted. Each node-list closure, valuation bound, source
bridge and blank-root theorem is independently checked by Lean 4.36.0-rc2.
"""
from collections import deque
from pathlib import Path
from tempfile import NamedTemporaryFile
import fcntl
import os

QS = (117, 309, 425, 446, 566, 670, 710, 726, 990)
D = 18
M = 17
OUT = Path("im-results/agent8-p1-precision-source/QBatch18.lean")


def graph(q: int, side: int) -> list[tuple[int, int]]:
    L = 16 * q + 8 + side
    root = (0, (12 if side == 0 else 10) * q + 4)
    seen = {root}
    queue = deque((root,))
    while queue:
        m, z = queue.popleft()
        assert m <= M and z > 0 and z % 1024 != 0
        assert z % (1 << (D - m)) != 0
        for t in range(10):
            if z % (1 << t) != 0:
                continue
            numerator = L + m + t + z // (1 << t)
            if numerator % 2 == 0:
                continue
            next_state = (m + t + 1, numerator // 2)
            if next_state not in seen:
                seen.add(next_state)
                queue.append(next_state)
                assert len(seen) < 1000
    return sorted(seen)


def emit_side(q: int, side: int) -> str:
    stem = f"q{q}l{side}"
    nodes = graph(q, side)
    L = 16 * q + 8 + side
    z0 = (12 if side == 0 else 10) * q + 4
    data = ",\n".join(f"  ({m},{z})" for m, z in nodes)
    print(f"q={q} side={side} nodes={len(nodes)} maxcost={max(m for m,_ in nodes)}")
    return f"""def {stem} : List (Nat × Nat) := [
{data}
]

theorem {stem}_check : checkGraph {L} {stem} = true := by decide

theorem {stem}_bound :
    {stem}.all (fun p => decide
      (p.1 ≤ {M} ∧ ¬2^({D}-p.1)∣p.2 ∧ ¬1024∣p.2)) = true := by decide

theorem {stem}_root : (0,{z0})∈{stem} := by decide

theorem {stem}_small (m z : Nat) (hm : (m,z)∈{stem}) : m≤{M} := by
  have h := (List.all_eq_true.mp {stem}_bound) (m,z) hm
  exact (of_decide_eq_true h).1

theorem {stem}_precise (m z : Nat) (hm : (m,z)∈{stem}) :
    ¬2^({D}-m)∣z := by
  have h := (List.all_eq_true.mp {stem}_bound) (m,z) hm
  exact (of_decide_eq_true h).2.1

theorem {stem}_no1024 (m z : Nat) (hm : (m,z)∈{stem}) :
    ¬1024∣z := by
  have h := (List.all_eq_true.mp {stem}_bound) (m,z) hm
  exact (of_decide_eq_true h).2.2

theorem {stem}_closed (m z t v zp : Nat) (hm : (m,z)∈{stem})
    (hd : z=2^t*v) (hn : 2*zp+1={L}+m+t+v) :
    (m+t+1,zp)∈{stem} := by
  have hmod := {stem}_no1024 m z hm
  have ht : t<10 := by
    by_cases hh : t<10
    · exact hh
    have hp : 1024∣2^t := by
      have h := Nat.pow_dvd_pow 2 (by omega : 10≤t)
      simpa using h
    exact False.elim (hmod (Nat.dvd_trans hp ⟨v,hd⟩))
  exact checkGraph_sound {L} {stem} {stem}_check m z t v zp hm ht hd hn
"""


def emit_q(q: int) -> str:
    return f"""theorem q{q}_source_gateway_excluded (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*({q}+2^{D}*r)+2)-2*(16*({q}+2^{D}*r)+2)-10) := by
  exact all_lifted_gateways_excluded_adaptive {D} {q} r {M}
    (by decide) (by decide) (by decide)
    q{q}l0 q{q}l1 q{q}l0_root q{q}l1_root
    q{q}l0_closed q{q}l1_closed
    q{q}l0_small q{q}l1_small
    q{q}l0_precise q{q}l1_precise
    q{q}l0_no1024 q{q}l1_no1024

#print axioms q{q}_source_gateway_excluded
"""


def generate() -> str:
    lines = [
        "import AdaptiveP1Gate",
        "import Q33Finite",
        "set_option maxRecDepth 16384",
        "set_option maxHeartbeats 100000000",
        "namespace BB6.Agent8Batch18",
        "open BB6.Agent9Q33 BB6.Agent8AdaptiveP1",
    ]
    for q in QS:
        for side in (0, 1):
            lines.append(emit_side(q, side))
        lines.append(emit_q(q))
    lines.append("end BB6.Agent8Batch18")
    return "\n\n".join(lines) + "\n"


def main() -> None:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    lock_path = OUT.with_suffix(OUT.suffix + ".lock")
    with lock_path.open("a", encoding="utf-8") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        with NamedTemporaryFile("w", encoding="utf-8", dir=OUT.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(generate())
        os.replace(temporary, OUT)


if __name__ == "__main__":
    main()
