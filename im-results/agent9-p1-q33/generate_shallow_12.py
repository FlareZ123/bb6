"""Produce twelve original-P1 kernel-checked shallow affine gateway certificates.

The generator is untrusted. Every generated certificate is checked by Lean.
All writes are atomic with advisory locking on the Linux CI runner.
"""
from collections import deque
import fcntl
import os
from pathlib import Path
import tempfile

Q0 = [109, 253, 397, 409, 413, 681, 793, 877, 1017, 1021, 165, 225]
P = 4096
OUT = Path("im-results/agent9-p1-q33/Q12Shallow.lean")


def nodes(q0: int, feeder: int):
    c = 12 if feeder == 0 else 10
    root = (0, c * q0 + 4, c * P)
    seen = {root}
    queue = deque([root])
    while queue:
        m, a, b = queue.popleft()
        k = (a & -a).bit_length()
        assert 0 < k <= 10 and a % (1 << k) != 0 and b % (1 << k) == 0
        for t in range(k):
            if a % (1 << t):
                continue
            assert b % (1 << (t + 1)) == 0
            v = 16 * q0 + 8 + feeder + m + t + a // (1 << t)
            if v % 2 == 0:
                continue
            next_node = (m + t + 1, v // 2, 8 * P + b // (1 << (t + 1)))
            if next_node not in seen:
                seen.add(next_node)
                queue.append(next_node)
                assert len(seen) < 2000
    return sorted((m, a, b, (a & -a).bit_length()) for m, a, b in seen)


def generate() -> str:
    source = [
        "import AffineAdaptive",
        "import GenericCritical41K",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 100000000",
        "namespace BB6.Agent9Shallow",
        "open BB6.Agent9Adaptive",
        "def P : Nat := 4096",
    ]
    for q0 in Q0:
        for f in (0, 1):
            entries = nodes(q0, f)
            name = f"q{q0}l{f}"
            L = 16 * q0 + 8 + f
            c = 12 if f == 0 else 10
            k = ((c * q0 + 4) & -(c * q0 + 4)).bit_length()
            source.append(
                f"def {name} : List (Nat×Nat×Nat×Nat) := [\n" +
                ",\n".join(f"  ({m},{a},{b},{kk})" for m, a, b, kk in entries) +
                "\n]"
            )
            source.append(f"""theorem {name}_check : check {L} P {name} = true := by decide

theorem {name}_closed (r m z t v zp : Nat)
    (hm : (m,z) ∈ decode r {name}) (hd : z=2^t*v)
    (hn : 2*zp+1=16*({q0}+P*r)+{8+f}+m+t+v) :
    (m+t+1,zp)∈decode r {name} := by
  have hn' : 2*zp+1=16*P*r+{L}+m+t+v := by
    simp only [Nat.mul_add,Nat.mul_assoc] at hn ⊢
    omega
  exact check_sound {L} P {name} {name}_check r m z t v zp hm hd hn'

theorem {name}_bound (r m z : Nat) (hm : (m,z) ∈ decode r {name}) :
    m≤41 ∧ ¬1024∣z := check_bounds {L} P {name} {name}_check r m z hm

theorem {name}_root (r : Nat) :
    (0,{c}*({q0}+P*r)+4)∈decode r {name} := by
  apply List.mem_map.mpr
  refine ⟨(0,{c*q0+4},{c}*P,{k}), ?_, ?_⟩
  · decide
  · change (0,{c*q0+4}+{c}*P*r)=(0,{c}*({q0}+P*r)+4)
    simp [Nat.mul_add,Nat.mul_assoc]
    omega
""")
        source.append(f"""theorem no_critical_q{q0} (r : Nat) :
  ¬ BB6.Agent1.Reach 2
    (14*2^(16*({q0}+P*r)+2)-2*(16*({q0}+P*r)+2)-10) := by
  exact BB6.Agent9Generic41K.critical_unreachable_of_shadow41K
    ({q0}+P*r) (by omega) (decode r q{q0}l0) (decode r q{q0}l1)
    (q{q0}l0_root r) (q{q0}l1_root r)
    (q{q0}l0_closed r) (q{q0}l1_closed r)
    (fun m z h => (q{q0}l0_bound r m z h).1)
    (fun m z h => (q{q0}l1_bound r m z h).1)
    (fun m z h => (q{q0}l0_bound r m z h).2)
    (fun m z h => (q{q0}l1_bound r m z h).2)

#print axioms no_critical_q{q0}
""")
        print(f"q={q0}: {sum(len(nodes(q0, f)) for f in (0,1))} nodes")
    source.append("end BB6.Agent9Shallow")
    return "\n\n".join(source) + "\n"


def main() -> None:
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.with_suffix(".lean.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        with tempfile.NamedTemporaryFile("w", dir=OUT.parent, encoding="utf-8", delete=False) as stream:
            temp = Path(stream.name)
            stream.write(generate())
        os.replace(temp, OUT)


if __name__ == "__main__":
    main()
