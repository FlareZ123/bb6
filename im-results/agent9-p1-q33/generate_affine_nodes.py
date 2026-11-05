"""Generate two exact finite affine dyadic-shadow certificates for q=33+2^64*r.

The emitted Lean source is kernel-checked via by decide; the generator is not
trusted as a proof oracle. Deterministic, atomically replaced under a file lock.
"""
from collections import deque
import fcntl
import os
from pathlib import Path
import tempfile

P = 1 << 64
OUTPUT = Path("im-results/agent9-p1-q33/Q33AffineNodes.lean")


def compute(feeder: int):
    multiplier = 12 if feeder == 0 else 10
    root = (0, multiplier * 33 + 4, multiplier * P)
    visited = {root}
    queue = deque([root])
    while queue:
        m, a, b = queue.popleft()
        assert a > 0 and a % 1024 != 0 and b % 1024 == 0
        valuation = (a & -a).bit_length() - 1
        for t in range(valuation + 1):
            assert b % (1 << (t + 1)) == 0
            base = 536 + feeder + m + t + a // (1 << t)
            if base % 2 == 0:
                continue
            successor = (m + t + 1, base // 2, 8 * P + b // (1 << (t + 1)))
            if successor not in visited:
                visited.add(successor)
                queue.append(successor)
                assert len(visited) < 1000
    return sorted(visited)


def generate() -> str:
    lines = [
        "import AffineGeneric",
        "set_option maxHeartbeats 100000000",
        "set_option maxRecDepth 8192",
        "namespace BB6.Agent9Affine",
        "def P : Nat := 18446744073709551616",
    ]
    for feeder in (0, 1):
        nodes = compute(feeder)
        lines.append(f"def nodes{feeder} : List (Nat×Nat×Nat) := [")
        lines.append(",\n".join(f"  ({m},{a},{b})" for m, a, b in nodes))
        lines.append("]")
        lines.append(
            f"theorem check{feeder} : check {536 + feeder} P nodes{feeder} = true := by\n"
            "  decide"
        )
        lines.append(f"#print axioms check{feeder}")
        print(f"feeder={feeder} nodes={len(nodes)} max_cost={max(n[0] for n in nodes)}")
    lines.append("end BB6.Agent9Affine")
    return "\n".join(lines) + "\n"


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    lock = OUTPUT.with_suffix(OUTPUT.suffix + ".lock")
    with lock.open("a") as handle:
        fcntl.flock(handle, fcntl.LOCK_EX)
        with tempfile.NamedTemporaryFile("w", dir=OUTPUT.parent, delete=False, encoding="utf-8") as stream:
            path = Path(stream.name)
            stream.write(generate())
        os.replace(path, OUTPUT)


if __name__ == "__main__":
    main()
