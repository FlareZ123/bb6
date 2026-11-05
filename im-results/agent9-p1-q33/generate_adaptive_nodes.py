"""Generate kernel-checked adaptive affine cones for all q=33+2^40*r."""
from collections import deque
import fcntl
import os
from pathlib import Path
import tempfile

P = 1 << 40
OUTPUT = Path("im-results/agent9-p1-q33/Q33AdaptiveNodes.lean")


def compute(feeder: int):
    multiplier = 12 if feeder == 0 else 10
    root = (0, multiplier * 33 + 4, multiplier * P)
    visited = {root}
    queue = deque([root])
    while queue:
        m, a, b = queue.popleft()
        k = (a & -a).bit_length()
        assert 0 < k <= 10 and a % (1 << k) != 0 and b % (1 << k) == 0
        for t in range(k):
            if a % (1 << t):
                continue
            assert b % (1 << (t + 1)) == 0
            base = 536 + feeder + m + t + a // (1 << t)
            if base % 2 == 0:
                continue
            successor = (m + t + 1, base // 2, 8 * P + b // (1 << (t + 1)))
            if successor not in visited:
                visited.add(successor)
                queue.append(successor)
                assert len(visited) < 1000
    return sorted((m, a, b, (a & -a).bit_length()) for m, a, b in visited)


def generate() -> str:
    lines = [
        "import AffineAdaptive",
        "set_option maxHeartbeats 100000000",
        "set_option maxRecDepth 8192",
        "namespace BB6.Agent9Adaptive",
        "def P : Nat := 1099511627776",
    ]
    for feeder in (0, 1):
        nodes = compute(feeder)
        lines.append(f"def nodes{feeder} : List (Nat×Nat×Nat×Nat) := [")
        lines.append(",\n".join(f"  ({m},{a},{b},{k})" for m, a, b, k in nodes))
        lines.append("]")
        lines.append(
            f"theorem check{feeder} : check {536 + feeder} P nodes{feeder} = true := by\n"
            "  decide"
        )
        lines.append(f"#print axioms check{feeder}")
        print(f"feeder={feeder} nodes={len(nodes)} max_cost={max(n[0] for n in nodes)}")
    lines.append("end BB6.Agent9Adaptive")
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
