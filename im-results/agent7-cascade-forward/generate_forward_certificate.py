"""Generate source-checkable #746 forward reset certificates.

The Python trace supplies only candidates. Lean rechecks every edge against
the complete, proven ResetParent relation, using kernel reduction.
"""
import argparse
import os
import tempfile
from pathlib import Path
from filelock import FileLock


def witness(h: int) -> tuple[int, int, int, bool]:
    p, k = 1, 0
    while h + k + 5 >= 8 * p:
        p, k = 2 * p, k + 1
    if h + k + 4 == 4 * p:
        raise ValueError(f"Halting reset {h}")
    a = 4 * p + (h + k) // 2
    if (h + k) % 2 == 0:
        u, t, odd = a, 0, False
        assert 6 * p - 1 <= u <= 8 * p - 3
        assert 2 * u == 8 * p + h + k
    else:
        q, t = a + 3, 0
        while q % 2 == 0:
            q //= 2
            t += 1
        d, odd = q, True
        u = (3 ** (t + 1) * d - 5) // 2
        assert d % 2 == 1
        assert 6 * p + 1 <= (1 << t) * d <= 8 * p - 1
        assert 2 * u + 5 == 3 ** (t + 1) * d
        assert 2 * ((1 << t) * d) == 8 * p + h + k + 5
    assert h < u
    return u, k, t, odd


def generate(n: int, chunk_size: int) -> str:
    cap = 4 * (1 << n) - n - 4
    h, heights, edges = 2, [2], []
    while h <= cap:
        j = h.bit_length() - 2
        if 4 <= j <= n and j % 6 in (4, 5) and h == 4 * (1 << j) - j - 4:
            raise ValueError(f"Reached forbidden fatal reset {h} at n={j}")
        u, k, t, odd = witness(h)
        edges.append((u, k, t, odd))
        h = u
        heights.append(h)

    chunks = [edges[i:i + chunk_size] for i in range(0, len(edges), chunk_size)]
    def tail(i: int) -> str:
        result = "[]"
        for j in range(len(chunks) - 1, i - 1, -1):
            result = f"(seg{j} ++ {result})"
        return result

    out = ["import ForwardProof",
           "namespace CascadeForwardCert",
           "set_option maxRecDepth 1000000",
           "set_option maxHeartbeats 0",
           "set_option exponentiation.threshold 4096"]
    for i, chunk in enumerate(chunks):
        start = heights[i * chunk_size]
        end = heights[min((i + 1) * chunk_size, len(edges))]
        out.append(f"private def seg{i} : List Edge := [")
        out.extend(
            f"  ⟨{u},{k},{t},{str(odd).lower()}⟩" + ("," if j + 1 < len(chunk) else "")
            for j, (u, k, t, odd) in enumerate(chunk)
        )
        out.append("]")
        out.append(
            f"private theorem seg{i}_ok : "
            f"segment stepOk (badHeight {n}) {end} {start} seg{i} = true := by decide"
        )
    out.append(f"private def fullCert : List Edge := {tail(0)}")
    out.append(
        f"theorem checked : check stepOk (badHeight {n}) "
        f"(CascadeManyShield.fatal {n}) 2 fullCert = true := by"
    )
    out.append("  unfold fullCert")
    for i in range(len(chunks)):
        start = heights[i * chunk_size]
        end = heights[min((i + 1) * chunk_size, len(edges))]
        out.append(
            f"  rw [segment_append stepOk (badHeight {n}) "
            f"(CascadeManyShield.fatal {n}) {end} seg{i} {start} "
            f"{tail(i + 1)} seg{i}_ok]"
        )
    out.extend([
        "  decide",
        f"theorem no_fatal_survivors_through_{n} (i : Nat) "
        f"(hi : 4 ≤ i) (hbound : i ≤ {n}) (hres : i%6=4 ∨ i%6=5) :",
        "    ¬CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal i,0) :=",
        f"  certified_survivor_exclusion {n} fullCert checked i hi hbound hres",
        "#print axioms checked",
        f"#print axioms no_fatal_survivors_through_{n}",
        "end CascadeForwardCert",
    ])
    print(f"certificate n={n} edges={len(edges)} chunks={len(chunks)} final_bits={h.bit_length()}")
    return "\n".join(out) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, default=1024)
    parser.add_argument("--chunk-size", type=int, default=150)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.index < 4 or args.chunk_size < 1:
        parser.error("index must be >=4 and chunk-size >=1")
    result = generate(args.index, args.chunk_size)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with FileLock(str(args.output) + ".lock"):
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=args.output.parent,
                                         delete=False) as f:
            tmp = Path(f.name)
            f.write(result)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, args.output)


if __name__ == "__main__":
    main()
