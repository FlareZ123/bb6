"""Generate independent, kernel-checked Lean modules for long #746 reset prefixes.

The Python computation supplies only untrusted candidate edges. Every module
checks its own exact ResetParent path using ordinary Lean decide, then exports
a SafePath theorem; the final proof composes the proof-bearing segments.
"""
import argparse
import os
from pathlib import Path
import tempfile

from filelock import FileLock
from generate_forward_certificate import witness


def atomic_write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with FileLock(str(path) + ".lock"):
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         delete=False) as file:
            tmp = Path(file.name)
            file.write(content)
            file.flush()
            os.fsync(file.fileno())
        os.replace(tmp, path)


def generate(index: int, chunk_size: int, directory: Path) -> None:
    fatal = (1 << (index + 2)) - index - 4
    heights, edges = [2], []
    h = 2
    while h <= fatal:
        n = h.bit_length() - 2
        if 4 <= n <= index and n % 6 in (4, 5) and h == (1 << (n + 2)) - n - 4:
            raise ValueError(f"Reached a fatal reset at index {n}")
        edge = witness(h)
        edges.append(edge)
        h = edge[0]
        heights.append(h)

    chunks = [edges[i:i + chunk_size] for i in range(0, len(edges), chunk_size)]
    names = [f"Forward{index}_{i:03d}" for i in range(len(chunks))]
    safes = [f"path_{index}_{i:03d}" for i in range(len(chunks))]
    for i, chunk in enumerate(chunks):
        start = heights[i * chunk_size]
        end = heights[min((i + 1) * chunk_size, len(edges))]
        name, safe = names[i], safes[i]
        source = [
            "import ForwardSafe",
            "namespace CascadeForwardCert",
            "set_option maxRecDepth 1000000",
            "set_option maxHeartbeats 0",
            "set_option exponentiation.threshold 4096",
            f"private def {name}_edges : List Edge := [",
        ]
        source.extend(
            f"  ⟨{u},{k},{t},{str(odd).lower()}⟩" + ("," if j + 1 < len(chunk) else "")
            for j, (u, k, t, odd) in enumerate(chunk)
        )
        source.extend([
            "]",
            f"private theorem {name}_check : segment stepOk (badHeight {index}) "
            f"{end} {start} {name}_edges = true := by decide",
            f"theorem {safe} : SafePath CascadeResetInverse.ResetParent "
            f"(badHeight {index}) {start} {end} :=",
            f"  segment_safe stepOk stepOk_sound (badHeight {index}) "
            f"{end} {name}_edges {start} {name}_check",
            f"#print axioms {safe}",
            "end CascadeForwardCert",
        ])
        atomic_write(directory / f"{name}.lean", "\n".join(source) + "\n")

    result = [f"import {name}" for name in names]
    result.extend([
        "namespace CascadeForwardCert",
        "set_option maxRecDepth 1000000",
        "set_option maxHeartbeats 0",
        f"private theorem cap_{index} : CascadeManyShield.fatal {index} < {h} := by decide",
        f"private theorem full_path_{index} : SafePath CascadeResetInverse.ResetParent "
        f"(badHeight {index}) 2 {h} := by",
    ])
    term = safes[-1]
    for safe in reversed(safes[:-1]):
        term = f"SafePath.trans {safe} ({term})"
    result.append("  exact " + term)
    result.extend([
        f"theorem no_fatal_survivors_through_{index} (n : Nat) "
        f"(hn : 4 ≤ n) (hbound : n ≤ {index}) "
        "(hres : n%6=4 ∨ n%6=5) :",
        "    ¬CascadeSweep.ReachC (2,0) (CascadeManyShield.fatal n,0) :=",
        f"  safePath_survivor_exclusion {index} {h} full_path_{index} "
        f"cap_{index} n hn hbound hres",
        f"#print axioms full_path_{index}",
        f"#print axioms no_fatal_survivors_through_{index}",
        "end CascadeForwardCert",
    ])
    atomic_write(directory / f"Forward{index}Final.lean", "\n".join(result) + "\n")
    print(f"Index {index}: {len(edges)} first-reset edges, "
          f"{len(chunks)} independently checked modules, final bits={h.bit_length()}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, required=True)
    parser.add_argument("--chunk-size", type=int, default=16)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    if args.index < 4 or args.chunk_size < 1:
        parser.error("index must be >=4 and chunk-size >=1")
    generate(args.index, args.chunk_size, args.output_dir)


if __name__ == "__main__":
    main()
