"""Generate Lean kernel-checkable complete reverse-cone certificates for #746.

The Python inverse only proposes finite witnesses. Lean verifies every enumerated
parent, the entire cone closure, and exclusion of the genuine post-blank root.
Run from CI after the unchanged source-connected FastParents proofs compile.
"""

import argparse
import os
import tempfile
from pathlib import Path

from reset_inverse_fast import predecessor_heights


def reverse_cone(target: int) -> list[int]:
    seen = {target}
    pending = [target]
    while pending:
        for parent in predecessor_heights(pending.pop()):
            if parent not in seen:
                seen.add(parent)
                pending.append(parent)
    return sorted(seen)


def generate(index: int, chunk_size: int, output: Path) -> tuple[int, int]:
    if index < 4 or chunk_size < 1:
        raise ValueError("Index must be at least 4 and chunk size positive")
    target = 4 * (1 << index) - index - 4
    ancestors = reverse_cone(target)
    if target not in ancestors or 2 in ancestors:
        raise ValueError("Reverse cone reaches the genuine root or lacks its target")
    chunks = [ancestors[i:i + chunk_size] for i in range(0, len(ancestors), chunk_size)]
    label = f"cone{index}"
    lines = [
        "import FastClosedCert",
        "set_option exponentiation.threshold 1000",
        "set_option maxRecDepth 20000",
        "set_option maxHeartbeats 6000000",
        "namespace CascadeResetInverse",
    ]
    for i, chunk in enumerate(chunks):
        lines.append(f"private def {label}Chunk{i}:List Nat := [")
        for j in range(0, len(chunk), 4):
            sep = "," if j + 4 < len(chunk) else ""
            lines.append("  " + ", ".join(map(str, chunk[j:j + 4])) + sep)
        lines.append("]")
    lines.append(f"private def {label}Chunks:List (List Nat) := [" +
                 ", ".join(f"{label}Chunk{i}" for i in range(len(chunks))) + "]")
    for i in range(len(chunks)):
        lines.extend([
            f"private theorem {label}Check{i} :",
            f"  fastCheckChunk {label}Chunks.flatten {label}Chunk{i}=true := by decide",
        ])
    lines.extend([
        f"private theorem {label}Closed : fastClosedCert {label}Chunks.flatten=true := by",
        "  apply fastClosedCert_of_chunks",
        "  intro c hc",
        f"  simp only [{label}Chunks, List.mem_cons, List.not_mem_nil, or_false] at hc",
        "  rcases hc with " + " | ".join("rfl" for _ in chunks),
    ])
    for i in range(len(chunks)):
        lines.append(f"  · exact {label}Check{i}")
    lines.extend([
        f"def {label}:List Nat := {label}Chunks.flatten",
        f"theorem {label}_closed : fastClosedCert {label}=true := {label}Closed",
        f"theorem {label}_target : {target} ∈ {label} := by decide",
        f"theorem {label}_no_root : 2 ∉ {label} := by decide",
        f"theorem blank_excludes_fatal_{index} :",
        f"    ¬CascadeSweep.ReachC (2,0) ({target},0) :=",
        f"  fastClosedCert_excludes {label} {target} {label}_closed {label}_target {label}_no_root",
        f"#print axioms blank_excludes_fatal_{index}",
        "end CascadeResetInverse",
    ])
    output.parent.mkdir(parents=True, exist_ok=True)
    lock = output.with_name(output.name + ".lock")
    lock.mkdir()
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", newline="\n",
                                     dir=output.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write("\n".join(lines) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, output)
    finally:
        lock.rmdir()
    return len(ancestors), len(chunks)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--index", type=int, default=257)
    parser.add_argument("--chunk-size", type=int, default=16)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print("Generated reverse-cone certificate:", generate(args.index, args.chunk_size, args.output))
