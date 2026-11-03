"""Generate kernel-checkable Machine C forward-return certificates.

The Python model is an independent transcription of published Agent46 equations.
Generated Lean files are checked by the kernel using `by decide`.
File writes are atomically replaced under filelock. Python 3.10+ and filelock.
"""
from __future__ import annotations

from hashlib import sha256
import json
import os
from pathlib import Path
import tempfile
from filelock import FileLock

ROOT = Path(__file__).resolve().parent
TOTAL = 150052
CHUNK = 1024
EXPECTED_SHA256 = "d82b4a6b23f9f769c144400bebd51428050778bdc437bf17e6bb61561585e14a"

def bounce(k: int, c: int) -> tuple[int, int] | None:
    while c >= 4:
        if k % 2:
            if c <= 2 * k + 6:
                return 2 * k + 6 - c, c
            k, c = 2*k+3, c-(2*k+3)
        else:
            if c == 4: return 2*k+2, 3
            if c == 5: return None
            if c <= 2*k+8: return 2*k+8-c, c-1
            k, c = 2*k+4, c-(2*k+5)
    return None

def step(p: tuple[int, int]) -> tuple[int, int] | None:
    a, k = p
    if a == 0:
        if k == 0: return None
        if k == 1: return 0, 4
        return bounce(1, 2*k+1)
    if a == 1:
        if k == 0: return 5, 1
        if k == 1: return 2, 3
        if k == 2: return 2, 5
        if k == 3: return 0, 7
        return bounce(4, 2*k-3)
    if k == 0: return a-2, 2
    if 2*k <= a: return a-2*k, 2*k+2
    return bounce(a-1, 2*k-a+3)

def atomic_replace(path: Path, source: str) -> None:
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8",
                                 newline="\n", dir=path.parent, delete=False) as fh:
        fh.write(source)
        temporary = Path(fh.name)
    os.replace(temporary, path)

def generate() -> None:
    state = (5, 1)
    digest = sha256()
    boundaries = [(0, state)]
    for index in range(TOTAL):
        digest.update(f"{index},{state[0]},{state[1]}\n".encode("ascii"))
        nxt = step(state)
        assert nxt is not None, (index, state)
        assert nxt[0] + 2*nxt[1] >= state[0] + 2*state[1] + 2
        state = nxt
        if (index+1) % CHUNK == 0 or index+1 == TOTAL:
            boundaries.append((index+1, state))
    digest.update(f"{TOTAL},{state[0]},{state[1]}\n".encode("ascii"))
    assert state == (621619, 213453)
    assert len(boundaries) == 148
    assert digest.hexdigest() == EXPECTED_SHA256

    chunks: dict[int,str] = {}
    prefixes: dict[int,str] = {
        0: "theorem prefix_0 : ForwardMass.run FastC.next (5,1) 0 = some (5,1) := rfl"
    }
    for i in range(147):
        begin, (a,k) = boundaries[i]
        end, (x,y) = boundaries[i+1]
        delta = end-begin
        chunks[i] = (
            f"theorem chunk_{i} : ForwardMass.run FastC.next ({a},{k}) {delta} "
            f"= some ({x},{y}) := by\n  decide"
        )
        prefixes[i+1] = (
            f"theorem prefix_{i+1} : ForwardMass.run FastC.next (5,1) {end} "
            f"= some ({x},{y}) := by\n"
            f"  have hsplit : {end} = {begin}+{delta} := by omega\n"
            f"  rw [hsplit]\n"
            f"  rw [ForwardMass.run_add, prefix_{i}]\n"
            f"  simpa only [Option.bind_some] using chunk_{i}"
        )

    with FileLock(str(ROOT/".certificate.lock")):
        for group in range(15):
            sl = range(group*10, min((group+1)*10, 147))
            source = "\n\n".join([
                "import FastC\n\nset_option maxRecDepth 200000\nset_option maxHeartbeats 20000000",
                "namespace FastCChunks",
                *(chunks[i] for i in sl),
                "end FastCChunks\n",
            ])
            atomic_replace(ROOT/f"FastChunks{group:02d}.lean", source)
            lo = 0 if group == 0 else group*10+1
            hi = min((group+1)*10, 147)
            imports = ([] if group == 0 else [f"import FastPrefix{group-1:02d}"])
            imports.append(f"import FastChunks{group:02d}")
            source = "\n\n".join([
                "\n".join(imports),
                "namespace FastCChunks",
                *(prefixes[i] for i in range(lo, hi+1)),
                *(["#print axioms prefix_147"] if group == 14 else []),
                "end FastCChunks\n",
            ])
            atomic_replace(ROOT/f"FastPrefix{group:02d}.lean", source)
        manifest = {
            "total": TOTAL, "chunk": CHUNK,
            "target": [1,524260], "target_weight": 1048521,
            "end": [621619,213453], "end_weight": 1048525,
            "sha256": digest.hexdigest(), "boundaries": boundaries,
        }
        atomic_replace(ROOT/"manifest.json", json.dumps(manifest, indent=2)+"\n")
    print(json.dumps({k:v for k,v in manifest.items() if k!="boundaries"}, indent=2))

if __name__ == "__main__":
    generate()
