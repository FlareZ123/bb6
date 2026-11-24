"""Generate proposed residue certificates; Lean checks every certificate and coverage."""
from pathlib import Path
import sys

out = Path(sys.argv[1])
out.mkdir(parents=True, exist_ok=True)
certs = set()
survivors = []
for n in range(14, 10001, 2):
    cs = {(n + 2) // 2}
    for j in range(1, n):
        C = n + 3 + j
        cs = {c // 2 for c in cs if c % 2 == 0} | {(c + C) // 2 for c in cs if (c + C) % 2 == 0}
        if not cs:
            K = j + 1
            certs.add((n % (1 << K), K - 1))
            break
    else:
        survivors.append(n)
assert survivors == [30, 286, 350, 1614, 2990, 3342]
chunks = []
chunk = []
cost = 0
for r, k in sorted(certs, key=lambda x: (x[1], x[0])):
    if chunk and (len(chunk) >= 32 or cost + k > 1700):
        chunks.append(chunk)
        chunk = []
        cost = 0
    chunk.append((r, k))
    cost += k
if chunk:
    chunks.append(chunk)
assert len(certs) == 587 and len(chunks) == 39
for i, chunk in enumerate(chunks):
    s = "import CertCore\nopen BB6.Agent28ModScreen\nnamespace BB6.Agent28ModScreen\nset_option maxRecDepth 200000\nset_option maxHeartbeats 0\nset_option exponentiation.threshold 20000\n"
    s += f"def cert{i} : List (Nat × Nat) := {chunk}\n"
    s += f"theorem cert{i}_ok : cert{i}.all checkCert = true := by decide\n"
    s += "end BB6.Agent28ModScreen\n"
    (out / f"Cert{i}.lean").write_text(s, encoding="utf-8")
