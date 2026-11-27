"""Generate untrusted checkpoint lists; Lean independently checks every transition."""
import argparse
from pathlib import Path

RANGES = [(15002, 29820, 30007), (29822, 52576, 59647),
          (52578, 98832, 105159), (98834, 124832, 197671)]

def backward(q, zs):
    return sorted({c for z in zs if 1 <= (c := (2*z) % q) <= q-3})

def generate(i, out):
    lo, hi, F = RANGES[i]
    L = F.bit_length()
    pre = min(512, F-hi-5)
    top = F-pre
    q = F
    zs = list(range(1,F-2))
    while q > top:
        q -= 1
        zs = backward(q,zs)
    ns = f"BB6.Agent43Adaptive{i}"
    lines = ["import BatchCarryChunks", "set_option maxHeartbeats 0",
             "set_option maxRecDepth 1000000", f"namespace {ns}",
             "open BB6.Agent9BatchCarry"]
    def checkpoint(j, xs):
        lines.append(f"def z{j} : List Nat := [" + ",".join(map(str,xs)) + "]")
    checkpoint(0,zs)
    lines += [f"theorem cert0 : Verified {F} {hi} {top} {top} z0 :=",
              f"  packed_start {L} {F} {hi} {top} {pre} z0",
              "    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)"]
    j = 0
    visits = 0
    while q > lo+4:
        d = min(64 if len(zs)>128 else 256 if len(zs)>32 else 512, q-lo-4)
        old = q
        for _ in range(d):
            assert q%2 or q-4>hi or (q-2)//2 not in zs, (i,q)
            visits += len(zs)
            q -= 1
            zs = backward(q,zs)
        assert q%2 or q-4>hi or (q-2)//2 not in zs, (i,q)
        j += 1
        checkpoint(j,zs)
        lines += [f"theorem cert{j} : Verified {F} {hi} {top} {q} z{j} :=",
                  f"  extend_block {F} {hi} {top} {old} {d} z{j-1} z{j}",
                  f"    (by decide) (by decide) (by decide) cert{j-1} (by decide +kernel)"]
    lines += [f"theorem adaptive_interval : ∀ n, {lo}≤n → n≤{hi} → n%2=0 →",
              "    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) :=",
              f"  verified_interval {F} {hi} {top} {lo} {q} z{j}",
              f"    (by decide) (by decide) (by decide) (by decide) (by decide) cert{j}",
              "#print axioms adaptive_interval", f"end {ns}"]
    out.mkdir(parents=True,exist_ok=True)
    p=out/f"AdaptiveBatch{i}.lean"
    p.write_text("\n".join(lines)+"\n")
    print(f"{p}: {j} local checks, {visits} sparse visits, {len(zs)} final states")

if __name__ == "__main__":
    p=argparse.ArgumentParser()
    p.add_argument("index",type=int,choices=range(len(RANGES)))
    p.add_argument("out",type=Path)
    a=p.parse_args()
    generate(a.index,a.out)
