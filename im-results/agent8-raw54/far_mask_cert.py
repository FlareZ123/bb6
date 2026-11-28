#!/usr/bin/env python3
"""Generate source-verifiable FAR masks from untrusted 1RD DFA mutations.

This program is NOT trusted. The generated Lean proof checks FAR.Data.fastValid
against original semantics using kernel reduction, with no oracle for C++ output.
"""
import argparse
from pathlib import Path

PARENT = "1RB---_1RC---_0RD---_1LD0LE_---1RD_------"

def parse(code):
    s = code.replace("_", "")
    if len(s) != 36:
        raise ValueError(code)
    p = []
    for i in range(0, 36, 3):
        w = s[i:i+3]
        if w == "---":
            p.append(None)
        else:
            if w[0] not in "01" or w[1] not in "LR" or w[2] not in "ABCDEF":
                raise ValueError(w)
            p.append((int(w[0]), w[1] == "R", ord(w[2])-65))
    return p

def masks(p, raw, rev):
    d = len(raw)//2
    if len(raw) != 2*d or not all(0 <= v < d for v in raw) or raw[0] != 0:
        raise ValueError("invalid anchored DFA")
    N = 6*d+1
    H = N-1
    halt = 1 << H
    T = [0]*(2*N)
    T[H] = halt
    T[N+H] = halt
    rules = []
    for l in range(d):
        for q in range(6):
            for a in range(2):
                v = p[2*q+a]
                dst = a*N + 6*l+q
                if v is None:
                    T[dst] = halt
                    continue
                w,right,n = v
                if right == rev:
                    for j in range(d):
                        for b in range(2):
                            if raw[2*j+b] == l:
                                rules.append((dst,b*N+6*j+n,w*N))
                else:
                    T[dst] = 1 << (6*raw[2*l+w] + n)
    for step in range(2*N*N+1):
        changed = False
        for dst,src,off in rules:
            bits = T[src]
            val = T[dst]
            while bits:
                x = bits & -bits
                j = x.bit_length()-1
                val |= T[off+j]
                bits -= x
            if val != T[dst]:
                T[dst] = val
                changed = True
        if not changed:
            break
    else:
        raise ValueError("non-convergent saturation")
    z = halt
    for step in range(N):
        zn = z
        for j in range(N):
            if T[j] & z:
                zn |= 1 << j
        if zn == z:
            break
        z = zn
    if z & 1:
        raise ValueError("blank state reaches unassigned transition")
    return T[:N], T[N:], z

def term(p):
    s = "(fun _ => (none : Option Transition))"
    for i, v in enumerate(p):
        if v is None:
            continue
        w,right,n = v
        mv = f"⟨{str(bool(w)).lower()},{str(right).lower()},{n}⟩"
        s = f"(refine {s} ({i//2},{str(bool(i%2)).lower()}) (some {mv}))"
    return s

def source(code, rev, raw, idx):
    p = parse(code)
    base = parse(PARENT)
    if any(v is not None and v != p[i] for i,v in enumerate(base)):
        raise ValueError("not descendant of Raw54 E1=1RD parent")
    d = len(raw)//2
    r0,r1,z = masks(p,raw,rev)
    def nums(xs):
        return ",".join(map(str,xs))
    data = f"⟨0,[{nums(raw)}],[{nums(r0)}],[{nums(r1)}],{z}⟩"
    ns = f"OneRDMask{idx:03d}"
    never = (
      "  exact FAR.reflectNever m (FAR.Data.sound C q "
      "(FAR.Data.fastValid_sound C q valid) (reflectTable m) "
      "(FAR.reflectCompatible p m hm))"
      if rev else
      "  exact FAR.Data.sound C p (FAR.Data.fastValid_sound C p valid) m hm"
    )
    return f"""import Raw54OneRDBankAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace BB6.Agent8Raw54.{ns}
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay

/-- Original 1RD partial table {code} with {sum(v is None for v in p)} holes. -/
abbrev p : PartialMachine := {term(p)}
{('abbrev q : PartialMachine := FAR.reflectPartial p' if rev else '')}
/-- Untrusted saturation masks; checked against original FAR semantics. -/
def C : FAR.Data {d} := {data}
theorem valid : C.fastValid {('q' if rev else 'p')} = true := by decide +kernel
theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
{never}
theorem cover : Cover (WeightedBound 1006) p := by
  apply Cover.leaf
  intro m hm
  exact weighted_never 1006 m (never m hm)
#print axioms valid
#print axioms cover
end BB6.Agent8Raw54.{ns}
"""

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("ledger", type=Path)
    ap.add_argument("--index", type=int, required=True)
    ap.add_argument("--out", type=Path, required=True)
    a = ap.parse_args()
    records = [x.split(chr(9)) for x in a.ledger.read_text().splitlines() if x.strip()]
    if len(records) != 251:
        raise ValueError(f"expected 251 candidates, got {len(records)}")
    if len(set(row[0] for row in records)) != 251:
        raise ValueError("duplicate source partial table")
    row = records[a.index]
    code,rev,d,raw = row[:4]
    if len(raw) != 2*int(d):
        raise ValueError("DFA dimension mismatch")
    a.out.write_text(source(code,bool(int(rev)),[int(c,36) for c in raw],a.index))
    print(f"source-replay: index={a.index} table={code} rev={rev} dimension={d} path={a.out}")

if __name__ == "__main__":
    main()
