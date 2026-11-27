#!/usr/bin/env python3
"""Emit a kernel-checkable exact growing right-suffix certificate for Raw39 0LE/4084.
No simulator conclusion is trusted by the Lean certificate: every chunk is rfl
against the original run0, and the pump is quantified over arbitrary right tails.
"""
from pathlib import Path
import sys

TABLE = "1RB0LE_1RC1RA_0RD0RF_1LD0RA_1LA1LB_1RD---"
RULES = TABLE.replace("_", "")
ENTRY = 153471
PERIOD = 15364
PREFIX = 31  # scanned cell is stored in l
GROWTH = 18
CHUNK = 128

def step(z, arbitrary=False):
    q,l,r = z
    s = int(l[0]) if l else 0
    rule = RULES[3*(2*q+s):3*(2*q+s+1)]
    assert rule != "---"
    w,d,q = rule
    q = ord(q)-ord("A")
    if d == "R":
        if arbitrary:
            assert r, "cycle read the arbitrary suffix"
        return q,(r[0] if r else "0")+w+l[1:],r[1:]
    assert d == "L"
    return q,l[1:],w+r

def trace(z, count, arbitrary=False):
    out=[(0,z)]
    for i in range(1,count+1):
        z=step(z,arbitrary)
        if i%CHUNK==0 or i==count:
            out.append((i,z))
    return out

def lit(z, suffix):
    q,l,r=z
    return f'mk {q} "{l}" "{r}" {suffix}'

def emit_chain(out,name,rows,arbitrary):
    suffix="R" if arbitrary else "[]"
    arg=" (R : List Bool)" if arbitrary else ""
    actual=" R" if arbitrary else ""
    for j,(_,z) in enumerate(rows):
        out.append(f'def {name}Z{j}{arg} : Z0 := {lit(z,suffix)}')
    for j in range(len(rows)-1):
        cost=rows[j+1][0]-rows[j][0]
        out.append(f'theorem {name}C{j}{arg} : run0 table {cost} ({name}Z{j}{actual}) = some ({name}Z{j+1}{actual}) := by rfl')
    def combine(a,b):
        if a+1==b:
            return f'{name}C{a}{actual}'
        mid=(a+b)//2
        left=combine(a,mid)
        right=combine(mid,b)
        th=f'{name}J{a}_{b}'
        cost=rows[b][0]-rows[a][0]
        out.append(f'theorem {th}{arg} : run0 table {cost} ({name}Z{a}{actual}) = some ({name}Z{b}{actual}) := by\n  exact join0 ({left}) ({right})')
        return th+actual
    return combine(0,len(rows)-1)

def main(path):
    entry=trace((0,"",""),ENTRY)
    q,L,R=entry[-1][1]
    assert q==0 and len(R)==204 and len(L)==173
    P,T=R[:PREFIX],R[PREFIX:]
    cycle=trace((q,L,P),PERIOD,True)
    q2,L2,R2=cycle[-1][1]
    assert q2==q and L2==L and R2[:PREFIX]==P
    Q=R2[PREFIX:]
    assert Q=="000101000101000101" and len(Q)==GROWTH
    out=["import Raw39LE4084Simplified","set_option maxRecDepth 100000","set_option maxHeartbeats 0","namespace BB6.Agent43Raw39LE4084Pump","open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent11Raw39LE4084Simplified","def word (s : String) : List Bool := s.toList.map (· == '1')","def mk (q : Fin 6) (l r : String) (R : List Bool) : Z0 := ⟨q, word l, word r ++ R⟩"]
    e=emit_chain(out,"ent",entry,False)
    c=emit_chain(out,"cyc",cycle,True)
    out += [
      f'def family (n : Nat) : Z0 := mk 0 "{L}" "{P}" (rep (word "{Q}") n ++ word "{T}")',
      f'theorem first : run0 table {ENTRY} ⟨0,[],[]⟩ = some (family 0) := by\n  exact {e}',
      f'theorem arbitrary_tail (R : List Bool) : run0 table {PERIOD} (mk 0 "{L}" "{P}" R) = some (mk 0 "{L}" "{P}" (word "{Q}" ++ R)) := by\n  exact {c}',
      f'theorem growth (n : Nat) : run0 table {PERIOD} (family n) = some (family (n+1)) := by\n  simpa only [family,rep] using arbitrary_tail (rep (word "{Q}") n ++ word "{T}")',
      f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=\n  never_of_growth table family {ENTRY} (fun _ => {PERIOD}) first (by intro; decide) growth m hm',
      '#print axioms arbitrary_tail','#print axioms never',
      'end BB6.Agent43Raw39LE4084Pump']
    Path(path).write_text("\n".join(out)+"\n")
    print(f"entry={ENTRY} period={PERIOD} growth={Q} chunks={len(entry)+len(cycle)-2}")

if __name__=="__main__":
    main(sys.argv[1] if len(sys.argv)>1 else "Raw39LE4084Pump.lean")
