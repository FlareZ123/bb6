#!/usr/bin/env python3
"""Reconstruct the M5334 source-level certificate (Lean 4.36.0-rc2).
Generator is untrusted: all primitive and pump identities are checked by Lean.
Usage: python3 generate_m5334.py > Raw56LCM5334.lean
"""
from dataclasses import dataclass

TABLE = '1RB0LA_1RC0RA_0RD1RF_1LD1LE_0RB1LC_---1RA'
TAB = {(q,b): v[3*b:3*b+3] for q,v in enumerate(TABLE.split('_')) for b in range(2)}
# direction, state, source prefix, destination prefix, input and output words, cost
MACROS = dict(zip('abcde', [
    ('L',0,'011','000','011','011',13),
    ('R',1,'011011011','0','011','101',7),
    ('L',0,'101101101','00','101','011',13),
    ('R',0,'011011011','10','011','011',7),
    ('L',0,'011011011','000','011','011',13),
]))
OPS = 'a 78 b 50 c 97 d 57 e 116 d 61 e 136 d 53 e 156 d 97 e 176 d 53 e 196 d 105 e 216 d 53 e 236 d 57 e 256 d 109 e 276 d 53 e 296 d 57 e 316 d 61 e 336 d 53 e 356 d 121 e 376 d 53 e 396 d 69 e 416 d 53 e 436 d 57 e 456 d 65 e 476 d 53 e 496 d 57 e 516 d 51 e 536 d 53 e 556 d 55'.split()

@dataclass(frozen=True)
class C:
    q: int
    l: str
    r: str
    b: str = '011'

def step(c):
    v=TAB[c.q,int(c.l[0]) if c.l else 0]
    assert v != '---'
    q=ord(v[2])-65
    if v[1]=='R':
        assert not c.r or c.r[0] in '01'
        return C(q,(c.r[:1] or '0')+v[0]+c.l[1:],c.r[1:],c.b)
    return C(q,c.l[1:],v[0]+c.r,c.b)

def word(s): return f'(bits! "{s}")' if s else '[]'
def block(s): return 'P' if s=='011' else word(s)
def fmt(s,b):
    if 'X' not in s: return word(s)
    a,z=s.split('X')
    return ' ++ '.join([word(a),f'rep {block(b)} n',word(z)])
def cf(c): return f'⟨{c.q},{fmt(c.l,c.b)},{fmt(c.r,c.b)}⟩'

print('''import SweepPumping

namespace BB6.Agent4Raw56LCM5334
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent50Zipper
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def p : PartialMachine := fun (q,b) =>
  match q.val,b with''')
for (q,b),v in TAB.items():
    rhs='none' if v=='---' else f'some (some ⟨{str(v[0]=="1").lower()},{str(v[1]=="R").lower()},{ord(v[2])-65}⟩)'
    print(f'  | {q},{str(bool(b)).lower()} => {rhs}')
print('''  | _,_ => none

open Lean
syntax "bits!" str : term
macro_rules
  | `(bits! $s:str) => do
    let xs ← s.getString.toList.mapM fun c => if c == '1' then `(true) else `(false)
    `([$[$xs.toArray],*])
def P : List Bool := bits! "011"

theorem rep_add (n m : Nat) : rep P (n+m) = rep P n ++ rep P m := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp only [Nat.succ_add,rep,ih,List.append_assoc]
''')
start=C(0,'011X01111110','0'*10)
print(f'def G (n : Nat) : Z0 := {cf(start)}')
c=start; names=[]; costs=[]; defined=set()
def emit(k,d,proof):
    global c
    name=f's{len(names):03}';names.append(name);costs.append(k)
    print(f'theorem {name} (n : Nat) : run0 p {k} {cf(c)} = some {cf(d)} := {proof}')
    c=d
for op in OPS:
    if op.isdigit():
        rem=int(op)
        while rem:
            k=min(rem,100);d=c
            for _ in range(k): d=step(d)
            emit(str(k),d,'rfl');rem-=k
        continue
    dr,q,pre,dp,b,ob,k=MACROS[op]
    assert c.q==q and c.b==b
    src,dest=(c.l,c.r) if dr=='L' else (c.r,c.l)
    assert src.startswith(pre+'X') and dest.startswith(dp)
    suf,ds=src[len(pre)+1:],dest[len(dp):]
    lp,rp,L,R=(pre,dp,suf,ds) if dr=='L' else (dp,pre,ds,suf)
    d=C(q,pre+suf,dp+'X'+ds,ob) if dr=='L' else C(q,dp+'X'+ds,pre+suf,ob)
    nm='block'+str('abcde'.index(op))
    if op not in defined:
        l,r=(f'{word(lp)} ++ {block(b)} ++ L',f'{word(rp)} ++ R') if dr=='L' else (f'{word(lp)} ++ L',f'{word(rp)} ++ {block(b)} ++ R')
        ll,rr=(f'{word(lp)} ++ L',f'{word(rp)} ++ {block(ob)} ++ R') if dr=='L' else (f'{word(lp)} ++ {block(ob)} ++ L',f'{word(rp)} ++ R')
        print(f'theorem {nm} (L R : List Bool) : run0 p {k} ⟨{q},{l},{r}⟩ = some ⟨{q},{ll},{rr}⟩ := rfl')
        defined.add(op)
    emit(f'({k}*n)',d,f'\n  sweep{dr} p {q} ({word(lp)}) ({word(rp)}) {block(b)} {block(ob)} {k} {nm} n ({word(L)}) ({word(R)})')
assert c==C(0,'011'*3+'X'+'011'*23+'01111110','0'*10)
print('theorem epoch (n : Nat) : run0 p (9509+500*n) (G n) = some (G (n+25)) := by')
print(f'  have h := {names[0]} n')
for name in names[1:]: print(f'  have h := join0 h ({name} n)')
print('''  have heq : rep P 3 ++ rep P n ++ rep P 23 = rep P 1 ++ rep P (n+25) := by
    rw [← rep_add,← rep_add,← rep_add]
    congr 1 <;> omega
  have hc : (⟨0,rep P 3 ++ rep P n ++ rep P 23 ++ (bits! "01111110"),(bits! "0000000000")⟩ : Z0) = G (n+25) := by
    rw [heq]
    rfl''')
print(f"  have hc' : {cf(c)} = G (n+25) := by")
print('''    simp only [List.append_assoc] at hc ⊢
    rw [show rep P 3 = (bits! "011011011") by rfl,''')
print(f'      show rep P 23 ++ (bits! "01111110") = {word("011"*23+"01111110")} by rfl] at hc')
print('''    exact hc
  rw [hc'] at h''')
print(f'  have ht : {" + ".join(costs)} = 9509+500*n := by omega')
print('''  rw [ht] at h
  exact h''')
c=C(0,'','');rem=8505;names=[]
while rem:
    k=min(rem,100);d=c
    for _ in range(k):d=step(d)
    name=f'e{len(names):03}';names.append(name)
    print(f'theorem {name} : run0 p {k} {cf(c)} = some {cf(d)} := rfl');c=d;rem-=k
assert c==C(0,start.l.replace('X','011'*23),start.r)
print('theorem entry : run0 p 8505 ⟨0,[],[]⟩ = some (G 23) := by')
print(f'  have h := {names[0]}')
for name in names[1:]:print(f'  have h := join0 h {name}')
print('''  exact h

theorem never (m : Machine) (hm : compatible p m) : NeverHalts m := by
  apply never_of_growth p (fun k => G (23+25*k)) 8505 (fun k => 9509+500*(23+25*k))
  · exact entry
  · intro k; omega
  · intro k
    simpa only [Nat.mul_succ, Nat.add_assoc] using epoch (23+25*k)
  · exact hm

#print axioms epoch
#print axioms entry
#print axioms never
end BB6.Agent4Raw56LCM5334''')
