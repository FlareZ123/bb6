#!/usr/bin/env python3
"""Reproduce the C1=1LC exhaustive first-hole certificate; Lean checks every witness."""
from pathlib import Path
from collections import Counter
import subprocess,tempfile

ROOT=(7,24,11,24,14,10,3,16,12,11,24,24)
HARD={
 (7,2,11,21,14,10,3,16,12,11,24,3):('C1OneLC',''),
 (7,7,11,21,14,10,3,16,12,11,24,17):('C1Pair','false'),
 (7,20,11,21,14,10,3,16,12,11,24,17):('C1Pair','true'),
 (7,21,11,24,14,10,3,16,12,11,9,3):('C1Carry',''),
 (7,21,11,24,14,10,3,16,12,11,1,9):('C1Triple','.one'),
 (7,21,11,24,14,10,3,16,12,11,3,9):('C1Stack','false'),
 (7,21,11,24,14,10,3,16,12,11,5,9):('C1Triple','.zero'),
 (7,21,11,24,14,10,3,16,12,11,7,9):('C1TwoBlocks',''),
 (7,21,11,24,14,10,3,16,12,11,13,9):('C1Triple','.two'),
 (7,21,11,24,14,10,3,16,12,11,17,9):('C1Stack','true'),
 (7,21,11,24,14,10,3,16,12,11,7,14):('C1Alternating','false'),
 (7,22,11,24,14,10,3,16,12,11,23,1):('C1Alternating','true'),
}

def scan(p,cap):
    l=r=q=h=0; hist=[]; right={}; left={}
    for n in range(cap+1):
        s=2*q+(r&1); c=p[s]
        if c==24:return ('hole',n,s)
        for k in reversed(right.get((q,r),[])):
            a,b,old=hist[k]
            if h<old:continue
            rad=max(0,old-min(x[2] for x in hist[k:]))
            if ((l^a)&((1<<rad)-1))==0:return ('cycle',k,n-k,True,old-rad)
        for k in reversed(left.get((q,l),[])):
            a,b,old=hist[k]
            if h>old:continue
            rad=max(0,max(x[2] for x in hist[k:])-old)
            if ((r^b)&((1<<(rad+1))-1))==0:return ('cycle',k,n-k,False,old+rad)
        hist.append((l,r,h));right.setdefault((q,r),[]).append(n);left.setdefault((q,l),[]).append(n)
        r=(r&~1)|((c>>1)&1); q=c//4
        if c&1:l=(l<<1)|(r&1);r>>=1;h+=1
        else:r=(r<<1)|(l&1);l>>=1;h-=1
    return ('open',)

def refine(p,s,m):return p[:s]+(m,)+p[s+1:]

def build():
    pending=[]
    def walk(p):
        a=scan(p,250)
        if a[0]=='cycle':return a
        if a[0]=='open':
            pending.append(p); return a
        _,n,s=a
        if p.count(24)==1:return ('last',n,s)
        return ('split',n,s,[walk(refine(p,s,m)) for m in range(24)])
    tree=walk(ROOT)
    with tempfile.TemporaryDirectory() as d:
        exe=Path(d)/'far'
        subprocess.run(['g++','-std=c++17','-O3',str(Path(__file__).with_name('c1_one_lc_far.cpp')),'-o',str(exe)],check=True)
        inp=''.join(f'{i} '+ ' '.join(map(str,p))+'\n' for i,p in enumerate(pending))
        raw=subprocess.run([str(exe),'5'],input=inp,text=True,capture_output=True,check=True).stdout
    witness={pending[a[0]]:a[1:] for line in raw.splitlines() if (a:=list(map(int,line.split())))[1]!=-1}
    assert len(pending)==159 and len(witness)==143,(len(pending),len(witness))
    used=set(); ct=Counter(); max_hole=0
    def fill(p,t):
        nonlocal max_hole
        if t[0]=='open':
            if p in witness:t=('far',witness[p])
            else:
                t=scan(p,5000)
                if t[0]=='hole':
                    assert p.count(24)==1
                    t=('last',t[1],t[2])
                if t[0]=='open':
                    assert p in HARD,p
                    used.add(p);t=('hard',*HARD[p])
        ct[t[0]]+=1
        if t[0] in ('last','split'):max_hole=max(max_hole,t[1])
        if t[0]=='split':return (*t[:3],[fill(refine(p,t[2],m),c) for m,c in enumerate(t[3])])
        return t
    tree=fill(ROOT,tree)
    assert used==set(HARD) and max_hole==592,(used,max_hole)
    print('census',ct,'max_hole',max_hole)
    return tree,max_hole+6

def generate(tree,bound):
    defs=[]; proofs=[]; count=0
    def arr(xs):return '['+','.join(map(str,xs))+']'
    def bo(b):return 'true' if b else 'false'
    def slot(s):return f'({s//2},{bo(s%2)})'
    def move(m):return f'⟨{bo((m//2)%2)},{bo(m%2)},{m//4}⟩'
    def leaf(t):
        typ,*x=t
        if typ=='cycle':
            e,k,right,b=x
            return f'BB6.Agent6F0.side_cover B _ {e} {k} {bo(right)} ({b}) (by decide) (by decide)'
        if typ=='last':
            n,s=x
            return f'last_cover B _ {n} {slot(s)} (by omega) (by decide) (by decide) (by decide) (by decide)'
        if typ=='far':
            rev,d,*vals=x[0]; N=6*d+1; dfa=vals[:2*d]; a=vals[2*d:2*d+N]; b=vals[2*d+N:2*d+2*N]; z=vals[-1]
            assert len(vals)==2*d+2*N+1
            name='far_reflect' if rev else 'far_cover'
            return f'{name} B _ (⟨0,{arr(dfa)},{arr(a)},{arr(b)},{z}⟩ : FAR.Data {d}) (by decide)'
        if typ=='hard':
            ns,arg=x; return f'transport B _ _ (by decide) (BB6.Agent6{ns}.cover {arg+" " if arg else ""}B)'
        raise ValueError(t)
    def walk(t,parent=None,s=None,m=None):
        nonlocal count
        if t[0]!='split':return leaf(t)
        count+=1;i=count;name=f'p{i}'
        defs.append(f'def {name} : PartialMachine := '+('FAR.fromCodes '+arr(ROOT) if parent is None else f'refine {parent} {slot(s)} (some {move(m)})'))
        _,n,s,children=t
        ch=[walk(c,name,s,j) for j,c in enumerate(children)]
        out=[f'theorem close{i} (B : Nat) (hB : {bound} ≤ B) : Cover (WeightedBound B) {name} := by',
             f'  apply branch_cover B {name} {n} {slot(s)} (by omega) (by decide) (by decide) (by decide)',
             '  intro mv','  rcases mv with ⟨w,r,q⟩','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by','    have := q.isLt','    omega','  rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r']
        out+=['  · exact '+x for x in ch];proofs.append('\n'.join(out))
        return f'close{i} B hB'
    walk(tree)
    header='''import C1ZeroLCCover
import C1OneLCSweep
import C1OneLCPair
import C1OneLCTriple
import C1OneLCTwoBlocks
import C1OneLCAlternating
import C1OneLCStack
import C1OneLCCarry
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent6C1OneLCParent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt
open BB6.Agent6C1ZeroLC (branch_cover last_cover)

theorem far_cover {d : Nat} (B : Nat) (p : PartialMachine) (C : FAR.Data d)
    (h : C.fastValid p = true) : Cover (WeightedBound B) p :=
  .leaf _ (fun m hm => weighted_never B m (C.sound p (C.fastValid_sound p h) m hm))

theorem far_reflect {d : Nat} (B : Nat) (p : PartialMachine) (C : FAR.Data d)
    (h : C.fastValid (FAR.reflectPartial p) = true) : Cover (WeightedBound B) p :=
  .leaf _ (fun m hm => weighted_never B m
    (FAR.reflectNever m (C.sound _ (C.fastValid_sound _ h) _ (FAR.reflectCompatible p m hm))))

theorem transport (B : Nat) (p q : PartialMachine)
    (h : ∀ i : Fin 6, ∀ b : Bool, p (i,b) = q (i,b))
    (hc : Cover (WeightedBound B) q) : Cover (WeightedBound B) p := by
  have he : p = q := by funext s; exact h s.1 s.2
  rw [he]; exact hc
'''
    footer=f'\ntheorem cover_oneLC (B : Nat) (hB : {bound} ≤ B) : Cover (WeightedBound B) (FAR.fromCodes {arr(ROOT)}) := close1 B hB\n#print axioms cover_oneLC\nend BB6.Agent6C1OneLCParent\n'
    return header+'\n'+'\n'.join(defs)+'\n\n'+'\n\n'.join(proofs)+'\n'+footer

if __name__=='__main__':
    tree,bound=build()
    dest=Path(__file__).with_name('C1OneLCParent.lean')
    dest.write_text(generate(tree,bound));print(dest)
