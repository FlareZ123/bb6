"""Reproduce and generate the raw124/F1=0LF/F0=1RB weighted audit.
Run from the raw124 directory. The search is untrusted; Lean checks every leaf.
"""
import json
import subprocess
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import sys

ROOT = Path(__file__).resolve().parent
PARENT = '1RB---_1RC---_0RD---_1LD1RE_---1LF_1RB0LF'
BOUND = 1088
MOVES = [w+d+q for w,d,q in product('01','LR','ABCDEF')]
PROVEN = {
    '1RB0LE_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF': ('Raw124ZeroLFHard0', 'p0', 'neverHard0'),
    '1RB---_1RC1RF_0RD0RB_1LD1RE_0RA1LF_1RB0LF': ('Raw124ZeroLFHard1', 'p1', 'neverHard1'),
    '1RB---_1RC1RF_0RD0RB_1LD1RE_1RA1LF_1RB0LF': ('Raw124ZeroLFHard2', 'p2', 'neverHard2'),
    '1RB---_1RC1RA_0RD0RE_1LD1RE_0RB1LF_1RB0LF': ('Raw124ZeroLFHard3', 'p3', 'neverHard3'),
    '1RB0RD_1RC---_0RD1LA_1LD1RE_1RB1LF_1RB0LF': ('Raw124ZeroLFPairReturn', 'p4', 'neverHard4'),
    '1RB0RE_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF': ('Raw124ZeroLFBlockGrowth', 'p1539', 'never1539'),
    '1RB1RF_1RC1RA_0RD0RB_1LD1RE_---1LF_1RB0LF': ('Raw124ZeroLFBlockGrowth', 'p1547', 'never1547'),
}

def parse(s):
    s=s.replace('_',''); assert len(s)==36
    return tuple(s[i:i+3] for i in range(0,36,3))

def show(p): return '_'.join(''.join(p[i:i+2]) for i in range(0,12,2))
def slot(s): return f'({s//2},{str(bool(s%2)).lower()})'
def move(a): return f'⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩'
def masks(p,rev,dfa):
    assert len(dfa)>=2 and len(dfa)%2==0 and dfa[0]==0
    d=len(dfa)//2; N=6*d+1; H=N-1; halt=1<<H
    T=[0]*(2*N); T[H]=T[N+H]=halt; rules=[]
    for l,q,a in product(range(d),range(6),range(2)):
        mv=p[2*q+a]; dst=a*N+6*l+q
        if mv=='---': T[dst]=halt; continue
        w=int(mv[0]); r=int(mv[1]=='R'); nxt=ord(mv[2])-65
        if r!=rev: T[dst]=1<<(6*dfa[2*l+w]+nxt)
        else:
            for j,b in product(range(d),range(2)):
                if dfa[2*j+b]==l: rules.append((dst,b*N+6*j+nxt,w*N))
    while True:
        z=halt
        while True:
            zz=z
            for j in range(N):
                if T[j]&z: z|=1<<j
            if z==zz: break
        assert not z&1,(show(p),dfa)
        changed=False
        for dst,src,off in rules:
            v=T[dst]; bits=T[src]
            while bits:
                b=bits&-bits; v|=T[off+b.bit_length()-1]; bits^=b
            if v!=T[dst]: T[dst]=v; changed=True
        if not changed: return d,dfa,T[:N],T[N:],z

def main():
    prefix=ROOT/'child-0lf-1rb'
    subprocess.run(['g++','-std=c++20','-O3',str(ROOT/'fast_partition.cpp'),'-o',str(ROOT/'fast_partition')],check=True)
    subprocess.run([str(ROOT/'fast_partition'),PARENT,'3000','32',str(prefix)],check=True)
    rawtree=prefix.with_suffix('.json').read_bytes(); rawopen=prefix.with_suffix('.open').read_bytes()
    tree=json.loads(rawtree); opens=rawopen.decode().splitlines()
    assert len(opens)==len(set(opens))==60
    far_src=ROOT.parent/'agent11-tnf-raw86'/'search.cpp'
    if not far_src.exists(): far_src=ROOT/'search.cpp'
    subprocess.run(['g++','-std=c++20','-O3',str(far_src),'-o',str(ROOT/'search-0lf-1rb')],check=True)
    result=subprocess.run([str(ROOT/'search-0lf-1rb'),'6'],input=''.join(f'{i} {p.replace("_","")}\n' for i,p in enumerate(opens)),text=True,stdout=subprocess.PIPE,check=True)
    far={}
    for row in result.stdout.splitlines():
        i,packed=row.split();p=opens[int(i)];assert p not in far
        far[p]=(int(packed[0]),list(map(int,packed[1:])))
    assert len(far)==53 and set(far).isdisjoint(PROVEN) and set(far)|set(PROVEN)==set(opens)
    # Preserve the machine-keyed witnesses and hashes rather than only numeric IDs.
    records={'parent':PARENT,'bound':BOUND,'cap':3000,'lookback':32,
             'tree_sha256':hashlib.sha256(rawtree).hexdigest(),
             'open_sha256':hashlib.sha256(rawopen).hexdigest(),
             'far':far,'proven':PROVEN}
    (ROOT/'child-0lf-1rb-witnesses.json').write_text(json.dumps(records,indent=2)+'\n')
    stats=Counter()
    def build(node,p):
        tag,*v=node; stats[tag]+=1
        if tag=='open':
            code=v[0];assert code==show(p)
            if code in PROVEN:
                mod,pname,proof=PROVEN[code]
                ns='BB6.Agent2'+mod.removeprefix('Raw124')
                # Existing proof namespaces include Raw124 after Agent2.
                ns='BB6.Agent2'+mod
                return f'.proven {ns}.{pname} {ns}.{proof}'
            rev,dfa=far[code];d,D,L,R,z=masks(p,rev,dfa)
            return f'.far {str(bool(rev)).lower()} {d} ⟨0,{D},{L},{R},{z}⟩'
        if tag=='cycle':
            e,k,r,h=v;return f'.cycle {e} {k} {str(bool(r)).lower()} ({h})'
        if tag=='last':
            n,s=v;return f'.last {n} {slot(s)}'
        assert tag=='split'
        n,s,kids=v;assert len(kids)==24 and p[s]=='---'
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(build(k,p[:s]+(mv,)+p[s+1:]) for k,mv in zip(kids,MOVES))+'])'
    imports=['ThreeHoleAudit']+list(dict.fromkeys(v[0] for v in PROVEN.values()))
    header=''.join(f'import {m}\n' for m in imports)+f'''
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent2Raw124ZeroLF1RB
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole
abbrev p124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev pBranch : PartialMachine := refine p124 (5,true) (some ⟨false,false,5⟩)
abbrev pChild : PartialMachine := refine pBranch (5,false) (some ⟨true,true,1⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem pChild_root : pChild initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pChild_nohalt : weightedTNFNoAssignedHalt pChild :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt)
'''
    tag,n,s,kids=tree; assert tag=='split' and len(kids)==24
    stats['split']+=1
    p=parse(PARENT);assert p[s]=='---'
    body=header
    for i,(k,mv) in enumerate(zip(kids,MOVES)):
        body+=f'\ndef kid{i:02} : Audit := {build(k,p[:s]+(mv,)+p[s+1:])}\n'
        body+=f'theorem check{i:02} : check {BOUND} (refine pChild {slot(s)} (some {move(mv)})) kid{i:02} = true := by decide\n'
    assert stats==Counter(open=60,cycle=1379,last=287,split=75),stats
    body+='\ndef kids : Move → Audit := byMove ['+','.join(f'kid{i:02}' for i in range(24))+']\n'
    body+=f'''theorem kids_checked (mv : Move) : check {BOUND} (refine pChild {slot(s)} (some mv)) (kids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''
    body+='\n'.join(f'  · exact check{12*w+6*r+q:02}' for q,w,r in product(range(6),range(2),range(2)))+'\n'
    body+=f'''
def tree : Audit := .split {n} {slot(s)} kids
theorem tree_checked : check {BOUND} pChild tree = true := by
  change (queryOK {BOUND} pChild {n} {slot(s)} && allMoves (fun mv => check {BOUND} (refine pChild {slot(s)} (some mv)) (kids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨by decide,allMoves_of _ kids_checked⟩
noncomputable def certificate : WeightedTNFCertificate {BOUND} pChild 6 :=
  certified {BOUND} pChild tree pChild_root pChild_nohalt tree_checked
theorem bound_all : ∀ m, compatible pChild m → WeightedBound {BOUND} m := certificate.sound
#print axioms tree_checked
#print axioms bound_all
end BB6.Agent2Raw124ZeroLF1RB
'''
    (ROOT/'Raw124ZeroLF1RB.lean').write_text(body)
    print('partition',stats,'bound',BOUND,'FAR',len(far),'proven',len(PROVEN),'bytes',len(body.encode()))

if __name__=='__main__':main()
