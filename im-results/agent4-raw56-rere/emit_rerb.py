#!/usr/bin/env python3
"""Emit kernel-checkable Raw56 E1=1RE/E0=0RB five-hole child certificates from exact cut output.
Input: tree JSON, DFS open list, FAR witness bank, and five run-language automata proofs.
The candidate tree and FAR search remain untrusted; original canonicalCheck
and canonicalSound establish the universal result. No native_decide.
"""
import argparse
import json
from pathlib import Path

NS = 'BB6.Agent4Raw56.RERB'
MOD = 'Raw56RERB'
PARENT = '1RB---_1RC---_0RD---_1LD1LE_0RB1RE_------'
BOUND = 7014
PROOF = 'BB6.Agent4Raw56RERBAutomata'
PROVEN = {
    '1RB1LC_1RC0LA_0RD0LF_1LD1LE_0RB1RE_---0LB': '0',
    '1RB---_1RC0LA_0RD0LF_1LD1LE_0RB1RE_1LB1LC': '1',
    '1RB0LF_1RC1LA_0RD0RE_1LD1LE_0RB1RE_---0LD': '2',
    '1RB1LF_1RC1LA_0RD---_1LD1LE_0RB1RE_0RA0LF': '3',
    '1RB1LF_1RC1LA_0RD---_1LD1LE_0RB1RE_0RE0LF': '4',
}
HEAD = f'''set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier
'''

def parse(s):
    s = s.replace('_', '')
    assert len(s) == 36
    return [s[i:i+3] for i in range(0, 36, 3)]

def show(p):
    return '_'.join(''.join(p[i:i+2]) for i in range(0, 12, 2))

def move(i):
    return f'{i//12}{"R" if i%12>=6 else "L"}{chr(65+i%6)}'

def mv(i):
    return f'⟨{str(bool(i//12)).lower()},{str(i%12>=6).lower()},{i%6}⟩'

def slot(i):
    return f'({i//2},{str(bool(i%2)).lower()})'

def support(p):
    return max([2]+[max(i//2,ord(v[2])-65)+1 for i,v in enumerate(p) if v!='---'])

def far(code,p):
    # Identical finite saturation used by the existing Raw40 certificate emitter.
    rev=int(code[0]); D=[int(x,16) for x in code[1:]]; n=len(D)//2
    N=6*n+1; H=N-1; halt=1<<H; T=[0]*(2*N); T[H]=T[N+H]=halt; rules=[]
    assert len(D)==2*n and all(0<=x<n for x in D)
    for l in range(n):
        for q in range(6):
            for a in range(2):
                m=p[2*q+a]; dst=a*N+6*l+q
                if m=='---': T[dst]=halt; continue
                w,r,k=int(m[0]),m[1]=='R',ord(m[2])-65
                if r!=rev: T[dst]=1<<(6*D[2*l+w]+k)
                else:
                    for j in range(n):
                        for b in range(2):
                            if D[2*j+b]==l: rules.append((dst,b*N+6*j+k,w*N))
    while True:
        z=halt
        while True:
            old=z
            for j in range(N):
                if T[j]&z: z|=1<<j
            assert not z&1,(code,p)
            if old==z: break
        changed=False
        for dst,src,off in rules:
            v=T[dst];bits=T[src]
            while bits:
                k=(bits&-bits).bit_length()-1;v|=T[off+k];bits&=bits-1
            if v!=T[dst]: T[dst]=v;changed=True
        if not changed:
            return f'.far {str(bool(rev)).lower()} {n} ⟨0,{D},{T[:N]},{T[N:]},{z}⟩'

def size(t):
    return 1+sum(map(size,t[3])) if t[0]=='split' else 1

def main():
    ap=argparse.ArgumentParser();ap.add_argument('tree',type=Path);ap.add_argument('opens',type=Path)
    ap.add_argument('bank',type=Path);ap.add_argument('output',type=Path)
    args=ap.parse_args(); out=args.output;out.mkdir(parents=True,exist_ok=True)
    tree=json.loads(args.tree.read_text());rows=args.opens.read_text().splitlines()
    bank={int(i):c for i,c in (x.split() for x in args.bank.read_text().splitlines())}
    assert len(rows)==len(set(rows))
    assert set(PROVEN) <= set(rows), set(PROVEN)-set(rows)
    assert set(bank) | {i for i,s in enumerate(rows) if s in PROVEN} == set(range(len(rows)))
    it=iter(enumerate(rows)); manifest=[]; parent=parse(PARENT); cut=support(parent)
    def emit(mod, imports, body):
        imports=list(dict.fromkeys(imports))
        (out/f'{mod}.lean').write_text(''.join(f'import {x}\n' for x in imports)+HEAD+'\n'.join(body)+f'\nend {NS}\n')
        manifest.append([mod,imports])
    base=['def p : PartialMachine := fun s => match s.1.val,s.2 with']
    for i,v in enumerate(parent):
        if v!='---':base.append(f'  | {i//2},{str(bool(i%2)).lower()} => some (some {mv(int(v[0])*12+6*(v[1]=="R")+ord(v[2])-65)})')
    base+=['  | _,_ => none','theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide',
        '''theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide''',
        f'theorem supported : TNFSupport p {cut} := supportOK_sound _ _ (by decide)']
    emit(MOD+'Base',['Raw40Nores','Raw56RERBAutomata'],base)
    def ordinary(t,p):
        typ=t[0]
        if typ=='cycle':
            assert type(t[3]) is int and t[3] in (0,1)
            return f'.cycle {t[1]} {t[2]} {str(bool(t[3])).lower()} ({t[4]})'
        if typ=='last':return f'.last {t[1]} {slot(t[2])}'
        if typ=='open':
            i,s=next(it);assert s==show(p)==t[1]
            return f'.proven {PROOF}.M{PROVEN[s]}.table {PROOF}.M{PROVEN[s]}.never' if s in PROVEN else far(bank[i],p)
        assert typ=='split' and len(t[3])==24 and p[t[2]]=='---'
        n,s,kids=t[1:]
        return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(ordinary(k,p[:s]+[move(i)]+p[s+1:]) for i,k in enumerate(kids))+'])'
    def gen(t,p,cut):
        if cut==6 or t[0]!='split':return f'.closed ({ordinary(t,p)})'
        n,s,kids=t[1:];assert len(kids)==24 and p[s]=='---'
        return f'.split {n} {slot(s)} (byPartialMove [\n'+',\n'.join(gen(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1)) for i,k in enumerate(kids))+'])'
    cases='''  rcases m with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
'''
    def combine(name,n,s,cut,names):
        assert cut>=5
        lines=[f'def k{name} : Move → PartialAudit := byPartialMove [{",".join("t"+x for x in names)}]',
               f'def t{name} : PartialAudit := .split {n} {slot(s)} k{name}',
               f'theorem q{name} : zipQueryOK {BOUND} p{name} {n} {slot(s)} = true := by decide']
        ck=f'''theorem ck{name} (m : Move) : (if m.next.val ≤ {cut} then canonicalCheck {BOUND} (refine p{name} {slot(s)} (some m)) (max {cut} (m.next.val+1)) (k{name} m) else true) = true := by
'''+cases
        nr=f'''theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = [] := by
  unfold t{name}
  apply noresSplit
  intro m h
'''+cases
        for q in range(6):
            for w in range(2):
                for r in range(2):
                    nm=names[12*w+6*r+q];ck+=f'  · exact c{nm}\n';nr+=f'  · exact nr{nm}\n'
        lines += [ck.rstrip(),f'''theorem c{name} : canonicalCheck {BOUND} p{name} {cut} t{name} = true := by
  simp only [t{name},canonicalCheck,q{name},Bool.true_and]
  exact allMoves_of _ ck{name}''',nr.rstrip()]
        return lines
    def shard(t,p,cut,name,expr,lines):
        lines.append(f'abbrev p{name} := {expr}')
        if size(t)<=96:
            lines += [f'def t{name} : PartialAudit := {gen(t,p,cut)}',
                      f'theorem c{name} : canonicalCheck {BOUND} p{name} {cut} t{name} = true := by decide +kernel',
                      f'theorem nr{name} : canonicalResiduals p{name} {cut} t{name} = [] := by decide +kernel']
            return
        n,s,kids=t[1:];names=[]
        for i,k in enumerate(kids):
            nm=f'{name}_{i:02}';names.append(nm)
            shard(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1),nm,f'refine p{name} {slot(s)} (some {mv(i)})',lines)
        lines.extend(combine(name,n,s,cut,names))
    current=[]; cur_size=0; counter=0; current_name=None
    def new_name():
        nonlocal counter
        counter+=1;return f'{MOD}Part{counter:03}'
    def flush():
        nonlocal current,cur_size,current_name
        if current_name:emit(current_name,[MOD+'Base'],current)
        current=[];cur_size=0;current_name=None
    def visit(t,p,cut,name,expr):
        nonlocal current,cur_size,current_name
        sz=size(t)
        if sz<=600:
            if current_name and cur_size+sz>600:flush()
            if not current_name:current_name=new_name()
            shard(t,p,cut,name,expr,current);cur_size+=sz
            return current_name
        n,s,kids=t[1:];names=[];imports=[]
        for i,k in enumerate(kids):
            nm=f'{name}_{i:02}';names.append(nm)
            imports.append(visit(k,p[:s]+[move(i)]+p[s+1:],max(cut,i%6+1),nm,f'refine ({expr}) {slot(s)} (some {mv(i)})'))
        flush();mod=new_name();emit(mod,imports,[f'abbrev p{name} := {expr}']+combine(name,n,s,cut,names));return mod
    n,s,kids=tree[1:];imports=[];names=[]
    for i,k in enumerate(kids):
        nm=f'_{i:02}';names.append(nm)
        imports.append(visit(k,parent[:s]+[move(i)]+parent[s+1:],max(cut,i%6+1),nm,f'refine p {slot(s)} (some {mv(i)})'))
    flush();assert next(it,None) is None
    end=['abbrev ptop := p']+combine('top',n,s,cut,names)+[f'''theorem all_quotient : ∀ m, TNFQuotientCompatible p m → WeightedBound {BOUND} m := by
  intro m hm
  rcases canonicalSound {BOUND} p {cut} ttop (by decide) supported root nohalt ctop m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [nrtop] at he; contradiction

theorem all : ∀ m, compatible p m → WeightedBound {BOUND} m := by
  intro m hm
  exact all_quotient m (compatible_quotient hm)
#print axioms all_quotient
#print axioms all''']
    emit(MOD+'All',imports,end)
    (out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print('modules',len(manifest),'nodes',size(tree),'open',len(rows))

if __name__=='__main__':main()
