"""Emit FastBiDFA proof data from compact deterministic stack summaries.
The fixed-point discovery is untrusted; Lean checks each discovered edge/row.
"""
from collections import defaultdict,deque
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def witness(table,dl,dr):
    d=[dl,dr]; p=table.replace('_',''); p=[p[i:i+3] for i in range(0,36,3)]
    edges=[defaultdict(set),defaultdict(set)]; wait=[defaultdict(list),defaultdict(list)]
    seen={(0,0,0,0)};todo=deque(seen)
    for e in edges:e[0].add((0,0))
    def add(q,a,l,r):
        s=(q,a,l,r)
        if s not in seen:seen.add(s);todo.append(s)
    def pop(s,b,src):
        q,a,l,r=s;m=p[2*q+a];w,drct,n=int(m[0]),m[1],ord(m[2])-65
        if drct=='R':add(n,b,d[0][2*l+w],src)
        else:add(n,b,src,d[1][2*r+w])
    while todo:
        s=todo.popleft();q,a,l,r=s;m=p[2*q+a]
        if m=='---':raise ValueError('reaches unknown')
        w,drct,n=int(m[0]),m[1],ord(m[2])-65
        side=int(drct=='R');dest=d[1-side][2*(l if side else r)+w];old=l if side else r
        e=(w,old)
        if e not in edges[1-side][dest]:
            edges[1-side][dest].add(e)
            for st in wait[1-side][dest]:pop(st,*e)
        x=r if side else l
        wait[side][x].append(s)
        for b,y in edges[side][x]:pop(s,b,y)
    return edges,sorted(seen)

def trie(xs):
    xs=set(xs)
    if not xs:return '.empty'
    if xs=={0}:return '.leaf'
    return '(.branch '+trie(x//2 for x in xs if x%2==0)+' '+trie(x//2 for x in xs if x%2)+')'

def arr(xs):return '#['+','.join(xs)+']'
def bs(b):return str(bool(b)).lower()
def emit(i,table,dl,dr,expected):
    es,S=witness(table,dl,dr)
    n=len(S);e=sum(len(v) for side in es for v in side.values())
    assert (n,e)==tuple(expected),(i,n,e)
    out=[f'namespace M{i}','def table : PartialMachine := fun s =>','  match s.1.val,s.2 with']
    p=table.replace('_','')
    for j in range(12):
        m=p[3*j:3*j+3]
        if m!='---':out.append(f'  | {j//2},{bs(j%2)} => some (some ⟨{bs(m[0]=="1")},{bs(m[1]=="R")},{ord(m[2])-65}⟩)')
    out.append('  | _,_ => none')
    for name,d,esd in zip(['leftGraph','rightGraph'],[dl,dr],es):
        pred=arr('['+','.join(f'({bs(b)},{y})' for b,y in sorted(esd[x]))+']' for x in range(len(d)//2))
        out.append(f'def {name} : Graph := ⟨{arr(map(str,d))},{pred}⟩')
    rs=defaultdict(set)
    for q,a,l,r in S:rs[q*2+a,l].add(r)
    for s in range(12):
        out.append(f'def row{s} : Array Trie := '+arr(trie(rs[s,l]) for l in range(len(dl)//2)))
    out.append('def cert : Cert := ⟨leftGraph,rightGraph,'+arr(f'row{s}' for s in range(12))+'⟩')
    for s in range(12):
        out.append(f'theorem row_checked{s} : rowCheck table cert {s//2} {bs(s%2)} = true := by decide')
    out.extend(['theorem checked : check table cert = true := by',
        '  apply check_of_rows',
        '  · decide',
        '  · decide',
        '  · decide',
        '  · intro q a',
        '    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega',
        '    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases a',
        *[f'    · exact row_checked{s}' for s in range(12)],
        'theorem live_all (n : Nat) : ∃ z, run0 table n ⟨0,[],[]⟩ = some z := by',
        '  obtain ⟨z,hz,_⟩ := live checked (inv_start checked) n',
        '  exact ⟨z,hz⟩',
        'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := BB6.Agent32FastBiDFA.never table cert checked m hm',
        '#print axioms never',
        '#print axioms live_all',
        f'end M{i}'])
    return '\n'.join(out)

def main():
    spec=json.loads((ROOT/'rungram_cert.json').read_text())
    out=['import FastBiDFA','set_option maxRecDepth 100000','set_option maxHeartbeats 0','namespace BB6.Agent32Raw59LB1RunGram','open BB6Coverage BB6Coverage.Agent31Pump BB6.Agent1NGram BB6.Agent32FastBiDFA']
    for i,t in spec.items():out.append(emit(i,t['table'],*t['dfa'],[t['states'],t['edges']]))
    out.append('end BB6.Agent32Raw59LB1RunGram')
    (ROOT/'Raw59LB1RunGram.lean').write_text('\n'.join(out)+'\n')
if __name__=='__main__':main()
