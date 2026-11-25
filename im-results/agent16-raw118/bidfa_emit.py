"""Reproduce a finite fixed-point witness from two supplied deterministic stack summaries."""
from pathlib import Path
from collections import defaultdict,deque
import sys
def witness(table,dl,dr):
    d=[dl,dr];p=table.replace('_','');p=[p[i:i+3] for i in range(0,36,3)]
    edges=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)];seen={(0,0,0,0)};todo=deque(seen)
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
    es=[sorted((dst,b,src) for dst,rs in e.items() for b,src in rs) for e in edges]
    return es,sorted(seen)
def boolstr(x):return str(bool(x)).lower()
def emit(i,table,dl,dr):
    es,states=witness(table,dl,dr)
    out=[f'namespace M{i}', 'def table : PartialMachine := fun s =>', '  match s.1.val,s.2 with']
    p=table.replace('_','')
    for j in range(12):
        m=p[3*j:3*j+3]
        if m!='---':out.append(f'  | {j//2},{boolstr(j%2)} => some (some ⟨{boolstr(m[0]=="1")},{boolstr(m[1]=="R")},{ord(m[2])-65}⟩)')
    out.append('  | _,_ => none')
    out.append('def cert : Cert := ⟨'+str(dl)+','+str(dr)+',')
    for e in es:out.append('  ['+','.join(f'⟨{a},{boolstr(b)},{c}⟩' for a,b,c in e)+'],')
    out.append('  ['+','.join(f'⟨{q},{boolstr(a)},{l},{r}⟩' for q,a,l,r in states)+']⟩')
    out.extend(['theorem checked : check table cert = true := by decide',
        'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := Agent16BiDFA.never table cert checked m hm',
        '#print axioms never',f'end M{i}'])
    return '\n'.join(out),len(states),sum(map(len,es))
EXAMPLES=[
    (361,"1RB---_1RC0LC_0RD---_1LD1RE_0LF0LE_1RF0RB","012134445134","012134445134",64,15),
    (365,"1RB1LD_1RC0RA_0RD---_1LD1RE_0LF0LE_1RF0RB","012134536777718873","012134536777718873",82,18),
    (378,"1RB0LE_1RC1LA_0RD---_1LD1RE_0LF0LE_1RF0RB","012134445134","012134445134",71,15),
    (379,"1RB1LD_1RC1LA_0RD---_1LD1RE_0LF0LE_1RF0RB","012134445134","012134445134",71,15),
    (387,"1RB---_1RC1LD_0RD---_1LD1RE_0LF0LE_1RF0RB","012134445134","012134445134",64,15),
    (1967,"1RB---_1RC1LF_0RD0RF_1LD1RE_1LA0LE_1LB0RC","01234563744389887443","01234567454487239455",73,22),
]
if __name__=='__main__':
    print('import BiDFA\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6Coverage.Agent16BiDFA.Raw118\nopen BB6Coverage Agent16BiDFA')
    for i,p,l,r,n,e in EXAMPLES:
        code,nn,ee=emit(i,p,[int(x,36) for x in l],[int(x,36) for x in r]);assert (nn,ee)==(n,e);print(code)
    print('end BB6Coverage.Agent16BiDFA.Raw118')
