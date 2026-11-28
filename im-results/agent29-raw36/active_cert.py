"""Replay active inverse-stack candidates and emit source-checked Lean certificates."""
from collections import defaultdict
from pathlib import Path
import json

def mask(n): return (1<<n)-1

def push(p,x,b):
    kind,k,c,m,base=p
    if kind==0:return ((x<<1)|b)&mask(k)
    if kind==1:
        sh=(c+m-1).bit_length();dm=mask(sh);v=x>>1;j=v&dm
        if (x&1)!=b:v=((v<<sh)|1)&mask(sh*k)
        elif j:v=(v&~dm)|(c if j+1==c+m else j+1)
        return (v<<1)|b
    if kind==2:return ((((x>>k)*base+b)%m)<<k)|(((x<<1)|b)&mask(k))
    assert kind==3
    v=x&mask(k);r=x>>k;old=v>>(k-1) if k else b;pm=mask(c)
    if base==0:
        if not r:r=pm+1 if old else 0
        else:
            r-=1;r=((r<<1)|(r>>(c-1)))&pm
            if not old:r&=m
            r+=1
    else:
        prior=r&1;r>>=1;r=((r<<1)|(r>>(c-1)))&pm
        if prior!=old:r&=m
        r=(r<<1)|old
    return (r<<k)|(((v<<1)|b)&mask(k))

def replay(table,lp,rp,expected):
    t=table.replace('_','');moves=[t[i:i+3] for i in range(0,36,3)];params=[lp,rp]
    T=[[mask(p[2])<<(p[1]+1) if p[0]==3 and p[4]==1 else 0] for p in params]
    ids=[{v[0]:0} for v in T];E=[defaultdict(set),defaultdict(set)];D=[{},{}];W=[defaultdict(list),defaultdict(list)]
    for e in E:e[0].add((0,0))
    rows=[(0,0,0,0)];seen=set(rows)
    def add(z):
        assert moves[z[0]*2+z[1]]!='---',(table,z)
        if z not in seen:seen.add(z);rows.append(z)
        assert len(rows)<=expected[0],(table,'row overflow')
    def pop(z,e,j):
        q,a,l,r=z;mv=moves[2*q+a];n=ord(mv[2])-65
        add((n,e[0],j,e[1]) if mv[1]=='R' else (n,e[0],e[1],j))
    for z in rows:
        q,a,l,r=z;mv=moves[q*2+a];w=int(mv[0]);d=int(mv[1]=='L');x=(l,r)[d];y=(l,r)[1-d]
        if (x,w) not in D[d]:
            v=push(params[d],T[d][x],w)
            if v not in ids[d]:ids[d][v]=len(T[d]);T[d].append(v)
            D[d][x,w]=ids[d][v]
        j=D[d][x,w];e=(w,x)
        if e not in E[d][j]:
            E[d][j].add(e)
            for zz,k in W[d][j]:pop(zz,e,k)
        W[1-d][y].append((z,j))
        for e in sorted(E[1-d][y]):pop(z,e,j)
    assert [len(rows),len(T[0]),len(T[1])]==list(expected),(table,expected,len(rows),list(map(len,T)))
    return T,E,D,rows

def trie(xs):
    if not xs:return '.empty'
    if xs==[0]:return '.leaf'
    return '(.branch '+trie([x//2 for x in xs if x%2==0])+' '+trie([x//2 for x in xs if x%2])+')'

def emit(i,t,lp,rp,n,l,r):
    T,E,D,S=replay(t,lp,rp,[n,l,r]);p=t.replace('_','');p=[p[j:j+3] for j in range(0,36,3)]
    bit=lambda b:str(bool(b)).lower();A='BB6.Agent4Automata'
    def stack(d):
        es=','.join('['+','.join(f'({bit(b)},{j})' for b,j in sorted(E[d][k]))+']' for k in range(len(T[d])))
        ps=','.join(f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(len(T[d])))
        return f'⟨#[{es}],#[{ps}]⟩'
    rows=[trie(sorted(rr+len(T[1])*ll for q,a,ll,rr in S if 2*q+a==j)) for j in range(12)]
    lines=[f'namespace M{i}','def table : PartialMachine := fun s => match s.1.val,s.2 with']
    for j,a in enumerate(p):
        if a!='---':lines.append(f'  | {j//2},{bit(j%2)} => some (some ⟨{bit(a[0]=="1")},{bit(a[1]=="R")},{ord(a[2])-65}⟩)')
    lines+=['  | _,_ => none',f'def cert : {A}.Cert := ⟨{stack(0)},{stack(1)},#[{",".join(rows)}]⟩']
    for j in range(12):
        q,a=j//2,bit(j%2)
        lines.append(f'theorem row{j} : ({A}.row cert ({q}:Fin 6) {a}).all (fun i => {A}.stateStepOK table cert ({q}:Fin 6) {a} (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by decide')
    lines.append(f'theorem rows_checked : (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a => ({A}.row cert q a).all (fun i => {A}.stateStepOK table cert q a (i/cert.right.edges.size) (i%cert.right.edges.size)))) = true := by\n  simp [BB6.Agent1NGram.bits,List.finRange,'+','.join(f'row{j}' for j in range(12))+']')
    lines.append(f'theorem checked : {A}.check table cert = true := by\n  unfold {A}.check\n  rw [rows_checked]\n  rfl')
    lines.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := {A}.never table cert checked m hm\n#print axioms never\nend M{i}')
    return '\n'.join(lines)

def generate(records,out,stem):
    out=Path(out);out.mkdir(parents=True,exist_ok=True);result={}
    for k in range(0,len(records),8):
        module=f'{stem}Active{k//8:02d}';ns='BB6.Agent29'+module
        lines=['import TwoSidedAutomata','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage']
        for i,row in enumerate(records[k:k+8],k):
            t,*v=row;lines.append(emit(i,t,*v));result[t]=(module,f'{ns}.M{i}')
        lines.append(f'end {ns}');(out/(module+'.lean')).write_text('\n'.join(lines)+'\n')
    return result

def read_results(path):
    for line in Path(path).read_text().splitlines():
        i,t,*v=line.split()
        if v[0]!='MISS':yield int(i),[t,json.loads(v[0]),json.loads(v[1]),*map(int,v[2:])]

if __name__=='__main__':
    import sys
    generate([v for i,v in read_results(sys.argv[1])],sys.argv[2],sys.argv[3])
