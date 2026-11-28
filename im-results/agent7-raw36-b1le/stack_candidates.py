"""Reconstruct finite active inverse-stack certificates from compact parameters.
All generated certificates are checked by independent TwoSidedAutomata.
"""
from collections import defaultdict
import json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent4-two-sided-automata'))
from quotient import compress

def parameters(v):
    kind,*a=v
    if kind=='n':
        k,n=a; f=lambda x,b: ((x<<1)|b)&((1<<k)-1)
        return [(0,f)]*2,n
    if kind=='r':
        k,c,m,n=a; sh=(c+m-1).bit_length();dm=(1<<sh)-1;mask=(1<<(sh*k))-1
        def f(x,b):
            old=x&1;v=x>>1;j=v&dm
            if old!=b:v=((v<<sh)|1)&mask
            elif j:v=(v&~dm)|(c if j+1==c+m else j+1)
            return (v<<1)|b
        return [(0,f)]*2,n
    if kind=='m':
        k,m,base,n=a;mask=(1<<k)-1
        return [(0,lambda x,b: (((x>>k)*base+b)%m)<<k | (((x&mask)<<1|b)&mask))]*2,n
    if kind=='d':
        return [(0,lambda x,b,D=D:D[2*x+b]) for D in a],None
    if kind=='p':
        k,period,typ,mask0,init,n=a;mask=(1<<k)-1;pm=(1<<period)-1
        def f(x,b):
            v=x&mask; r=x>>k;old=v>>(k-1) if k else b
            if typ==0:
                if r==0:nb=0 if not old else init+1
                else:
                    m=r-1;m=((m<<1)|(m>>(period-1)))&pm
                    if not old:m&=mask0
                    nb=m+1
            else:
                m=r>>1;prior=r&1;m=((m<<1)|(m>>(period-1)))&pm
                if prior!=old:m&=mask0
                nb=(m<<1)|old
            return (nb<<k)|(((v<<1)|b)&mask)
        return [(0 if typ==0 else ((init<<1)<<k),f)]*2,n
    raise ValueError(v)

def replay(p,v):
    params,n=parameters(v);T=[[s] for s,f in params];ids=[{s:0} for s,f in params];D=[{},{}];E=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    for e in E:e[0].add((0,0))
    seen={(0,0,0,0)};todo=list(seen)
    def add(z):
        if z not in seen:
            assert p[2*z[0]+z[1]]!='---',(p,v,z)
            seen.add(z);todo.append(z);assert len(todo)<=150000
    def pop(z,e,j):
        q,a,l,r=z;b,k=e;m=p[2*q+a];s=ord(m[2])-65
        add((s,b,j,k) if m[1]=='R' else (s,b,k,j))
    for z in todo:
        q,a,l,r=z;m=p[2*q+a];assert m!='---';w=int(m[0]);d=int(m[1]=='L');x=(l,r)[d];y=(l,r)[1-d]
        if (x,w) not in D[d]:
            state=params[d][1](T[d][x],w)
            if state not in ids[d]:ids[d][state]=len(T[d]);T[d].append(state)
            D[d][x,w]=ids[d][state]
        j=D[d][x,w];e=(w,x)
        if e not in E[d][j]:
            E[d][j].add(e)
            for zz,k in wait[d][j]:pop(zz,e,k)
        wait[1-d][y].append((z,j))
        for e in E[1-d][y]:pop(z,e,j)
    assert n is None or n==len(seen),(p,v,n,len(seen))
    return True,len(seen),E,seen,D,T

def trie(xs):
    if not xs:return '.empty'
    if xs==[0]:return '.leaf'
    return '(.branch '+trie([x//2 for x in xs if x%2==0])+' '+trie([x//2 for x in xs if x%2==1])+')'

def emit(i,t,v):
    p=[t[j:j+3] for j in range(0,36,3)];ok,n,E,S,D,T=compress(p,replay(p,v));A='BB6.Agent4Automata';bit=lambda b:str(bool(b)).lower()
    def stack(d):
        es=','.join('['+','.join(f'({bit(b)},{j})' for b,j in sorted(E[d][k]))+']' for k in range(len(T[d])))
        ps=','.join(f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(len(T[d])))
        return f'⟨#[{es}],#[{ps}]⟩'
    rows=[trie(sorted(r+len(T[1])*l for q,a,l,r in S if q==j//2 and a==j%2)) for j in range(12)]
    lines=[f'namespace M{i}','def table : PartialMachine := fun s => match s with']
    for j,a in enumerate(p):
        if a!='---':lines.append(f'  | ({j//2},{bit(j%2)}) => some (some ⟨{bit(a[0]=="1")},{bit(a[1]=="R")},{ord(a[2])-65}⟩)')
    lines+=['  | _ => none',f'def cert : {A}.Cert := ⟨{stack(0)},{stack(1)},#[{",".join(rows)}]⟩']
    for j in range(12):
        q,a=j//2,bit(j%2)
        lines.append(f'theorem row{j} : ({A}.row cert ({q}:Fin 6) {a}).all (fun i => {A}.stateStepOK table cert ({q}:Fin 6) {a} (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by decide')
    lines.append(f'theorem rows_checked : (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a => ({A}.row cert q a).all (fun i => {A}.stateStepOK table cert q a (i/cert.right.edges.size) (i%cert.right.edges.size)))) = true := by\n  simp [BB6.Agent1NGram.bits,List.finRange,'+','.join(f'row{j}' for j in range(12))+']')
    lines.append(f'theorem checked : {A}.check table cert = true := by\n  unfold {A}.check\n  rw [rows_checked]\n  rfl')
    lines.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := {A}.never table cert checked m hm\n#print axioms never\nend M{i}')
    return '\n'.join(lines),n,tuple(map(len,T))

def generate(rows,out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True);ns='BB6.Agent7Raw36B1LEAutomata';xs=[(i,t,v) for i,(t,v) in enumerate(rows) if v[0] not in ('f','s')];modules={}
    for j in range(0,len(xs),16):
        name=f'Raw36B116Automata{j//16:02d}';lines=['import TwoSidedAutomata','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage']
        for i,t,v in xs[j:j+16]:
            source,n,shape=emit(i,t,v);lines.append(source);modules[t]=(name,f'{ns}.M{i}');print(i,v[0],n,shape,flush=True)
        lines.append(f'end {ns}');(out/(name+'.lean')).write_text('\n'.join(lines)+'\n')
    return modules

if __name__=='__main__':
    rows=[(t,json.loads(v)) for t,v in (line.split('\t') for line in Path(sys.argv[1]).read_text().splitlines())];generate(rows,sys.argv[2])
