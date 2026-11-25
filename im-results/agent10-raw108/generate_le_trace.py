"""Candidate generator; every instruction list is checked by Lean."""
from pathlib import Path
import sys
TABLES=[('false','1RB0RF_1RC0LE_0RD1RB_1LD1RE_0RA1LB_0LB---',192167),('true','1RB1RF_1RC0LE_0RD1RB_1LD1RE_0RA1LB_0RD---',191383)]

def packmoves(t):
    s=t.replace('_','')
    return [s[i:i+3] for i in range(0,36,3)]

def ordinary(tr,z):
    q,l,r=z
    mv=tr[2*q+(l%2)]
    if mv=='---': return None
    w,d,q=mv;w=int(w);q=ord(q)-65
    if d=='R': return (q,r%2+2*(w+2*(l//2)),r//2)
    return (q,l//2,w+2*r)

def alt(k):return (4**k-1)//3

def instructions(table):
    tr=packmoves(table);z=(0,0,0);out=[];pending=0;start=z
    def flush():
        nonlocal pending,start
        if pending:out.append(('ordinary',pending,start,z));pending=0;start=z
    while True:
        q,l,r=z;k=0;typ=None
        if q==1 and l%4==3:
            a=l
            while a%4==3:k+=1;a//=4
            typ='left';end=(q,a,4**k*r+alt(k))
        elif q==1 and l%2==0 and r%4==1:
            a=r
            while a%4==1:k+=1;a//=4
            typ='right';end=(q,2*(4**k*(l//2)+4**k-1),a)
        if k>=2:
            flush();out.append((typ,k,z,end));z=end;start=z
            continue
        nextz=ordinary(tr,z)
        if nextz is None:flush();return out,z
        z=nextz;pending+=1
        if pending>=64:flush()

def literal(z):return '⟨'+','.join(map(str,z))+'⟩'
def generate(root):
    root=Path(root);root.mkdir(exist_ok=True)
    head='import Raw108LEFastCore\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace BB6.Agent10Raw108LEFast\nopen BB6Coverage BB6Coverage.Agent13PackedZipper\n'
    tail='\nend BB6.Agent10Raw108LEFast\n'
    proofs=[]
    for v,table,expected in TABLES:
        instructions_,end=instructions(table)
        assert end[0]==5 and end[1]%2==1
        cost=lambda i: i[1]*(1 if i[0]=='ordinary' else 2)
        assert sum(map(cost,instructions_))==expected
        groups=[instructions_[i:i+32] for i in range(0,len(instructions_),32)]
        name='A' if v=='false' else 'B';lines=[];ns=[];starts=[];ends=[]
        for j,g in enumerate(groups):
            n=sum(map(cost,g));a=g[0][2];b=g[-1][3]
            assert all(x[3]==y[2] for x,y in zip(g,g[1:]))
            assert not ends or ends[-1]==a
            starts.append(a);ends.append(b);ns.append(n)
            ins='['+','.join(f'.{t} {k}' for t,k,_,_ in g)+']'
            lines.append(f'theorem {name}step{j} : runP (table {v}) {n} {literal(a)} = some {literal(b)} :=\n  execList_sound {v} {ins} {literal(a)} {literal(b)} (by decide +kernel)')
        def join(lo,hi):
            if hi-lo==1:return f'{name}step{lo}'
            mid=(lo+hi)//2
            a,b,c=starts[lo],ends[mid-1],ends[hi-1]
            n,k=sum(ns[lo:mid]),sum(ns[mid:hi]);x,y=join(lo,mid),join(mid,hi)
            ident=f'{name}join{lo}_{hi}'
            lines.append(f'theorem {ident} : runP (table {v}) {n+k} {literal(a)} = some {literal(c)} :=\n  joinN (p := table {v}) (n := {n}) (k := {k}) (t := {n+k}) (a := {literal(a)}) (b := {literal(b)}) (c := {literal(c)}) (by decide) {x} {y}')
            return ident
        proof=join(0,len(groups))
        lines.append(f'theorem {name}full : runP (table {v}) {expected} startP = some {literal(end)} :=\n  {proof}')
        lines.append(f'#print axioms {name}full')
        mod=f'Raw108LEFast{name}'
        (root/(mod+'.lean')).write_text(head+'\n\n'.join(lines)+tail)
        proofs.append(mod)
        print(v,expected,'instructions',len(instructions_),'chunks',len(groups),'terminal',end[0],end[1]%2)
    return proofs

if __name__=='__main__':generate(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parent)
