"""Decode compact exact witnesses and emit kernel-checked TwoSidedAutomata source."""
from pathlib import Path
from collections import defaultdict
import base64,lzma,hashlib,json,sys
HERE=Path(__file__).resolve().parent
A='BB6.Agent4Automata'

def load(name,sha):
    raw=lzma.decompress(base64.b64decode((HERE/(name+'.xz.b64')).read_text()))
    assert hashlib.sha256(raw).hexdigest()==sha
    return raw

def parse(t):
    t=t.replace('_','');return tuple(t[i:i+3] for i in range(0,36,3))

def replay(p,ds,cap=150000):
    T=[[0],[0]];ids=[{0:0},{0:0}];D=[{},{}];E=[defaultdict(set),defaultdict(set)];wait=[defaultdict(list),defaultdict(list)]
    for e in E:e[0].add((0,0))
    seen={(0,0,0,0)};todo=list(seen)
    def add(z):
        if z not in seen:
            assert p[2*z[0]+z[1]]!='---'
            seen.add(z);todo.append(z);assert len(todo)<=cap
    def pop(z,e,j):
        q,a,l,r=z;b,k=e;m=p[2*q+a];s=ord(m[2])-65
        add((s,b,j,k) if m[1]=='R' else (s,b,k,j))
    for z in todo:
        q,a,l,r=z;m=p[2*q+a];assert m!='---';w=int(m[0]);d=int(m[1]=='L');x=(l,r)[d];y=(l,r)[1-d]
        if (x,w) not in D[d]:
            state=ds[d][2*T[d][x]+w]
            if state not in ids[d]:ids[d][state]=len(T[d]);T[d].append(state)
            D[d][x,w]=ids[d][state]
        j=D[d][x,w];e=(w,x)
        if e not in E[d][j]:
            E[d][j].add(e)
            for zz,k in wait[d][j]:pop(zz,e,k)
        wait[1-d][y].append((z,j))
        for e in E[1-d][y]:pop(z,e,j)
    return True,len(seen),E,seen,D,T

def trie(xs):
    if not xs:return '.empty'
    if xs==[0]:return '.leaf'
    return '(.branch '+trie([x//2 for x in xs if x%2==0])+' '+trie([x//2 for x in xs if x%2]) + ')'

def emit(i,t,dls,drs,n,compressor=None):
    p=parse(t);ok,n2,E,S,D,T=replay(p,[dls,drs]);assert ok and n2==n,(i,n,n2)
    if compressor is not None:ok,n2,E,S,D,T=compressor(p,(ok,n2,E,S,D,T))
    bit=lambda x:str(bool(x)).lower()
    def stack(d):
        es=','.join('['+','.join(f'({bit(b)},{j})' for b,j in sorted(E[d][k]))+']' for k in range(len(T[d])))
        ps=','.join(f'({D[d].get((k,0),0)},{D[d].get((k,1),0)})' for k in range(len(T[d])))
        return f'⟨#[{es}],#[{ps}]⟩'
    rows=[trie(sorted(r+len(T[1])*l for q,a,l,r in S if 2*q+a==j)) for j in range(12)]
    codes=[24 if s=='---' else 4*(ord(s[2])-65)+2*int(s[0])+int(s[1]=='R') for s in p]
    lines=[f'namespace M{i}',f'def table : PartialMachine := FAR.fromCodes {codes}',f'def cert : {A}.Cert := ⟨{stack(0)},{stack(1)},#[{",".join(rows)}]⟩']
    for j in range(12):
        q,a=j//2,bit(j%2)
        lines.append(f'theorem row{j} : ({A}.row cert ({q}:Fin 6) {a}).all (fun i => {A}.stateStepOK table cert ({q}:Fin 6) {a} (i/cert.right.edges.size) (i%cert.right.edges.size)) = true := by decide')
    lines.append(f'theorem rows_checked : (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a => ({A}.row cert q a).all (fun i => {A}.stateStepOK table cert q a (i/cert.right.edges.size) (i%cert.right.edges.size)))) = true := by\n  simp [BB6.Agent1NGram.bits,List.finRange,'+','.join(f'row{j}' for j in range(12))+']')
    lines.append(f'theorem checked : {A}.check table cert = true := by\n  unfold {A}.check\n  rw [rows_checked]\n  rfl')
    lines.append(f'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := {A}.never table cert checked m hm\n#print axioms never\nend M{i}')
    return '\n'.join(lines)

def generate(rows,out,stem='Raw36D112Learn',chunk=6,compressor=None):
    out=Path(out);out.mkdir(exist_ok=True,parents=True);mapping={}
    for j in range(0,len(rows),chunk):
        mod=stem+f'{j//chunk:02}';ns='BB6.Agent18'+mod;lines=['import TwoSidedAutomata','import FARCheck','set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage']
        for i,t,n,dl,dr in rows[j:j+chunk]:
            lines.append(emit(i,t,dl,dr,n,compressor));mapping[t]=(mod,f'{ns}.M{i}')
        lines.append('end '+ns);(out/(mod+'.lean')).write_text('\n'.join(lines)+'\n')
    return mapping

if __name__=='__main__':
    rows=json.loads(load('learned.json','0da94c68329f654db1b5c0195a670c2ee58031ef716e23dba5667a432c14521a'))
    old=load('remaining74.txt','d60bcc1439f1a933e2fbbf5677c3771eb834ab8a53e297f8d4985f7afc601340').decode().splitlines()
    new=load('remaining48.txt','e5d19697d18d57280ff8547f3191caa7216f58de9a80742062e13aaa6b41e80a').decode().splitlines()
    assert len(old)==74 and len(new)==48 and len(rows)==22
    assert all(old[i]==t for i,t,*_ in rows)
    assert set(old)-{t for _,t,*_ in rows}-{old[i] for i in [22,71,72,73]}==set(new)
    out=Path(sys.argv[1]);generate(rows,out)
    (out/'remaining74.txt').write_text('\n'.join(old)+'\n')
    (out/'remaining48.txt').write_text('\n'.join(new)+'\n')
    print('Generated 22 exact certificates and exact 48-machine residual.')
