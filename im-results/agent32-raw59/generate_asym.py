"""Deterministic fixed-window certificates; candidate engine is untrusted."""
from pathlib import Path
import subprocess, tempfile, sys
BASE='BB6.Agent32AsymNGram'
ROOT=Path(__file__).resolve().parent

def emit(root, name, table, line, routed=False):
    l,r,n,L,R,S=line.split();l,r,n=map(int,(l,r,n));size=1<<(l+r)
    def edges(s):
        return sorted(2*int(x)+b for x,v in (a.split(':') for a in s.rstrip(',').split(',')) for b in (0,1) if int(v)&(1<<b))
    L,R=edges(L),edges(R)
    rows=[[] for _ in range(12)]
    for j in map(int,S.rstrip(',').split(',')):
        rows[j//size].append(j%size)
    assert sum(map(len,rows))==n
    nodes={};defs=[]
    def trie(xs):
        if not xs:return '.empty'
        if xs==[0]:return '.leaf'
        key=(trie([x//2 for x in xs if x%2==0]),trie([x//2 for x in xs if x%2==1]))
        if key not in nodes:
            nodes[key]=f't{len(defs)}'
            defs.append(f'def {nodes[key]} : Trie := .branch {key[0]} {key[1]}')
        return nodes[key]
    lt,rt=trie(L),trie(R);ts=[trie(row) for row in rows]
    ns=f'{BASE}.{name}'
    def write(mod,imports,body):
        (root/(mod+'.lean')).write_text('\n'.join([*(f'import {x}' for x in imports),'set_option maxRecDepth 100000','set_option maxHeartbeats 0',f'namespace {ns}','open BB6Coverage BB6.Agent1NGram',*body,f'end {ns}','']))
    p=table.replace('_','');moves=[]
    for j in range(12):
        a=p[j*3:j*3+3]
        v='none' if a=='---' else f'some (some ⟨{str(a[0]=="1").lower()},{str(a[1]=="R").lower()},{ord(a[2])-65}⟩)'
        moves.append(f'  | {j//2},{str(bool(j%2)).lower()} => {v}')
    write(name+'Data',['AsymNGram'],[*defs,'def table : PartialMachine := fun s => match s.1.val,s.2 with',*moves,'  | _,_ => none',f'def cert : {BASE}.Cert := ⟨{l-1},{r-1},{lt},{rt},#[{",".join(ts)}]⟩'])
    if routed:
        route='BB6.Agent32TrieRoute'
        modules=[]
        for j in range(12):
            q,a=j//2,str(bool(j%2)).lower();mod=name+f'Row{j:02}';modules.append(mod)
            write(mod,[name+'Data','TrieRoute'],[f'theorem row{j:02} : {route}.routeRow table cert {q} {a} = true := by decide'])
        write(name,modules,[f'theorem allRows (q : Fin 6) (a : Bool) : {route}.routeRow table cert q a = true := by','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases a',*(f'  · exact row{j:02}' for j in range(12)),f'theorem checked : {BASE}.check table cert = true :=',f'  {route}.route_check_of_rows (by decide) (by decide) (by decide) allRows','theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  {BASE}.never table cert checked m hm','#print axioms never'])
    else:
        modules=[]
        for j in range(12):
            q,a=j//2,str(bool(j%2)).lower();mod=name+f'Row{j:02}';modules.append(mod)
            write(mod,[name+'Data'],[f'theorem row{j:02} : ({BASE}.row cert {q} {a}).all (fun i =>',f'    {BASE}.stateStepOK table cert {q} {a} (i/2^(cert.nR+1)) (i%2^(cert.nR+1))) = true := by decide'])
        write(name,modules,[f'theorem allRows (q : Fin 6) (a : Bool) : ({BASE}.row cert q a).all (fun i =>',f'    {BASE}.stateStepOK table cert q a (i/2^(cert.nR+1)) (i%2^(cert.nR+1))) = true := by','  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega','  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl','  all_goals cases a',*(f'  · exact row{j:02}' for j in range(12)),f'theorem checked : {BASE}.check table cert = true :=',f'  {BASE}.check_of_rows (by decide) (by decide) (by decide) allRows', 'theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=',f'  {BASE}.never table cert checked m hm','#print axioms never'])
    print(name,l,r,n,len(L),len(R),len(defs),flush=True)
    return name

def generate(out,branch=None):
    out.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory() as d:
        exe=Path(d)/'ngram_asym'
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'ngram_asym.cpp'),'-o',str(exe)],check=True)
        entries=[ln.split() for ln in (ROOT/'asym_manifest.txt').read_text().splitlines() if ln.strip()]
        if branch is not None:entries=[e for e in entries if e[0]==branch]
        names=[]
        for b,i,t,l,r,n,eL,eR in entries:
            data=subprocess.check_output([str(exe)],input=f'{i} {t} {l} {r}\n',text=True).strip().split(maxsplit=1)
            assert data[0]==i
            actual=data[1].split();assert actual[:3]==[l,r,n]
            assert len(actual[3].rstrip(',').split(','))==int(eL)
            assert len(actual[4].rstrip(',').split(','))==int(eR)
            names.append(emit(out,f'Raw59Asym{b}M{i}',t,data[1]))
        assert names
        (out/('Raw59Asym'+(branch or 'All')+'.lean')).write_text(''.join(f'import {name}\n' for name in names))
if __name__=='__main__':generate(Path(sys.argv[1]),sys.argv[2] if len(sys.argv)>2 else None)
