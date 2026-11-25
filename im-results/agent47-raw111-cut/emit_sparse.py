"""Emit source-level sparse n-gram certificates for the last two raw111 leaves."""
from pathlib import Path
import subprocess

TABLES = {
    3: ("1RB---_1RC0LC_0RD0LF_1LD1RE_0RF0RC_1LB0RA",29419,345,1183),
    9: ("1RB0LB_1RC0LA_0RD0RF_1LD1RE_---0RC_1LF1RA",1945,243,315),
}
BASE="BB6.Agent47SparseNGram"

def emit(root, i, table, data):
    k,n,L,R,S=data.split()
    k=int(k); n=int(n); M=1<<k
    assert k==23 and n==TABLES[i][1]
    def edge(s):
        return sorted(2*int(x)+b for x,v in (a.split(":") for a in s.rstrip(",").split(",")) for b in (0,1) if int(v)&(1<<b))
    L,R=edge(L),edge(R)
    assert (len(L),len(R))==TABLES[i][2:]
    rows=[[] for _ in range(12)]
    for j in map(int,S.rstrip(",").split(",")):
        rows[j//(M*M)].append(j%(M*M))
    assert sum(map(len,rows))==n
    nodes={}; defs=[]
    def trie(xs):
        if not xs:return ".empty"
        if xs==[0]:return ".leaf"
        a=trie([x//2 for x in xs if x%2==0])
        b=trie([x//2 for x in xs if x%2==1])
        key=(a,b)
        if key not in nodes:
            name=f"t{len(defs)}"
            nodes[key]=name
            defs.append(f"def {name} : Trie := .branch {a} {b}")
        return nodes[key]
    lt,rt=trie(L),trie(R)
    ts=[trie(r) for r in rows]
    name=f"Raw111Sparse{i}"
    ns=f"{BASE}.{name}"
    def write(mod,imports,body):
        (root/(mod+".lean")).write_text("\n".join([*(f"import {x}" for x in imports),"set_option maxRecDepth 100000","set_option maxHeartbeats 0",f"namespace {ns}","open BB6Coverage BB6.Agent1NGram",*body,f"end {ns}",""]))
    p=table.replace("_","")
    moves=[]
    for j in range(12):
        a=p[j*3:j*3+3]
        v="none" if a=="---" else f"some (some ⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩)"
        moves.append(f"  | {j//2},{str(bool(j%2)).lower()} => {v}")
    write(name+"Data",["SparseNGram"],[*defs,"def table : PartialMachine := fun s => match s.1.val,s.2 with",*moves,"  | _,_ => none",
        f"def cert : {BASE}.Cert := ⟨{k-1}, {lt}, {rt}, #[{','.join(ts)}]⟩"])
    modules=[]
    for j in range(12):
        q,a=j//2,str(bool(j%2)).lower()
        mod=name+f"Row{j:02}"
        modules.append(mod)
        write(mod,[name+"Data"],[f"theorem row{j:02} : ({BASE}.row cert {q} {a}).all (fun i =>",
            f"    {BASE}.stateStepOK table cert {q} {a} (i/2^(cert.n+1)) (i%2^(cert.n+1))) = true := by decide"])
    write(name,modules,[
        f"theorem allRows (q : Fin 6) (a : Bool) : ({BASE}.row cert q a).all (fun i =>",
        f"    {BASE}.stateStepOK table cert q a (i/2^(cert.n+1)) (i%2^(cert.n+1))) = true := by",
        "  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega",
        "  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl","  all_goals cases a",
        *(f"  · exact row{j:02}" for j in range(12)),
        f"theorem checked : {BASE}.check table cert = true :=",
        f"  {BASE}.check_of_rows (by decide) (by decide) (by decide) allRows",
        "theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=",
        f"  {BASE}.never table cert checked m hm","#print axioms never"])
    print(name,n,"states",len(L),len(R),"edges",len(defs),"shared trie nodes",flush=True)
    return name,ns

def generate(root,work):
    exe=work/"ngram_sparse"
    subprocess.run(["g++","-O3","-std=c++17",str(root/"ngram_sparse.cpp"),"-o",str(exe)],check=True)
    inp="".join(f"{i} {t[0]}\n" for i,t in TABLES.items())
    out=subprocess.check_output([str(exe),"23"],input=inp,text=True)
    result={}
    for line in out.splitlines():
        i,data=line.split(maxsplit=1);i=int(i);table=TABLES[i][0]
        result[table]=emit(root,i,table,data)
    assert len(result)==2
    return result

if __name__=="__main__":
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        generate(Path(__file__).resolve().parent,Path(d))
