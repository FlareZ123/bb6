"""Split existing sparse Trie.all certificates into bounded source-check shards."""
import json
import re
from functools import lru_cache
from pathlib import Path

BASE = "BB6.Agent47SparseNGram"
ROOT = Path(__file__).resolve().parent

def split(root, name, child, leaf_limit=256, group_limit=3000):
    data = (root / (name + "Data.lean")).read_text()
    nodes = {a:(b,c) for a,b,c in re.findall(
        r"^def (t\d+) : Trie := \.branch (\S+) (\S+)$", data, re.M)}
    rows = re.search(r"^def cert : .*? := ⟨\d+, \S+, \S+, #\[(.*?)\]⟩$", data, re.M).group(1).split(",")
    assert len(rows) == 12
    @lru_cache(None)
    def count(t):
        if t == ".empty": return 0
        if t == ".leaf": return 1
        return sum(count(x) for x in nodes[t])
    def check(j, path):
        idx = "i"
        for b in reversed(path):
            idx = f"(2*{idx}+{b})"
        q,a = j//2,str(bool(j%2)).lower()
        return f"(fun i => {BASE}.stateStepOK table cert {q} {a} ({idx}/2^(cert.n+1)) ({idx}%2^(cert.n+1)))"
    def term(t,j,path):
        t = "Trie"+t if t.startswith(".") else t
        return f"{t}.all {check(j,path)}"
    def proof_name(j,path):
        return f"p{j:02}_{path or 'root'}"
    groups = []
    row_parts = [[] for _ in rows]
    row_groups = [set() for _ in rows]
    def cut(t,j,path):
        p = proof_name(j,path)
        goal = f"theorem {p} : {term(t,j,path)} = true := "
        n = count(t)
        if not n:
            row_parts[j].append(goal + "by rfl")
        elif n <= leaf_limit:
            if not groups or groups[-1][0]+n > group_limit:
                groups.append([0,[]])
            groups[-1][0] += n
            groups[-1][1].append(goal + "by decide")
            row_groups[j].add(len(groups)-1)
        else:
            e,o = nodes[t]
            a,b = cut(e,j,path+"0"),cut(o,j,path+"1")
            row_parts[j].append(goal + "by\n"+
                f"  change ({term(e,j,path+'0')} && {term(o,j,path+'1')}) = true\n"+
                f"  exact Eq.mpr (Bool.and_eq_true _ _) ⟨{a},{b}⟩")
        return p
    for j,t in enumerate(rows):
        p = cut(t,j,"")
        q,a = j//2,str(bool(j%2)).lower()
        row_parts[j].append(f"theorem row{j:02} : ({BASE}.row cert {q} {a}).all {check(j,'')} = true := by\n  exact {p}")
    def module(i):
        return f"{name}Chunk{i:03}"
    def write(mod, imports, body):
        (root/(mod+".lean")).write_text("\n".join([
            *(f"import {x}" for x in imports),
            "set_option maxRecDepth 100000","set_option maxHeartbeats 0",
            f"namespace {BASE}.{name}","open BB6Coverage BB6.Agent1NGram",
            *body,f"end {BASE}.{name}",""]))
    for i,(_,body) in enumerate(groups):
        write(module(i),[name+"Data"],body)
    for j in range(12):
        write(f"{name}Row{j:02}",[name+"Data",*(module(i) for i in sorted(row_groups[j]))],row_parts[j])
    assert sum(g[0] for g in groups)==sum(map(count,rows))
    return [{"child":child,"group":f"{child}-{i:03}","module":module(i),"leaves":g[0]}
            for i,g in enumerate(groups)]

def prepare():
    import subprocess,sys,tempfile
    sparse = ROOT.parent/"agent47-raw111-cut"
    sys.path.insert(0,str(sparse))
    from emit_sparse import emit
    specs = [
        ("1LF",1596,"1RB1LF_1RC0LB_0RD0RD_1LD1RE_0RA1RA_---1LB",22,"Raw60LFSparse",(14522,176,2550)),
        ("1RE",495,"1RB1RE_1RC0LB_0RD1LF_1LD1RE_1LC1RA_---1LB",25,"Raw60RESparse",(93002,102,13901))]
    plan=[]
    with tempfile.TemporaryDirectory() as temp:
        exe=Path(temp)/"ngram"
        subprocess.run(["g++","-O3","-std=c++17",str(sparse/"ngram_sparse.cpp"),"-o",str(exe)],check=True)
        for child,i,table,width,name,expected in specs:
            ident,data=subprocess.check_output([str(exe),str(width)],input=f"{i} {table}\n",text=True).strip().split(maxsplit=1)
            assert ident==str(i)
            emit(ROOT,i,table,data,width=width,module_name=name,expected=expected)
            plan += split(ROOT,name,child)
    (ROOT/"raw60_sparse_plan.json").write_text(json.dumps(plan,indent=2)+"\n")
    print("Sparse proof chunks:",len(plan),"cover",sum(x["leaves"] for x in plan),"states")

if __name__=="__main__":
    prepare()
