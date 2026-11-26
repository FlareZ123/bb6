"""Regenerate the exact M211 kernel-checkable invariant and source adapter."""
from pathlib import Path
from m211_prefix_certificate import (
    discover, check_macros, check_source_macros, build_automaton, trim,
    check_invariant, run_source_zip, MOVES,
)
ROOT=Path(__file__).resolve().parent

def lb(w):
    return "["+",".join("true" if int(c) else "false" for c in w)+"]"

def ln(xs):
    return "["+",".join(map(str,sorted(xs)))+"]"

def edge_tree(edges,lo,hi):
    if hi-lo==1:
        return f"(.leaf {ln(edges[lo,'0'])} {ln(edges[lo,'1'])})"
    mid=(lo+hi)//2
    return f"(.node {mid} {edge_tree(edges,lo,mid)} {edge_tree(edges,mid,hi)})"

def trie_tree(pairs):
    if not pairs: return ".miss"
    if any(not w for w,i in pairs):
        assert len(pairs)==1
        return f"(.hit .r{pairs[0][1]})"
    z,o=(trie_tree([(w[1:],i) for w,i in pairs if w[0]==b]) for b in "01")
    return f"(.node {z} {o})"

def make_rules(rules):
    rows=list(rules.items())
    code="inductive RuleId where\n"
    code+="\n".join(f"  | r{i}" for i in range(len(rows)))+"\n  deriving DecidableEq\n"
    for name,fn,typ in [
        ("lhs",lambda k,v:lb(k),"List Bool"),
        ("rhs",lambda k,v:lb(v[0]),"List Bool"),
        ("cost",lambda k,v:str(v[1]),"Nat"),
    ]:
        code+=f"def {name} : RuleId → {typ}\n"
        code+="\n".join(f"  | .r{i} => {fn(k,v)}" for i,(k,v) in enumerate(rows))+"\n"
    return code

def make_table():
    code="def table : PartialMachine := fun s => match s.1.val,s.2 with\n"
    for i,m in enumerate(MOVES):
        if m=="---": continue
        q,b=i//2,i%2
        code+=f"  | {q},{str(bool(b)).lower()} => some (some ⟨{str(m[0]=='1').lower()},{str(m[1]=='R').lower()},{ord(m[2])-65}⟩)\n"
    return code+"  | _,_ => none\n"

def zlean(z):
    q,L,R=z
    return f"⟨{q},{lb(L)},{lb(R)}⟩"

def make_entry(entry):
    t,seed=entry
    now=(0,[],[])
    rows=[]
    for i in range(0,t,500):
        dt=min(500,t-i)
        nxt=run_source_zip(*now,dt)
        rows.append((dt,now,nxt))
        now=nxt
    assert now==(1,[],list(map(int,seed[1:])))
    code=""
    for i,(dt,z,z2) in enumerate(rows):
        out="root seed" if i==len(rows)-1 else zlean(z2)
        code+=f"theorem entry{i} : run0 table {dt} {zlean(z)} = some ({out}) := by rfl\n"
    code+=f"\ntheorem entry : run0 table {t} ⟨0,[],[]⟩ = some (root seed) := by\n"
    code+="  have h0 := entry0\n"
    for i in range(1,len(rows)):
        code+=f"  have h{i} := join0 h{i-1} entry{i}\n"
    return code+f"  exact h{len(rows)-1}\n"

def main():
    rules,entry=discover()
    check_macros(rules,entry)
    check_source_macros(rules,entry)
    edges,final,n,rounds=build_automaton(rules,entry[1])
    assert (n,sum(map(len,edges.values())),rounds)==(1763,1819,8)
    check_invariant(rules,entry,edges,final)
    edges,final,n=trim(edges,final)
    assert (n,sum(map(len,edges.values())),final)==(1232,1267,163)
    check_invariant(rules,entry,edges,final)
    invariant=(ROOT/"m211_invariant.lean.in").read_text()
    for key,value in {
        "RULES":make_rules(rules),"EDGES":edge_tree(edges,0,n),
        "FINAL":str(final),"TRIE":trie_tree([(k,i) for i,k in enumerate(rules)]),
        "SEED":lb(entry[1]),
    }.items():
        invariant=invariant.replace("@"+key+"@",value)
    source=(ROOT/"m211_source.lean.in").read_text()
    source=source.replace("@TABLE@",make_table()).replace("@ENTRY@",make_entry(entry))
    (ROOT/"Raw57LB1M211Invariant.lean").write_text(invariant)
    (ROOT/"Raw57LB1M211.lean").write_text(source)
    print("Generated M211 invariant and original-source adapter")

if __name__=="__main__":
    main()
