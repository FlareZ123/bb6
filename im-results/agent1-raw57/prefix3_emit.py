"""Generate Lean certificates for end-marked exact prefix rewriting.

Discovery is not trusted: Lean checks every macro, frontier inclusion,
prefix-trie totality, and the initial configuration.
"""
from pathlib import Path
from collections import defaultdict,deque
import json
ROOT=Path(__file__).resolve().parent

def automaton(seed,rules):
    edges=defaultdict(set)
    n=1
    for a in seed:
        edges[n-1,a].add(n); n+=1
    final=n-1
    trie={}; normal=[]
    for l,(r,t) in rules.items():
        assert r and l and t>0 and set(l+r)<=set("01#")
        q=0
        for a in r[:-1]:
            if (q,a) not in trie:
                trie[q,a]=n; n+=1
            v=trie[q,a]
            normal.append((q,a,v,""));q=v
        normal.append((q,r[-1],0,l))
    normal=list(dict.fromkeys(normal))
    def walk(q,w):
        S={q}
        for a in w:
            S={j for x in S for j in edges.get((x,a),())}
            if not S:break
        return S
    rounds=0
    while True:
        count=0;rounds+=1
        for p,a,q,w in normal:
            e=edges[p,a];new=walk(q,w)-e
            count+=len(new);e.update(new)
        if not count:break
    assert final in walk(0,seed)
    assert all(walk(0,l)<=walk(0,r) for l,(r,t) in rules.items())
    return edges,final,n,rounds

def trim(edges,final):
    graph=defaultdict(set);rev=defaultdict(set)
    for (i,a),js in edges.items():
        graph[i].update(js)
        for j in js:rev[j].add(i)
    def reach(g,s):
        seen={s};todo=[s]
        for i in todo:
            for j in g[i]-seen:
                seen.add(j);todo.append(j)
        return seen
    keep=sorted(reach(graph,0)&reach(rev,final))
    ix={q:i for i,q in enumerate(keep)}
    out=defaultdict(set)
    for (i,a),js in edges.items():
        if i in ix:out[ix[i],a]={ix[j] for j in js if j in ix}
    return out,ix[final],len(keep)

def symlist(s):
    return "["+",".join({"0":".z","1":".o","#":".e"}[a] for a in s)+"]"

def bits(xs):
    return "["+",".join("true" if int(x) else "false" for x in xs)+"]"

def edge_tree(edges,lo,hi):
    if hi-lo==1:
        return "(.leaf "+" ".join(str(sorted(edges[lo,a])) for a in "01#")+")"
    mid=(lo+hi)//2
    return f"(.node {mid} {edge_tree(edges,lo,mid)} {edge_tree(edges,mid,hi)})"

def trie_tree(pairs):
    if not pairs:return ".miss"
    for w,i in pairs:
        if not w:return f"(.hit .r{i})"
    return "(.node "+" ".join(trie_tree([(w[1:],i) for w,i in pairs if w[0]==a]) for a in "01#")+")"

def rule_code(rules):
    out="inductive Sym where\n  | z\n  | o\n  | e\n  deriving DecidableEq\n\ndef decode : List Sym → List Bool\n  | [] => []\n  | .z::w => false::decode w\n  | .o::w => true::decode w\n  | .e::_ => []\n\n"
    out+="inductive RuleId where\n"+"\n".join(f"  | r{i}" for i in range(len(rules)))+"\n  deriving DecidableEq\n"
    for name,fn,typ in [("lhs",lambda k,v:symlist(k),"List Sym"),("rhs",lambda k,v:symlist(v[0]),"List Sym"),("cost",lambda k,v:str(v[1]),"Nat")]:
        out+=f"\ndef {name} : RuleId → {typ}\n"+"\n".join(f"  | .r{i} => {fn(k,v)}" for i,(k,v) in enumerate(rules.items()))+"\n"
    return out

def table_code(s):
    moves=[s[i:i+3] for i in range(0,36,3)]
    return "def table : PartialMachine := fun s => match s.1.val,s.2 with\n"+"".join(f"  | {i//2},{str(bool(i%2)).lower()} => some (some ⟨{str(a[0]=='1').lower()},{str(a[1]=='R').lower()},{ord(a[2])-65}⟩)\n" for i,a in enumerate(moves) if a!="---")+"  | _,_ => none\n"

def step_run(s,q,L,R,t):
    moves=[s[i:i+3] for i in range(0,36,3)]
    L,R=deque(L),deque(R)
    for _ in range(t):
        a=L.popleft() if L else 0
        assert a in (0,1)
        m=moves[2*q+a];assert m!="---"
        b=int(m[0]);q=ord(m[2])-65
        if m[1]=="R":
            c=R.popleft() if R else 0
            assert c in (0,1)
            L.appendleft(b);L.appendleft(c)
        else:R.appendleft(b)
    return q,list(L),list(R)

def entry_code(s,entry,q,side,seed):
    z=(0,[],[]);rows=[]
    for i in range(0,entry,500):
        dt=min(500,entry-i)
        nxt=step_run(s,*z,dt)
        rows.append((dt,z,nxt));z=nxt
    w=list(map(int,seed.split("#")[0]))
    assert z==(q,w,[]) if side=="L" else z==(q,[],w)
    if not rows:return "theorem entry : run0 table 0 ⟨0,[],[]⟩ = some (root seed) := by rfl"
    def cfg(z):return f"⟨{z[0]},{bits(z[1])},{bits(z[2])}⟩"
    out=""
    for i,(dt,a,b) in enumerate(rows):
        rhs="root seed" if i==len(rows)-1 else cfg(b)
        out+=f"theorem entry{i} : run0 table {dt} {cfg(a)} = some ({rhs}) := by rfl\n"
    out+=f"theorem entry : run0 table {entry} ⟨0,[],[]⟩ = some (root seed) := by\n  have h0 := entry0\n"
    for i in range(1,len(rows)):out+=f"  have h{i} := join0 h{i-1} entry{i}\n"
    return out+f"  exact h{len(rows)-1}"

def emit(module,cert):
    seed=cert["seed"];rules=cert["rules"];q=cert["state"];side=cert["side"]
    s=cert["table"].replace("_","");entry=cert["entry"]
    for l,(r,t) in rules.items():
        end=l.endswith("#");assert end==r.endswith("#")
        a=list(map(int,l.rstrip("#")))+([] if end else [2])
        b=list(map(int,r.rstrip("#")))+([] if end else [2])
        z=step_run(s,q,a if side=="L" else [],a if side=="R" else [],t)
        assert z==((q,b,[]) if side=="L" else (q,[],b))
    ed,fin,n,rounds=automaton(seed,rules)
    if "census" in cert:assert [n,sum(map(len,ed.values())),rounds]==cert["census"]
    ed,fin,n=trim(ed,fin)
    ns="BB6Coverage.Agent1"+module
    inv=(ROOT/"m211_invariant.lean.in").read_text().replace("BB6Coverage.Agent1Raw57LB1M211",ns)
    inv=inv.replace("List Bool","List Sym").replace("(b : Bool)","(b : Sym)")
    inv=inv.replace("  | leaf (z o : List Nat)","  | leaf (z o e : List Nat)").replace("  | .leaf z o => if b then o else z","  | .leaf z o e => match b with\n    | .z => z\n    | .o => o\n    | .e => e")
    inv=inv.replace("  | node (z o : Trie)","  | node (z o e : Trie)").replace("| .hit i => p == lhs i","| .hit i => decide (p = lhs i)").replace("  | .node z o => !(S.contains final) &&\n      checkTrie (step S false) (p++[false]) z &&\n      checkTrie (step S true) (p++[true]) o","  | .node z o e => !(S.contains final) &&\n      checkTrie (step S .z) (p++[.z]) z &&\n      checkTrie (step S .o) (p++[.o]) o &&\n      checkTrie (step S .e) (p++[.e]) e")
    inv=inv.replace("| node z o ihz iho =>","| node z o e ihz iho ihe =>").replace("using h.1.1\n","using h.1.1.1\n").replace("ihz (step S false) (p++[false]) w h.1.2 ha","ihz (step S .z) (p++[.z]) w h.1.1.2 ha").replace("iho (step S true) (p++[true]) w h.2 ha","iho (step S .o) (p++[.o]) w h.1.2 ha")
    inv=inv.replace("\ndef trie : Trie", "      · obtain ⟨i,R,hr⟩ := ihe (step S .e) (p++[.e]) w h.2 ha\n        exact ⟨i,R,by simpa only [List.append_assoc,List.singleton_append] using hr⟩\n\ndef trie : Trie")
    for k,v in {"RULES":rule_code(rules),"EDGES":edge_tree(ed,0,n),"FINAL":str(fin),"TRIE":trie_tree([(l,i) for i,l in enumerate(rules)]),"SEED":symlist(seed)}.items():inv=inv.replace("@"+k+"@",v)
    src=(ROOT/"m211_source.lean.in").read_text().replace("Raw57LB1M211",module).replace("List Bool","List Sym")
    src=src.replace("⟨1,[],w.tail⟩",f"⟨{q},decode w,[]⟩" if side=="L" else f"⟨{q},[],decode w⟩").replace("⟨14922,seed",f"⟨{entry},seed")
    src=src.replace("@TABLE@",table_code(s)).replace("@ENTRY@",entry_code(s,entry,q,side,seed))
    (ROOT/(module+"Invariant.lean")).write_text(inv)
    (ROOT/(module+".lean")).write_text(src)
    print(module,n,sum(map(len,ed.values())),"states/edges")

if __name__=="__main__":
    import sys
    emit(sys.argv[1],json.loads((ROOT/sys.argv[2]).read_text()))
