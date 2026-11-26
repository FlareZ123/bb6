#!/usr/bin/env python3
"""Generate full Raw124 F1=0LF child candidates for F0=0RE or 1RE.
Adapted from Agent32's generate_1la.py; all leaves require Lean checks.
Run: python generate.py OUTPUT_DIRECTORY BRANCH
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from collections import Counter, defaultdict
from itertools import product

HERE = Path(__file__).resolve().parent
OLD = HERE.parent / "agent2-tnf-raw124"
FAR_SRC = HERE.parent / "agent11-tnf-raw86" / "search.cpp"
sys.path.insert(0, str(OLD))
from generate_0lf_0ra import masks, parse, show, slot, move
BRANCH = sys.argv[2]
SPEC = {"1RE":{"bound":271,"open":89,"cycle":2370,"last":1038,"split":152,"tree":"9854c5883b6c59fc59fbe8cc6ffbf95e384e5a3c57a20d51ffab3bc3dc216ae7","hash":"a3ee92fe9eb8e6a66c5006e95ae24be769a703a185e73a3ecea5c5058742bd39","hard":[42],"auto":{"32":[[3,2,3],4304],"34":[[4,3,4],801],"35":[[5,3,3],1204],"40":[[3,2,1],80],"48":[[3,2,2],481],"67":[[3,1,5],703],"68":[[3,1,6],361],"69":[[3,3,2],280],"71":[[3,1,6],331],"72":[[3,1,6],160]}},"0RE":{"bound":597,"open":125,"cycle":2160,"last":844,"split":136,"tree":"b96f0bd2b5270fce7630cf89a07ae684139eaddbc8c6a4098c38f986e34073f2","hash":"6403309b93b3f8da043c8554deb65d6e883411356a7789969ff860847d688e46","hard":[],"auto":{"4":[[6,1,8],4007],"40":[[3,3,2],292],"43":[[2,3,1],67],"44":[[2,3,2],131],"45":[[3,1,5],179],"46":[[3,5,1],547],"47":[[2,3,2],144],"48":[[2,1,5],132],"49":[[3,3,2],312],"50":[[2,3,3],124],"52":[[3,1,3],140],"54":[[3,3,2],256],"56":[[3,3,2],256],"57":[[3,3,2],370],"58":[[3,3,2],258],"59":[[3,1,5],67],"61":[[2,3,1],70],"62":[[3,3,2],263],"63":[[3,1,5],98],"100":[[2,1,5],105]}}}[BRANCH]
PARENT = f"1RB---_1RC---_0RD---_1LD1RE_---1LF_{BRANCH}0LF"
B = SPEC["bound"]
NS = f"BB6.Agent7Raw124ZeroLF{BRANCH}"
PREFIX = f"Raw124ZeroLF{BRANCH}"
PARAMS = {int(i):tuple(v[0]) for i,v in SPEC["auto"].items()}
EXPECTED = {int(i):v[1] for i,v in SPEC["auto"].items()}
HARD = set(SPEC["hard"])
def custom_module(i):
    return PREFIX+f"M{i}"
MOVES = [w+d+q for w,d,q in product("01","LR","ABCDEF")]

def bit(x):
    return str(bool(x)).lower()

def pushfun(n,cap,mod):
    def push(x,b):
        v,runs=x
        if v!=b:return (b,(1,)+runs[:n-1])
        j=runs[0]
        if j==0:return x
        return (b,((j+1 if j<cap+mod-1 else cap),)+runs[1:])
    return push

def run(p,params):
    # Existing run-aware two-stack relation, with sorted inverse edges so
    # the generated certificate numbering is deterministic.
    P=pushfun(*params)
    blank=(0,(0,));tab=[[blank],[blank]]
    ids=[{blank:0},{blank:0}];D=[{},{}]
    def dfa(d,i,b):
        k=(i,b)
        if k in D[d]:return D[d][k]
        y=P(tab[d][i],b);j=ids[d].get(y)
        if j is None:
            j=len(tab[d]);tab[d].append(y);ids[d][y]=j
        D[d][k]=j
        return j
    edges=[defaultdict(set),defaultdict(set)]
    wait=[defaultdict(list),defaultdict(list)]
    for e in edges:e[0].add((0,0))
    seen={(0,0,0,0)};todo=[(0,0,0,0)]
    def add(x):
        if x not in seen:
            assert p[2*x[0]+x[1]]!="---",x
            assert len(todo)<150000
            seen.add(x);todo.append(x)
    def pop(x,edge,pushed):
        q,b,l,r=x;m=p[2*q+b];s=ord(m[2])-65;c,pre=edge
        add((s,c,pushed,pre) if m[1]=="R" else (s,c,pre,pushed))
    for c in todo:
        q,b,l,r=c;m=p[2*q+b];w=int(m[0]);d=int(m[1]=="L")
        x=r if d else l;j=dfa(d,x,w)
        if (w,x) not in edges[d][j]:
            edges[d][j].add((w,x))
            for cc,jj in wait[d][j]:pop(cc,(w,x),jj)
        z=l if d else r;wait[1-d][z].append((c,j))
        for e in sorted(edges[1-d][z]):pop(c,e,j)
    return edges,seen,D,tab

def trie(xs):
    if not xs:return ".empty"
    if xs==[0]:return ".leaf"
    return f"(.branch {trie([x//2 for x in xs if x%2==0])} {trie([x//2 for x in xs if x%2==1])})"

def emit_auto(out,i,p):
    edges,seen,D,T=run(p,PARAMS[i])
    assert len(seen)==EXPECTED[i]
    print("automaton",i,len(seen),len(T[0]),len(T[1]),flush=True)
    def stack(d):
        E=",".join("["+",".join(f"({bit(b)},{j})" for b,j in sorted(edges[d][k]))+"]" for k in range(len(T[d])))
        P=",".join(f"({D[d].get((k,0),0)},{D[d].get((k,1),0)})" for k in range(len(T[d])))
        return f"⟨#[{E}],#[{P}]⟩"
    rows=[trie(sorted(r+len(T[1])*l for qq,aa,l,r in seen if (qq,aa)==(q,a))) for q,a in product(range(6),range(2))]
    cases="\n".join(f"  | {slot(s)} => "+("none" if m=="---" else f"some (some {move(m)})") for s,m in enumerate(p))
    h=f"""import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}.Auto{i}
open BB6Coverage
def table : PartialMachine := fun s => match s with
{cases}
  | _ => none
def cert : BB6.Agent4Automata.Cert := ⟨{stack(0)}, {stack(1)}, #[{','.join(rows)}]⟩
"""
    for q,a in product(range(6),range(2)):
        h+=f"""theorem checked_row_{q}_{a} :
  (BB6.Agent4Automata.row cert ({q} : Fin 6) {bit(a)}).all
    (fun i => BB6.Agent4Automata.stateStepOK table cert ({q} : Fin 6) {bit(a)}
      (i / cert.right.edges.size) (i % cert.right.edges.size)) = true := by decide
"""
    h+="""theorem left_nonempty : decide (0 < cert.left.edges.size) = true := by decide
theorem right_nonempty : decide (0 < cert.right.edges.size) = true := by decide
theorem left_seed : (cert.left.pop 0).contains (false,0) = true := by decide
theorem right_seed : (cert.right.pop 0).contains (false,0) = true := by decide
theorem start_state : BB6.Agent4Automata.stateOK cert 0 false 0 0 = true := by decide
theorem rows_checked :
  (List.finRange 6).all (fun q => BB6.Agent1NGram.bits.all (fun a =>
    (BB6.Agent4Automata.row cert q a).all
      (fun i => BB6.Agent4Automata.stateStepOK table cert q a
        (i / cert.right.edges.size) (i % cert.right.edges.size)))) = true := by
"""
    h+="  simp [BB6.Agent1NGram.bits, List.finRange, "+", ".join(f"checked_row_{q}_{a}" for q,a in product(range(6),range(2)))+"]\n"
    h+="""theorem checked : BB6.Agent4Automata.check table cert = true := by
  unfold BB6.Agent4Automata.check
  rw [left_nonempty, right_nonempty, left_seed, right_seed, start_state, rows_checked] <;> rfl
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent4Automata.never table cert checked m hm
#print axioms never
"""
    h+=f"end {NS}.Auto{i}\n"
    (out/f"{PREFIX}Auto{i}.lean").write_text(h)

def main(out):
    out.mkdir(parents=True,exist_ok=True)
    data=out/"partition";data.mkdir(exist_ok=True)
    fast=data/"fast"; search=data/"search"
    subprocess.run(["g++","-O3","-std=c++20",str(OLD/"fast_partition.cpp"),"-o",str(fast)],check=True)
    subprocess.run([str(fast),PARENT,"3000","32",str(data/BRANCH)],check=True)
    rawtree=(data/(BRANCH+".json")).read_bytes();rawopen=(data/(BRANCH+".open")).read_bytes()
    assert hashlib.sha256(rawtree).hexdigest()==SPEC["tree"]
    assert hashlib.sha256(rawopen).hexdigest()==SPEC["hash"]
    opens=rawopen.decode().splitlines()
    assert len(opens)==len(set(opens))==SPEC["open"]
    tree=json.loads(rawtree)
    subprocess.run(["g++","-O3","-std=c++20",str(FAR_SRC),"-o",str(search)],check=True)
    raw=subprocess.check_output([str(search),"5"],input="".join(f"{i} {x.replace('_','')}\n" for i,x in enumerate(opens)),text=True)
    far={int(i):(int(code[0]),list(map(int,code[1:]))) for i,code in (line.split() for line in raw.splitlines())}
    assert not (set(far)&set(PARAMS) or set(far)&HARD or set(PARAMS)&HARD)
    assert set(far)|set(PARAMS)|HARD==set(range(len(opens)))
    for i in PARAMS:emit_auto(out,i,parse(opens[i]))
    for i in HARD:
        assert (HERE/(custom_module(i)+".lean")).is_file()
    lookup={s:i for i,s in enumerate(opens)}
    header=f"""import Raw124FastAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent2Raw124FastAudit
"""
    base=header+"""abbrev p124 : PartialMachine := refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev pBranch : PartialMachine := refine p124 (5,true) (some ⟨false,false,5⟩)
abbrev pChild : PartialMachine := refine pBranch (5,false) (some ⟨true,false,0⟩)
theorem p124_nohalt : weightedTNFNoAssignedHalt p124 :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)
theorem pChild_root : pChild initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem pChild_nohalt : weightedTNFNoAssignedHalt pChild :=
  weightedTNFNoAssignedHalt_refine _ _ _ (weightedTNFNoAssignedHalt_refine _ _ _ p124_nohalt)
""".replace("⟨true,false,0⟩",move(BRANCH))+f"end {NS}\n"
    (out/f"{PREFIX}Base.lean").write_text(base)
    stats=Counter()
    order=[]
    def build(node,p):
        tag,*v=node;stats[tag]+=1
        if tag=="open":
            code=v[0];assert code==show(p);i=lookup[code]
            if i in HARD:return f".proven {NS}M{i}.table {NS}M{i}.never"
            if i in PARAMS:return f".proven Auto{i}.table Auto{i}.never"
            rev,dfa=far[i];d,D,L,R,z=masks(p,rev,dfa)
            return f".far {bit(rev)} {d} ⟨0,{D},{L},{R},{z}⟩"
        if tag=="cycle":
            e,k,r,h=v;return f".cycle {e} {k} {bit(r)} ({h})"
        if tag=="last":
            n,s=v;return f".last {n} {slot(s)}"
        assert tag=="split"
        n,s,kids=v;assert len(kids)==24 and p[s]=="---"
        return (n,s,[build(k,p[:s]+(mv,)+p[s+1:]) for k,mv in zip(kids,MOVES)])
    def show_a(t):
        if isinstance(t,str):return t
        n,s,kids=t
        return f".split {n} {slot(s)} (byMove [\n"+",\n".join(map(show_a,kids))+"])"
    def emit(t,pexpr,name):
        mod=PREFIX+"Kid"+name
        expr=show_a(t);imports=[PREFIX+"Base"]
        if isinstance(t,str) or (len(expr)<18000 and expr.count(".split")<=4):
            imports += [f"{PREFIX}Auto{i}" for i in PARAMS if f"Auto{i}.table" in expr]
            imports += list(dict.fromkeys(custom_module(i) for i in HARD if f"{NS}M{i}.table" in expr))
            body=f"def kid{name} : Audit := {expr}\ntheorem check{name} : fastCheck {B} {pexpr} kid{name} = true := by decide\n"
        else:
            n,s,kids=t;names=[]
            for j,k in enumerate(kids):
                nn=f"{name}_{j:02}";names.append(nn)
                imports.append(emit(k,f"(refine {pexpr} {slot(s)} (some {move(MOVES[j])}))",nn))
            body=f"def kids{name} : Move → Audit := byMove ["+",".join("kid"+nn for nn in names)+"]\n"
            body+=f"theorem checks{name} (mv : Move) : fastCheck {B} (refine {pexpr} {slot(s)} (some mv)) (kids{name} mv) = true := by\n"
            body+="  rcases mv with ⟨w,r,q⟩\n  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega\n  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl\n  all_goals cases w <;> cases r\n"
            body+="\n".join("  · exact check"+names[q+6*r+12*w] for q,w,r in product(range(6),range(2),range(2)))+"\n"
            body+=f"def kid{name} : Audit := .split {n} {slot(s)} kids{name}\ntheorem check{name} : fastCheck {B} {pexpr} kid{name} = true := by\n  change (fastQuery {B} {pexpr} {n} {slot(s)} && allMoves (fun mv => fastCheck {B} (refine {pexpr} {slot(s)} (some mv)) (kids{name} mv))) = true\n  simp only [Bool.and_eq_true]\n  exact ⟨by decide,allMoves_of _ checks{name}⟩\n"
        (out/(mod+".lean")).write_text("".join(f"import {m}\n" for m in imports)+header+body+f"end {NS}\n")
        order.append(mod)
        return mod
    t=build(tree,parse(PARENT))
    assert stats==Counter({k:SPEC[k] for k in ("open","cycle","last","split")}),stats
    m=emit(t,"pChild","Root")
    (out/(PREFIX+".lean")).write_text(f"import {m}\n"+header+f"""noncomputable def certificate : WeightedTNFCertificate {B} pChild 6 := fastCertified {B} pChild kidRoot pChild_root pChild_nohalt checkRoot
theorem bound_all : ∀ m, compatible pChild m → WeightedBound {B} m := certificate.sound
#print axioms checkRoot
#print axioms bound_all
end {NS}
""")
    (out/"build_order.txt").write_text("\n".join([PREFIX+"Base"]+[custom_module(i) for i in sorted(HARD)]+[f"{PREFIX}Auto{i}" for i in PARAMS]+order+[PREFIX])+"\n")
    print(stats,"modules",len(list(out.glob(PREFIX+"*.lean"))))

if __name__=="__main__":
    main(Path(sys.argv[1]).resolve())
