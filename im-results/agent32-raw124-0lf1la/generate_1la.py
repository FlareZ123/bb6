#!/usr/bin/env python3
"""Generate the exhaustive Raw124 F1=0LF, F0=1LA weighted child certificate.

Discovery is untrusted. The generated source uses Raw124FastAudit and
TwoSidedAutomata for all proof obligations. No native_decide.
Run: python generate_1la.py OUTPUT_DIRECTORY
"""
import hashlib
import base64
import gzip
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
PARENT = "1RB---_1RC---_0RD---_1LD1RE_---1LF_1LA0LF"
B = 1045
NS = "BB6.Agent32Raw124ZeroLF1LA"
PREFIX = "Raw124ZeroLF1LA"
PARAMS = {102:(3,1,2),137:(3,1,2),7:(3,1,3),73:(3,2,2),77:(3,2,2),79:(3,2,2),116:(3,2,2),117:(3,2,2),209:(4,1,3),135:(4,2,2),136:(3,1,5),184:(3,3,3),118:(4,3,2),119:(4,3,2),120:(4,3,2)}
EXPECTED = {102:57,137:43,7:160,73:104,77:164,79:118,116:194,117:194,209:116,135:852,136:246,184:235,118:413,119:413,120:413}
HARD = {24,85,86,95,101,114,193,194,205}
def custom_module(i):
    return PREFIX + (f'M{i}' if i in (24,95) else 'Seven')
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
    subprocess.run([str(fast),PARENT,"3000","32",str(data/"1LA")],check=True)
    rawtree=(data/"1LA.json").read_bytes();rawopen=(data/"1LA.open").read_bytes()
    assert hashlib.sha256(rawtree).hexdigest()=="9f3e0fa5f0961481973a853c1967cb3a66ace7dcae73dfb3db4c84a0f6529fb8"
    assert hashlib.sha256(rawopen).hexdigest()=="16edad9792a2509e5096f0394fe4e691cc8e9762c3a86fab3c8111a97a648bce"
    opens=rawopen.decode().splitlines()
    assert len(opens)==len(set(opens))==232
    tree=json.loads(rawtree)
    raw=gzip.decompress(base64.b64decode((HERE/"witnesses.far.gz.b64").read_bytes())).decode()
    far={int(i):(int(code[0]),list(map(int,code[1:]))) for i,code in (line.split() for line in raw.splitlines())}
    assert len(far)==208 and len(PARAMS)==15 and len(HARD)==9
    assert len(set(far)|set(PARAMS)|HARD)==232
    for i in PARAMS:emit_auto(out,i,parse(opens[i]))
    for suffix in ("Seven","M24","M95"):
        name=PREFIX+suffix
        (out/(name+".lean")).write_bytes(gzip.decompress(base64.b64decode((HERE/(name+".lean.gz.b64")).read_bytes())))
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
"""+f"end {NS}\n"
    (out/f"{PREFIX}Base.lean").write_text(base)
    stats=Counter()
    order=[]
    def build(node,p):
        tag,*v=node;stats[tag]+=1
        if tag=="open":
            code=v[0];assert code==show(p);i=lookup[code]
            if i in HARD:return f".proven BB6.Agent32Raw124M{i}.table BB6.Agent32Raw124M{i}.never"
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
            imports += list(dict.fromkeys(custom_module(i) for i in HARD if f"Raw124M{i}.table" in expr))
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
    assert stats==Counter(open=232,cycle=2955,last=1690,split=212),stats
    m=emit(t,"pChild","Root")
    (out/(PREFIX+".lean")).write_text(f"import {m}\n"+header+f"""noncomputable def certificate : WeightedTNFCertificate {B} pChild 6 := fastCertified {B} pChild kidRoot pChild_root pChild_nohalt checkRoot
theorem bound_all : ∀ m, compatible pChild m → WeightedBound {B} m := certificate.sound
#print axioms checkRoot
#print axioms bound_all
end {NS}
""")
    (out/"build_order.txt").write_text("\n".join([PREFIX+"Base"]+[PREFIX+x for x in ("Seven","M24","M95")]+[f"{PREFIX}Auto{i}" for i in PARAMS]+order+[PREFIX])+"\n")
    print(stats,"modules",len(list(out.glob(PREFIX+"*.lean"))))

if __name__=="__main__":
    main(Path(sys.argv[1]).resolve())
