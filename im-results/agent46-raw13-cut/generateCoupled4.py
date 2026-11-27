"""Generate an exact four-hole cut from explicit witnesses; never assume a timeout is nonhalting."""
import json, subprocess, tempfile
from itertools import product
from collections import Counter
from generate import D, MOVES, boolean, move, slot, tally, emit as leaf_emit
from generateOneFAR import codes, fmt, saturate
from emitauto import emit_fixtures, bits

ROOT="1RB1LD1RC---1LA1RE1LF0LA---0RD------"
GRAFT="1RB1LD1RC---1LA1RE1LF0LA---0RD1LC---"
LATE="1RB1LD1RC0RB1LA1RE1LF0LA1LA0RD1LE---"
B=62123
PUB="BB6.Agent46Raw13CoupledParent.published"
H=f"(h : NeverHalts {PUB})"
MODULE="Raw13Coupled4"
NS="BB6.Agent46Raw13Coupled4"
AUTO="BB6Coverage.Agent31Pump.Auto.Raw13Coupled4Auto"
HEADER=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut
open BB6.Agent50TNFPilot BB6.Agent10ZipAudit
"""
def write(name,imports,body):
    (D/(name+".lean")).write_text("".join(f"import {x}\n" for x in imports)+HEADER+body+"\nend "+NS+"\n")

def late_module(raw,n,s,index):
    # Zipper lists exactly match SparseZipper.move, including stored zero cells.
    p=[raw[i:i+3] for i in range(0,36,3)]
    assert p.count("---")==1 and p[s]=="---"
    q,h,l,r=0,0,[],[]
    points=[(0,q,h,l[:],r[:])]
    for k in range(n):
        a=p[2*q+(l[0] if l else 0)]
        assert a!="---",(k,raw)
        w=int(a[0]);q=ord(a[2])-65
        if a[1]=="R":h+=1;l=[r[0] if r else 0,w]+l[1:];r=r[1:]
        else:h-=1;l=l[1:];r=[w]+r
        if (k+1)%512==0 or k+1==n:points.append((k+1,q,h,l[:],r[:]))
    assert 2*q+(l[0] if l else 0)==s
    # Full ordinary zero rows: weighted bound from their simple zero-edge graph.
    dist=[0]
    for st in range(1,6):
        v=st;seen=set();d=0
        while v!=0 and v not in seen and p[2*v]!="---" and p[2*v][0]=="0":
            seen.add(v);v=ord(p[2*v][2])-65;d+=1
        if v==0:dist.append(d)
    assert n+1+max(dist)<=B
    tag=f"L{index}"
    lines=[f"namespace {tag}","open BB6Coverage.Agent50Zipper BB6Coverage.Agent10ZipAudit",
           f"def p : PartialMachine := FAR.fromCodes {fmt(codes(raw))}"]
    def bs(xs):return bits("".join(map(str,xs)))
    for i,(_,q,h,l,r) in enumerate(points):
        lines.append(f"def z{i} : Z := ⟨{q},({h}),{bs(l)},{bs(r)}⟩")
    for i in range(len(points)-1):
        k=points[i+1][0]-points[i][0]
        lines.append(f"theorem t{i}_{i+1} : zrun p {k} z{i} = some z{i+1} := by rfl")
    def merge(a,b):
        if b==a+1:return f"t{a}_{b}"
        c=(a+b)//2
        x,y=merge(a,c),merge(c,b)
        k=points[b][0]-points[a][0]
        nm=f"t{a}_{b}"
        lines.append(f"theorem {nm} : zrun p {k} z{a} = some z{b} := join {x} {y}")
        return nm
    last=len(points)-1
    trace=merge(0,last)
    lines.append(f"""theorem trace : zrun p {n} start = some z{last} := {trace}
theorem read_ok : zipRead p {n} = some {slot(s)} := by
  unfold zipRead
  rw [trace]
  rfl
theorem checked : zipCheck {B} p (.last {n} {slot(s)}) = true := by
  simp only [zipCheck, zipQueryOK, read_ok] <;> rfl
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide
theorem bound (m : Machine) (hm : compatible p m) : WeightedBound {B} m :=
  (certifiedZip {B} p (.last {n} {slot(s)}) (by decide) nohalt checked).sound m hm
def witness : Machine := weightedTNFDefaultCompletion p
theorem witness_halts : HaltsAfter witness {n} := by
  have hr := zrun_sound p witness (weightedTNFDefaultCompletion_compatible p) {n} start z{last} trace
  rw [start_embed] at hr
  constructor
  · rw [hr]; rfl
  · rw [show {n+1} = {n}+1 by rfl, run_append, hr]
    rfl
#print axioms bound
#print axioms witness_halts
end {tag}""")
    return "\n".join(lines)

def main():
    path=D/"coupled4-candidates.json"
    data=json.loads(path.read_text()) if path.exists() else dict(far=[],auto=[],last=[],unresolved=[])
    manual={
        "1RB1LD1RC0RB1LA1RE1LF0LA0LA0RD1LA---":("Raw13Stride3Counter","zeroLA"),
        "1RB1LD1RC0RB1LA1RE1LF0LA1RA0RD1LA---":("Raw13Stride3Counter","oneRA"),
        "1RB1LD1RC1LE1LA1RE1LF0LA0RC0RD0LE---":("Raw13NestedSweep","oneLE"),
        "1RB1LD1RC1RC1LA1RE1LF0LA0RC0RD0LE---":("Raw13NestedSweep","oneRC"),
    }
    fixtures=[f for f in data["auto"] if f["table"] not in manual]
    auton={x["table"]:i for i,x in enumerate(fixtures)}
    assert len(auton)==len(fixtures)
    emit_fixtures(fixtures,D/(MODULE+"Auto.lean"),MODULE+"Auto")
    from pathlib import Path
    rawlist=(D/"coupled4-hard.txt").read_text().split()
    fw={t:(rev,df) for t,rev,df in data["far"]}
    transfers={}
    transfer_lines=[]
    for srcidx,dstidx,R in [(49,47,35704029313),(51,55,34630289537)]:
        src,dst=rawlist[srcidx],rawlist[dstidx]
        if dst in auton or dst in fw or dst in manual:continue
        tag=f"T{dstidx}"
        if src in auton:
            i=auton[src];sp=f"{AUTO}.p{i}";proof=f"{AUTO}.never{i}"
        elif src in fw:
            rev,df=fw[src];dfa=list(map(int,df));a,b,z=saturate(codes(src),dfa,rev)
            sp=f"{tag}Source";proof=f"{tag}SourceNever";pp=f"(FAR.reflectPartial {sp})" if rev else sp
            transfer_lines += [f"def {sp} : PartialMachine := FAR.fromCodes {fmt(codes(src))}",
                f"def {tag}FAR : FAR.Data {len(dfa)//2} := ⟨0,{fmt(dfa)},{fmt(a)},{fmt(b)},{z}⟩",
                f"theorem {tag}OK : {tag}FAR.fastValid {pp} = true := by decide",
                f"theorem {proof} : ∀ m, compatible {sp} m → NeverHalts m := BB6.Agent31ThreeHole.farSound {sp} {boolean(rev)} {tag}FAR {tag}OK"]
        else:continue
        transfers[dst]=tag
        transfer_lines += [f"def {tag} : PartialMachine := FAR.fromCodes {fmt(codes(dst))}",
            f"theorem {tag}Never : ∀ m, compatible {tag} m → NeverHalts m := BB6.Agent46FiniteStateTransfer.never (p:={sp}) (R:={R}) (by decide) {proof}",
            f"#print axioms {tag}Never"]
    write(MODULE+"Transfer",["FiniteStateTransfer",MODULE+"Auto","Agent46CompleteCut"],"\n".join(transfer_lines))
    late={LATE:(62122,11)}
    for t,n,s in data["last"]:
        if t in late:assert late[t]==(n,s)
        elif n<=B-6:late[t]=(n,s)
    late_names={t:i for i,t in enumerate(late)}
    write(MODULE+"Late",["Raw13Coupled3","Agent46CompleteCut"],
          "\n".join(late_module(t,n,s,late_names[t]) for t,(n,s) in late.items()))
    with tempfile.TemporaryDirectory() as tmp:
        tmp=__import__("pathlib").Path(tmp)
        exe=tmp/"graft"
        subprocess.run(["g++","-std=c++17","-O3",str(D/"frontier_graft.cpp"),"-o",str(exe)],check=True)
        args=[tmp/x for x in ("far","auto","graft.txt","late")]
        args[0].write_text("".join(f"{t} {r} {d}\n" for t,r,d in data["far"]))
        args[1].write_text("\n".join([*auton,*manual,*transfers])+"\n")
        args[2].write_text(GRAFT+"\n")
        args[3].write_text("".join(f"{t} {n} {s}\n" for t,(n,s) in late.items()))
        tree=json.loads(subprocess.check_output([str(exe),str(D/"frontier-dfa-bank.txt"),*map(str,args)],input=ROOT+" 6 4\n",text=True))
    assert tree[:3]==["split",10,10]
    counts,masses=Counter(),Counter();tally(tree,4,6,counts,masses)
    assert sum(masses.values())==25**4
    print("counts",counts,"mass",masses,flush=True)
    def emit(t):
        if t is None:return ".unresolved"
        tag,*v=t
        if tag=="graft":
            assert v[0]==GRAFT
            return ".bounded BB6.Agent46Raw13Coupled3.parent 134 (BB6.Agent46Raw13Coupled3.bound h)"
        if tag=="far":
            raw,rev,df=v;dfa=list(map(int,df));a,b,z=saturate(codes(raw),dfa,rev)
            return f".closed (.far {boolean(rev)} {len(dfa)//2} ⟨0,{fmt(dfa)},{fmt(a)},{fmt(b)},{z}⟩)"
        if tag=="auto":
            if v[0] in transfers:
                tag=transfers[v[0]];return f".closed (.proven {tag} {tag}Never)"
            if v[0] in manual:
                module,x=manual[v[0]];ns="BB6.Agent46"+module
                return f".closed (.proven ({ns}.p .{x}) ({ns}.never .{x}))"
            i=auton[v[0]];return f".closed (.proven {AUTO}.p{i} {AUTO}.never{i})"
        if tag=="late":
            i=late_names[v[0]];return f".bounded L{i}.p {B} L{i}.bound"
        if tag=="split":
            n,s,kids=v
            return f".split {n} {slot(s)} (byCutMove [\n"+",\n".join(map(emit,kids))+"])"
        return leaf_emit(t)
    base="""abbrev parent := BB6.Agent46Raw13CoupledParent.p5
def next (mv : Move) := refine parent (5,false) (some mv)
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ (
  weightedTNFNoAssignedHalt_refine _ _ _ BB6.Agent46Raw13.raw13_nohalt))))
"""
    write(MODULE+"Base",["Raw13Coupled3","Agent46CompleteCut"],base)
    modules=[]
    for i,k in enumerate(tree[3]):
        assert k is not None
        tag=f"{i:02}";name=MODULE+"Kid"+tag;modules.append(name)
        p=f"next {move(MOVES[i])}"
        write(name,[MODULE+"Base",MODULE+"Auto",MODULE+"Late",MODULE+"Transfer","Raw13Stride3Counter"],
              f"def kid{tag} {H} : Cut := {emit(k)}\n"+
              f"theorem checked{tag} {H} : check {B} ({p}) 6 (kid{tag} h) = true := by rfl\n")
    terms=",".join(f"kid{i:02} h" for i in range(24))
    cases="\n".join(f"  · exact checked{12*w+6*r+q:02} h" for q,w,r in product(range(6),range(2),range(2)))
    out=f"""def kids {H} : Move → Cut := byCutMove [{terms}]
theorem kids_checked {H} (mv : Move) : check {B} (next mv) 6 (kids h mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
{cases}
def parentCut {H} : Cut := .split 10 (5,false) (kids h)
theorem parent_checked {H} : check {B} parent 6 (parentCut h) = true := by
  change (zipQueryOK {B} parent 10 (5,false) &&
    BB6.Agent31ThreeHole.allMoves (fun mv =>
      if mv.next.val ≤ 6 then check {B} (next mv) (nextCut 6 mv) (kids h mv) else true)) = true
  simp only [Bool.and_eq_true]
  refine ⟨by decide, BB6.Agent31ThreeHole.allMoves_of _ ?_⟩
  intro mv
  have hv : mv.next.val ≤ 6 := by omega
  have hn : nextCut 6 mv = 6 := by unfold nextCut; omega
  simp [hv,hn,kids_checked h mv]
theorem coverage {H} (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound {B} m ∨ ∃ e ∈ residuals parent 6 (parentCut h), TNFQuotientCompatible e.2 m :=
  sound {B} parent 6 (parentCut h) (by decide) (support6 parent) (by decide)
    parent_nohalt (parent_checked h) m hm
theorem residual_count {H} : (residuals parent 6 (parentCut h)).length = {counts["open"]} := by rfl
theorem residual_mass {H} : openMass 4 6 (parentCut h) = {masses["open"]} := by rfl
#print axioms coverage
#print axioms residual_count
#print axioms residual_mass
"""
    if not counts["open"]:
        out+=f"""
theorem witness_compatible : compatible parent L0.witness := by
  intro s t hs
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;>
    (first | exact hs | contradiction | simp_all [parent, BB6.Agent46Raw13CoupledParent.p5,
      BB6.Agent46Raw13CoupledParent.p4, BB6.Agent46Raw13CoupledParent.p3,
      BB6.Agent46Raw13CoupledParent.p2, BB6.Agent46Raw13CoupledParent.p1,
      BB6.Agent46Raw13.raw13, BB6.Agent46Raw13.afterB, L0.witness, L0.p,
      weightedTNFDefaultCompletion, refine, FAR.fromCodes])

theorem empty_complement {H} : residuals parent 6 (parentCut h) = [] :=
  List.length_eq_zero_iff.mp (residual_count h)
theorem bound_quotient {H} (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound {B} m := by
  rcases coverage h m hm with hb | ⟨e,he,_⟩
  · exact hb
  · rw [empty_complement h] at he
    simp at he
theorem bound {H} (m : Machine) (hm : compatible parent m) : WeightedBound {B} m := by
  let e : StatePerm := ⟨id,id,fun _ => rfl,fun _ => rfl⟩
  apply bound_quotient h m
  refine ⟨e,rfl,?_⟩
  have he : renameTable e m = m := by
    funext s
    rcases s with ⟨q,b⟩
    unfold renameTable
    change (m (q,b)).map (renameMove e) = m (q,b)
    cases hh : m (q,b) with
    | none => rfl
    | some mv => cases mv <;> rfl
  rw [he]
  exact hm
theorem exact_threshold {H} (N : Nat) :
    (∀ m, compatible parent m → WeightedBound N m) ↔ {B} ≤ N := by
  constructor
  · intro hb
    have hd : 0 ∈ delays (zeroNext L0.witness) 0 :=
      (mem_delays_iff (by decide)).mpr ⟨0, TerminalPath.stop 0 (by decide)⟩
    have hw := hb _ witness_compatible 62122 0 L0.witness_halts hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (bound h m hm k d hk hd) hb
#print axioms bound_quotient
#print axioms exact_threshold
"""
    write(MODULE,modules,out)
    (D/"coupled4-tree.json").write_text(json.dumps(tree,separators=(",",":"))+"\n")

if __name__=="__main__":main()
