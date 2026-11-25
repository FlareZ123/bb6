"""Source-level structural audit partitioning shared with the accepted raw110 proof."""
from pathlib import Path
from dataclasses import dataclass
from itertools import product
from generate_four_hole import move
ROOT=Path(__file__).resolve().parent
MOVES=[w+d+q for w,d,q in product("01","LR","ABCDEF")]
B=10000
NS="BB6.Agent7Raw123"
HEADER=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {NS}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
"""
def emit(name,imports,lines):
    (ROOT/(name+".lean")).write_text("".join(f"import {i}\n" for i in imports)+HEADER+"\n".join(lines)+f"\nend {NS}\n")

@dataclass
class Node:
    head: str
    children: list | None = None
    size: int = 1
    open_count: int = 0

def render(n):
    if n.children is None:
        return n.head
    if n.open_count==0:
        return n.head+" (byMove [\n"+",\n".join(render(k) for k in n.children)+"])"
    return n.head+" (byPartialMove [\n"+",\n".join(render_partial(k) for k in n.children)+"])"

def render_partial(n):
    return "(.closed ("+render(n)+"))" if n.open_count==0 else render(n)

def build_module(node,p,rootname,imports,limit=180,shardlimit=9000):
    """Chunk proofs structurally. Closed regions stay Audit so residual
    extraction never visits their certificate data."""
    shards=[]
    def local(n,p,name,code):
        partial=n.open_count!=0
        ty="PartialAudit" if partial else "Audit"
        checker="partialCheck" if partial else "zipCheck"
        if n.size<=limit:
            code.append(f"def {name} : {ty} := {render(n)}\ntheorem {name}_checked : {checker} {B} {p} {name} = true := by rfl\n")
            return
        n0,s0=n.head.removeprefix(".split ").split(" ",1)
        child_names=[]
        for j,k in enumerate(n.children):
            kname=f"{name}_k{j:02}"
            kp=f"(refine {p} {s0} (some {move(MOVES[j])}))"
            local(k,kp,kname,code)
            child_names.append(kname if not partial or k.open_count else f"(.closed {kname})")
        bymove="byPartialMove" if partial else "byMove"
        kidexpr=f"({bymove} ["+",".join(child_names)+"])"
        code.append(f"def {name} : {ty} := {n.head} {kidexpr}\ntheorem {name}_checked : {checker} {B} {p} {name} = true := by")
        code.append(f"  change (zipQueryOK {B} {p} {n0} {s0} && allMoves (fun mv => {checker} {B} (refine {p} {s0} (some mv)) ({kidexpr} mv))) = true")
        code.append("""  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r""")
        for q,w,r in product(range(6),range(2),range(2)):
            code.append(f"  · exact {name}_k{12*w+6*r+q:02}_checked")
    def descend(n,p,name):
        if n.size<=shardlimit:
            mod=f"Raw123Shard_{name}"
            code=[]
            local(n,p,name,code)
            emit(mod,imports,code)
            return mod
        # Recursively emit child modules; parent only checks first-hole split.
        n0,s0=n.head.removeprefix(".split ").split(" ",1)
        child_names=[]; child_mods=[]
        for j,k in enumerate(n.children):
            kname=f"{name}_k{j:02}"
            child_mods.append(descend(k,f"(refine {p} {s0} (some {move(MOVES[j])}))",kname))
            child_names.append(kname if not n.open_count or k.open_count else f"(.closed {kname})")
        partial=n.open_count!=0
        ty="PartialAudit" if partial else "Audit"
        checker="partialCheck" if partial else "zipCheck"
        bymove="byPartialMove" if partial else "byMove"
        kidexpr=f"({bymove} ["+",".join(child_names)+"])"
        code=[f"def {name} : {ty} := {n.head} {kidexpr}",f"theorem {name}_checked : {checker} {B} {p} {name} = true := by",
        f"  change (zipQueryOK {B} {p} {n0} {s0} && allMoves (fun mv => {checker} {B} (refine {p} {s0} (some mv)) ({kidexpr} mv))) = true",
        """  simp only [Bool.and_eq_true]
  refine ⟨by rfl, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r"""]
        for q,w,r in product(range(6),range(2),range(2)):
            code.append(f"  · exact {name}_k{12*w+6*r+q:02}_checked")
        mod=f"Raw123Shard_{name}"
        emit(mod,child_mods,code)
        return mod
    return descend(node,p,rootname)

