#!/usr/bin/env python3
"""Generate a compositional *membership* certificate for the Raw56 1LB parent.

Avoids the monolithic 24-branch residual trace/list equality. Every local
proof uses existing independently checked child equation nr_XX and the eight
source-preserving parent table equalities. Soundness derives from canonicalSound
plus canonicalResiduals_split_subset, not from trusting this generator.
"""
import argparse
from pathlib import Path
from split_lb_parent import split_parent, NS

ORDER = [0,6,12,18,1,7,13,19,2,8,14,20,3,9,15,21,4,10,16,22,5,11,17,23]
TABLES = [6168,21109,21049,23706,39232,39234,39233,42763]
EQ = ",".join("eq"+str(i) for i in TABLES)

def generate(prep: Path, helper: Path):
    split_parent(prep)
    d=prep/"E11LB"
    reduced=(d/"Raw56LBE11LBReduced.lean").read_text()
    assert reduced.count("abbrev table6168 :=")==1
    assert reduced.count("theorem residual_tables :")==1
    block=reduced[reduced.index("abbrev table6168 :="):reduced.index("theorem residual_tables :")]
    hardline=next(x for x in reduced.splitlines() if x.startswith("def hardTables :"))
    assert all(("theorem eq"+str(i)+" :") in block for i in TABLES)
    base=reduced[:reduced.index("abbrev table6168 :=")].replace("import Raw56LBE11LBAll","import Raw56LBTopDefs",1)
    alltable="def allTables : List PartialMachine := ["+",".join("table"+str(i) for i in TABLES)+"]\n"
    tabletxt=base+block+"\n"+alltable+hardline+"\n#print axioms eq42763\nend "+NS+"\n"
    (d/"Raw56LBTopTables.lean").write_text(tabletxt)
    scripthelper=helper.read_text()
    (d/"CanonicalResidualSubset.lean").write_text(scripthelper)
    # Elaborate each child independently; the only nontrivial closed worlds
    # are the eight nonempty residual lists. Use propositional simplification
    # after rewriting list membership to the original eight table names.
    children=[]
    for k in ORDER:
        kk=f"{k:02}"
        children.append(f"""
theorem subset_{kk} (e : List Move × PartialMachine)
    (he : e ∈ canonicalResiduals p_{kk} 5 t_{kk}) : e.2 ∈ allTables := by
  have h : e.2 ∈ (canonicalResiduals p_{kk} 5 t_{kk}).map Prod.snd :=
    List.mem_map_of_mem Prod.snd he
  simp only [nr_{kk},List.map_nil,List.map_cons,{EQ},
    List.mem_cons,List.not_mem_nil,or_false] at h
  all_goals simp only [allTables,List.mem_cons,List.not_mem_nil,or_false]
  all_goals simp_all
  all_goals grind
""")
    childrenSource=("import Raw56LBTopTables\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace "+NS+"\n"+ "\n".join(children)+"\n#print axioms subset_23\nend "+NS+"\n")
    (d/"Raw56LBTopChildren.lean").write_text(childrenSource)
    # First-query discrimination exactly mirrors the source-accepted cktop
    # proof's 24 terms, so it never expands a giant concatenated list.
    branches="\n".join("  · exact subset_"+f"{k:02}"+" x hx" for k in ORDER)
    root="""import Raw56LBTopChildren
import CanonicalResidualSubset
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent4Raw56LB.E11LB
open BB6Coverage BB6.Agent19CanonicalPartial

theorem root_residual_subset (e : List Move × PartialMachine)
  (he : e ∈ canonicalResiduals ptop 5 ttop) : e.2 ∈ allTables := by
  refine BB6.Agent4Raw56Root.canonicalResiduals_split_subset ptop 5 8 (2,true) ktop allTables ?_ e he
  intro mv x hx
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
"""+branches+"\n#print axioms root_residual_subset\nend "+NS+"\n"
    (d/"Raw56LBTopSubset.lean").write_text(root)
    source_head=reduced[:reduced.index("abbrev table6168 :=")]
    assert "import Raw56LBE11LBAll" in source_head
    source_head=source_head.replace("import Raw56LBE11LBAll",
        "import Raw56LBTopSubset\nimport Raw56LBTopChecks",1)
    theorem=reduced[reduced.index("theorem reduced_quotient :"):]
    original_call="rcases partial_quotient m hm with h | ⟨e,he,hc⟩"
    new_call="rcases canonicalSound 1000000 p 5 ttop (by decide) supported root nohalt ctop m hm with h | ⟨e,he,hc⟩"
    assert theorem.count(original_call)==1
    theorem=theorem.replace(original_call,new_call,1)
    old_mid=("have hh : e.snd ∈ residuals.map Prod.snd := List.mem_map_of_mem Prod.snd he\n"
             "    rw [residual_tables] at hh")
    assert theorem.count(old_mid)==1
    theorem=theorem.replace(old_mid,"have hh : e.snd ∈ allTables := root_residual_subset e he",1)
    reduction=source_head+theorem
    assert reduction.count("theorem reduced_quotient :")==1
    assert "theorem residual_tables :" not in reduction
    (d/"Raw56LBTopSubsetReduction.lean").write_text(reduction)
    for n in ("Raw56LBTopTables","Raw56LBTopChildren","Raw56LBTopSubset","Raw56LBTopSubsetReduction"):
        print("SOURCE",n,len((d/(n+".lean")).read_text()),flush=True)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--prep",type=Path,required=True)
    p.add_argument("--helper",type=Path,required=True)
    a=p.parse_args()
    generate(a.prep,a.helper)

if __name__=="__main__":
    main()
