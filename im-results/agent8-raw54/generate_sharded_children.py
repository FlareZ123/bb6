"""Common exact-source audit sharding for the formerly monolithic LB/LF children."""
from collections import Counter
from generate_ra import Node, zrun, table, refine, all_moves, slot, move, MOVES, fuse_sparse, parse

def assemble(root_dir,tree,certs,deps,parent_code,BOUND,label,namespace,base,expected,threshold=50,leaf_checks=None):
    leaf_checks=leaf_checks or {}
    stats=Counter()
    root=Node(tree,certs,deps,stats)
    assert stats==expected,stats
    # A prechecked expensive leaf must remain an independent theorem.
    def enlarge(node,p):
        if node.children:
            for c,mv in zip(node.children,MOVES):
                enlarge(c,refine(p,node.s,mv))
            node.size=sum(c.size for c in node.children)
        elif node.tag=='open' and p in leaf_checks:
            node.size=threshold+1
    if leaf_checks:enlarge(root,parse(parent_code))
    for module in sorted(set(deps.values())):
        if (root_dir/(module+"Data.lean")).exists():
            fuse_sparse(root_dir,module)
    header=f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace {namespace}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent47PartialAudit
open BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6.Agent48PrefixAudit
"""
    def write(name,imports,body):
        (root_dir/(name+".lean")).write_text("".join("import "+m+"\n" for m in sorted(set(imports)))+header+body+"\nend "+namespace+"\n")
    def emit_tree(node,p,expr,name,t,threshold):
        mod=f"Raw54{label}Shard"+name.removeprefix(label.lower()+"Shard").replace("_","X")
        imports={base}
        body=[]
        def local(n,c,p2,e2,prefix):
            imports.update(c.deps)
            if c.tag=='open' and p2 in leaf_checks:
                module,table_name,proof=leaf_checks[p2]
                imports.add(module)
                body.extend([f"def {n} : Audit := {c.term()}",
                    f"theorem {n}_checked : zipCheck {BOUND} ({e2}) {n} = true := by",
                    f"  have h : ({e2}) = {table_name} := tableOK_sound _ _ (by decide)",
                    "  rw [h]",f"  exact {proof}"])
                return
            body.extend([
                f"def {n} : Audit := {c.term()}",
                f"def {n}Table : PartialMachine := {table(p2)}",
                f"theorem {n}Table_eq : {n}Table = ({e2}) := tableOK_sound _ _ (by decide)",
                f"def {n}Prefix : Z := {zrun(p2,prefix)}",
                f"theorem {n}_checked : zipCheck {BOUND} ({e2}) {n} = true := by",
                f"  rw [← {n}Table_eq, ← checkAt_eq {BOUND} {n}Table {n} {prefix} {n}Prefix (by rfl)]",
                "  decide"])
        if node.size<=threshold or not node.children:
            local(name,node,p,expr,t)
        else:
            names=[]
            for j,c in enumerate(node.children):
                cn=f"{name}_{j:02d}"
                p2=refine(p,node.s,MOVES[j])
                e2=f"refine ({expr}) {slot(node.s)} (some {move(MOVES[j])})"
                if c.size>threshold:
                    imports.add(emit_tree(c,p2,e2,cn,node.n,threshold))
                else:local(cn,c,p2,e2,node.n)
                names.append(cn)
            kids="byMove ["+", ".join(names)+"]"
            body.extend([
                f"def {name} : Audit := .split {node.n} {slot(node.s)} ({kids})",
                f"theorem {name}_checked : zipCheck {BOUND} ({expr}) {name} = true := by",
                f"  change (zipQueryOK {BOUND} ({expr}) {node.n} {slot(node.s)} && allMoves (fun mv => zipCheck {BOUND} (refine ({expr}) {slot(node.s)} (some mv)) ({kids} mv))) = true",
                "  simp only [Bool.and_eq_true]",
                "  refine ⟨by decide, allMoves_of _ ?_⟩",
                all_moves([n+"_checked" for n in names])])
        write(mod,imports,"\n".join(body))
        return mod
    name=label.lower()+"ShardRoot"
    module=emit_tree(root,parse(parent_code),"parent",name,0,threshold)
    write("Raw54"+label+"Complete",[module],f"""theorem complete_checked : zipCheck {BOUND} parent {name} = true := {name}_checked
theorem complete_cover : ∀ m, compatible parent m → WeightedBound {BOUND} m :=
  (certifiedZip {BOUND} parent {name} parent_root parent_nohalt complete_checked).sound
#print axioms complete_cover""")
    print(stats,"root module",module,flush=True)
