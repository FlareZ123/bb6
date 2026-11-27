#!/usr/bin/env python3
"""Generate conditional or complete 25-way parent consumer from accepted banks."""
import json,pathlib,sys
out=pathlib.Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
expected=json.loads(pathlib.Path(__file__).with_name("child-banks.json").read_text())
known={};B=187672026
codes=[0,1,2,3,4,5,6,7,8,9,10,13,15,19,20,21,22,23]
for directory in map(pathlib.Path,sys.argv[2:]):
    paths=([directory/"manifest.json"] if (directory/"manifest.json").is_file() else
           [p for p in directory.rglob("manifest.json") if "reuse" not in p.relative_to(directory).parts]);assert len(paths)==1,paths
    m=json.loads(paths[0].read_text());c=m["claim"]
    t=json.loads(c["parent_table"]);i=t[5]
    assert t==[7,24,11,24,14,i,24,16,6,11,24,24] and i in codes
    assert i not in known
    if str(i) in expected:assert str(m["workflow"]["run_id"])==str(expected[str(i)][0])
    assert c["weighted_bound"]<=B
    assert c["theorem"].endswith(".weighted"),c
    ns=c["theorem"].rsplit(".",1)[0]
    assert len(m["roots"])==1,m["roots"]
    known[i]=(m["roots"][0]["module"],ns,c["weighted_bound"])
missing=[i for i in codes if i not in known]
assert set(missing)<={1,9,21},missing
lines=["import ParentCore",*("import "+a[0] for a in known.values()),"""set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace BB6.Agent3OneLBParent
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent31ThreeHole
"""]
for i,(_,ns,b) in known.items():
    lines.append(f"""theorem cover{i} : Cover (WeightedBound B) (child {i}) := by
  have ht : child {i} = {ns}.parent := tableOK_sound _ _ (by decide +kernel)
  rw [ht]
  exact Cover.leaf _ (fun m hm k d hk hd =>
    Nat.le_trans ({ns}.weighted.sound m hm k d hk hd) (by decide : {b} ≤ B))
""")
args=" ".join(f"(h{i} : Cover (WeightedBound B) (child {i}))" for i in missing)
lines.append(f"theorem parent_cover {args} : Cover (WeightedBound B) parent := by")
lines.append("  apply parent_cover_of\n  intro i hi\n  simp only [openCodes,List.mem_cons,List.not_mem_nil,or_false] at hi")
lines.append("  rcases hi with "+" | ".join("rfl" for i in codes))
lines.extend("  · exact "+(f"h{i}" if i in missing else f"cover{i}") for i in codes)
if not missing:
    lines.append("""theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound B m :=
  parent_cover.sound
theorem cover_at {M : Nat} (hM : B ≤ M) : Cover (WeightedBound M) parent :=
  Cover.leaf _ (fun m hm k d hk hd =>
    Nat.le_trans (all_completions_weighted m hm k d hk hd) hM)
#print axioms all_completions_weighted
#print axioms cover_at""")
lines.extend(["#print axioms parent_cover","end BB6.Agent3OneLBParent"])
(out/("ParentAssembly.lean" if not missing else "ParentPartial.lean")).write_text("\n".join(lines)+"\n")
print("Missing explicit parent premises:",missing)
