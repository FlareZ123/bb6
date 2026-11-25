"""Generate actual source-level nonhalting certificates for selected raw110 leaves."""
from pathlib import Path
import sys,json,subprocess
from generate_multi import generate
root=Path(__file__).resolve().parent
rows=json.loads((root/'Raw110Candidates.json').read_text())
selected={int(x) for x in sys.argv[1:]} if len(sys.argv)>1 else {r['kid'] for r in rows}
rows=[r for r in rows if r['kid'] in selected]
widths=sorted({r['width'] for r in rows}-{3})
if widths:subprocess.run([sys.executable,str(root/'specialize.py'),*map(str,widths)],check=True)
for p in rows:
    name=f'Raw110B{p["kid"]:02d}L{p["j"]:03d}'
    width=p['width'];suffix="" if width==3 else str(width);ns="BB6BlockFAR"+suffix+"."+name
    print(name,flush=True)
    generate(p['table'],root,width,p['cap'],p['mod'],p['runs'],p['flip'],name)
    s=f"""import {name}Proof
import BlockFARBridge{suffix}
"""
    if p['flip']:s+="import FARBi\n"
    s+=f"""
namespace BB6.Agent13{name}
open BB6Coverage

"""
    if not p['flip']:
        s+=f"""def table : PartialMachine := BB6BlockFAR{suffix}.partialTable {ns}.machine
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6BlockFAR{suffix}.transfer_never {ns}.machine m hm {ns}.never
"""
    else:
        s+=f"""open BB6Coverage.FAR

def table : PartialMachine := reflectPartial (BB6BlockFAR{suffix}.partialTable {ns}.machine)

theorem reflect_table : reflectPartial table = BB6BlockFAR{suffix}.partialTable {ns}.machine := by
  funext x
  rcases x with ⟨q,b⟩
  have h : ∀ q : Fin 6, ∀ b : Bool, reflectPartial table (q,b) = BB6BlockFAR{suffix}.partialTable {ns}.machine (q,b) := by decide
  exact h q b

theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := by
  apply reflectNever m
  apply BB6BlockFAR{suffix}.transfer_never {ns}.machine (reflectTable m)
  · rw [← reflect_table]
    exact reflectCompatible table m hm
  · exact {ns}.never
"""
    s+=f"\n#print axioms never\nend BB6.Agent13{name}\n"
    (root/(name+".lean")).write_text(s)
