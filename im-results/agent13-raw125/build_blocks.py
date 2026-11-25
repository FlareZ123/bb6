"""Regenerate selected exact block-FAR witnesses and source bridges."""
from pathlib import Path
import re, sys, subprocess
ROOT=Path(__file__).resolve().parent
BLOCK=ROOT.parent/"agent13-block-far"
sys.path.insert(0,str(BLOCK))
from generate_multi import generate

def rows():
    return [line.split() for line in (ROOT/"special.txt").read_text().splitlines() if line and not line.startswith("#") and line.split()[1]=="B"]

def specialize_sparse(width):
    if width==3:return
    s=(BLOCK/"SparseBlockFAR.lean").read_text()
    k=2**width
    s=re.sub(r"\b48\b",str(6*k),s)
    s=re.sub(r"\b8\b",str(k),s)
    s=s.replace("import BlockFAR",f"import BlockFAR{width}").replace("namespace BB6BlockFAR","namespace BB6BlockFAR"+str(width)).replace("end BB6BlockFAR","end BB6BlockFAR"+str(width))
    (BLOCK/f"SparseBlockFAR{width}.lean").write_text(s)

def build(selected):
    entries=[(j,r) for j,r in enumerate(rows()) if j in selected]
    widths=sorted({int(r[2]) for _,r in entries}-{3})
    if widths:subprocess.run([sys.executable,str(BLOCK/"specialize.py"),*map(str,widths)],check=True)
    for w in widths:specialize_sparse(w)
    for j,(table,kind,w,cap,mod,runs,flip) in entries:
        width,cap,mod,runs,flip=map(int,(w,cap,mod,runs,flip))
        name=f"Raw125Block{j:02}";suffix="" if width==3 else str(width)
        ns="BB6BlockFAR"+suffix+"."+name
        # Sparse lookup avoids enormous packed arrays for large alphabets.
        sparse=width>=5
        generate(table,ROOT,width,cap,mod,runs,bool(flip),name,minimize_left=sparse,sparse=sparse)
        s=f"import {name}Proof\nimport BlockFARBridge{suffix}\n"
        if flip:s+="import FARBi\n"
        s+=f"\nnamespace BB6.Agent13{name}\nopen BB6Coverage\n\n"
        if not flip:
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
        (ROOT/(name+".lean")).write_text(s)
        print(name,"generated",flush=True)

if __name__=="__main__":
    build(set(map(int,sys.argv[1:])) if len(sys.argv)>1 else set(range(len(rows()))))
