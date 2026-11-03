"""Generate a kernel-checkable Machine C mixed96 certificate from scratch.

Generated BFS is untrusted. Lean must check every PBlock and AllBlocks
before the candidate exclusion is asserted. All writes are locked + atomic.
"""
from collections import deque
from pathlib import Path
import fcntl
import os
import tempfile

MA=MK=96
MC=48
NA=NK=96
NC=50

def nextc(a,k,c):
    if c==1: return a,k+1,0
    if c==2: return None
    if c==3: return a,k+2,1
    if c==0:
        if a==0: return 1,0,2*k+2
        if a==1: return (5,0,1) if k==0 else (2,2,2*k-1)
        return a-2,1,2*k+1
    if a==0:
        return (2*k+2,2,c-3) if k%2==0 else (2*k+3,0,c)
    return a-1,k+1,c-1

def qc(c):
    return c if c<2 else 2+(c-2)%48

def index(a,k,c):
    return (a*96+k)*50+c

def graph():
    seen=bytearray(NA*NK*NC)
    start=index(5,0,1)
    seen[start]=1
    queue=deque([start])
    edges=0
    while queue:
        i=queue.popleft()
        a=i//(96*50); k=i//50%96; c=i%50
        for aa in (a,a+96):
            for kk in (k,k+96):
                for cc in ((c,) if c<2 else (c,c+48)):
                    t=nextc(aa,kk,cc)
                    if t is None: continue
                    edges+=1
                    j=index(t[0]%96,t[1]%96,qc(t[2]))
                    if not seen[j]:
                        seen[j]=1
                        queue.append(j)
    assert (sum(seen),edges)==(260672,2022544)
    assert seen[start] and not seen[index(13,31,0)]
    return seen

def atomic_write(path,content):
    path=Path(path)
    path.parent.mkdir(parents=True,exist_ok=True)
    lockfd=os.open(str(path)+".lock",os.O_RDWR|os.O_CREAT,0o600)
    with os.fdopen(lockfd,"r") as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        fd,temp=tempfile.mkstemp(dir=path.parent,prefix=".a41-",suffix=".tmp")
        try:
            with os.fdopen(fd,"w",encoding="utf-8") as out:
                out.write(content)
                out.flush()
                os.fsync(out.fileno())
            os.replace(temp,path)
        finally:
            if os.path.exists(temp):
                os.unlink(temp)
            fcntl.flock(lock,fcntl.LOCK_UN)

def generate(root):
    root=Path(root)
    seen=graph()
    rows=[sum(int(seen[index(a,k,c)])<<c for c in range(50))
          for a in range(96) for k in range(96)]
    text="import Std\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace A41\n"
    text+="def getRow96 (a:Nat): Array Nat :=\n  match a with\n"
    for a in range(96):
        text+=f"  | {a} => #["+",".join(map(str,rows[a*96:(a+1)*96]))+"]\n"
    text+="  | _ => #[]\n\n"
    text+="def s96 (a k c:Nat):Bool := if a<96 && k<96 && c<50 then Nat.testBit ((getRow96 a)[k]!) c else false\n"
    text+="theorem s96_origin : s96 5 0 1 = true := by decide\n"
    text+="theorem s96_target : s96 13 31 0 = false := by decide\nend A41\n"
    atomic_write(root/"Rows96Split.lean",text)
    for a in range(96):
        block=f"""import Mixed96Finite
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace A41
theorem pblock{a} : (List.range 96).all (checkRow {a}) = true := by decide
#print axioms pblock{a}
end A41
"""
        atomic_write(root/f"PBlock{a}.lean",block)
    source="".join(f"import PBlock{a}\n" for a in range(96))
    source+="import Lean.Elab.Tactic.Omega\nnamespace A41\n"
    source+="theorem allRows : (List.range 96).all (fun a => (List.range 96).all (checkRow a))=true := by\n"
    source+="  apply List.all_eq_true.mpr\n  intro a ha\n"
    source+="  have halt : a<96 := by simpa using List.mem_range.mp ha\n"
    source+="  have cases : "+" ∨ ".join(f"a={a}" for a in range(96))+" := by omega\n"
    source+="  rcases cases with "+" | ".join(["rfl"]*96)+"\n"
    for a in range(96):
        source+=f"  · exact pblock{a}\n"
    source+="#print axioms allRows\nend A41\n"
    atomic_write(root/"AllBlocks.lean",source)
    print("B0/B0/B2 mixed96:",sum(seen),"/",len(seen),"reached;",
          "generated 96 independent Lean block certificates")

if __name__=="__main__":
    import sys
    generate(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent)
