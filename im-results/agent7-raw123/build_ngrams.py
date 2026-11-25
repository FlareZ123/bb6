"""Recreate fixed n-gram witnesses. Each row is independently kernel checked."""
from pathlib import Path
from itertools import product
import sys, subprocess, tempfile
ROOT=Path(__file__).resolve().parent
NG=ROOT.parent/"agent1-ngram"
sys.path.insert(0,str(NG))
from emit_ngram import emit

def rows():
    return [line.split() for line in (ROOT/"special.txt").read_text().splitlines() if line and not line.startswith("#") and line.split()[1]=="N"]

def build(selected):
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/"ngram"
        subprocess.run(["g++","-std=c++17","-O3",str(NG/"ngram.cpp"),"-o",str(exe)],check=True)
        for j,(table,kind,k) in enumerate(rows()):
            if j not in selected:continue
            data=subprocess.run([str(exe),k],input=f"{j} {table}\n",text=True,capture_output=True,check=True).stdout.strip()
            idx,cert=data.split(maxsplit=1);assert int(idx)==j and int(cert.split()[0])<=int(k)
            name=f"Raw123NGram{j:02}";ns=f"BB6.Agent7{name}"
            body=emit(j,table,cert)
            old=f"theorem ok{j} : check p{j} c{j} = true := by decide"
            checks=[]
            for q,a in product(range(6),["false","true"]):
                checks.append(f"theorem row{q}{a} : (row c{j} {q} {a}).all (fun i => stateStepOK p{j} c{j} {q} {a} (i/2^(c{j}.n+1)) (i%2^(c{j}.n+1))) = true := by decide")
            checks.append(f"""theorem ok{j} : check p{j} c{j} = true := by
  unfold check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro a _
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a""")
            checks += [f"  · exact row{q}{a}" for q,a in product(range(6),["false","true"])]
            assert old in body
            body=body.replace(old,"\n".join(checks))
            (ROOT/(name+".lean")).write_text(f"""import NGramCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent1NGram
{body}
def table : PartialMachine := p{j}
theorem never_source (m : Machine) (hm : compatible table m) : NeverHalts m := never{j} m hm
#print axioms never_source
end {ns}
""")
            print(name,k,cert.split()[1],flush=True)

if __name__=="__main__":
    build(set(map(int,sys.argv[1:])) if len(sys.argv)>1 else set(range(len(rows()))))
