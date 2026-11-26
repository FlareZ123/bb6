"""Recreate the two A1=0RB n-gram witnesses from the source-accepted checker."""
from pathlib import Path
from itertools import product
import sys, subprocess, tempfile
ROOT=Path(__file__).resolve().parent
NG=ROOT.parent/'agent1-ngram'
sys.path.insert(0,str(NG))
from emit_ngram import emit
cases={655:('1RB0RB1RC0LE0RD0RA1LD1LA1LF1RB1LC---',11,4971),
       515:('1RB0RB1RC1RE0RD---1LD1LA0RB1LF1RE0LF',10,3041)}
def build(selected):
    with tempfile.TemporaryDirectory() as tmp:
        exe=Path(tmp)/'ngram'
        subprocess.run(['g++','-std=c++17','-O3',str(NG/'ngram.cpp'),'-o',str(exe)],check=True)
        for i in selected:
            table,k,n=cases[i]
            data=subprocess.run([str(exe),str(k)],input=f'{i} {table}\n',text=True,capture_output=True,check=True).stdout.strip()
            ident,cert=data.split(maxsplit=1)
            assert int(ident)==i and tuple(map(int,cert.split()[:2]))==(k,n)
            name=f'Raw40ZeroRBNGram{i}'
            ns=f'BB6.Agent19Raw40.ZeroRBNGram{i}'
            body=emit(i,table,cert)
            old=f'theorem ok{i} : check p{i} c{i} = true := by decide'
            checks=[]
            for q,a in product(range(6),['false','true']):
                checks.append(f'theorem row{q}{a} : (row c{i} {q} {a}).all (fun j => stateStepOK p{i} c{i} {q} {a} (j/2^(c{i}.n+1)) (j%2^(c{i}.n+1))) = true := by decide')
            checks.append(f'''theorem ok{i} : check p{i} c{i} = true := by
  unfold check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨by decide, by decide⟩, by decide⟩, ?_⟩
  apply List.all_eq_true.mpr
  intro q _
  apply List.all_eq_true.mpr
  intro a _
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases a''')
            checks += [f'  · exact row{q}{a}' for q,a in product(range(6),['false','true'])]
            assert old in body
            body=body.replace(old,'\n'.join(checks))
            (ROOT/(name+'.lean')).write_text(f'''import NGramCertificate
set_option maxRecDepth 6000000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6.Agent1NGram
{body}
def table : PartialMachine := p{i}
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never{i} m hm
#print axioms never
end {ns}
''')
if __name__=='__main__': build(list(map(int,sys.argv[1:])) or list(cases))
