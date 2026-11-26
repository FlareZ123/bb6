"""Deterministically emit independently kernel-checkable n-gram proof modules.
Uses Agent1's generator/checker; large witnesses get one check per state/bit row."""
from pathlib import Path
from itertools import product
import sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent1-ngram'))
from emit_ngram import emit

def render(i,table,cert,ns):
    body=emit(i,table,cert)
    old=f'theorem ok{i} : check p{i} c{i} = true := by decide'
    k,n=map(int,cert.split()[:2]);checks=[]
    if n>=1000:
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
    return f'''namespace {ns}
open BB6Coverage BB6.Agent1NGram
{body}
def table : PartialMachine := p{i}
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m := never{i} m hm
#print axioms never
end {ns}
'''

def generate(p:Path,fam,c):
    tables=dict(l.split() for l in (p/'miss6.txt').read_text().splitlines())
    mods=[]; proven=[]
    header='import NGramCertificate\nset_option maxRecDepth 6000000\nset_option maxHeartbeats 0\n'
    group=[];count=0;j=0
    def emit_group():
        nonlocal j,count,group
        if not group:return
        name=f'Raw40A{fam}{c}NGram{j:02}'
        (ROOT/(name+'.lean')).write_text(header+'\n'.join(group))
        mods.append(name);j+=1;count=0;group=[]
    for line in (p/'ngram.txt').read_text().splitlines():
        i,cert=line.split(maxsplit=1);k,n=map(int,cert.split()[:2]);ns=f'BB6.Agent19Raw40.A{fam}{c}NGram.Leaf{i}'
        if count+n>2000:emit_group()
        group.append(render(i,tables[i],cert,ns));count+=n;proven.append((int(i),ns))
    emit_group();return mods,proven
if __name__=='__main__': print(generate(Path(sys.argv[1]),sys.argv[2],sys.argv[3]))
