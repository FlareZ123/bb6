"""Regenerate complete translated-cycle/last-hole proofs for 46 Raw47 D3 cylinders.
Usage: python generate_closed.py WORKDIR OUTPUTDIR
WORKDIR contains executable cut (agent7-raw49/cut.cpp) and d3.open.
"""
import json, pathlib, sys, subprocess, hashlib
root = pathlib.Path(sys.argv[1]).resolve()
out = pathlib.Path(sys.argv[2]).resolve()
out.mkdir(parents=True, exist_ok=True)
ids = [5,77,108,121,122,123,124,131,239,265,352,355,356,359,362,365,370,371,394,396,399,406,417,437,438,442,513,685,716,1011,1014,1019,1025,1028,1033,1048,1051,1052,1056,1063,1071,1080,1118,1135,1174,1185]
assert hashlib.sha256((root/'d3.open').read_bytes()).hexdigest() == '4ae501c6ae90d482f77d8ba65b060717112e402571f887c20fdcd4c4b0bce41d'
tables = (root/'d3.open').read_text().splitlines()
def b(x): return str(bool(x)).lower()
def slot(s): return f'({s//2},{b(s%2)})'
def emit(t):
    tag,*a=t
    if tag=='cycle': return f'.cycle {a[0]} {a[1]} {b(a[2])} ({a[3]})'
    if tag=='last': return f'.last {a[0]} {slot(a[1])}'
    if tag=='split': return f'.split {a[0]} {slot(a[1])} (byMove [\n'+',\n'.join(map(emit,a[2]))+'\n])'
    raise ValueError(t)
for i in ids:
    table=tables[i]; path=out/f'cut{i}'
    subprocess.run([str(root/'cut'),table,'1000','32','7',str(path)],check=True,stdout=subprocess.DEVNULL)
    assert not path.with_suffix('.open').read_text()
    tree=json.loads(path.with_suffix('.json').read_text())
    rows=[]
    for s in range(12):
        x=table.replace('_','')[3*s:3*s+3]
        if x!='---': rows.append(f'  | {s//2},{b(s%2)} => some (some ⟨{b(int(x[0]))},{b(x[1]=="R")},{ord(x[2])-65}⟩)')
    source=f'''import CanonicalPartial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50.Raw47D3C{i}
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

def p : PartialMachine := fun s =>
  match s.1.val,s.2 with
'''+ '\n'.join(rows)+'''
  | _,_ => none
theorem root : p initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt p := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

def tree : Audit := '''+emit(tree)+'''
theorem checked : prefixCheck 227 p tree = true := by decide
theorem bound (m : Machine) (hm : compatible p m) : WeightedBound 227 m :=
  (certifiedZip 227 p tree root nohalt (by simpa only [prefixCheck_eq] using checked)).sound m hm
theorem all_quotient (m : Machine) (hm : TNFQuotientCompatible p m) : WeightedBound 227 m :=
  quotientSafe root bound m hm
#print axioms all_quotient
end BB6.Agent50.Raw47D3C'''+str(i)+'\n'
    (out/f'Raw47D3C{i}.lean').write_text(source)
