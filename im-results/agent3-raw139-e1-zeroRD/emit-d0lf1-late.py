#!/usr/bin/env python3
"""Exact packed first-query certificates for the four long ordinary D0=1LF leaves.
Snapshots are untrusted; every bounded segment and the final Cover are kernel checked.
The fast transition bridge is adapted from Agent48's emit_late.py.
"""
from pathlib import Path
import sys
CASES={
1101:([7,19,11,20,14,24,22,16,1,13,4,18],148136,5),
1106:([7,19,11,20,14,24,22,16,1,13,4,19],134470,5),
2775:([7,22,11,6,14,11,22,16,24,13,2,4],11175,8),
2962:([7,20,11,7,14,10,22,16,24,13,2,16],31937,8),
}
B=148142

def generate(out, key, chunk=4000):
    table,n,s=CASES[key]
    assert table[s]==24 and table.count(24)==1 and n+6<=B
    prefix=f'D0LF1Late{key}'; ns=f'BB6.Agent3D0LF1Late.H{key}'
    hdr=f'''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath BB6Coverage.Agent10ZipAudit
'''
    def write(suffix,body):
        (out/(prefix+suffix+'.lean')).write_text(body+f'end {ns}\n')
    bit=lambda v:str(bool(v)).lower()
    code='import PackedAudit\n'+hdr+f'def parent : PartialMachine := fromCodes {table}\ndef lookup (q : Fin 6) (b : Bool) : Option Move :=\n  match q.val,b with\n'
    for i,v in enumerate(table):
        code+=f'  | {i//2},{bit(i%2)} => '+('none' if v==24 else f'some ⟨{bit(v&2)},{bit(v&1)},{v//4}⟩')+'\n'
    code+='  | _,_ => none\n'+'''def tab : PartialMachine := fun s => (lookup s.1 s.2).map some
theorem same : parent = tab := tableOK_sound _ _ (by decide +kernel)
def stepFast (z : P) : Option P := (lookup z.q (z.l % 2 == 1)).map (fun mv => moveP mv z)
theorem stepFast_eq (z : P) : stepP parent z = stepFast z := by
  rw [same]
  unfold stepP stepFast readP tab
  cases lookup z.q (z.l % 2 == 1) <;> rfl
def runFast : Nat → P → Option P
  | 0,z => some z
  | n+1,z => (stepFast z).bind (runFast n)
theorem runFast_eq (n : Nat) (z : P) : runFast n z = runP parent n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    simp only [runFast,runP,stepFast_eq]
    cases h : stepFast z with
    | none => rfl
    | some u => exact ih u
theorem join {n k : Nat} {a b c : P}
    (h : runFast n a = some b) (g : runFast k b = some c) :
    runFast (n+k) a = some c := by
  simp only [runFast_eq] at h g ⊢
  exact joinP h g
'''
    write('Core',code)
    q=l=r=0; cuts=[0]; cfg='import '+prefix+'Core\n'+hdr+'def z0 : P := startP\n'
    for i in range(n):
        v=table[2*q+l%2];assert v!=24,(key,i)
        w=v//2%2;q=v//4
        if v%2:l=r%2+2*w+4*(l//2);r//=2
        else:l//=2;r=w+2*r
        if (i+1)%chunk==0 or i+1==n:
            cuts.append(i+1);cfg+=f'def z{i+1} : P := ⟨{q},{hex(l)},{hex(r)}⟩\n'
    assert 2*q+l%2==s
    write('Configs',cfg); names=[]; terms=[]
    for j in range(0,len(cuts)-1,4):
        mod=f'Step{j//4:03}';names.append(prefix+mod);code='import '+prefix+'Configs\n'+hdr
        for a,b in zip(cuts[j:j+4],cuts[j+1:j+5]):
            code+=f'theorem c{a} : runFast {b-a} z{a} = some z{b} := by decide +kernel\n';terms.append((a,b,f'c{a}'))
        write(mod,code)
    agg=[]
    def combine(ts):
        if len(ts)==1:return ts[0][2]
        mid=len(ts)//2;a,b,c=ts[0][0],ts[mid][0],ts[-1][1]
        l,r=combine(ts[:mid]),combine(ts[mid:]);name=f'agg{a}_{c}'
        agg.append(f'theorem {name} : runFast {c-a} z{a} = some z{c} := @join {b-a} {c-b} z{a} z{b} z{c} {l} {r}\n')
        return name
    joined=combine(terms)
    code=''.join(f'import {m}\n' for m in names)+hdr+''.join(agg)+f'''theorem reached : runP parent {n} startP = some z{n} := by
  rw [← runFast_eq]
  exact {joined}
theorem checked : packedCheck {B} parent (.last {n} ({s//2},{bit(s%2)})) = true := by
  simp only [packedCheck,packedQueryOK,readRunP,reached,Option.map_some]
  decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({table} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
theorem cover : Cover (WeightedBound {B}) parent :=
  (certifiedPacked {B} parent _ root nohalt checked).toCover
#print axioms reached
#print axioms checked
#print axioms cover
'''
    write('',code)
    print(key,n,s,len(terms),'chunks', 'final q,l,r bits',q,l.bit_length(),r.bit_length())
    return prefix
if __name__=='__main__':
    out=Path(sys.argv[1]);out.mkdir(parents=True,exist_ok=True)
    for key in CASES:generate(out,key)
