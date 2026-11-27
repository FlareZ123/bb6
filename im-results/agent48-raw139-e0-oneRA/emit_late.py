#!/usr/bin/env python3
"""Emit kernel-checkable sharded replays for candidate late leaves.
Usage: emit_late.py partition.json spec-compact.json output-dir [threshold=10000]
Use the existing PackedAudit semantic closure; no trusted native execution.
"""
import json,pathlib,sys
part,spec=(json.load(open(x)) for x in sys.argv[1:3])
out=pathlib.Path(sys.argv[3]);out.mkdir(parents=True,exist_ok=True)
threshold=int(sys.argv[4]) if len(sys.argv)>4 else 10000
B=spec['bound']
family=spec['prefix'].removeprefix('Raw139E0')
assert family in ('OneRA','OneLD')
names=[];roots=[];mapping={}
BASE="""def tab : PartialMachine := fun s => (lookup s.1 s.2).map some
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
theorem join {n k : Nat} {a c d : P}
    (h : runFast n a = some c) (g : runFast k c = some d) :
    runFast (n+k) a = some d := by
  induction n generalizing a with
  | zero => have e : a = c := Option.some.inj h; subst a; simpa only [Nat.zero_add] using g
  | succ n ih =>
    rw [Nat.succ_add]
    simp only [runFast] at h ⊢
    cases hs : stepFast a with
    | none => simp [hs] at h
    | some u => exact ih (by simpa [hs] using h)
"""
for i,(N,S) in sorted(spec['late'].items(),key=lambda p:int(p[0])):
    if N<threshold:continue
    T=part['open'][int(i)];assert T.count(24)==1 and T[S]==24
    prefix=f'{family}Late{i}';ns=f'BB6.Agent48{family}Late.R{i}'
    def write(suffix,body):
        (out/(prefix+suffix+'.lean')).write_text(body)
        return prefix+suffix
    hdr=f'''set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace {ns}
open BB6Coverage BB6Coverage.FAR BB6Coverage.Agent13PackedZipper BB6.Agent3PackedAudit BB6.Agent31ThreeHole BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent8TNFPath BB6Coverage.Agent10ZipAudit
'''
    end=f'end {ns}\n'
    code='import PackedAudit\n'+hdr+f'def parent : PartialMachine := fromCodes {T}\ndef lookup (q : Fin 6) (b : Bool) : Option Move :=\n  match q.val,b with\n'
    for j,v in enumerate(T):
        code+=f'  | {j//2},{str(bool(j%2)).lower()} => '+('none' if v==24 else f'some ⟨{str(bool(v//2%2)).lower()},{str(bool(v%2)).lower()},{v//4}⟩')+'\n'
    code+='  | _,_ => none\n'+BASE
    q=l=r=0;cuts=[0];code+='def z0 : P := startP\n'
    for j in range(N):
        v=T[2*q+l%2];assert v!=24
        w=v//2%2;q=v//4
        if v%2:l=r%2+2*w+4*(l//2);r//=2
        else:l//=2;r=w+2*r
        if (j+1)%4000==0 or j+1==N:
            cuts.append(j+1);code+=f'def z{j+1} : P := ⟨{q},{l},{r}⟩\n'
    assert 2*q+l%2==S
    core=write('Core',code+end);names.append(core)
    steps=[];terms=[]
    for j in range(0,len(cuts)-1,8):
        code=f'import {core}\n'+hdr
        for a,b in zip(cuts[j:j+8],cuts[j+1:j+9]):
            code+=f'theorem c{a} : runFast {b-a} z{a} = some z{b} := by decide +kernel\n'
            terms.append((a,b,f'c{a}'))
        steps.append(write(f'Step{j//8:03}',code+end))
    names+=steps
    agg=[]
    def combine(ts):
        if len(ts)==1:return ts[0][2]
        mid=len(ts)//2;a,c,d=ts[0][0],ts[mid][0],ts[-1][1]
        l,r=combine(ts[:mid]),combine(ts[mid:]);name=f'agg{a}_{d}'
        agg.append(f'theorem {name} : runFast {d-a} z{a} = some z{d} := @join {c-a} {d-c} z{a} z{c} z{d} {l} {r}\n')
        return name
    joined=combine(terms)
    code=''.join(f'import {m}\n' for m in steps)+hdr+''.join(agg)+f'''theorem reached : runP parent {N} startP = some z{N} := by
  rw [← runFast_eq]
  exact {joined}
theorem checked : packedCheck {B} parent (.last {N} ({S//2},{str(bool(S%2)).lower()})) = true := by
  simp only [packedCheck,packedQueryOK,readRunP,reached,Option.map_some]
  decide +kernel
theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({T} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {B} m :=
  (certifiedPacked {B} parent _ root nohalt checked).sound
theorem cover : Cover (WeightedBound {B}) parent := .leaf parent all_completions_weighted
#print axioms all_completions_weighted
#print axioms cover
'''
    main=write('',code+end);roots.append(main);names.append(main)
    mapping[str(i)]={'table':T,'steps':N,'slot':S,'namespace':ns,'module':main}
(out/'late-roots.txt').write_text('\n'.join(roots)+'\n')
(out/'late-order.txt').write_text('\n'.join(names)+'\n')
(out/'late-map.json').write_text(json.dumps(mapping,separators=(',',':'))+'\n')
