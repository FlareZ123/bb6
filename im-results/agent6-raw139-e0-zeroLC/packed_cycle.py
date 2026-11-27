"""Exact segmented cycle proof for D0=0LA leaf 529; avoids a monolithic kernel replay."""
from pathlib import Path
import sys
p=Path(sys.argv[1]);p.mkdir(exist_ok=True,parents=True)
T=[7,22,11,24,14,9,0,16,8,11,4,14];q=h=0;l=[];r=[];steps=7679;period=740;points=[(0,q,h,l,r)]
for i in range(1,steps+period+1):
 v=T[2*q+(l[0] if l else 0)];assert v!=24;w=(v>>1)&1;q=v>>2
 if v&1:h+=1;l=[r[0] if r else 0,w]+l[1:];r=r[1:]
 else:h-=1;l=l[1:];r=[w]+r
 if (i<=steps and (i%128==0 or i==steps)) or i==steps+period:points.append((i,q,h,l,r))
NS='BB6.Agent6ZeroLCLongCycle';head='import Hybrid\nimport ZipThreeHoleAudit\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\nnamespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent50Zipper BB6Coverage.Agent31Pump BB6Coverage.Agent10ZipAudit\n'
bl=lambda a:'['+','.join('true' if x else 'false' for x in a)+']'
s=head+f'def p : PartialMachine := fromCodes {T}\n'
for j,(i,q,h,l,r) in enumerate(points):s+=f'def z{j} : Z := ⟨{q}, {h}, {bl(l)}, {bl(r)}⟩\n'
(p/'ZLCCycleData.lean').write_text(s+f'end {NS}\n');mods=[]
for j in range(0,len(points)-2,4):
 name=f'ZLCCycleCut{j//4:02}';mods.append(name);s='import ZLCCycleData\n'+head
 for k in range(j,min(j+4,len(points)-2)):
  n=points[k+1][0]-points[k][0];s+=f'theorem step{k} : zrun p {n} z{k} = some z{k+1} := by decide +kernel\n'
 (p/(name+'.lean')).write_text(s+f'end {NS}\n')
def join(lo,hi):
 if hi==lo+1:return f'step{lo}'
 mid=(lo+hi)//2;return f'(@BB6Coverage.Agent50Zipper.join p {points[mid][0]-points[lo][0]} {points[hi][0]-points[mid][0]} z{lo} z{mid} z{hi} {join(lo,mid)} {join(mid,hi)})'
a=len(points)-2;b=a+1
s=''.join('import '+m+'\n' for m in mods)+head+f'''theorem entry : zrun p {steps} start = some z{a} := {join(0,a)}
theorem window : zipWindow p false (-68) {period} z{a} = some z{b} := by decide +kernel
theorem tail : zipTailEq false (-68) z{a} z{b} = true := by decide +kernel
theorem cycleOK : zipCycle p {steps} {period} false (-68) = true := by
  unfold zipCycle
  rw [entry]
  change (match zipWindow p false (-68) {period} z{a} with | none => false | some d => zipTailEq false (-68) z{a} d) = true
  rw [window]
  exact tail
theorem c : Cover (WeightedBound 80377) p := .leaf _ (fun m hm => weighted_never 80377 m (zipCycle_sound p {steps} {period} false (-68) (by decide) cycleOK m hm))
#print axioms c
end {NS}
'''
(p/'ZeroLCLongCycle.lean').write_text(s)
