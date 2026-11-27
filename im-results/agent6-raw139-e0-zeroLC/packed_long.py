"""Generate segmented kernel checks for all nine long last-hole leaves."""
import pathlib,sys
P=pathlib.Path(sys.argv[1]);P.mkdir(exist_ok=True,parents=True)
H=[]
for line in pathlib.Path(__file__).with_name('hard-witnesses.md').read_text().splitlines():
 a=[x.strip() for x in line.split('|')]
 if len(a)==6 and a[2].isdigit() and a[4].startswith('late '):
  H.append((list(map(int,a[3].split(','))),*map(int,a[4].split()[1:])))
assert len(H)==9
NS='BB6.Agent6ZeroLCLong'
header='import PackedZipper\nimport ZipThreeHoleAudit\nimport Hybrid\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6Coverage.Agent13PackedZipper\n'
mods=[]
for i,(t,n,s) in enumerate(H):
 name=f'ZeroLCLong{i}';p=f'p{i}';q=l=r=0;points=[(0,q,l,r)]
 for k in range(1,n+1):
  v=t[2*q+(l&1)];assert v!=24
  w=(v>>1)&1;q=v>>2
  if v&1:l,r=(r&1)+2*(w+2*(l>>1)),r>>1
  else:l,r=l>>1,w+2*r
  if k%512==0 or k==n:points.append((k,q,l,r))
 assert t[2*q+(l&1)]==24 and 2*q+(l&1)==s and t.count(24)==1
 first=name+'Data';src=header+f'def {p} : PartialMachine := fromCodes {t}\n'
 for j,(k,q,l,r) in enumerate(points):src+=f'def z{i}_{j} : P := ⟨{q}, {l}, {r}⟩\n'
 (P/(first+'.lean')).write_text(src+f'end {NS}\n');cutmods=[]
 for j in range(0,len(points)-1,12):
  cut=name+f'Cut{j//12:03}';cutmods.append(cut);src=f'import {first}\n'+header
  for h in range(j,min(j+12,len(points)-1)):
   m=points[h+1][0]-points[h][0];src+=f'theorem step{i}_{h} : runP {p} {m} z{i}_{h} = some z{i}_{h+1} := by decide +kernel\n'
  (P/(cut+'.lean')).write_text(src+f'end {NS}\n')
 src=''.join('import '+a+'\n' for a in cutmods)+header
 def join(lo,hi):
  if hi==lo+1:return f'step{i}_{lo}'
  mid=(lo+hi)//2;return f'(joinP {join(lo,mid)} {join(mid,hi)})'
 j=len(points)-1;src+=f'''theorem run{i} : runP {p} {n} startP = some z{i}_{j} := {join(0,j)}
theorem read{i} : BB6Coverage.Agent10ZipAudit.zipRead {p} {n} = some ({s//2},{str(bool(s%2)).lower()}) := by
  rw [← readRunP_eq]
  unfold readRunP
  rw [run{i}]
  decide
theorem c{i} : Cover (WeightedBound 80377) {p} := by
  refine .leaf _ (certifiedZip 80377 {p} (.last {n} ({s//2},{str(bool(s%2)).lower()})) (by decide +kernel) (BB6.Agent6Hybrid.fromCodes_nohalt _) ?_).sound
  simp only [zipCheck, zipQueryOK, read{i}]
  decide +kernel
#print axioms c{i}
end {NS}
'''
 (P/(name+'.lean')).write_text(src);mods.append(name)
(P/'ZeroLCLongQueries.lean').write_text(''.join('import '+a+'\n' for a in mods)+''.join(f'#print axioms {NS}.c{i}\n' for i in range(len(mods))))
