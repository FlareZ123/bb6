import json,pathlib,sys
from collections import Counter
from search import far,tree,scan
from scan import ORDER
from emit_family import code_name,bl,slot
OPEN='open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent6ChunkSupport\n'
OPT='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
def emit(code,spec,out,limit=225,tr=None):
 P=spec['parent'];NS=spec.get('namespace','BB6.Agent6E0ZeroLC.D0ZeroRC.C1'+code_name(code));prefix=spec.get('prefix','A6E0LCD0RCC1'+code_name(code))
 if tr is None:
  counts=Counter();opens=[];tr=tree(P,counts,opens,250,2);assert dict(counts)==spec['counts'] and opens==spec['open']
 else:
  counts=Counter(spec['counts']);opens=spec['open']
 rec={int(i):r for i,r in spec['recipes'].items()};idx={tuple(t):i for i,t in enumerate(opens)}
 blocks=sorted(i for i,r in rec.items() if r[0] in ('block','phase'));bmodule={i:prefix+f'Block{j//8:02}' for j,i in enumerate(blocks)}
 def max_late(r):
  if r[0]=='late':return int(r[1])
  if r[0]=='split':return max([int(r[1])]+[max_late(x) for x in r[3]])
  return 0
 B=max(counts['maxquery'],max((max_late(r) for r in rec.values()),default=0))+6
 def size(t):return 1+sum(map(size,t[3])) if t[0]=='split' else 1
 def node(t,deps):
  k,*a=t
  if k=='cycle':e,s,r,x=a;return f'.cycle {e} {s} {bl(r)} ({x})'
  if k=='last':n,s=a;return f'.last {n} {slot(s)}'
  if k=='far':rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
  if k=='split':n,s,children=a;return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(node(c,deps) for c in children)+'])'
  if k=='open':
   i=idx[tuple(a[0])];r=rec[i]
   if r[0] in ('block','phase'):deps.add(bmodule[i]);return f'.proven {NS}.H{i}.ctr {NS}.H{i}.never'
   if r[0]=='cycle':return node(r,deps)
   if r[0]=='late':assert a[0].count(24)==1 and scan(a[0],r[1])==('hole',r[1],r[2]);return node(('last',*r[1:]),deps)
   if r[0]=='far':c=far(a[0],*r[1:]);assert c;return node(('far',*c),deps)
  raise ValueError(t)
 seq=[0];files=[]
 def make(p,t):
  ident=seq[0];seq[0]+=1;name=prefix+f'Part{ident:04}';ns=NS+f'.Part{ident:04}'
  intro=f'namespace {ns}\n'+OPEN+f'def parent : PartialMachine := fromCodes {p}\n'
  if size(t)<=limit:
   deps=set();st=node(t,deps)
   s='import A6ChunkSupport\n'+''.join(f'import {m}\n' for m in sorted(deps))+OPT+intro+f'''def tree : Audit := {st}
theorem checked : fastCheck {B} parent tree = true := by decide +kernel
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s
  unfold parent fromCodes
  cases h : ({p} : List Nat)[2 * s.1.val + s.2.toNat]? with
  | none => simp [h]
  | some n => by_cases hn : n < 24 <;> simp [h, hn]
noncomputable def certificate : WeightedTNFCertificate {B} parent 6 :=
  certifiedFast {B} parent tree (by decide) nohalt checked
theorem cover : Cover (WeightedBound {B}) parent := Cover.leaf _ certificate.sound
'''
  else:
   _,n,k,children=t;parts={}
   for v,c in zip(ORDER,children):
    q=p.copy();q[k]=v;parts[v]=make(q,c)
   s='import A6ChunkSupport\n'+''.join(f'import {m}\n' for m,_ in parts.values())+OPT+intro+f'''theorem cover : Cover (WeightedBound {B}) parent := by
  apply Cover.branch parent {slot(k)} (by decide)
  intro t _
  cases t with
  | none => exact firstHoleHaltCover {B} parent {slot(k)} {n} (by decide) (by decide) (by decide)
  | some mv =>
    rcases mv with ⟨w,r,q⟩
    have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
      have := q.isLt
      omega
    rcases hq with h|h|h|h|h|h <;> subst q <;> cases w <;> cases r
'''
   for v in range(24):
    _,cn=parts[v];s+=f'''    · have he : refine parent {slot(k)} (some ⟨{bl(v&2)},{bl(v&1)},{v//4}⟩) = {cn}.parent := by
        apply tableOK_sound
        decide
      rw [he]
      exact {cn}.cover
'''
  s+=f'#print axioms cover\nend {ns}\n';(out/(name+'.lean')).write_text(s);files.append(name);return name,ns
 m,ns=make(P,tr)
 s=f'''import {m}
namespace {NS}
{OPEN}def parent : PartialMachine := {ns}.parent
theorem all_completions_weighted : ∀ m, compatible parent m → WeightedBound {B} m := {ns}.cover.sound
#print axioms all_completions_weighted
end {NS}
'''
 name=prefix+'Cover';(out/(name+'.lean')).write_text(s);files.append(name)
 manifest={'code':code,'namespace':NS,'prefix':prefix,'bound':B,'root_module':name,'part_modules':files[:-1],'block_count':len(blocks)+len(nested),'nested_block_module':nested_module if nested else None,'tree_nodes':size(tr),'open_count':len(opens)}
 manifest_name=spec.get('manifest_name',f'chunk_manifest_{code}.json')
 (out/manifest_name).write_text(json.dumps(manifest,indent=2))
 return manifest
if __name__=='__main__':
 specs=json.load(open(sys.argv[1]));out=pathlib.Path(sys.argv[2]);codes=list(map(int,sys.argv[3:])) or list(map(int,specs))
 spec_by_code={str(code):specs for code in codes} if 'parent' in specs else specs
 manifests=[]
 for code in codes:
  manifest=emit(code,spec_by_code[str(code)],out);manifests.append(manifest);print(code,len(manifest['part_modules'])+1,flush=True)
 (out/'chunk_manifest.json').write_text(json.dumps(manifests,indent=2))
