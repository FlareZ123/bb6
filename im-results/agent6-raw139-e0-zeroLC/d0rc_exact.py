"""Reconstruct and emit exact E0=0LC/D0=0RC weighted Cover. Usage: d0rc_exact.py WORK."""
import sys,json,re
from pathlib import Path
from multiprocessing import Pool
ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/'agent48-raw139-f1-oneLA'),str(ROOT.parent/'agent48-raw139-f1-oneRA')]
from scan import *
from blockcert import generate
from emit_family import block_source,bl,slot
P=[7,24,11,24,14,24,9,16,8,11,24,24]
NS='BB6.Agent6E0ZeroLCD0RC'
B=616
params=[(1,1,2),(1,2,2),(2,1,2),(2,2,2),(2,1,3),(2,1,4),(2,1,5),(2,1,6),(2,1,7),(2,2,3),(2,2,4),(2,2,5),(2,2,6),(3,1,2),(3,1,3),(3,1,4),(3,2,2),(3,2,3),(3,2,4),(4,1,2),(4,1,3),(4,1,4)]
def solve(p):
 a=scan(p,600)
 if a[0]=='cycle':return a
 if a[0]=='hole':
  assert p.count(24)==1,(p,a)
  return ('last',*a[1:])
 f=find_far(p,3)
 if f:return ('far',*f)
 for w in [2,3]:
  for r,c,m in params:
   d=generate(p,w,c,m,r,False,60000)
   if d:return ('block',w,c,m,r,False)
  for r,m in product([2,3,4],[2,3,4,5,6,7]):
   d=generate(p,w,1,m,r,False,60000,True)
   if d:return ('block',w,1,m,r,True)
 a=scan(p,2000)
 if a[0]=='cycle':return a
 if a[0]=='hole':assert p.count(24)==1;return ('last',*a[1:])
 raise ValueError(p)
def census(c):
 p=P.copy();p[5]=c;ct=Counter();op=[];t=tree(p,ct,op,250,2);return c,t,dict(ct),op
def main():
 work=Path(sys.argv[1]);work.mkdir(parents=True,exist_ok=True)
 datafile=work/'data.json'
 if not datafile.exists():
  with Pool(4) as pool:
   data=list(pool.imap(census,ORDER))
   jobs=[p for c,t,ct,op in data for p in op]
   rs=list(pool.imap(solve,jobs,chunksize=1))
  assert len(jobs)==630 and Counter(x[0] for x in rs)=={'block':419,'far':194,'cycle':13,'last':4}
  datafile.write_text(json.dumps({'census':data,'recipes':list(zip(jobs,rs))},separators=(',',':')))
 x=json.loads(datafile.read_text())
 out=work/'proof';out.mkdir(exist_ok=True)
 rec={tuple(t):r for t,r in x['recipes']};assert len(rec)==630
 opts='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
 bs={};parts=[];sources={}
 for i,(t,r) in enumerate(rec.items()):
  if r[0]!='block':continue
  _,w,c,m,n,phase=r;d=generate(t,w,c,m,n,False,60000,phase);assert d
  nm=f'ZLCD0RCBlock{i//8:03}';bs[t]=(i,nm)
  if nm not in sources:sources[nm]=[];parts.append(nm)
  sources[nm].append(block_source(NS,i,list(t),d).replace('(by decide)\ntheorem never','(by decide +kernel)\ntheorem never'))
 for nm,chunks in sources.items():
  (out/(nm+'.lean')).write_text('import BlockFAR2\nimport BlockFARBridge\nimport FastThreeHoleAudit\n'+opts+''.join(chunks))
 seen=set();used=set();maxq=0
 def normalize(t):
  if t[0]=='open':
   p=tuple(t[1]);assert p not in seen;seen.add(p);r=rec[p];return ['block',p] if r[0]=='block' else r
  if t[0]=='split':return [*t[:3],[normalize(c) for c in t[3]]]
  return t
 def size(t):return sum(map(size,t[3])) if t[0]=='split' else 1
 def audit(t,deps):
  nonlocal maxq
  k,*a=t
  if k=='cycle':e,s,r,z=a;return f'.cycle {e} {s} {bl(r)} ({z})'
  if k=='last':n,s=a;maxq=max(maxq,n);return f'.last {n} {slot(s)}'
  if k=='far':rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
  if k=='block':p=a[0];i,m=bs[p];deps.add(m);used.add(p);return f'.proven {NS}.H{i}.ctr {NS}.H{i}.never'
  if k=='split':n,s,cs=a;maxq=max(maxq,n);return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(audit(c,deps) for c in cs)+'])'
  raise ValueError(t)
 header='namespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10FastAudit BB6.Agent6Hybrid\n'
 def emit(p,t,name):
  nonlocal maxq
  deps={'Hybrid'}
  if size(t)<=100:term=f'.closed ({audit(t,deps)})'
  else:
   _,n,s,kids=t;maxq=max(maxq,n);terms=[]
   for j,(ch,v) in enumerate(zip(kids,ORDER)):
    q=p.copy();assert q[s]==24;q[s]=v
    if ch[0]=='split':
     cn=name+'_'+str(j);emit(q,ch,cn);deps.add(cn);terms.append(f'.covered p{cn} c{cn}')
    else:terms.append(f'.closed ({audit(ch,deps)})')
   term=f'.split {n} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+'])'
  src=header+f'''def p{name} : PartialMachine := fromCodes {p}
def t{name} : Hybrid {B} := {term}
theorem c{name} : Cover (WeightedBound {B}) p{name} := sound {B} p{name} t{name} (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms c{name}
end {NS}
'''
  (out/(name+'.lean')).write_text(''.join('import '+d+'\n' for d in sorted(deps))+opts+src);parts.append(name)
 q=scan(P,250);assert q[0]=='hole' and q[2]==5,q
 assert [r[0] for r in x['census']]==ORDER
 root=['split',q[1],5,[normalize(r[1]) for r in x['census']]]
 assert seen==set(rec);emit(P,root,'Raw139E0ZeroLCD0RC');assert used==set(bs) and maxq==610 and size(root)==15894
 print('leaves',size(root),'maxquery',maxq,'modules',len(parts),flush=True)
 # Group adjacent independent/small dependent declarations; imports remain a DAG.
 dst=work/'imports';dst.mkdir(exist_ok=True)
 groups=[];cur=[];nbytes=0
 for name in parts:
  s=(out/(name+'.lean')).read_text();block=name.startswith('ZLCD0RCBlock')
  if cur and (len(cur)>=12 or nbytes+len(s)>20000 or block or cur[0].startswith('ZLCD0RCBlock')):groups.append(cur);cur=[];nbytes=0
  cur.append(name);nbytes+=len(s)
 if cur:groups.append(cur)
 keys={n:(group[0] if len(group)==1 else f'ZLCD0RCBatch{i:03}') for i,group in enumerate(groups) for n in group}
 for g in groups:
  name=keys[g[0]];deps=set();chunks=[]
  for n in g:
   s=(out/(n+'.lean')).read_text();deps.update(keys.get(d,d) for d in re.findall(r'^import (\w+)$',s,re.M));chunks.append(re.sub(r'^import \w+\n','',s,flags=re.M))
  deps.discard(name);(dst/(name+'.lean')).write_text(''.join('import '+d+'\n' for d in sorted(deps))+''.join(chunks))
 root=keys[parts[-1]]
 if root!='Raw139E0ZeroLCD0RC':(dst/'Raw139E0ZeroLCD0RC.lean').write_text(f'import {root}\n#print axioms BB6.Agent6E0ZeroLCD0RC.cRaw139E0ZeroLCD0RC\n')
 print('batched',len(groups),'root',root)
if __name__=='__main__':main()
