"""Emit compositional exact branch proofs with 80377 global weighted bound."""
from broad_discover import *
from emit_family import (block_source,bl,slot,generate,generate_offset,emit_offset,
                         offset_block_source,ensure_offset_backend,table_text)
import re
B=80377
BLOCK=('block','phase','mirror','mirrorphase','offset')
def emit(code,data,rec,out):
 out.mkdir(exist_ok=True,parents=True)
 NS=f'BB6.Agent6ZeroLCBroad.C{code:02d}';prefix=f'ZLCBroad{code:02d}'
 t0=P.copy();t0[6]=code
 ids={tuple(t):i for i,t in enumerate(data['open'])};used=set();blocks={}
 def finish(t,r):
  k,*a=r
  if k=='split':
   n,s,kids=a;assert t[s]==24 and len(kids)==24
   return ['split',n,s,[finish(t[:s]+[v]+t[s+1:],ch) for v,ch in zip(ORDER,kids)]]
  if tuple(t) in long_index:
   j=long_index[tuple(t)];return ['covered',f'ZeroLCLong{j}',f'BB6.Agent6ZeroLCLong.p{j}',f'BB6.Agent6ZeroLCLong.c{j}']
  if tuple(t)==LCYCLE:return ['covered','ZeroLCLongCycle','BB6.Agent6ZeroLCLongCycle.p','BB6.Agent6ZeroLCLongCycle.c']
  if k in BLOCK:
   i=len(blocks);blocks[i]=(t,r);return ['block',i]
  if k=='far':
   f=far(t,*a);assert f;return ['far',*f]
  if k=='late':assert t.count(24)==1;return ['last',*a]
  assert k in ('cycle','last'),r
  return r
 def expand(t,n):
  if n[0]=='split':
   _,k,s,kids=n;assert t[s]==24 and len(kids)==24
   return ['split',k,s,[expand(t[:s]+[v]+t[s+1:],ch) for v,ch in zip(ORDER,kids)]]
  if n[0]=='open':
   assert n[1]==t;i=ids[tuple(t)];assert i not in used;used.add(i);return finish(t,rec[i])
  return n
 tree=expand(t0,data['tree']);assert used==set(rec)
 opts='set_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n'
 manifest=[];modmap={}
 def put(name,body,deps):
  (out/(name+'.lean')).write_text(''.join('import '+m+'\n' for m in sorted(deps))+body);manifest.append(name)
 for j in range(0,len(blocks),8):
  name=prefix+f'Block{j//8:04d}';body=opts;deps={'BlockFAR2','BlockFARBridge','FastThreeHoleAudit','FARBi'}
  for i in range(j,min(j+8,len(blocks))):
   t,r=blocks[i];k,*a=r;modmap[i]=name
   if k=='offset':
    w,c,m,n,off=a;ensure_offset_backend(w);certname=prefix+f'Offset{i}'
    scratch=out.parent/'offset';scratch.mkdir(exist_ok=True)
    z=generate_offset(table_text(t),scratch,width=w,cap=c,mod=m,runs=n,name=certname,minimize_left=True,offset=off)
    emit_offset(out,certname,z,off)
    deps|={certname+'Proof','BlockFARBridge4' if w==4 else 'BlockFARBridge'}
    body+=offset_block_source(NS,i,t,w,certname)
   else:
    w,c,m,n=a[:4];flip=k.startswith('mirror');phase=k.endswith('phase')
    z=generate(t,w,c,m,n,flip,60000,phase);assert z,(t,r)
    if len(a)>4:assert [z['left_states'],z['right_nodes']]==a[4:],(t,r)
    body+=block_source(NS,i,t,z,flip)
  put(name,body,deps)
 def size(t):return sum(map(size,t[3])) if t[0]=='split' else 1
 def special(t):return any(map(special,t[3])) if t[0]=='split' else t[0]=='covered'
 def audit(t,deps):
  k,*a=t
  if k=='cycle':e,s,r,z=a;return f'.cycle {e} {s} {bl(r)} ({z})'
  if k=='last':n,s=a;return f'.last {n} {slot(s)}'
  if k=='far':rev,d,dfa,t0,t1,z=a;return f'.far {bl(rev)} {d} ⟨0,{dfa},{t0},{t1},{z}⟩'
  if k=='block':i=a[0];deps.add(modmap[i]);return f'.proven {NS}.H{i}.ctr {NS}.H{i}.never'
  if k=='split':n,s,cs=a;return f'.split {n} {slot(s)} (byMove [\n'+',\n'.join(audit(c,deps) for c in cs)+'])'
  raise ValueError(t)
 header=opts+'namespace '+NS+'\nopen BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent6OneLFZipHybrid\n'
 def node(p,t,name):
  deps={'OneLFZipHybrid'}
  if t[0]=='covered':
   _,mod,q,c=t;deps.add(mod);term=f'.covered {q} {c}'
  elif size(t)<=100 and not special(t):term=f'.closed ({audit(t,deps)})'
  else:
   _,n,s,kids=t;terms=[]
   for j,(ch,v) in enumerate(zip(kids,ORDER)):
    q=p.copy();assert q[s]==24;q[s]=v
    if ch[0] in ('split','covered'):
     cn=name+'_'+str(j);node(q,ch,cn);deps.add(cn);terms.append(f'.covered p{cn} c{cn}')
    else:terms.append(f'.closed ({audit(ch,deps)})')
   term=f'.split {n} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+'])'
  src=header+f'''def p{name} : PartialMachine := fromCodes {p}
def t{name} : Hybrid {B} := {term}
theorem c{name} : Cover (WeightedBound {B}) p{name} := sound {B} p{name} t{name} (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms c{name}
end {NS}
'''
  put(name,src,deps)
 root=f'ZLCBroadRoot{code:02d}';node(t0,tree,root)
 print('branch',code,'leaves',size(tree),'blocks',len(blocks),'modules',len(manifest),flush=True)
 # Batch small modules in topological order.
 groups=[];cur=[];nbytes=0
 for name in manifest:
  s=(out/(name+'.lean')).read_text();block='Block' in name
  if cur and (len(cur)>=8 or nbytes+len(s)>20000 or block or 'Block' in cur[0]):groups.append(cur);cur=[];nbytes=0
  cur.append(name);nbytes+=len(s)
 if cur:groups.append(cur)
 keys={n:(g[0] if len(g)==1 else f'{prefix}Batch{i:04}') for i,g in enumerate(groups) for n in g}
 for g in groups:
  dst=keys[g[0]];deps=set();chunks=[]
  for n in g:
   s=(out/(n+'.lean')).read_text();deps.update(keys.get(m,m) for m in re.findall(r'^import (\w+)$',s,re.M));chunks.append(re.sub(r'^import \w+\n','',s,flags=re.M))
  deps.discard(dst)
  (out/(dst+'.lean')).write_text(''.join('import '+m+'\n' for m in sorted(deps))+''.join(chunks))
 for n in manifest:
  if keys[n]!=n:(out/(n+'.lean')).unlink()
 if keys[root]!=root:(out/(root+'.lean')).write_text('import '+keys[root]+'\n#print axioms '+NS+'.c'+root+'\n')
 print('batched',len(groups),'root',root,flush=True)
def final(out):
 out.mkdir(exist_ok=True,parents=True);n,s=scan(P,250)[1:];assert s==6
 src='import OneLFZipHybrid\nimport Raw139E0ZeroLCD0RC\n'+''.join(f'import ZLCBroadRoot{c:02d}\n' for c in BROAD)
 src+='''set_option maxHeartbeats 0
namespace BB6.Agent6E0ZeroLCExact
open BB6Coverage BB6Coverage.FAR BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent6OneLFZipHybrid
def parent : PartialMachine := fromCodes [7,24,11,24,14,24,24,16,8,11,24,24]
theorem child9 : Cover (WeightedBound 80377) BB6.Agent6E0ZeroLCD0RC.pRaw139E0ZeroLCD0RC :=
  .leaf _ (fun m hm k d hk hd => Nat.le_trans (BB6.Agent6E0ZeroLCD0RC.cRaw139E0ZeroLCD0RC.sound m hm k d hk hd) (by omega))
'''
 terms=[]
 for c in ORDER:
  if c in BROAD:
   ns=f'BB6.Agent6ZeroLCBroad.C{c:02d}';root=f'ZLCBroadRoot{c:02d}';terms.append(f'.covered {ns}.p{root} {ns}.c{root}')
  elif c==9:terms.append('.covered BB6.Agent6E0ZeroLCD0RC.pRaw139E0ZeroLCD0RC child9')
  else:
   t=P.copy();t[6]=c;k,e,period,d,x=scan(t,250);assert k=='cycle';terms.append(f'.closed (.cycle {e} {period} {bl(d)} ({x}))')
 src+=f'def root : Hybrid {B} := .split {n} {slot(s)} (byHybridMove [\n'+',\n'.join(terms)+f'''])
theorem weighted : Cover (WeightedBound {B}) parent := sound {B} parent root (by decide +kernel) (fromCodes_nohalt _) (by decide +kernel)
#print axioms weighted
end BB6.Agent6E0ZeroLCExact
'''
 (out/'E0ZeroLCCover.lean').write_text(src)
if __name__=='__main__':
 work=Path(sys.argv[2]);work.mkdir(parents=True,exist_ok=True)
 if sys.argv[1]=='final':final(work)
 else:
  code=int(sys.argv[1]);assert code in BROAD;data=partition(code,work);rec=recipes(data,work);emit(code,data,rec,work/'imports')
