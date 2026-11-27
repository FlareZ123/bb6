"""Graft exact residual witnesses into the saved first-query partition; no search."""
import json,sys,pathlib
from collections import Counter,defaultdict
from compressed import patch_candidate_replay
patch_candidate_replay()
from package6 import first_hole
from scan import ORDER
src=pathlib.Path(sys.argv[1]);out=pathlib.Path(sys.argv[2]);out.mkdir(parents=True,exist_ok=True)
c=int(sys.argv[3]); ext=json.loads(pathlib.Path(__file__).with_name('residuals.json').read_text())
part=json.loads((src/'partition.json').read_text()); spec=json.loads((src/'spec-compact.json').read_text())
assert spec['parent']==[7,24,11,24,14,c,24,16,6,11,24,24]
assert part['counts']==spec['counts']
old=part['open']; idx={tuple(t):i for i,t in enumerate(old)}
solved={}
def put(i,w):
 i=int(i);assert i not in solved
 solved[i]=w
for r,ids in spec['block_groups']:
 for i in ids:put(i,['wide',*r])
for i,r in spec['late'].items():put(i,['last',*r])
for i,r in spec['proven'].items():put(i,['proven',r])
for r in ext['single']:
 if r['c']==c:
  i=r['index']; assert old[i]==r['table']
  if 'wide' in r:put(i,['wide',*r['wide']])
  elif 'last' in r:put(i,['last',*r['last']])
  elif 'proven' in r:put(i,['proven',r['proven']])
  else:raise ValueError(('unresolved',c,i))
for r in ext['split']:
 if r['c']==c:
  i=r['index'];assert old[i]==r['table']
  assert first_hole(r['table'],r['query'][0])==('hole',*r['query'])
  assert sorted(x['v'] for x in r['children'])==list(range(24))
  put(i,['split',r['query'],{x['v']:x for x in r['children']}])
assert set(solved)==set(range(len(old))),('unresolved',c, sorted(set(range(len(old)))-set(solved)))
opens=[];groups=defaultdict(list);late={};proven={};mapping=dict(spec.get('external_module_by_namespace',{}));wide={};counts=Counter();maxquery=0
def node(t,w,key):
 global maxquery
 typ,*a=w
 if typ=='split':
  (n,s),kids=a; assert t[s]==24
  maxquery=max(maxquery,n);counts['split']+=1
  out=[]
  for v in ORDER:
   t2=t.copy();t2[s]=v;child=kids[v]
   assert child['table']==t2
   out.append(node(t2,child['w'],key+'V'+str(v)))
  return ['split',n,s,out]
 if typ=='cycle':
  counts['cycle']+=1;return w
 i=len(opens);opens.append(t);counts['open']+=1
 if typ=='last':
  assert t.count(24)==1 and first_hole(t,a[0])==('hole',*a)
  late[str(i)]=a
 elif typ=='proven':
  ns,=a
  if ns=='BB6.Agent12Counter286':
   assert t==[7,21,11,13,14,1,24,16,6,11,16,11]
   mapping[ns]='Counter286Bridge'
  assert ns in mapping,ns
  proven[str(i)]=ns
 elif typ=='wide':
  width,cap,mod,runs,flip,phase=a
  if width<=3 and not flip:groups[tuple(a)].append(i)
  else:
   k=f'C{c:02d}I{key}';ns=f'BB6.Agent3OneLBWide{width}.OneLBWide{k}'
   wide[k]=[t,w];proven[str(i)]=ns;mapping[ns]=f'OneLBWide{k}Proof'
 else:raise ValueError((typ,t))
 return ['open',t]
def visit(n,t):
 global maxquery
 typ,*a=n
 if typ=='open':
  assert a[0]==t;i=idx[tuple(t)];return node(t,solved[i],str(i))
 counts[typ]+=1
 if typ=='split':
  steps,s,kids=a;maxquery=max(maxquery,steps);assert len(kids)==24 and t[s]==24
  ch=[]
  for v,k in zip(ORDER,kids):
   t2=t.copy();t2[s]=v;ch.append(visit(k,t2))
  return ['split',steps,s,ch]
 if typ=='last':maxquery=max(maxquery,a[0])
 return n
tree=visit(part['tree'],spec['parent'])
counts={k:counts[k] for k in ['cycle','last','split','far','open']};counts['maxquery']=maxquery
assert sum(counts[k] for k in ('cycle','last','far','open'))==1+23*counts['split']
assert len(opens)==len({tuple(t) for t in opens})
spec.update(counts=counts,bound=max([maxquery]+[v[0] for v in late.values()])+6,
 block_groups=[[list(k),v] for k,v in sorted(groups.items())],late=late,proven=proven,
 external_imports=sorted(mapping.values()),external_module_by_namespace=mapping)
for name,obj in [('partition.json',dict(tree=tree,open=opens,counts=counts)),('spec-compact.json',spec),('wide.json',wide)]:
 (out/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
print('exact graft',c,counts,'bound',spec['bound'],'wide',len(wide))
