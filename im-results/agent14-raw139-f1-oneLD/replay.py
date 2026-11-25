import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'agent48-raw139-f1-oneLA'))
from autopump import *
from pathlib import Path
import re
from scan import tree,Counter
p=[7,24,11,24,14,21,3,16,12,11,24,14];counts=Counter();opens=[];t=tree(p,counts,opens,600,3);D=dict(parent=p,counts=counts,open=opens,tree=t)
assert counts=={'maxquery':258,'split':13,'cycle':170,'last':53,'open':32,'far':45}
json.dump(D,open('f1-14-600.json','w'))
def w(s):return normalize([G(x[1:-1]) if x.startswith('(') else x for x in re.findall(r'\([01]+\)|[01]+',s)])
for line in Path('recipes.txt').read_text().splitlines():
 i,t,q,l,r,recipe=line.split();i,t,q=map(int,[i,t,q]);p=D['open'][i];c=(q,w(l),w(r));a=c;ops=[]
 assert evaluate(trace(p,t)[t],0)==evaluate(c,0),(i,t)
 for token in recipe.split(','):
  if token.isdigit():
   for _ in range(int(token)):
    b=step(p,a);assert b is not None;ops.append(('step',a,b));a=b
  else:
   side=token[0];prefix,cost=map(int,token[1:].split(':'));matches=[(b,op) for b,op in pump(p,a,side) if len(op[3])==prefix and op[6]==cost];assert len(matches)==1,(i,token,matches);b,op=matches[0];ops.append(('pump',a,b,op));a=b
 assert canonical(a[1])==canonical(targetnext(c)[1]) and canonical(a[2])==canonical(targetnext(c)[2]) and a[0]==q,i
 json.dump(dict(table=p,result=(t,c,(ops,a))),open(f'pump-{i}.json','w'),default=js)

assert {int(p.stem.split('-')[1]) for p in Path('.').glob('pump-*.json')} == set(range(32))-{25}
assert D['open'][25]==[7,11,11,24,14,21,3,16,12,11,3,14]
