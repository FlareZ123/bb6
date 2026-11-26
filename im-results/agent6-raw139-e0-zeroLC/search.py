"""Deterministic witness search for seven nontrivial C1 children of E0=0LC/D0=0RC.
The eighth (C1=0LF) has generate_zeroLF.py. Search alone is not a proof.
"""
import pathlib,sys
root=pathlib.Path(__file__).resolve().parent
sys.path[:0]=[str(root.parent/'agent48-raw139-f1-oneLA'),str(root.parent/'agent48-raw139-f1-oneRA')]
from scan import scan,tree,find_far,far
from blockcert import generate
from collections import Counter
from itertools import product
from multiprocessing import Pool
import json
CODES=[1,2,3,6,21,22,23]
def search_case(job):
 code,i,p=job
 a=scan(p,600)
 if a[0]=='cycle':return code,i,['cycle',*a[1:]]
 if a[0]=='hole':return code,i,['late',*a[1:]]
 f=find_far(p,3)
 if f:return code,i,['far',f[0],f[2]]
 for width in [2,3]:
  for runs,cap,mod in [(1,1,2),(1,2,2),(2,1,2),(2,2,2),(2,1,3),(2,1,4),(2,1,5),(2,1,6),(2,1,7),(2,2,3),(2,2,4),(2,2,5),(2,2,6),(3,1,2),(3,1,3),(3,1,4),(3,2,2),(3,2,3),(3,2,4),(4,1,2),(4,1,3),(4,1,4)]:
   c=generate(p,width,cap,mod,runs,False,60000)
   if c:return code,i,['block',width,cap,mod,runs,c['left_states'],c['right_nodes']]
  for runs,mod in product([2,3,4],[2,3,4,5,6,7]):
   c=generate(p,width,1,mod,runs,False,60000,True)
   if c:return code,i,['phase',width,1,mod,runs,c['left_states'],c['right_nodes']]
 a=scan(p,2000)
 if a[0]=='cycle':return code,i,['cycle',*a[1:]]
 if a[0]=='hole':return code,i,['late',*a[1:]]
 return code,i,['open']
if __name__=='__main__':
 codes=list(map(int,sys.argv[2:])) or CODES
 out=pathlib.Path(sys.argv[1])
 jobs=[];data={}
 for code in codes:
  p=[7,24,11,24,14,code,9,16,8,11,24,24];c=Counter();o=[];tr=tree(p,c,o,250,2)
  print('PARTITION',code,dict(c),flush=True)
  data[code]={'parent':p,'counts':dict(c),'open':o,'recipes':{}}
  jobs.extend((code,i,t) for i,t in enumerate(o))
 with Pool(4) as pool:
  for j,(code,i,r) in enumerate(pool.imap_unordered(search_case,jobs,chunksize=1)):
   data[code]['recipes'][str(i)]=r
   if j%20==0 or r[0] in ('open','late'):print('PROGRESS',j+1,len(jobs),code,i,r,flush=True)
 json.dump(data,out.open('w'),sort_keys=True,indent=2)
 for k,v in data.items():print('RESULT',k,Counter(r[0] for r in v['recipes'].values()),flush=True)
