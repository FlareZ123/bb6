"""Reconstruct one broad D0 branch and cache its exact witness recipes."""
from pathlib import Path
from multiprocessing import Pool
import json,subprocess,sys
ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT.parent/'agent48-raw139-f1-oneLA'),str(ROOT.parent/'agent48-raw139-f1-oneRA')]
from scan import scan,far,ORDER
from search import search_case
P=[7,24,11,24,14,24,24,16,8,11,24,24]
BROAD=[0,1,2,3,5,6,7,11,20,21,22,23]
H={};long_index={}
for line in (ROOT/'hard-witnesses.md').read_text().splitlines():
 a=[x.strip() for x in line.split('|')]
 if len(a)!=6 or not a[2].isdigit():continue
 t=tuple(map(int,a[3].split(',')));k,*args=a[4].split()
 H[t]=[k,*[{'true':True,'false':False}.get(x,int(x) if x.lstrip('-').isdigit() else x) for x in args]]
 if k=='late':long_index[t]=len(long_index)
assert len(H)==29 and len(long_index)==9
SPECIAL=(7,22,11,24,14,3,0,16,8,11,24,9)
LCYCLE=(7,22,11,24,14,9,0,16,8,11,4,14)
def discover(t):
 if tuple(t) in H:r=H[tuple(t)]
 else:_,_,r=search_case((0,0,t))
 if r[0]=='late' and t.count(24)>1:
  n,s=r[1:];assert t[s]==24
  return ['split',n,s,[['block',3,1,3,5] if tuple(t)==SPECIAL and v==9 else discover(t[:s]+[v]+t[s+1:]) for v in ORDER]]
 assert r[0]!='open',t
 return r
def job(pair):
 i,t=pair;return i,t,discover(t)
def partition(code,work):
 path=work/'partition.json'
 if not path.exists():
  s=(ROOT.parent/'agent48-raw139-e0-0re'/'replay.cpp').read_text()
  assert 'for(int i=t-1;i>=0;i--)' in s
  s=s.replace('for(int i=t-1;i>=0;i--)','for(int i=t-1;i>=max(0,t-120);i--)')
  for c in ('<','>'):
   s=s.replace('if((a.b[C/64]^b.b[C/64]) && i'+c+'C/64)return false;','')
  cpp=work/'partition.cpp';cpp.write_text(s);exe=work/'partition'
  subprocess.run(['g++','-O3','-std=c++17',str(cpp),'-o',str(exe)],check=True)
  t=P.copy();t[6]=code
  with path.open('wb') as f:subprocess.run([str(exe),'250','2',*map(str,t)],stdout=f,check=True)
 data=json.loads(path.read_text());c=data['counts'];assert c['open']==len(data['open'])
 assert c['cycle']+c['last']+c['far']+c['open']==23*c['split']+1
 expected={0:1143,1:1447,2:863,3:1441,5:953,6:778,7:965,11:686,20:1332,21:1319,22:1012,23:1384}
 assert len(data['open'])==expected[code],(code,c)
 return data
def recipes(data,work):
 path=work/'recipes.jsonl';found={}
 if path.exists():
  for i,t,r in map(json.loads,path.read_text().splitlines()):
   assert t==data['open'][i] and i not in found
   found[i]=r
 with Pool(2) as pool,path.open('a') as f:
  jobs=[(i,t) for i,t in enumerate(data['open']) if i not in found]
  for i,t,r in pool.imap_unordered(job,jobs,chunksize=1):
   found[i]=r;f.write(json.dumps([i,t,r])+'\n');f.flush()
 assert set(found)==set(range(len(data['open'])))
 return found
if __name__=='__main__':
 work=Path(sys.argv[2]);work.mkdir(parents=True,exist_ok=True);code=int(sys.argv[1]);assert code in BROAD
 data=partition(code,work);recipes(data,work)
