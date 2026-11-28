"""Reconstruct exact-table evidence from a hash-bound, sorted OPEN roster.

Only for durable storage of incomplete research frontiers; never proves a
branch. The original Lean audit must independently check the resulting
evidence and equality of literal tables. A missing entry remains OPEN.
"""
import base64,gzip,hashlib,json,lzma,sys,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
MOVES=[w+d+q for w in '01' for d in 'LR' for q in 'ABCDEF']
def expand(i,tree=None):
 p='1RB---_1RC'+MOVES[i]+'_0RD---_0LD1LB_------_------'
 raw=tree.read_text() if tree else subprocess.check_output(['node',str(ROOT/'canonical_search.cjs'),p,str(max(4,i%6+1)),'tree'],text=True)
 got=json.loads(raw)
 assert got['parent']==p and got['cut']==max(4,i%6+1)
 keys=sorted(t.replace('_','') for t in got['opens'])
 assert len(keys)==len(set(keys))
 a=json.loads(lzma.decompress(base64.b64decode((ROOT/f'd1-{i:02d}-compact.json.xz.b64').read_text())))
 assert hashlib.sha256('\n'.join(keys).encode()).hexdigest()==a['digest']
 assert len(keys)==len(a['data'])
 e={'bound':a['bound'],'far':[],'sweep':[],'manual':[],'cycle':[],'regular':[],'missing':[]}
 for j,(t,v) in enumerate(zip(keys,a['data'])):
  pretty='_'.join(t[k:k+6] for k in range(0,36,6))
  if v is None:e['missing'].append(pretty)
  elif isinstance(v,str):e['far'].append([pretty,v])
  elif v[0]=='s':e['sweep'].append([j,t,*v[1:]])
  elif v[0]=='m':e['manual'].append([pretty,v[1]])
  elif v[0]=='c':e['cycle'].append([pretty,v[1:]])
  elif v[0]=='r':e['regular'].append([pretty,*v[1:]])
  else:raise ValueError(v)
 return e
if __name__=='__main__':
 i=int(sys.argv[1]);e=expand(i,Path(sys.argv[2]) if len(sys.argv)>2 else None)
 (ROOT/f'd1-{i:02d}-evidence.json.gz.b64').write_text(base64.b64encode(gzip.compress(json.dumps(e,separators=(',',':')).encode(),mtime=0)).decode()+'\n')
 print({k:len(v) if isinstance(v,list) else v for k,v in e.items()})
