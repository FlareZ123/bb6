"""Assemble a literal-hash-bound direct D1 source-audit fixture.

Never report a closed Cover unless every canonical OPEN leaf has an exact
candidate and the generated Lean source passes its kernel checks.
"""
import argparse,base64,gzip,hashlib,json,lzma
from pathlib import Path

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--census',required=True,type=Path)
    ap.add_argument('--far',type=Path);ap.add_argument('--stack',type=Path)
    ap.add_argument('--extras',type=Path);ap.add_argument('--out',required=True,type=Path)
    a=ap.parse_args()
    got=json.loads(gzip.decompress(a.census.read_bytes()))
    keys=sorted(t.replace('_','') for t in got['opens'])
    assert len(keys)==len(set(keys))==got['stats']['open']
    candidates={}
    def assign(t,v,origin):
        k=t.replace('_','');assert k in keys,(origin,k)
        # FAR wins over N-gram, which wins over later structured evidence.
        # Alternate valid certificates need not have the same representation.
        if k in candidates:return
        candidates[k]=v
    if a.far:
        for line in a.far.read_text().splitlines():
            if line.strip():
                t,c=line.split();assign(t,['f',c],'FAR')
    if a.stack:
        for t,v in json.loads(a.stack.read_text()):
            assert v[0] in ('n','r','m','d','p')
            assign(t,v,'stack')
    if a.extras:
        d=json.loads(a.extras.read_text())
        for t,v in (d.items() if isinstance(d,dict) else d):
            assign(t,v,'extras')
    missing=sorted(set(keys)-set(candidates))
    fixture={'bound':got['stats']['score'],
      'digest':hashlib.sha256('\n'.join(keys).encode()).hexdigest(),
      'data':[candidates.get(k,None) for k in keys]}
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(base64.b64encode(lzma.compress(json.dumps(fixture,separators=(',',':')).encode(),preset=9)).decode()+'\n')
    status={'parent':got['parent'],'bound':fixture['bound'],'open':len(keys),
      'classified':len(candidates),'missing':len(missing),
      'coverage_sha256':fixture['digest'],
      'kinds':{k:sum(v[0]==k for v in candidates.values()) for k in ['f','n','r','m','d','p','s','c']}
    a.out.with_suffix('.status.json').write_text(json.dumps(status,indent=2)+'\n')
    a.out.with_suffix('.missing.txt').write_text('\n'.join(missing)+'\n')
    print(json.dumps(status),flush=True)
    if missing:raise SystemExit(3)
if __name__=='__main__':main()
