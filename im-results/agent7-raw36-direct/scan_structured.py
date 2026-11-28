"""Transfer learned regular-stack parameter families to new Raw36 direct leaves.

The parameter seeds come from surviving exact-machine candidates, not from
unchecked inference about neighboring machines. Replay constructs a fresh
finite invariant for the new literal and the Lean kernel remains decisive.
"""
import argparse,base64,gzip,hashlib,json,lzma,sys,time
from multiprocessing import Pool
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parent
R7=ROOT.parent/'agent7-raw36-b1le'
sys.path.insert(0,str(R7))
from stack_candidates import replay

def seeds(limit):
    counts=Counter()
    for p in R7.glob('evidence*.json.xz.b64'):
        try:d=json.loads(lzma.decompress(base64.b64decode(p.read_text())))
        except Exception:continue
        for v in d.get('data',[]):
            if not isinstance(v,list) or not v or v[0] not in ('r','m','p'):continue
            counts[tuple(v[:-1])]+=1
    # High-priority generic motifs absent from the archived seeds.
    for k in (1,2,3,4):
        for cap in (2,3,4,5):
            for modulus in (2,3,4):
                counts[('r',k,cap,modulus)]+=1
    for k in (0,1,2,3):
        for modulus in (2,3,4,5,7,8,9,11,13):
            for base in (2,4):
                counts[('m',k,modulus,base)]+=1
    return [list(p) for p,_ in counts.most_common(limit)],counts

PARAMS=[]
def setup(ps):
    global PARAMS;PARAMS=ps

def test(table):
    p=tuple(table.replace('_','')[i:i+3] for i in range(0,36,3))
    for spec in PARAMS:
        v=[*spec,None]
        try:
            _,n,_,_,_,_=replay(p,v)
            v[-1]=n
            return table,v
        except (AssertionError,IndexError,ValueError,MemoryError,ZeroDivisionError):
            pass
    return table,None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--census',required=True,type=Path)
    ap.add_argument('--far',type=Path);ap.add_argument('--ngram',type=Path)
    ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--limit',type=int,default=60);ap.add_argument('--workers',type=int,default=4)
    a=ap.parse_args();assert 1<=a.limit<=400 and 1<=a.workers<=16
    a.out.mkdir(parents=True,exist_ok=True)
    data=json.loads(gzip.decompress(a.census.read_bytes()))
    keys=set(data['opens'])
    done=set()
    if a.far and a.far.exists():
        done|={l.split()[0] for l in a.far.read_text().splitlines() if l.strip()}
    if a.ngram and a.ngram.exists():
        done|={t for t,v in json.loads(a.ngram.read_text())}
    assert done<=keys
    P,count=seeds(a.limit)
    cases=sorted(keys-done)
    found=[];missing=[];start=time.monotonic()
    with Pool(processes=a.workers,initializer=setup,initargs=(P,)) as pool:
        for t,v in pool.imap_unordered(test,cases,chunksize=1):
            if v:found.append([t,v])
            else:missing.append(t)
    found.sort();missing.sort()
    assert len(found)+len(missing)==len(cases)
    (a.out/'structured.json').write_text(json.dumps(found,separators=(',',':')))
    (a.out/'remaining.txt').write_text('\n'.join(missing)+'\n')
    stat={'parent':data['parent'],'scanned':len(cases),'inherited_done':len(done),
      'seeds':len(P),'hits':len(found),'remaining':len(missing),
      'kinds':{k:sum(v[0]==k for t,v in found) for k in ['r','m','p']},
      'elapsed_sec':round(time.monotonic()-start,3),
      'remaining_sha256':hashlib.sha256('\n'.join(missing).encode()).hexdigest()}
    (a.out/'summary.json').write_text(json.dumps(stat,indent=2)+'\n')
    print(json.dumps(stat),flush=True)
if __name__=='__main__':main()
