"""Search finite inverse-stack certificates on exact direct Raw36 holdouts.

Candidate discovery only: the original Lean TwoSidedAutomata checker must
accept each literal certificate before any Cover/weighted bound is claimed.
"""
import argparse,gzip,hashlib,json,sys,time
from multiprocessing import Pool
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'agent7-raw36-b1le'))
from stack_candidates import replay

def test(job):
    table,kmax=job
    p=tuple(table.replace('_','')[i:i+3] for i in range(0,36,3))
    for k in range(1,kmax+1):
        try:
            _,n,_,_,_,_=replay(p,['n',k,None])
            return [table,['n',k,n]]
        except (AssertionError,ValueError,IndexError,MemoryError):
            pass
    return [table,None]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--census',required=True,type=Path)
    ap.add_argument('--found',type=Path);ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--kmax',type=int,default=5);ap.add_argument('--workers',type=int,default=4)
    a=ap.parse_args();assert 1<=a.kmax<=7 and 1<=a.workers<=16
    a.out.mkdir(parents=True,exist_ok=True)
    got=json.loads(gzip.decompress(a.census.read_bytes()))
    opens=sorted(got['opens']);assert len(opens)==len(set(opens))==got['stats']['open']
    far=set()
    if a.found and a.found.exists():
        far={line.split()[0] for line in a.found.read_text().splitlines() if line.strip()}
    assert far<=set(opens)
    cases=[(t,a.kmax) for t in opens if t not in far]
    hits=[];missing=[];before=time.monotonic()
    with Pool(a.workers) as pool:
        for table,v in pool.imap_unordered(test,cases,chunksize=3):
            if v:hits.append([table,v])
            else:missing.append(table)
    hits.sort();missing.sort()
    assert set(x[0] for x in hits)|set(missing)==set(t for t,_ in cases)
    (a.out/'ngram.json').write_text(json.dumps(hits,separators=(',',':')))
    (a.out/'remaining.txt').write_text('\n'.join(missing)+'\n')
    summary={'parent':got['parent'],'canonical_open':len(opens),'prior_far':len(far),
      'ngram_hits':len(hits),'remaining':len(missing),'kmax':a.kmax,
      'counts':{str(k):sum(v[1][1]==k for v in hits) for k in range(1,a.kmax+1)},
      'elapsed_sec':round(time.monotonic()-before,3),
      'remaining_digest':hashlib.sha256('\n'.join(missing).encode()).hexdigest()}
    (a.out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary),flush=True)
if __name__=='__main__':main()
