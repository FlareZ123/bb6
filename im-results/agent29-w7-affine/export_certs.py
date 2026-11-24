"""Regenerate Lean JSONL input from the independent affine discovery engine."""
import argparse
import gzip
import json
from pathlib import Path
import shutil
from affine_replay import Engine, N, Q, D, verify, fmt
from stream_entry import StreamEngine, verify_stream

CASES = {
    'N': (N((22,1)), N((38626190,262144)), 1000000),
    'A': ((0,1,(),()), N((508932094,)), 2000000),
    'Q': (Q((14,1)), Q((38101896,262144)), 1000000),
    'D': (D((100,1,0,0),(130,0,1,0),(30,0,0,1)),
          D((454337500,1048576,0,0),(10,0,1,0),(6,0,0,1)), 2000000),
    'E': (D((349479900,1048576),(5759218639205926131,0),(13,0)),
          Q((23036877419765819664,8589934592)), 2000000),
}

def export_case(name, out):
    start, target, limit = CASES[name]
    eng = Engine(start)
    status = eng.run(limit, target, seconds=float('inf'))
    if status != 'target':
        raise RuntimeError((name, status, eng.i, fmt(eng.s)))
    verified = verify(eng, start, target)
    rules, ids = [], {}
    def index(r):
        if r is None:
            return 0
        if r not in ids:
            ops = [index(x) for x in r.ops]
            ids[r] = len(rules)+1
            rules.append([r.sh, r.base, r.delta, r.free, ops])
        return ids[r]
    ops = [index(r) for r in eng.ops]
    with (out / (name+'.jsonl')).open('w', encoding='utf-8') as f:
        for r in rules:
            f.write(json.dumps(['R',*r], separators=(',',':'))+'\n')
        for i in range(0,len(ops),1000):
            f.write(json.dumps(['P',ops[i:i+1000]], separators=(',',':'))+'\n')
    print(name, 'operations',len(ops),'rules',verified,flush=True)

def export_dentry(out):
    start = (3,1,(),())
    target = D((70691118354036414594808423388,),
               (10456559309013950571,), (939468133961604901,))
    path = out / 'Dentry.jsonl.gz'
    with gzip.open(path,'wt',compresslevel=3) as f:
        eng=StreamEngine(start,f)
        final=eng.run(15000000,lambda s:s==target)
    verify_stream(path,start,lambda s:s==target)
    if final != target:
        raise RuntimeError('Dentry endpoint mismatch')
    with gzip.open(path,'rb') as src, (out/'Dentry.jsonl').open('wb') as dst:
        shutil.copyfileobj(src,dst)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, default=Path('.'))
    p.add_argument('names', nargs='*', choices=[*CASES,'Dentry'])
    args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    for name in args.names or [*CASES,'Dentry']:
        if name=='Dentry':export_dentry(args.out)
        else:export_case(name,args.out)
